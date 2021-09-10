import asyncio
import json
import logging
import time
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple
import traceback

import aiohttp
from blspy import AugSchemeMPL, G1Element, G2Element, PrivateKey

import chives.server.ws_connection as ws  # lgtm [py/import-and-import-from]
from chives.consensus.coinbase import create_puzzlehash_for_pk
from chives.consensus.constants import ConsensusConstants
from chives.protocols import farmer_protocol, harvester_protocol
#from chives.protocols.pool_protocol import (
#    ErrorResponse,
#    get_current_authentication_token,
#    GetFarmerResponse,
#    PoolErrorCode,
#    PostFarmerPayload,
#    PostFarmerRequest,
#    PutFarmerPayload,
#    PutFarmerRequest,
#    AuthenticationPayload,
#)
from chives.protocols.protocol_message_types import ProtocolMessageTypes
from chives.server.outbound_message import NodeType, make_msg
from chives.server.server import ssl_context_for_root
from chives.server.ws_connection import WSChivesConnection
from chives.types.blockchain_format.proof_of_space import ProofOfSpace
from chives.types.blockchain_format.sized_bytes import bytes32
from chives.util.bech32m import decode_puzzle_hash
from chives.util.config import load_config, save_config, config_path_for_filename
from chives.util.hash import std_hash
from chives.util.ints import uint8, uint16, uint32, uint64
from chives.util.keychain import Keychain
from chives.wallet.derive_keys import master_sk_to_farmer_sk, master_sk_to_pool_sk, master_sk_to_wallet_sk
#from chives.wallet.derive_keys import (
#    master_sk_to_farmer_sk,
#    master_sk_to_pool_sk,
#    master_sk_to_wallet_sk,
#    find_authentication_sk,
#    find_owner_sk,
#)
#from chives.wallet.puzzles.singleton_top_layer import SINGLETON_MOD

#singleton_mod_hash = SINGLETON_MOD.get_tree_hash()

log = logging.getLogger(__name__)

UPDATE_HARVESTER_CACHE_INTERVAL: int = 60
UPDATE_POOL_FARMER_INFO_INTERVAL: int = 300

"""
HARVESTER PROTOCOL (FARMER <-> HARVESTER)
"""

class HarvesterCacheEntry:
    def __init__(self):
        self.data: Optional[dict] = None
        self.last_update: float = 0

    def bump_last_update(self):
        self.last_update = time.time()

    def set_data(self, data):
        self.data = data
        self.bump_last_update()

    def needs_update(self):
        return time.time() - self.last_update > UPDATE_HARVESTER_CACHE_INTERVAL

    def expired(self):
        return time.time() - self.last_update > UPDATE_HARVESTER_CACHE_INTERVAL * 10


class Farmer:
    def __init__(
        self,
        root_path: Path,
        farmer_config: Dict,
        pool_config: Dict,
        keychain: Keychain,
        consensus_constants: ConsensusConstants,
    ):
        self._root_path = root_path
        self.config = farmer_config
        # Keep track of all sps, keyed on challenge chain signage point hash
        self.sps: Dict[bytes32, List[farmer_protocol.NewSignagePoint]] = {}

        # Keep track of harvester plot identifier (str), target sp index, and PoSpace for each challenge
        self.proofs_of_space: Dict[bytes32, List[Tuple[str, ProofOfSpace]]] = {}

        # Quality string to plot identifier and challenge_hash, for use with harvester.RequestSignatures
        self.quality_str_to_identifiers: Dict[bytes32, Tuple[str, bytes32, bytes32, bytes32]] = {}

        # number of responses to each signage point
        self.number_of_responses: Dict[bytes32, int] = {}

        # A dictionary of keys to time added. These keys refer to keys in the above 4 dictionaries. This is used
        # to periodically clear the memory
        self.cache_add_time: Dict[bytes32, uint64] = {}

        self.cache_clear_task: asyncio.Task

        self.constants = consensus_constants
        self._shut_down = False
        self.server: Any = None
        self.keychain = keychain
        self.state_changed_callback: Optional[Callable] = None
        self.log = log
        all_sks = self.keychain.get_all_private_keys()
#        self.all_root_sks: List[PrivateKey] = [sk for sk, _ in self.keychain.get_all_private_keys()]
        
        self._private_keys = [master_sk_to_farmer_sk(sk) for sk, _ in all_sks] + [
            master_sk_to_pool_sk(sk) for sk, _ in all_sks

#        self._private_keys = [master_sk_to_farmer_sk(sk) for sk in self.all_root_sks] + [
#            master_sk_to_pool_sk(sk) for sk in self.all_root_sks
        ]

        if len(self.get_public_keys()) == 0:
            error_str = "No keys exist. Please run 'chives keys generate' or open the UI."
            raise RuntimeError(error_str)

        # This is the farmer configuration
        self.farmer_target_encoded = self.config["xcc_target_address"]
        self.farmer_target = decode_puzzle_hash(self.farmer_target_encoded)
        
        self.community_target = self.constants.GENESIS_PRE_FARM_COMMUNITY_PUZZLE_HASH

        self.pool_public_keys = [G1Element.from_bytes(bytes.fromhex(pk)) for pk in self.config["pool_public_keys"]]

        # This is the pool configuration, which should be moved out to the pool once it exists
        self.pool_target_encoded = pool_config["xcc_target_address"]
        self.pool_target = decode_puzzle_hash(self.pool_target_encoded)
        self.pool_sks_map: Dict = {}
        for key in self.get_private_keys():
            self.pool_sks_map[bytes(key.get_g1())] = key

        assert len(self.farmer_target) == 32
        assert len(self.pool_target) == 32
        if len(self.pool_sks_map) == 0:
            error_str = "No keys exist. Please run 'chives keys generate' or open the UI."
            raise RuntimeError(error_str)

        # The variables below are for use with an actual pool

        # From p2_singleton_puzzle_hash to pool state dict
        self.pool_state: Dict[bytes32, Dict] = {}

        # From public key bytes to PrivateKey
        self.authentication_keys: Dict[bytes, PrivateKey] = {}

        # Last time we updated pool_state based on the config file
        self.last_config_access_time: uint64 = uint64(0)

        self.harvester_cache: Dict[str, Dict[str, HarvesterCacheEntry]] = {}

    async def _start(self):

        self.cache_clear_task = asyncio.create_task(self._periodically_clear_cache_and_refresh_task())

    def _close(self):
        self._shut_down = True

    async def _await_closed(self):
        await self.cache_clear_task


    def _set_state_changed_callback(self, callback: Callable):
        self.state_changed_callback = callback

    async def on_connect(self, peer: WSChivesConnection):
        # Sends a handshake to the harvester
        self.state_changed("add_connection", {})
        handshake = harvester_protocol.HarvesterHandshake(
            self.get_public_keys(),
            self.pool_public_keys,
        )
        if peer.connection_type is NodeType.HARVESTER:
            msg = make_msg(ProtocolMessageTypes.harvester_handshake, handshake)
            await peer.send_message(msg)

    def set_server(self, server):
        self.server = server

    def state_changed(self, change: str, data: Dict[str, Any]):
        if self.state_changed_callback is not None:
            self.state_changed_callback(change, data)

    def on_disconnect(self, connection: ws.WSChivesConnection):
        self.log.info(f"peer disconnected {connection.get_peer_info()}")
        self.state_changed("close_connection", {})

    def get_public_keys(self):
        return [child_sk.get_g1() for child_sk in self._private_keys]

    def get_private_keys(self):
        return self._private_keys

    def get_reward_targets(self, search_for_private_key: bool) -> Dict:
        if search_for_private_key:
            all_sks = self.keychain.get_all_private_keys()
            stop_searching_for_farmer, stop_searching_for_pool = False, False
            for i in range(500):
                if stop_searching_for_farmer and stop_searching_for_pool and i > 0:
                    break
                for sk, _ in all_sks:
                    ph = create_puzzlehash_for_pk(master_sk_to_wallet_sk(sk, uint32(i)).get_g1())

                    if ph == self.farmer_target:
                        stop_searching_for_farmer = True
                    if ph == self.pool_target:
                        stop_searching_for_pool = True
            return {
                "farmer_target": self.farmer_target_encoded,
                "pool_target": self.pool_target_encoded,
                "have_farmer_sk": stop_searching_for_farmer,
                "have_pool_sk": stop_searching_for_pool,
            }
        return {
            "farmer_target": self.farmer_target_encoded,
            "pool_target": self.pool_target_encoded,
        }

    def set_reward_targets(self, farmer_target_encoded: Optional[str], pool_target_encoded: Optional[str]):
        config = load_config(self._root_path, "config.yaml")
        if farmer_target_encoded is not None:
            self.farmer_target_encoded = farmer_target_encoded
            self.farmer_target = decode_puzzle_hash(farmer_target_encoded)
            config["farmer"]["xcc_target_address"] = farmer_target_encoded
        if pool_target_encoded is not None:
            self.pool_target_encoded = pool_target_encoded
            self.pool_target = decode_puzzle_hash(pool_target_encoded)
            config["pool"]["xcc_target_address"] = pool_target_encoded
        save_config(self._root_path, "config.yaml", config)

    async def _periodically_clear_cache_and_refresh_task(self):
        time_slept: uint64 = uint64(0)
        refresh_slept = 0
        while not self._shut_down:
            if time_slept > self.constants.SUB_SLOT_TIME_TARGET:
                now = time.time()
                removed_keys: List[bytes32] = []
                for key, add_time in self.cache_add_time.items():
                    if now - float(add_time) > self.constants.SUB_SLOT_TIME_TARGET * 3:
                        self.sps.pop(key, None)
                        self.proofs_of_space.pop(key, None)
                        self.quality_str_to_identifiers.pop(key, None)
                        self.number_of_responses.pop(key, None)
                        removed_keys.append(key)
                for key in removed_keys:
                    self.cache_add_time.pop(key, None)
                time_slept = uint64(0)
                log.debug(
                    f"Cleared farmer cache. Num sps: {len(self.sps)} {len(self.proofs_of_space)} "
                    f"{len(self.quality_str_to_identifiers)} {len(self.number_of_responses)}"
                )
            time_slept += 1
            refresh_slept += 1
            # Periodically refresh GUI to show the correct download/upload rate.
            if refresh_slept >= 30:
                self.state_changed("add_connection", {})
                refresh_slept = 0
            await asyncio.sleep(1)

    async def update_cached_harvesters(self) -> bool:
        # First remove outdated cache entries
        self.log.debug(f"update_cached_harvesters cache entries: {len(self.harvester_cache)}")
        remove_hosts = []
        for host, host_cache in self.harvester_cache.items():
            remove_peers = []
            for peer_id, peer_cache in host_cache.items():
                # If the peer cache is expired it means the harvester didn't respond for too long
                if peer_cache.expired():
                    remove_peers.append(peer_id)
            for key in remove_peers:
                del host_cache[key]
            if len(host_cache) == 0:
                self.log.debug(f"update_cached_harvesters remove host: {host}")
                remove_hosts.append(host)
        for key in remove_hosts:
            del self.harvester_cache[key]
        # Now query each harvester and update caches
        updated = False
        for connection in self.server.get_connections(NodeType.HARVESTER):
            cache_entry = await self.get_cached_harvesters(connection)
            if cache_entry.needs_update():
                self.log.debug(f"update_cached_harvesters update harvester: {connection.peer_node_id}")
                cache_entry.bump_last_update()
                response = await connection.request_plots(
                    harvester_protocol.RequestPlots(), timeout=UPDATE_HARVESTER_CACHE_INTERVAL
                )
                if response is not None:
                    if isinstance(response, harvester_protocol.RespondPlots):
                        new_data: Dict = response.to_json_dict()
                        if cache_entry.data != new_data:
                            updated = True
                            self.log.debug(f"update_cached_harvesters cache updated: {connection.peer_node_id}")
                        else:
                            self.log.debug(f"update_cached_harvesters no changes for: {connection.peer_node_id}")
                        cache_entry.set_data(new_data)
                    else:
                        self.log.error(
                            f"Invalid response from harvester:"
                            f"peer_host {connection.peer_host}, peer_node_id {connection.peer_node_id}"
                        )
                else:
                    self.log.error(
                        "Harvester did not respond. You might need to update harvester to the latest version"
                    )
        return updated

    async def get_cached_harvesters(self, connection: WSChivesConnection) -> HarvesterCacheEntry:
        host_cache = self.harvester_cache.get(connection.peer_host)
        if host_cache is None:
            host_cache = {}
            self.harvester_cache[connection.peer_host] = host_cache
        node_cache = host_cache.get(connection.peer_node_id.hex())
        if node_cache is None:
            node_cache = HarvesterCacheEntry()
            host_cache[connection.peer_node_id.hex()] = node_cache
        return node_cache

    async def get_harvesters(self) -> Dict:
        harvesters: List = []
        for connection in self.server.get_connections(NodeType.HARVESTER):
            self.log.debug(f"get_harvesters host: {connection.peer_host}, node_id: {connection.peer_node_id}")
            cache_entry = await self.get_cached_harvesters(connection)
            if cache_entry.data is not None:
                harvester_object: dict = dict(cache_entry.data)
                harvester_object["connection"] = {
                    "node_id": connection.peer_node_id.hex(),
                    "host": connection.peer_host,
                    "port": connection.peer_port,
                }
                harvesters.append(harvester_object)
            else:
                self.log.debug(f"get_harvesters no cache: {connection.peer_host}, node_id: {connection.peer_node_id}")

            #if connection.connection_type != NodeType.HARVESTER:
            #    continue

            #cache_entry = await self.get_cached_harvesters(connection)
            #if cache_entry is not None:
            #    harvester_object: dict = dict(cache_entry[0])
            #    harvester_object["connection"] = {
            #        "node_id": connection.peer_node_id.hex(),
            #        "host": connection.peer_host,
            #        "port": connection.peer_port,
            #    }
            #    harvesters.append(harvester_object)

        return {"harvesters": harvesters}

    async def _periodically_clear_cache_and_refresh_task(self):
        time_slept: uint64 = uint64(0)
        refresh_slept = 0
        while not self._shut_down:
            try:
                if time_slept > self.constants.SUB_SLOT_TIME_TARGET:
                    now = time.time()
                    removed_keys: List[bytes32] = []
                    for key, add_time in self.cache_add_time.items():
                        if now - float(add_time) > self.constants.SUB_SLOT_TIME_TARGET * 3:
                            self.sps.pop(key, None)
                            self.proofs_of_space.pop(key, None)
                            self.quality_str_to_identifiers.pop(key, None)
                            self.number_of_responses.pop(key, None)
                            removed_keys.append(key)
                    for key in removed_keys:
                        self.cache_add_time.pop(key, None)
                    time_slept = uint64(0)
                    log.debug(
                        f"Cleared farmer cache. Num sps: {len(self.sps)} {len(self.proofs_of_space)} "
                        f"{len(self.quality_str_to_identifiers)} {len(self.number_of_responses)}"
                    )
                time_slept += 1
                refresh_slept += 1
                # Periodically refresh GUI to show the correct download/upload rate.
                if refresh_slept >= 30:
                    self.state_changed("add_connection", {})
                    refresh_slept = 0

                # Handles harvester plots cache cleanup and updates
                if await self.update_cached_harvesters():
                    self.state_changed("new_plots", await self.get_harvesters())
            except Exception:
                log.error(f"_periodically_clear_cache_and_refresh_task failed: {traceback.print_exc()}")

            await asyncio.sleep(1)