#!/usr/bin/env python3
"""Compare ordered transactions and committed slots on three real runtimes.

The original checked host Core contract is independent of Rust Hull. The EVM
path mines transactions and reads their actual trace output and receipt-block
storage. No Python state transition or saved expected value is an oracle.
The keyed, dynamic-array and log profiles declare their observed slots in the
case and additionally require the Hull and EVM paths to show no nonzero
committed slot outside them. The log profile also compares the ordered
committed logs of every transaction: decoded original-Core journals, Hull
receipt logs and mined receipt logs, plus the EVM chain's complete log list.
The call-value profile sends value with each transaction and also compares the
contract's committed balance; the sender's balance is never observed.
Every profile also compares the contract's whole committed storage after
deployment and after every transaction: original Core enumerates its account,
Hull canonicalizes its committed entries, and the EVM rereads every slot the
prestate diffs reported (`check-evm-storage-diff.py` verifies that method).
With `--backend yul`, the EVM path runs the checked Rust driver's Yul through
the pinned solc, and imported Hull keeps Sonatina O0 images, as for the pure
profiles; `pathBackends` records each path's backend.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import math
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
import urllib.error

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("semantic_common", ROOT / "scripts/semantic-differential.py")
common = importlib.util.module_from_spec(spec)
spec.loader.exec_module(common)
CASE_SCHEMA = "solcore-lean.semantic-storage-case.v1"
ROLLBACK_CASE_SCHEMA = "solcore-lean.semantic-storage-rollback-case.v1"
KEYED_CASE_SCHEMA = "solcore-lean.semantic-keyed-storage-case.v1"
HISTORY_SCHEMA = "solcore-lean.storage-history.v2"
KEYED_HISTORY_SCHEMA = "solcore-lean.keyed-storage-history.v2"
ARRAY_CASE_SCHEMA = "solcore-lean.semantic-dynamic-array-case.v1"
ARRAY_HISTORY_SCHEMA = "solcore-lean.dynamic-array-history.v2"
LOG_CASE_SCHEMA = "solcore-lean.semantic-log-case.v1"
LOG_HISTORY_SCHEMA = "solcore-lean.log-history.v2"
VALUE_CASE_SCHEMA = "solcore-lean.semantic-call-value-case.v1"
VALUE_HISTORY_SCHEMA = "solcore-lean.call-value-history.v2"
BYTES_CASE_SCHEMA = "solcore-lean.semantic-bytes-case.v1"
BYTES_HISTORY_SCHEMA = "solcore-lean.bytes-history.v2"
LONG_BYTES_CASE_SCHEMA = "solcore-lean.semantic-long-bytes-case.v1"
LONG_BYTES_HISTORY_SCHEMA = "solcore-lean.long-bytes-history.v2"
NESTED_CASE_SCHEMA = "solcore-lean.semantic-nested-array-case.v1"
NESTED_HISTORY_SCHEMA = "solcore-lean.nested-array-history.v2"
MAPPING_CASE_SCHEMA = "solcore-lean.semantic-mapping-case.v1"
MAPPING_HISTORY_SCHEMA = "solcore-lean.mapping-history.v2"
LEDGER_CASE_SCHEMA = "solcore-lean.semantic-ledger-case.v1"
LEDGER_HISTORY_SCHEMA = "solcore-lean.ledger-history.v2"
MALFORMED_CASE_SCHEMA = "solcore-lean.semantic-malformed-calldata-case.v1"
MALFORMED_HISTORY_SCHEMA = "solcore-lean.malformed-calldata-history.v1"
MALFORMED_NESTED_CASE_SCHEMA = "solcore-lean.semantic-malformed-nested-array-case.v1"
MALFORMED_NESTED_HISTORY_SCHEMA = "solcore-lean.malformed-nested-array-history.v1"
MALFORMED_BYTES_CASE_SCHEMA = "solcore-lean.semantic-malformed-bytes-case.v1"
MALFORMED_BYTES_HISTORY_SCHEMA = "solcore-lean.malformed-bytes-history.v1"
METHODS_CASE_SCHEMA = "solcore-lean.semantic-methods-case.v1"
METHODS_HISTORY_SCHEMA = "solcore-lean.methods-history.v1"
LOOP_CASE_SCHEMA = "solcore-lean.semantic-storage-loop-case.v1"
LOOP_HISTORY_SCHEMA = "solcore-lean.storage-loop-history.v1"
KECCAK_LOOP_CASE_SCHEMA = "solcore-lean.semantic-keccak-loop-case.v1"
KECCAK_LOOP_HISTORY_SCHEMA = "solcore-lean.keccak-loop-history.v1"
TUPLE_CASE_SCHEMA = "solcore-lean.semantic-tuple-return-case.v1"
TUPLE_HISTORY_SCHEMA = "solcore-lean.tuple-return-history.v1"
# `declared`: per-case observed slots plus Hull/EVM containment; `abi`: calldata form;
# `logs`: ordered committed logs are part of every observation; `balances`: transactions
# carry call value and the contract's committed balance is observed; `deploymentLogs`:
# the deployment receipt must carry no logs even when transactions' logs are not compared;
# `senders`: each transaction names one of LEDGER_SENDERS, which sends it on every path.
# `encoding`: the canonical calldata a malformed-calldata profile changes, `array` by default.
_TWO_SLOT = {"planKey": "storagePlan", "keyed": False, "declared": False, "abi": "word",
    "signature": "run(uint256)", "selector": "0xa444f5e9",
    "historySchema": HISTORY_SCHEMA, "coreRunner": "rust-hull-storage-scenario",
    "scenarioSchema": "solcore-lean.storage-contract-scenario.v1"}
PROFILES = {
    "stateful-storage": {**_TWO_SLOT, "caseSchema": CASE_SCHEMA, "planSchema": "solcore-lean.storage-plan.v1",
        "corpusSchema": "solcore-lean.semantic-storage-corpus.v1", "originKind": "storage-generated",
        "contract": "SynthesizedStorage", "caseTool": "semantic-storage-tool", "rollback": False},
    "stateful-storage-rollback": {**_TWO_SLOT, "caseSchema": ROLLBACK_CASE_SCHEMA,
        "planSchema": "solcore-lean.storage-rollback-plan.v1",
        "corpusSchema": "solcore-lean.semantic-storage-rollback-corpus.v1", "originKind": "storage-rollback-generated",
        "contract": "SynthesizedRollback", "caseTool": "semantic-storage-rollback-tool", "rollback": True},
    "stateful-keyed-storage": {"caseSchema": KEYED_CASE_SCHEMA, "planSchema": "solcore-lean.keyed-storage-plan.v1",
        "planKey": "keyedStoragePlan", "corpusSchema": "solcore-lean.semantic-keyed-storage-corpus.v1",
        "originKind": "keyed-storage-generated", "contract": "SynthesizedKeyedStorage",
        "caseTool": "semantic-keyed-storage-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": KEYED_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256)", "selector": "0x7357f5d2", "rollback": True, "keyed": True,
        "declared": True, "abi": "keyed"},
    "stateful-dynamic-array": {"caseSchema": ARRAY_CASE_SCHEMA, "planSchema": "solcore-lean.dynamic-array-plan.v1",
        "planKey": "dynamicArrayPlan", "corpusSchema": "solcore-lean.semantic-dynamic-array-corpus.v1",
        "originKind": "dynamic-array-generated", "contract": "SynthesizedDynamicArray",
        "caseTool": "semantic-dynamic-array-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": ARRAY_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256[])", "selector": "0x9a94c44b", "rollback": True, "keyed": False,
        "declared": True, "abi": "array"},
    "stateful-logs": {"caseSchema": LOG_CASE_SCHEMA, "planSchema": "solcore-lean.log-plan.v1",
        "planKey": "logPlan", "corpusSchema": "solcore-lean.semantic-log-corpus.v1",
        "originKind": "log-generated", "contract": "SynthesizedLogs",
        "caseTool": "semantic-log-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": LOG_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256)", "selector": "0x7357f5d2", "rollback": True, "keyed": False,
        "declared": True, "abi": "flags", "logs": True},
    "stateful-call-value": {"caseSchema": VALUE_CASE_SCHEMA, "planSchema": "solcore-lean.call-value-plan.v1",
        "planKey": "callValuePlan", "corpusSchema": "solcore-lean.semantic-call-value-corpus.v1",
        "originKind": "call-value-generated", "contract": "SynthesizedCallValue",
        "caseTool": "semantic-call-value-tool", "coreRunner": "rust-hull-value-scenario",
        "scenarioSchema": "solcore-lean.value-contract-scenario.v1", "historySchema": VALUE_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256)", "selector": "0x7357f5d2", "rollback": True, "keyed": False,
        "declared": True, "abi": "value", "balances": True, "deploymentLogs": True},
    "stateful-bytes": {"caseSchema": BYTES_CASE_SCHEMA, "planSchema": "solcore-lean.bytes-plan.v1",
        "planKey": "bytesPlan", "corpusSchema": "solcore-lean.semantic-bytes-corpus.v1",
        "originKind": "bytes-generated", "contract": "SynthesizedBytes",
        "caseTool": "semantic-bytes-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": BYTES_HISTORY_SCHEMA,
        "signature": "run(uint256,bytes)", "selector": "0x220eb9b6", "rollback": True, "keyed": False,
        "declared": True, "abi": "bytes"},
    # The bytes protocol over eight chunks: `maxPayload`, the observed `slots` and
    # the `countSlot`/`tailSlot` names replace the bytes profile's defaults. A case
    # reaches about 75 KB, so a native shrink response carries at most 32 candidates.
    "stateful-long-bytes": {"caseSchema": LONG_BYTES_CASE_SCHEMA, "planSchema": "solcore-lean.long-bytes-plan.v1",
        "planKey": "longBytesPlan", "corpusSchema": "solcore-lean.semantic-long-bytes-corpus.v1",
        "originKind": "long-bytes-generated", "contract": "SynthesizedLongBytes",
        "caseTool": "semantic-long-bytes-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": LONG_BYTES_HISTORY_SCHEMA,
        "signature": "run(uint256,bytes)", "selector": "0x220eb9b6", "rollback": True, "keyed": False,
        "declared": True, "abi": "bytes", "maxPayload": 256, "slots": [str(slot) for slot in range(11)],
        "countSlot": "9", "tailSlot": "10", "shrinkBatch": 16},
    # One mapping case embeds the fixed Keccak closure (about 110 KB of Core),
    # so each bounded native shrink response carries at most 16 candidates.
    "stateful-mapping": {"caseSchema": MAPPING_CASE_SCHEMA, "planSchema": "solcore-lean.mapping-plan.v1",
        "planKey": "mappingPlan", "corpusSchema": "solcore-lean.semantic-mapping-corpus.v1",
        "originKind": "mapping-generated", "contract": "SynthesizedMapping",
        "caseTool": "semantic-mapping-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": MAPPING_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256,uint256)", "selector": "0x24b912e5", "rollback": True, "keyed": False,
        "declared": True, "abi": "mapping", "shrinkBatch": 16},
    # The ledger embeds the same closure, so it keeps the mapping's bounded batch.
    "stateful-ledger": {"caseSchema": LEDGER_CASE_SCHEMA, "planSchema": "solcore-lean.ledger-plan.v1",
        "planKey": "ledgerPlan", "corpusSchema": "solcore-lean.semantic-ledger-corpus.v1",
        "originKind": "ledger-generated", "contract": "SynthesizedLedger",
        "caseTool": "semantic-ledger-tool", "coreRunner": "rust-hull-ledger-scenario",
        "scenarioSchema": "solcore-lean.ledger-contract-scenario.v1", "historySchema": LEDGER_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256,uint256,uint256)", "selector": "0x15509d2b", "rollback": True, "keyed": False,
        "declared": True, "abi": "ledger", "senders": True, "shrinkBatch": 16},
    # One bounded uint256[][] input in the canonical nested head/tail encoding. A
    # case reaches about 70 KB, so a native shrink response carries at most 32 candidates.
    "stateful-nested-array": {"caseSchema": NESTED_CASE_SCHEMA, "planSchema": "solcore-lean.nested-array-plan.v1",
        "planKey": "nestedArrayPlan", "corpusSchema": "solcore-lean.semantic-nested-array-corpus.v1",
        "originKind": "nested-array-generated", "contract": "SynthesizedNestedArray",
        "caseTool": "semantic-nested-array-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": NESTED_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256[][])", "selector": "0x7095aff8", "rollback": True, "keyed": False,
        "declared": True, "abi": "nested", "shrinkBatch": 16},
    # The dynamic-array contract under malformed calldata. Original Core models
    # std's dispatcher and decoder; a std rejection is compared by its selector.
    "stateful-malformed-calldata": {"caseSchema": MALFORMED_CASE_SCHEMA, "planSchema": "solcore-lean.malformed-calldata-plan.v1",
        "planKey": "malformedCalldataPlan", "corpusSchema": "solcore-lean.semantic-malformed-calldata-corpus.v1",
        "originKind": "malformed-calldata-generated", "contract": "SynthesizedDynamicArray",
        "caseTool": "semantic-malformed-calldata-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": MALFORMED_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256[])", "selector": "0x9a94c44b", "rollback": True, "keyed": False,
        "declared": True, "abi": "malformed"},
    # The nested-array contract under malformed calldata, with std's lazy row
    # checks; cases reach about 80 KB.
    "stateful-malformed-nested-array": {"caseSchema": MALFORMED_NESTED_CASE_SCHEMA,
        "planSchema": "solcore-lean.malformed-nested-array-plan.v1", "planKey": "malformedNestedArrayPlan",
        "corpusSchema": "solcore-lean.semantic-malformed-nested-array-corpus.v1",
        "originKind": "malformed-nested-array-generated", "contract": "SynthesizedNestedArray",
        "caseTool": "semantic-malformed-nested-array-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": MALFORMED_NESTED_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256[][])", "selector": "0x7095aff8", "rollback": True, "keyed": False,
        "declared": True, "abi": "malformed", "encoding": "nested", "shrinkBatch": 16},
    # The long-bytes contract under malformed calldata, with std's payload
    # check and unread padding; cases reach about 80 KB.
    "stateful-malformed-bytes": {"caseSchema": MALFORMED_BYTES_CASE_SCHEMA,
        "planSchema": "solcore-lean.malformed-bytes-plan.v1", "planKey": "malformedBytesPlan",
        "corpusSchema": "solcore-lean.semantic-malformed-bytes-corpus.v1",
        "originKind": "malformed-bytes-generated", "contract": "SynthesizedLongBytes",
        "caseTool": "semantic-malformed-bytes-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": MALFORMED_BYTES_HISTORY_SCHEMA,
        "signature": "run(uint256,bytes)", "selector": "0x220eb9b6", "rollback": True, "keyed": False,
        "declared": True, "abi": "malformed", "encoding": "bytes", "maxPayload": 256,
        "slots": [str(slot) for slot in range(11)], "countSlot": "9", "tailSlot": "10", "shrinkBatch": 16},
    # One contract with two to four external methods over shared slots. Each
    # case records its methods; a missing selector is compared by std's selector.
    "stateful-methods": {"caseSchema": METHODS_CASE_SCHEMA, "planSchema": "solcore-lean.methods-plan.v1",
        "planKey": "methodsPlan", "corpusSchema": "solcore-lean.semantic-methods-corpus.v1",
        "originKind": "methods-generated", "contract": "SynthesizedMethods",
        "caseTool": "semantic-methods-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": METHODS_HISTORY_SCHEMA,
        "signature": None, "selector": None, "rollback": True, "keyed": False,
        "declared": True, "abi": "methods", "shrinkBatch": 16},
    # A bounded source while loop whose iterations read and write declared slots;
    # each transaction runs its input's bits under the plan's mask. A case reaches
    # about 70 KB, so a native shrink response carries at most 32 candidates.
    "stateful-storage-loops": {"caseSchema": LOOP_CASE_SCHEMA, "planSchema": "solcore-lean.storage-loop-plan.v1",
        "planKey": "storageLoopPlan", "corpusSchema": "solcore-lean.semantic-storage-loop-corpus.v1",
        "originKind": "storage-loop-generated", "contract": "SynthesizedStorageLoops",
        "caseTool": "semantic-storage-loop-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": LOOP_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256)", "selector": "0x7357f5d2", "rollback": True, "keyed": False,
        "declared": True, "abi": "loops", "shrinkBatch": 32},
    # The storage-loop protocol over Keccak-addressed std mapping entries, with
    # one log2 per iteration. A case embeds the mapping's Keccak closure, so a
    # native shrink response carries at most 16 candidates.
    "stateful-keccak-loops": {"caseSchema": KECCAK_LOOP_CASE_SCHEMA, "planSchema": "solcore-lean.keccak-loop-plan.v1",
        "planKey": "keccakLoopPlan", "corpusSchema": "solcore-lean.semantic-keccak-loop-corpus.v1",
        "originKind": "keccak-loop-generated", "contract": "SynthesizedKeccakLoops",
        "caseTool": "semantic-keccak-loop-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": KECCAK_LOOP_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256)", "selector": "0x7357f5d2", "rollback": True, "keyed": False,
        "declared": True, "abi": "keccak-loops", "logs": True, "shrinkBatch": 16},
    # One method that returns a static tuple of two to four Words; every path's
    # whole return data is compared. A case reaches about 60 KB, so a native
    # shrink response carries at most 32 candidates.
    "stateful-tuple-returns": {"caseSchema": TUPLE_CASE_SCHEMA, "planSchema": "solcore-lean.tuple-return-plan.v1",
        "planKey": "tupleReturnPlan", "corpusSchema": "solcore-lean.semantic-tuple-return-corpus.v1",
        "originKind": "tuple-return-generated", "contract": "SynthesizedTupleReturns",
        "caseTool": "semantic-tuple-return-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": TUPLE_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256)", "selector": "0x7357f5d2", "rollback": True, "keyed": False,
        "declared": True, "abi": "tuples", "shrinkBatch": 32},
}
HISTORY_SCHEMAS = {value["historySchema"] for value in PROFILES.values()}
REPORT_SCHEMA = "solcore-lean.semantic-storage-differential.v2"
PATHS = ("directCore", "importedHull", "rustEvm")
CONTAINMENT_PATHS = ("importedHull", "rustEvm")
SLOTS = ("0", "1")
COUNTER_SLOT = "0"
MAX_UNDECLARED_SLOTS = 256
# Whole committed storage: the observed contract's role and a bound on listed
# entries per account.
CONTRACT_ROLE = "contract"
MAX_ACCOUNT_SLOTS = 1024
# A scenario has one to eight ordered transactions; generation keeps three unless
# a longer random sequence is requested, and the fixed corpora keep one to three.
MAX_TRANSACTIONS = 8
ARRAY_SLOTS = ["0", "1", "2", "3", "4"]
MAX_ELEMENTS = 3
# Nested values have at most three rows of at most two elements. Slot 1 + 2i + j
# holds element (i, j)'s result, slot seven the row count, slot eight the element count.
NESTED_SLOTS = [str(slot) for slot in range(9)]
MAX_ROWS, MAX_COLUMNS = 3, 2
ROW_SLOT, CELL_SLOT = "7", "8"
LOG_SLOTS = ["0", "1"]
MAX_SITES, MAX_TOPICS, MAX_DATA_WORDS = 3, 4, 2
MAX_LOGS = 64
VALUE_SLOTS = ["0", "1"]
# Every value, including the deployment value, and a scenario's total stay
# within the funded local sender; original Core and Hull fund the caller with 2^80.
MAX_VALUE, MAX_TOTAL, CALLER_FUNDS = 2**70, 2**72, 2**80
BYTES_SLOTS = ["0", "1", "2", "3", "4"]
MAX_PAYLOAD = 64
# The longest payload any bytes profile admits; each profile checks its own bound.
MAX_PAYLOAD_BOUND = 256
# The mapping profile's counter slot and the mapping field's base slot.
MAPPING_COUNTER, MAPPING_BASE = 0, 1
# The malformed-calldata profile. Its original Core contract reverts with one of
# std's error selectors as a Word exactly where the pinned std's dispatcher or
# decoder rejects: `NoSelectorMatchedWithoutFallback()` and `ABIInputTruncated()`.
# `ArrayOutOfBounds()` and `NonPayableReceivedValue()` cannot arise there.
STD_NO_SELECTOR, STD_TRUNCATED = "0x4924aef0", "0x08638556"
STD_ERRORS = (STD_NO_SELECTOR, STD_TRUNCATED)
MAX_CALLDATA = 1024
MALFORMATION_KINDS = ("none", "short", "selector", "truncate", "trailing", "offset", "length")
TRAILING_PATTERNS = ("zeros", "ones", "ramp")
# std's bound on a 32-byte-element length, ~0 / 32.
MAX_ARRAY_LENGTH = 2**251 - 1
# Malformed nested values have at most four rows of at most three elements; the
# body reads at most three rows of two. Row malformations replace a row's table
# Word or its length Word. The canonical offset table starts at byte 100.
NESTED_MALFORMATION_KINDS = MALFORMATION_KINDS + ("row-offset", "row-length")
MALFORMED_MAX_ROWS, MALFORMED_MAX_COLUMNS, READ_ROWS = 4, 3, 3
TABLE_START = 100
# Malformed bytes add nonzero padding after a payload that does not fill its
# last Word. std bounds a decoded `bytes` length by ~0 - 63.
BYTES_MALFORMATION_KINDS = MALFORMATION_KINDS + ("padding",)
PADDING_PATTERNS = ("ones", "ramp", "last-byte")
MAX_BYTES_LENGTH = 2**256 - 64
# The several-methods profile: slot 0 the shared accumulator, slot 1 the shared
# call count, slot 2 + i method i's accumulator; methods `m_` and eight hex
# digits with at most two uint256 parameters.
METHODS_SLOTS = [str(slot) for slot in range(6)]
MIN_METHODS, MAX_METHODS, MAX_METHOD_ARITY = 2, 4, 2
METHOD_NAME = re.compile(r"m_[0-9a-f]{8}")
SELECTOR_ORDERS = ("ascending", "descending", "mixed")
# The storage-loop profile: slot 0 the accumulator, slot 1 the committed
# iteration total, slot 2 + i iteration i's result; plans admit these masks.
LOOP_SLOTS = [str(slot) for slot in range(9)]
LOOP_MASKS = (0, 1, 3, 7)
# The tuple-return profile: slot 0 the accumulator, slot 1 the committed call
# count, slot 2 the last committed input; plans return two to four Words.
TUPLE_SLOTS = [str(slot) for slot in range(3)]
TUPLE_ARITIES = (2, 3, 4)
# The ledger's fixed senders: Anvil's first three default accounts, in order; the first deploys.
LEDGER_SENDERS = (str(0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266), str(0x70997970C51812dc3A010C7d01b50e0d17dc79C8),
                  str(0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC))
# Ethereum Keccak-256, written from the Keccak reference for the slot check; the
# lane at index x + 5y has rotation KECCAK_ROTATIONS[x + 5y].
KECCAK_ROUND_CONSTANTS = (
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008)
KECCAK_ROTATIONS = (0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14)
RESOURCE_STATUSES = {"out-of-fuel", "out-of-gas", "timeout", "resource-limit", "output-limit"}
Finding, RpcError = common.Finding, common.RpcError


def save(path: Path, value) -> None:
    path.write_bytes(common.json_bytes(value))


def profile(case: dict) -> dict:
    if isinstance(case, dict):
        for value in PROFILES.values():
            if case.get("schema") == value["caseSchema"]:
                return value
    raise ValueError("unsupported storage case schema")


def expected_status(case: dict, transaction: dict) -> str | None:
    """The profile fixes completion polarity, not the returned value or world.
    A ledger's even flags may still revert for an insufficient balance, so only
    its odd flags fix a status; `ledger_fields` checks the rest. A std rejection
    of malformed calldata reverts whatever the flags."""
    if profile(case)["abi"] in ("malformed", "methods") and transaction.get("stdRejection") is not None:
        return "reverted"
    if profile(case)["abi"] == "methods":
        # A call's odd input sum reverts.
        return "reverted" if sum(int(common.word(value)) for value in transaction["inputs"]) % 2 else "returned"
    if profile(case)["abi"] == "keccak-loops":
        # Odd flags revert after every logged iteration.
        return "reverted" if int(common.word(transaction["flags"])) % 2 else "returned"
    parity = transaction["flags" if profile(case)["abi"] in ("array", "nested", "flags", "value", "bytes", "mapping", "ledger",
                                                             "malformed", "loops", "tuples") else "input"]
    odd = int(common.word(parity)) % 2
    if has_senders(case) and not odd:
        return None
    return "reverted" if profile(case)["rollback"] and odd else "returned"


def has_senders(case: dict) -> bool:
    return profile(case).get("senders", False)


def has_loops(case: dict) -> bool:
    return profile(case)["abi"] == "loops"


def loop_iterations(case: dict, transaction: dict) -> int:
    """The iterations a transaction runs: its input's bits under the plan's mask."""
    return int(common.word(transaction.get("input"), "transaction input")) & case[profile(case)["planKey"]]["mask"]


def has_keccak_loops(case: dict) -> bool:
    return profile(case)["abi"] == "keccak-loops"


def keccak_loop_keys(case: dict, transaction: dict) -> list[int]:
    """The keys of a transaction's iterations: the input's high bits and the
    counter's bits under the plan's key mask."""
    base = int(common.word(transaction.get("input"), "transaction input")) & (2**256 - 8)
    return [base | (index & case["keccakLoopPlan"]["keyMask"]) for index in range(loop_iterations(case, transaction))]


def keccak_loop_slots(case: dict) -> list[str]:
    """The Keccak-loop protocol's complete write set: slot zero and the entry
    slot of every key the transactions address, in increasing numeric order."""
    values = {0}
    for tx in case["transactions"]:
        values.update(entry_slot(key) for key in keccak_loop_keys(case, tx))
    return [str(value) for value in sorted(values)]


def keccak_loop_fields(case: dict, transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a returned row that break the Keccak-loop protocol: log `i`
    has the topics `i` and its key and one data Word, slot zero is the last
    log's data (unchanged without iterations), each addressed entry holds the
    data of the last log with its key and every other observed slot is
    unchanged, and the output is slot zero plus the iteration count. A revert
    is checked by rollback and the log shapes."""
    if row["status"] != "returned":
        return []
    keys = keccak_loop_keys(case, transaction)
    data = [common.hex_bytes(log["data"], "log data") for log in row["logs"]]
    fields = []
    if [log["topics"] for log in row["logs"]] != [[str(index), str(key)] for index, key in enumerate(keys)] or \
            any(len(value) != 32 for value in data):
        fields.append("logs")
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    expected = {entry["slot"]: int(entry["value"]) for entry in prior}
    if not fields:
        for key, value in zip(keys, data):
            expected[str(entry_slot(key))] = expected["0"] = int.from_bytes(value, "big")
        if after != expected:
            fields.append("committedStorage")
    if int.from_bytes(common.hex_bytes(row["output"], "output"), "big") != (after["0"] + len(keys)) % 2**256:
        fields.append("output")
    return fields


def loop_fields(case: dict, transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a returned row that break the loop protocol: slot one grows by
    the iteration count, slot zero is the last iteration's slot (unchanged
    without iterations), the slots above the last iteration are unchanged, and
    the output is slot zero plus slot one. A revert is checked by rollback."""
    if row["status"] != "returned":
        return []
    count = loop_iterations(case, transaction)
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    before = {entry["slot"]: int(entry["value"]) for entry in prior}
    fields = []
    if after["1"] != (before["1"] + count) % 2**256 or after["0"] != (after[str(1 + count)] if count else before["0"]) or \
            any(after[slot] != before[slot] for slot in LOOP_SLOTS[2 + count:]):
        fields.append("committedStorage")
    if int.from_bytes(common.hex_bytes(row["output"], "output"), "big") != (after["0"] + after["1"]) % 2**256:
        fields.append("output")
    return fields


def has_tuples(case: dict) -> bool:
    return profile(case)["abi"] == "tuples"


def tuple_arity(case: dict) -> int:
    return case[profile(case)["planKey"]]["arity"]


def output_words(case: dict, row: dict) -> int:
    """The Words a completed row's output carries: a returned tuple its arity,
    every other row one."""
    return tuple_arity(case) if has_tuples(case) and row["status"] == "returned" else 1


def tuple_fields(case: dict, transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a returned row that break the tuple protocol: slot one grows by
    one, slot two is the input, and the output's Words are, in order, the
    committed slot zero, the committed slot one, the prior slot zero and the
    prior slot two, cut to the arity. A revert is checked by rollback."""
    if row["status"] != "returned":
        return []
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    before = {entry["slot"]: int(entry["value"]) for entry in prior}
    fields = []
    if after["1"] != (before["1"] + 1) % 2**256 or after["2"] != int(common.word(transaction.get("input"), "transaction input")):
        fields.append("committedStorage")
    output = common.hex_bytes(row["output"], "output")
    words = [int.from_bytes(output[offset:offset + 32], "big") for offset in range(0, len(output), 32)]
    if len(output) % 32 or words != [after["0"], after["1"], before["0"], before["2"]][:tuple_arity(case)]:
        fields.append("output")
    return fields


def has_logs(case: dict) -> bool:
    return profile(case).get("logs", False)


def has_balances(case: dict) -> bool:
    return profile(case).get("balances", False)


def deployment_logs(case: dict) -> bool:
    return has_logs(case) or profile(case).get("deploymentLogs", False)


def deployment_value(case: dict) -> int:
    """The value the empty payable constructor receives; zero elsewhere."""
    if not has_balances(case):
        return 0
    plan = case.get(profile(case)["planKey"])
    value = int(common.word(plan.get("deploymentValue") if isinstance(plan, dict) else None, "deployment value"))
    if value > MAX_VALUE:
        raise ValueError("deployment value exceeds 2^70")
    return value


def expected_balance(case: dict, row: dict) -> str:
    """Committed balance the protocol implies: deployment value plus slot one."""
    accepted = next(int(entry["value"]) for entry in row["committedStorage"] if entry["slot"] == "1")
    return str((deployment_value(case) + accepted) % 2**256)


def keccak_permutation(lanes: list[int]) -> list[int]:
    rotate = lambda value, distance: ((value << distance) | (value >> (64 - distance))) & (2**64 - 1)
    state = list(lanes)
    for constant in KECCAK_ROUND_CONSTANTS:
        parity = [state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20] for x in range(5)]
        state = [state[index] ^ parity[(index - 1) % 5] ^ rotate(parity[(index + 1) % 5], 1) for index in range(25)]
        moved = [0] * 25
        for x in range(5):
            for y in range(5):
                moved[y + 5 * ((2 * x + 3 * y) % 5)] = rotate(state[x + 5 * y], KECCAK_ROTATIONS[x + 5 * y])
        state = [moved[index] ^ (~moved[(index + 1) % 5 + 5 * (index // 5)] & moved[(index + 2) % 5 + 5 * (index // 5)])
                 for index in range(25)]
        state[0] ^= constant
    return state


def keccak256(data: bytes) -> bytes:
    """Ethereum Keccak-256: rate 136 bytes and domain byte 0x01, not SHA3-256."""
    padded = bytearray(data) + b"\x01" + bytes(-(len(data) + 1) % 136)
    padded[-1] |= 0x80
    state = [0] * 25
    for offset in range(0, len(padded), 136):
        for index in range(17):
            state[index] ^= int.from_bytes(padded[offset + 8 * index:offset + 8 * index + 8], "little")
        state = keccak_permutation(state)
    return b"".join(lane.to_bytes(8, "little") for lane in state[:4])


def entry_slot(key: int) -> int:
    """The pinned std's slot of `entries[key]`: keccak256(base ++ key) over two big-endian Words."""
    return int.from_bytes(keccak256(MAPPING_BASE.to_bytes(32, "big") + (key % 2**256).to_bytes(32, "big")), "big")


def mapping_slots(transactions) -> list[str]:
    """The mapping protocol's complete write set: the counter and the entry slots
    of every key and wrapping successor, in increasing numeric order."""
    values = {MAPPING_COUNTER}
    for tx in transactions:
        key = int(common.word(tx.get("key") if isinstance(tx, dict) else None, "transaction key"))
        values.update((entry_slot(key), entry_slot(key + 1)))
    return [str(value) for value in sorted(values)]


def ledger_slots(transactions) -> list[str]:
    """The ledger protocol's complete write set: the counter and the entry slots
    of every transaction's sender and recipient, in increasing numeric order."""
    values = {MAPPING_COUNTER}
    for tx in transactions:
        sender = common.word(tx.get("sender") if isinstance(tx, dict) else None, "transaction sender")
        values.update((entry_slot(int(sender)), entry_slot(int(common.word(tx.get("recipient"), "transaction recipient")))))
    return [str(value) for value in sorted(values)]


def ledger_fields(transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a completed row that break the ledger protocol. Odd flags
    revert; an even-flag revert is an insufficient balance, so its payload (the
    credited balance) is below the amount. A returned row increments the
    counter, changes no declared slot but the counter and the two entries, and
    returns their sum; a transfer to another key credits exactly the amount and
    leaves a sender entry the amount does not wrap, and a self-transfer leaves an
    entry of at least the amount. Rollback is checked separately."""
    odd = int(transaction["flags"]) % 2 == 1
    amount = int(transaction["amount"])
    output = int.from_bytes(common.hex_bytes(row["output"], "output"), "big")
    if row["status"] == "reverted":
        return [] if odd or output < amount else ["output"]
    if row["status"] != "returned":
        return []
    if odd:
        return ["status"]
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    before = {entry["slot"]: int(entry["value"]) for entry in prior}
    source, target = str(entry_slot(int(transaction["sender"]))), str(entry_slot(int(transaction["recipient"])))
    kept = all(after[slot] == before[slot] for slot in after if slot not in ("0", source, target))
    moved = (after[source] >= amount if source == target else
             after[target] == (before[target] + amount) % 2**256 and after[source] + amount < 2**256)
    fields = [] if after["0"] == (before["0"] + 1) % 2**256 and kept and moved else ["committedStorage"]
    if output != (after[source] + after[target] + after["0"]) % 2**256:
        fields.append("output")
    return fields


def has_bytes(case: dict) -> bool:
    return profile(case)["abi"] == "bytes"


def payload(transaction: dict, limit: int = MAX_PAYLOAD_BOUND) -> bytes:
    """A bytes transaction's payload: at most `limit` bytes as canonical lowercase hex."""
    text = transaction.get("payload") if isinstance(transaction, dict) else None
    if not isinstance(text, str) or not re.fullmatch(r"0x(?:[0-9a-f]{2}){0,%d}" % limit, text):
        raise ValueError(f"bytes payloads carry 0..{limit} bytes as canonical lowercase hexadecimal")
    return bytes.fromhex(text[2:])


def bytes_layout(selected: dict) -> tuple[int, list[str], str, str]:
    """A bytes profile's payload bound, observed slots and count and last-byte slots."""
    return (selected.get("maxPayload", MAX_PAYLOAD), selected.get("slots", BYTES_SLOTS),
            selected.get("countSlot", "3"), selected.get("tailSlot", "4"))


def bytes_calldata(selector: str, flags: int, data: bytes) -> str:
    """Canonical head/tail ABI: flags, tail offset 64, length, payload, zero padding."""
    padded = data + bytes(-len(data) % 32)
    return selector + f"{flags:064x}{64:064x}{len(data):064x}" + padded.hex()


def payload_chunks(transaction: dict) -> list[int]:
    """The zero-padded 32-byte chunk Words the step folds."""
    data = payload(transaction)
    return [int.from_bytes((data[start:start + 32] + bytes(32))[:32], "big") for start in range(0, len(data), 32)]


def bytes_fields(transaction: dict, row: dict, prior: list[dict], count: str = "3", tail: str = "4") -> list[str]:
    """Fields of a completed row that break the bytes protocol: a returned
    transaction adds its payload length to the count slot (three, or nine for
    long bytes), leaves its last byte (zero when empty) in the tail slot (four,
    or ten) and returns the committed slot zero, count and last byte plus its
    calldata size. A revert is checked by rollback."""
    if row["status"] != "returned":
        return []
    data = payload(transaction)
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    before = {entry["slot"]: int(entry["value"]) for entry in prior}
    fields = []
    if after[count] != (before[count] + len(data)) % 2**256 or after[tail] != (data[-1] if data else 0):
        fields.append("committedStorage")
    size = 100 + len(data) + -len(data) % 32
    if int.from_bytes(common.hex_bytes(row["output"], "output"), "big") != (after["0"] + after[count] + after[tail] + size) % 2**256:
        fields.append("output")
    return fields


def has_nested(case: dict) -> bool:
    return profile(case)["abi"] == "nested"


def nested_values(transaction: dict) -> list[list[int]]:
    """A nested transaction's value: at most three rows of at most two canonical decimal Words."""
    values = transaction.get("values") if isinstance(transaction, dict) else None
    if not isinstance(values, list) or len(values) > MAX_ROWS or any(not isinstance(row, list) or len(row) > MAX_COLUMNS for row in values):
        raise ValueError("nested-array transactions carry at most three rows of at most two elements")
    return [[int(common.word(value, "nested element")) for value in row] for row in values]


def nested_calldata(selector: str, flags: int, values: list[list[int]]) -> str:
    """Canonical nested head/tail ABI: flags, head offset 64, the outer length,
    one offset per row measured from the start of the offset table, then each
    row's length and elements."""
    offsets, offset = [], 32 * len(values)
    for row in values:
        offsets.append(offset)
        offset += 32 + 32 * len(row)
    words = [flags, 64, len(values), *offsets, *(word for row in values for word in (len(row), *row))]
    return selector + "".join(f"{word:064x}" for word in words)


def nested_fields(transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a completed row that break the nested-array protocol: a
    returned transaction adds its row count to slot seven and its element count
    to slot eight and returns the committed slots zero, seven and eight. A
    revert is checked by rollback."""
    if row["status"] != "returned":
        return []
    values = nested_values(transaction)
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    before = {entry["slot"]: int(entry["value"]) for entry in prior}
    fields = []
    if after[ROW_SLOT] != (before[ROW_SLOT] + len(values)) % 2**256 or \
            after[CELL_SLOT] != (before[CELL_SLOT] + sum(len(cells) for cells in values)) % 2**256:
        fields.append("committedStorage")
    if int.from_bytes(common.hex_bytes(row["output"], "output"), "big") != (after["0"] + after[ROW_SLOT] + after[CELL_SLOT]) % 2**256:
        fields.append("output")
    return fields


def log_sites(case: dict) -> list[dict]:
    """The plan's static sites: increasing guards one to three, each with at
    most four topics and two data Words. Native replay checks the program."""
    plan = case.get("logPlan")
    sites = plan.get("sites") if isinstance(plan, dict) else None
    if not isinstance(sites, list) or len(sites) > MAX_SITES:
        raise ValueError("log plan requires at most three sites")
    previous = 0
    for site in sites:
        if not isinstance(site, dict) or set(site) != {"guard", "topics", "dataWords"} or any(type(site[key]) is not int for key in site):
            raise ValueError("log sites contain exactly integer guard, topics and dataWords")
        if not previous < site["guard"] <= 3 or not 0 <= site["topics"] <= MAX_TOPICS or not 0 <= site["dataWords"] <= MAX_DATA_WORDS:
            raise ValueError("log sites need increasing guards one to three, at most four topics and two data Words")
        previous = site["guard"]
    return sites


def guarded_sites(case: dict, transaction: dict) -> list[dict]:
    flags = int(common.word(transaction["flags"], "transaction flags"))
    return [site for site in log_sites(case) if flags >> site["guard"] & 1]


def expected_log_shapes(case: dict, transaction: dict) -> list[tuple[int, int]]:
    """Topic count and data bytes of each committed log: one per guarded site
    on return, none on revert. Topic and data values are never predicted."""
    if expected_status(case, transaction) == "reverted":
        return []
    if has_keccak_loops(case):
        # Two topics and one data Word per loop iteration.
        return [(2, 32)] * loop_iterations(case, transaction)
    return [(site["topics"], 32 * site["dataWords"]) for site in guarded_sites(case, transaction)]


def log_shapes(rows) -> list[tuple[int, int]]:
    return [(len(row["topics"]), len(common.hex_bytes(row["data"], "log data"))) for row in rows]


def logs(rows, label="committed logs") -> list[dict]:
    """Ordered `{address, topics, data}` records with canonical decimal Words."""
    if not isinstance(rows, list) or len(rows) > MAX_LOGS:
        raise ValueError(f"{label} must be a bounded ordered list")
    result = []
    for row in rows:
        if not isinstance(row, dict) or set(row) != {"address", "topics", "data"} or not isinstance(row["topics"], list) or len(row["topics"]) > MAX_TOPICS:
            raise ValueError("invalid committed log")
        address = common.word(row["address"], "log address")
        if int(address) >= 2**160:
            raise ValueError("log address exceeds 160 bits")
        result.append({"address": address, "topics": [common.word(topic, "log topic") for topic in row["topics"]],
                       "data": "0x" + common.hex_bytes(row["data"], "log data").hex()})
    return result


def scope(case: dict) -> str:
    return declared_scope(case) + "; the contract's whole committed storage on all paths after deployment and every transaction"


def declared_scope(case: dict) -> str:
    if has_keccak_loops(case):
        return ("ordered zero-value run(uint256,uint256) transactions, each running its input's bits under the plan's "
                "mask (at most seven) iterations of a source while loop that reads and writes the std mapping entry of "
                "the key (input & ~7) | (i & keyMask) and slot 0 and emits one log2 of the counter, the key and the "
                "written value; no constructor logs; initially empty storage; committed values at slot 0 and every "
                "addressed key's keccak256(1 ++ key) slot and ordered committed logs (address, topics, data) on all "
                "paths, the EVM chain's complete log list, and no nonzero undeclared slot on Hull/EVM; no "
                "gas/balance/nonce or memory equivalence")
    if has_tuples(case):
        return ("ordered zero-value run(uint256,uint256) transactions that return a static tuple of the plan's two to "
                "four Words, the step result, slot 1 after its write and slots 0 and 2 before theirs; initially empty "
                "storage; the whole return data and committed values at slots 0..2 on all paths and no nonzero "
                "undeclared slot on Hull/EVM; no gas/balance/nonce or memory equivalence")
    if has_loops(case):
        return ("ordered zero-value run(uint256,uint256) transactions, each running its input's bits under the plan's "
                "mask (at most seven) iterations of a source while loop that reads slots 0, 1, 1 + i and 2 + i and writes "
                "slot 2 + i and slot 0; initially empty storage; committed values at slots 0..8 on all paths and no "
                "nonzero undeclared slot on Hull/EVM; no gas/balance/nonce or memory equivalence")
    if profile(case)["abi"] == "keyed":
        return ("ordered zero-value run(uint256,uint256) transactions; initially empty storage; committed values at the "
                "declared counter/key/successor slots on all paths and no nonzero undeclared slot on Hull/EVM; "
                "no gas/balance/nonce equivalence")
    if profile(case)["abi"] == "array":
        return ("ordered zero-value run(uint256,uint256[]) transactions with canonical 0..3-element arrays; initially "
                "empty storage; committed values at slots 0..4 on all paths and no nonzero undeclared slot on Hull/EVM; "
                "no gas/balance/nonce equivalence")
    if has_methods(case):
        return ("ordered zero-value calls of one contract's two to four external methods (at most two uint256 parameters "
                "each, over shared slots) in canonical calldata, or of a missing selector with one Word; initially empty "
                "storage; committed values at slots 0..5 on all paths and no nonzero undeclared slot on Hull/EVM; a missing "
                "selector compared by std's error selector (original Core's selector Word for std's four revert bytes) when "
                "original Core reverts with it and std prescribes it; no gas/balance/nonce or memory equivalence")
    if has_malformed_bytes(case):
        return ("ordered zero-value run(uint256,bytes) transactions with canonical 0..256-byte payloads and one "
                "malformation of at most 1 KiB of calldata each; initially empty storage; committed values at slots "
                "0..10 on all paths and no nonzero undeclared slot on Hull/EVM; a std rejection compared by its error "
                "selector (original Core's selector Word for std's four revert bytes) when original Core reverts with "
                "it and std prescribes it; no gas/balance/nonce or memory equivalence")
    if has_malformed_nested(case):
        return ("ordered zero-value run(uint256,uint256[][]) transactions with canonical values of at most four rows of at "
                "most three elements and one malformation of at most 1 KiB of calldata each; initially empty storage; "
                "committed values at slots 0..8 on all paths and no nonzero undeclared slot on Hull/EVM; a std rejection "
                "compared by its error selector (original Core's selector Word for std's four revert bytes) when original "
                "Core reverts with it and std prescribes it; no gas/balance/nonce or memory equivalence")
    if profile(case)["abi"] == "malformed":
        return ("ordered zero-value run(uint256,uint256[]) transactions with one malformation of at most 1 KiB of calldata "
                "each; initially empty storage; committed values at slots 0..4 on all paths and no nonzero undeclared slot "
                "on Hull/EVM; a std rejection compared by its error selector (original Core's selector Word for std's four "
                "revert bytes) when original Core reverts with it and std prescribes it; no gas/balance/nonce equivalence")
    if has_nested(case):
        return ("ordered zero-value run(uint256,uint256[][]) transactions with canonical nested values of at most three "
                "rows of at most two elements; initially empty storage; committed values at slots 0..8 on all paths and "
                "no nonzero undeclared slot on Hull/EVM; no gas/balance/nonce or memory equivalence")
    if has_senders(case):
        return ("ordered zero-value run(uint256,uint256,uint256,uint256) transactions from three fixed funded senders on "
                "a sender-keyed Keccak-addressed ledger; initially empty storage; committed values at the counter and "
                "every sender's and recipient's keccak256(1 ++ key) slot on all paths and no nonzero undeclared slot on "
                "Hull/EVM; no gas/balance/nonce equivalence")
    if profile(case)["abi"] == "mapping":
        return ("ordered zero-value run(uint256,uint256,uint256) transactions on a Keccak-addressed mapping; initially "
                "empty storage; committed values at the counter and every key's and successor's keccak256(1 ++ key) slot "
                "on all paths and no nonzero undeclared slot on Hull/EVM; no gas/balance/nonce equivalence")
    if has_bytes(case):
        bound, slots, _, _ = bytes_layout(profile(case))
        return (f"ordered zero-value run(uint256,bytes) transactions with canonical, zero-padded 0..{bound}-byte payloads; "
                f"initially empty storage; committed values at slots 0..{slots[-1]} on all paths and no nonzero undeclared "
                "slot on Hull/EVM; no gas/balance/nonce or memory equivalence")
    if has_balances(case):
        return ("ordered value-bearing payable run(uint256,uint256) transactions after a funded payable deployment; "
                "committed slots 0/1 and the contract's committed balance on all paths and no nonzero undeclared slot on "
                "Hull/EVM; no sender-balance, gas or nonce equivalence")
    if has_logs(case):
        return ("ordered zero-value run(uint256,uint256) transactions; no constructor logs; initially empty storage; "
                "committed slots 0/1 and ordered committed logs (address, topics, data) on all paths, the EVM chain's "
                "complete log list, and no nonzero undeclared slot on Hull/EVM; no gas/balance/nonce equivalence")
    return "ordered zero-value run(uint256) transactions; initially empty committed slots 0/1; no gas/balance/nonce equivalence"


def encoding(selected: dict) -> str:
    """The canonical calldata a malformed-calldata profile changes."""
    return selected.get("encoding", "array")


def has_malformed_nested(case: dict) -> bool:
    return profile(case)["abi"] == "malformed" and encoding(profile(case)) == "nested"


def has_malformed_bytes(case: dict) -> bool:
    return profile(case)["abi"] == "malformed" and encoding(profile(case)) == "bytes"


def changed_calldata(canonical: bytes, malformation, kinds: tuple, position) -> bytes:
    """One malformation's change to a canonical encoding: none, a selector
    prefix, a selector xor mask, a cut, trailing bytes, or a Word replaced at the
    byte position `position` gives for it. An invalid malformation is rejected."""
    if not isinstance(malformation, dict) or malformation.get("kind") not in kinds:
        raise ValueError("unknown malformation")
    kind = malformation["kind"]
    fields = {"none": set(), "short": {"bytes"}, "selector": {"mask"}, "truncate": {"kept"}, "trailing": {"count", "pattern"},
              "offset": {"value"}, "length": {"value"}, "row-offset": {"row", "value"}, "row-length": {"row", "value"}}[kind]
    if set(malformation) != {"kind"} | fields:
        raise ValueError("malformation fields differ from its kind")
    if kind == "none":
        return canonical
    if kind == "short":
        count = malformation["bytes"]
        if type(count) is not int or not 0 <= count < 4:
            raise ValueError("short calldata keeps zero to three selector bytes")
        return canonical[:count]
    if kind == "selector":
        mask = int(common.word(malformation["mask"], "selector mask"))
        if not 0 < mask < 2**32:
            raise ValueError("a selector mask is a nonzero 32-bit value")
        return (int.from_bytes(canonical[:4], "big") ^ mask).to_bytes(4, "big") + canonical[4:]
    if kind == "truncate":
        kept = malformation["kept"]
        if type(kept) is not int or not 4 <= kept < len(canonical):
            raise ValueError("truncation keeps the selector and drops at least one byte")
        return canonical[:kept]
    if kind == "trailing":
        count, pattern = malformation["count"], malformation["pattern"]
        if type(count) is not int or not 1 <= count <= 64 or pattern not in TRAILING_PATTERNS:
            raise ValueError("trailing bytes are 1 to 64 bytes of zeros, ones or a ramp")
        tail = {"zeros": bytes(count), "ones": b"\xff" * count, "ramp": bytes((index + 1) % 256 for index in range(count))}[pattern]
        return canonical + tail
    at = position(malformation)
    value = int(common.word(malformation["value"], "malformation value"))
    return canonical[:at] + value.to_bytes(32, "big") + canonical[at + 32:]


def malformed_calldata(selector: str, tx: dict) -> bytes:
    """The calldata a malformed-calldata transaction sends: the canonical
    `run(uint256,uint256[])` encoding of its flags and values, changed by its one
    malformation. An invalid malformation is rejected."""
    values = tx.get("values")
    if not isinstance(values, list) or len(values) > MAX_ELEMENTS:
        raise ValueError("malformed-calldata transactions carry zero to three elements")
    words = [int(common.word(tx.get("flags"), "transaction flags")), 64, len(values),
             *(int(common.word(value, "array element")) for value in values)]
    canonical = bytes.fromhex(selector[2:]) + b"".join(word.to_bytes(32, "big") for word in words)
    return changed_calldata(canonical, tx.get("malformation"), MALFORMATION_KINDS,
                            lambda malformation: 36 if malformation["kind"] == "offset" else 68)


def malformed_nested_values(transaction: dict) -> list[list[int]]:
    """A malformed nested transaction's canonical value: at most four rows of at
    most three canonical decimal Words."""
    values = transaction.get("values") if isinstance(transaction, dict) else None
    if not isinstance(values, list) or len(values) > MALFORMED_MAX_ROWS or \
            any(not isinstance(row, list) or len(row) > MALFORMED_MAX_COLUMNS for row in values):
        raise ValueError("malformed nested-array transactions carry at most four rows of at most three elements")
    return [[int(common.word(value, "nested element")) for value in row] for row in values]


def malformed_nested_calldata(selector: str, tx: dict) -> bytes:
    """The calldata a malformed nested-array transaction sends: the canonical
    `run(uint256,uint256[][])` encoding of its flags and values, changed by its
    one malformation. A row malformation replaces the row's table Word or its
    length Word and names a present row."""
    values = malformed_nested_values(tx)
    canonical = bytes.fromhex(nested_calldata(selector, int(common.word(tx.get("flags"), "transaction flags")), values)[2:])
    offsets, offset = [], 32 * len(values)
    for row in values:
        offsets.append(offset)
        offset += 32 + 32 * len(row)

    def position(malformation):
        if malformation["kind"] in ("offset", "length"):
            return 36 if malformation["kind"] == "offset" else 68
        row = malformation["row"]
        if type(row) is not int or not 0 <= row < len(values):
            raise ValueError("a row malformation names a present row")
        return TABLE_START + (32 * row if malformation["kind"] == "row-offset" else offsets[row])
    return changed_calldata(canonical, tx.get("malformation"), NESTED_MALFORMATION_KINDS, position)


def malformed_bytes_calldata(selector: str, tx: dict) -> bytes:
    """The calldata a malformed-bytes transaction sends: the canonical
    `run(uint256,bytes)` encoding of its flags and payload, changed by its one
    malformation. Padding replaces the zero padding after a payload that does
    not fill its last Word with `0xff`, a ramp or a last `0x01`."""
    data = payload(tx)
    canonical = bytes.fromhex(bytes_calldata(selector, int(common.word(tx.get("flags"), "transaction flags")), data)[2:])
    malformation = tx.get("malformation")
    if isinstance(malformation, dict) and malformation.get("kind") == "padding":
        if set(malformation) != {"kind", "pattern"} or malformation["pattern"] not in PADDING_PATTERNS:
            raise ValueError("padding is ones, a ramp or a last nonzero byte")
        count = -len(data) % 32
        if count == 0:
            raise ValueError("padding needs a payload that does not fill its last Word")
        fill = {"ones": b"\xff" * count, "ramp": bytes(index + 1 for index in range(count)),
                "last-byte": bytes(count - 1) + b"\x01"}[malformation["pattern"]]
        start = 100 + len(data)
        return canonical[:start] + fill + canonical[start + count:]
    return changed_calldata(canonical, malformation, MALFORMATION_KINDS,
                            lambda change: 36 if change["kind"] == "offset" else 68)


def std_dynamic_head(data: bytes, selector: str) -> tuple:
    """std's dispatch and the head of `(uint256 flags, T value)` for a dynamic
    `T`: the error selector it reverts with, or None and the head offset `o`
    once `o <= size - 4` and 32 bytes remain at `4 + o`."""
    size = len(data)
    if size < 4 or data[:4] != bytes.fromhex(selector[2:]):
        return STD_NO_SELECTOR, 0
    if size < 68:
        return STD_TRUNCATED, 0
    offset = int.from_bytes(data[36:68], "big")
    if offset > size - 4 or size - (4 + offset) < 32:
        return STD_TRUNCATED, 0
    return None, offset


def std_array_length(data: bytes, start: int) -> int | None:
    """std's `checkArrayHead` for 32-byte elements of an array whose length Word
    is at `start`: the length, or None when it exceeds ~0 / 32 or its elements
    do not fit after the length Word."""
    length = int.from_bytes(data[start:start + 32], "big")
    if length > MAX_ARRAY_LENGTH or 32 * length > len(data) - (start + 32):
        return None
    return length


def std_rejection(data: bytes, selector: str) -> str | None:
    """The pinned std's dispatcher and decoder for `run(uint256,uint256[])`: the
    error selector it reverts with, or None when the method body runs."""
    error, offset = std_dynamic_head(data, selector)
    if error is not None:
        return error
    return None if std_array_length(data, 4 + offset) is not None else STD_TRUNCATED


def nested_std_decode(data: bytes, selector: str) -> tuple:
    """The pinned std's dispatcher and lazy decoder for `run(uint256,uint256[][])`:
    the error selector it reverts with, or None with the outer length and the
    length of each row the body reads, rows `i < min(n, 3)` in order. The whole
    offset table must fit; a read row's table Word `r` must not exceed
    `size - T`, 32 bytes must remain at `T + r` and its elements must fit. Rows
    past the third are never decoded."""
    error, offset = std_dynamic_head(data, selector)
    if error is not None:
        return error, 0, []
    rows = std_array_length(data, 4 + offset)
    if rows is None:
        return STD_TRUNCATED, 0, []
    table, widths = 36 + offset, []
    for index in range(min(rows, READ_ROWS)):
        entry = int.from_bytes(data[table + 32 * index:table + 32 * index + 32], "big")
        if entry > len(data) - table or len(data) - (table + entry) < 32:
            return STD_TRUNCATED, 0, []
        width = std_array_length(data, table + entry)
        if width is None:
            return STD_TRUNCATED, 0, []
        widths.append(width)
    return None, rows, widths


def bytes_std_decode(data: bytes, selector: str) -> tuple:
    """The pinned std's dispatcher and `bytes` decoder for `run(uint256,bytes)`:
    the error selector it reverts with, or None with the payload it copies.
    The payload must fit after its length Word, after which std's bound
    `~0 - 63` holds; the padding is neither required nor read."""
    error, offset = std_dynamic_head(data, selector)
    if error is not None:
        return error, b""
    length = int.from_bytes(data[4 + offset:36 + offset], "big")
    if length > len(data) - (36 + offset) or length > MAX_BYTES_LENGTH:
        return STD_TRUNCATED, b""
    return None, data[36 + offset:36 + offset + length]


def malformed_input(selected: dict, tx: dict) -> tuple:
    """The calldata a malformed-calldata transaction sends and std's prescribed
    outcome for it: the rejecting selector, or None."""
    if encoding(selected) == "nested":
        data = malformed_nested_calldata(selected["selector"], tx)
        return data, nested_std_decode(data, selected["selector"])[0]
    if encoding(selected) == "bytes":
        data = malformed_bytes_calldata(selected["selector"], tx)
        return data, bytes_std_decode(data, selected["selector"])[0]
    data = malformed_calldata(selected["selector"], tx)
    return data, std_rejection(data, selected["selector"])


def malformed_bytes_fields(case: dict, transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a returned row that break the long-bytes protocol on the
    payload std decodes from the malformed calldata: its length is added to
    slot nine, its last byte (zero when empty) is slot ten, and the committed
    sum of slots zero, nine and ten plus the actual calldata size is returned.
    A rejection is checked by its payload and every revert by rollback."""
    if row["status"] != "returned" or transaction.get("stdRejection") is not None:
        return []
    selector = profile(case)["selector"]
    data = malformed_bytes_calldata(selector, transaction)
    _, decoded = bytes_std_decode(data, selector)
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    before = {entry["slot"]: int(entry["value"]) for entry in prior}
    fields = []
    if after["9"] != (before["9"] + len(decoded)) % 2**256 or after["10"] != (decoded[-1] if decoded else 0):
        fields.append("committedStorage")
    if int.from_bytes(common.hex_bytes(row["output"], "output"), "big") != (after["0"] + after["9"] + after["10"] + len(data)) % 2**256:
        fields.append("output")
    return fields


def malformed_nested_fields(case: dict, transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a returned row that break the nested-array protocol on the
    Words std decodes from the malformed calldata: the decoded outer length is
    added to slot seven, the read rows' lengths to slot eight, and the committed
    sum of slots zero, seven and eight is returned. A rejection is checked by its
    payload and every revert by rollback."""
    if row["status"] != "returned" or transaction.get("stdRejection") is not None:
        return []
    selector = profile(case)["selector"]
    _, rows, widths = nested_std_decode(malformed_nested_calldata(selector, transaction), selector)
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    before = {entry["slot"]: int(entry["value"]) for entry in prior}
    fields = []
    if after[ROW_SLOT] != (before[ROW_SLOT] + rows) % 2**256 or after[CELL_SLOT] != (before[CELL_SLOT] + sum(widths)) % 2**256:
        fields.append("committedStorage")
    if int.from_bytes(common.hex_bytes(row["output"], "output"), "big") != (after["0"] + after[ROW_SLOT] + after[CELL_SLOT]) % 2**256:
        fields.append("output")
    return fields


def has_methods(case: dict) -> bool:
    return profile(case)["abi"] == "methods"


def method_signature(name: str, arity: int) -> str:
    return f"{name}({','.join(['uint256'] * arity)})"


def method_selector(signature: str) -> str:
    """The first four bytes of the signature's Keccak-256, as std computes them."""
    return "0x" + keccak256(signature.encode())[:4].hex()


def selector_order(selectors: list[str]) -> str:
    """Whether selectors read in declaration order ascend, descend or neither."""
    values = [int(selector, 16) for selector in selectors]
    pairs = list(zip(values, values[1:]))
    if all(left < right for left, right in pairs):
        return "ascending"
    if all(left > right for left, right in pairs):
        return "descending"
    return "mixed"


def contract_methods(case: dict) -> tuple[list[dict], str]:
    """A several-methods case's methods in declaration order and its missing
    selector, checked against the plan and the contract metadata: two to four
    distinct `m_` names with at most two uint256 parameters, Keccak selectors
    that neither collide nor equal the missing one, and their selector order."""
    plan, contract = case.get("methodsPlan"), case.get("contract")
    rows = plan.get("methods") if isinstance(plan, dict) else None
    if not isinstance(rows, list) or not MIN_METHODS <= len(rows) <= MAX_METHODS:
        raise ValueError("a methods plan has two to four methods")
    methods = []
    for row in rows:
        if not isinstance(row, dict) or set(row) != {"name", "arity", "stepProgram"} or not isinstance(row["stepProgram"], dict):
            raise ValueError("a planned method has exactly a name, an arity and a step program")
        name, arity = row["name"], row["arity"]
        if not isinstance(name, str) or not METHOD_NAME.fullmatch(name) or type(arity) is not int or not 0 <= arity <= MAX_METHOD_ARITY:
            raise ValueError("a method is named m_ and eight hex digits and has at most two uint256 parameters")
        signature = method_signature(name, arity)
        methods.append({"name": name, "signature": signature, "selector": method_selector(signature), "arity": arity})
    missing = plan.get("missingSelector")
    selectors = [method["selector"] for method in methods]
    if len({method["name"] for method in methods}) != len(methods) or len(set(selectors)) != len(selectors):
        raise ValueError("method names and selectors must be distinct")
    if not isinstance(missing, str) or not re.fullmatch(r"0x[0-9a-f]{8}", missing) or missing in selectors:
        raise ValueError("the missing selector is four bytes no method has")
    name = profile(case)["contract"]
    expected = {"name": name, "methods": methods, "selectorOrder": selector_order(selectors),
        "deployPath": [name + "Deploy"], "runtimePath": [name + "Deploy", name], "constructorCalldata": "0x"}
    if contract != expected:
        raise Finding("unsupported-scope", "input", "several-methods contract metadata differs from its plan")
    return methods, missing


def methods_dispatch(methods: list[dict], data: bytes) -> tuple:
    """The pinned std's dispatch over raw calldata: the rejecting selector or
    None, and the position of the method that runs. Short calldata or no
    matching selector reaches the default fallback; the first matching method
    in declaration order runs once its arguments' head exists."""
    if len(data) < 4:
        return STD_NO_SELECTOR, None
    selector = "0x" + data[:4].hex()
    for position, method in enumerate(methods):
        if method["selector"] == selector:
            if len(data) < 4 + 32 * method["arity"]:
                return STD_TRUNCATED, None
            return None, position
    return STD_NO_SELECTOR, None


def methods_calldata(methods: list[dict], missing: str, tx: dict) -> bytes:
    """A several-methods transaction's canonical calldata: its method's selector
    and Word inputs, or the missing selector with one Word."""
    inputs, name = tx.get("inputs"), tx.get("method")
    if not isinstance(inputs, list):
        raise ValueError("several-methods transactions carry a list of inputs")
    words = [int(common.word(value, "method input")) for value in inputs]
    if name is None:
        selector, arity = missing, 1
    else:
        found = [method for method in methods if method["name"] == name]
        if len(found) != 1:
            raise ValueError("a transaction names one declared method")
        selector, arity = found[0]["selector"], found[0]["arity"]
    if len(words) != arity or tx.get("selector") != selector:
        raise ValueError("a transaction carries its method's arguments and selector, or one Word with the missing selector")
    return bytes.fromhex(selector[2:]) + b"".join(word.to_bytes(32, "big") for word in words)


def methods_fields(case: dict, transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a returned call that break the shared-slot protocol: slot one
    counts the call, the called method's slot `2 + i` holds the new slot zero,
    every other method's slot keeps its value, and the call returns the sum of
    slots zero, one and `2 + i`. A rejection is checked by its payload and
    every revert by rollback."""
    if row["status"] != "returned" or transaction.get("stdRejection") is not None:
        return []
    methods, missing = contract_methods(case)
    _, position = methods_dispatch(methods, methods_calldata(methods, missing, transaction))
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    before = {entry["slot"]: int(entry["value"]) for entry in prior}
    own = str(2 + position)
    fields = []
    if after["1"] != (before["1"] + 1) % 2**256 or after[own] != after["0"] or \
            any(after[slot] != before[slot] for slot in METHODS_SLOTS[2:] if slot != own):
        fields.append("committedStorage")
    if int.from_bytes(common.hex_bytes(row["output"], "output"), "big") != (after["0"] + after["1"] + after[own]) % 2**256:
        fields.append("output")
    return fields


def uses_selector_rule(case: dict) -> bool:
    """Profiles whose original Core contract reverts with std's error selectors as a Word."""
    return isinstance(case, dict) and any(case.get("schema") == value["caseSchema"] and value["abi"] in ("malformed", "methods")
                                          for value in PROFILES.values())


def selector_rule(case: dict, tx: dict, rows: dict) -> str | None:
    """The std error selector a transaction's rows are compared by. It applies
    only when original Core reverted with exactly that selector as a Word and the
    transaction's prescribed std outcome is that rejection; every other row is
    compared exactly. A body revert whose Word equals a selector has the
    prescribed outcome acceptance, so it is compared exactly too."""
    selector = tx.get("stdRejection")
    core = rows.get("directCore")
    if profile(case)["abi"] not in ("malformed", "methods") or selector not in STD_ERRORS or not isinstance(core, dict):
        return None
    if core.get("status") != "reverted" or core.get("output") != "0x" + int(selector, 16).to_bytes(32, "big").hex():
        return None
    return selector


def comparable(case: dict, tx: dict, rows: dict) -> dict:
    """The rows as compared: under the selector rule, original Core's selector
    Word stands for std's four revert bytes. Hull and EVM are never changed."""
    selector = selector_rule(case, tx, rows)
    if selector is None:
        return rows
    return {name: {**row, "output": selector} if name == "directCore" else row for name, row in rows.items()}


def keyed_slots(transactions) -> list[str]:
    """The keyed protocol's complete write set: counter, keys and successors."""
    values = {int(COUNTER_SLOT)}
    for tx in transactions:
        key = int(common.word(tx.get("key") if isinstance(tx, dict) else None, "transaction key"))
        values.update((key, (key + 1) % 2**256))
    return [str(value) for value in sorted(values)]


def observed_slots(case: dict) -> tuple:
    return tuple(case["observedSlots"]) if profile(case)["declared"] else SLOTS


def validate_transactions(case: dict, selected: dict) -> None:
    transactions = case.get("transactions")
    if not isinstance(transactions, list) or not 1 <= len(transactions) <= MAX_TRANSACTIONS:
        raise ValueError(f"storage case requires 1 to {MAX_TRANSACTIONS} ordered transactions")
    ids = set()
    for tx in transactions:
        if not isinstance(tx, dict) or not isinstance(tx.get("id"), str) or not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", tx["id"]) or tx["id"] in ids:
            raise ValueError("transaction IDs must be unique bounded identifiers")
        ids.add(tx["id"])
        if selected["abi"] == "array":
            values = tx.get("values")
            if not isinstance(values, list) or len(values) > MAX_ELEMENTS:
                raise ValueError("dynamic-array transactions carry zero to three elements")
            words = [int(common.word(value, "array element")) for value in values]
            # Canonical head/tail ABI: flags, tail offset 64, length, elements.
            expected = selected["selector"] + "".join(f"{word:064x}" for word in
                [int(common.word(tx.get("flags"), "transaction flags")), 64, len(words), *words])
            if tx.get("calldata") != expected or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its canonical ABI encoding")
            continue
        if selected["abi"] == "methods":
            methods, missing = contract_methods(case)
            data = methods_calldata(methods, missing, tx)
            if tx.get("calldata") != "0x" + data.hex() or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its method call")
            if tx.get("stdRejection") != methods_dispatch(methods, data)[0]:
                raise ValueError("transaction std outcome differs from std's dispatch of its calldata")
            continue
        if selected["abi"] == "malformed":
            data, rejection = malformed_input(selected, tx)
            if len(data) > MAX_CALLDATA:
                raise ValueError("malformed calldata exceeds 1 KiB")
            if tx.get("calldata") != "0x" + data.hex() or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its malformation")
            if tx.get("stdRejection") != rejection:
                raise ValueError("transaction std outcome differs from std's decision on its calldata")
            continue
        if selected["abi"] == "nested":
            expected = nested_calldata(selected["selector"], int(common.word(tx.get("flags"), "transaction flags")), nested_values(tx))
            if tx.get("calldata") != expected or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its canonical nested ABI encoding")
            continue
        if selected["abi"] == "bytes":
            expected = bytes_calldata(selected["selector"], int(common.word(tx.get("flags"), "transaction flags")),
                                      payload(tx, bytes_layout(selected)[0]))
            if tx.get("calldata") != expected or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its canonical ABI encoding")
            continue
        if selected["abi"] == "mapping":
            words = [int(common.word(tx.get(field), "transaction " + field)) for field in ("flags", "key", "input")]
            if tx.get("calldata") != selected["selector"] + "".join(f"{word:064x}" for word in words) or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its three original Words")
            continue
        if selected["abi"] == "ledger":
            if tx.get("sender") not in LEDGER_SENDERS:
                raise ValueError("ledger transactions are sent by one of the fixed senders")
            words = [int(common.word(tx.get(field), "transaction " + field)) for field in ("flags", "recipient", "amount", "input")]
            if tx.get("calldata") != selected["selector"] + "".join(f"{word:064x}" for word in words) or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its four original Words")
            continue
        if selected["abi"] == "keccak-loops":
            if type(tx.get("iterations")) is not int or tx["iterations"] != loop_iterations(case, tx):
                raise ValueError("transaction iterations differ from its input under the loop mask")
            words = [int(common.word(tx.get(field), "transaction " + field)) for field in ("flags", "input")]
            if tx.get("calldata") != selected["selector"] + "".join(f"{word:064x}" for word in words) or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its original Word input")
            continue
        value = int(common.word(tx.get("input"), "transaction input"))
        if selected["abi"] == "loops" and (type(tx.get("iterations")) is not int or tx["iterations"] != loop_iterations(case, tx)):
            raise ValueError("transaction iterations differ from its input under the loop mask")
        prefix = {"keyed": "key", "flags": "flags", "value": "flags", "loops": "flags", "tuples": "flags"}.get(selected["abi"])
        words = f"{int(common.word(tx.get(prefix), 'transaction ' + prefix)):064x}" if prefix else ""
        sent = "0"
        if selected.get("balances"):
            sent = common.word(tx.get("value"), "call value")
            if int(sent) > MAX_VALUE:
                raise ValueError("call value exceeds 2^70")
        if tx.get("calldata") != selected["selector"] + words + f"{value:064x}" or tx.get("value") != sent:
            raise ValueError("transaction calldata/value differs from its original Word input")
    if selected.get("balances") and deployment_value(case) + sum(int(tx["value"]) for tx in transactions) > MAX_TOTAL:
        raise ValueError("a call-value scenario sends at most 2^72 in total")


def validate_case(case) -> None:
    selected = profile(case)
    plan = case.get(selected["planKey"])
    if not isinstance(plan, dict) or plan.get("schema") != selected["planSchema"] or (
            not isinstance(plan.get("methods"), list) if selected["abi"] == "methods" else not isinstance(plan.get("stepProgram"), dict)):
        raise ValueError("storage case requires its original checked step plan")
    if selected["abi"] == "loops" and (type(plan.get("mask")) is not int or plan["mask"] not in LOOP_MASKS):
        raise ValueError("storage-loop plan requires a mask of 0, 1, 3 or 7")
    if selected["abi"] == "keccak-loops" and any(type(plan.get(key)) is not int or plan[key] not in LOOP_MASKS
                                                 for key in ("mask", "keyMask")):
        raise ValueError("Keccak-loop plan requires a loop mask and a key mask of 0, 1, 3 or 7")
    if selected["abi"] == "tuples" and (type(plan.get("arity")) is not int or plan["arity"] not in TUPLE_ARITIES):
        raise ValueError("tuple-return plan requires an arity of 2, 3 or 4")
    if not isinstance(case.get("program"), dict) or not isinstance(case.get("source"), str):
        raise ValueError("storage case requires its original host Core program and source")
    if selected["abi"] == "keyed":
        validate_transactions(case, selected)
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != keyed_slots(case["transactions"]):
            raise Finding("unsupported-scope", "input", "keyed storage profile starts empty and observes the counter and every key and successor")
    elif selected["abi"] == "array":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != ARRAY_SLOTS:
            raise Finding("unsupported-scope", "input", "dynamic-array profile starts empty and observes slots zero through four")
    elif selected["abi"] == "methods":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != METHODS_SLOTS:
            raise Finding("unsupported-scope", "input", "several-methods profile starts empty and observes slots zero through five")
    elif selected["abi"] == "loops":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != LOOP_SLOTS:
            raise Finding("unsupported-scope", "input", "storage-loop profile starts empty and observes slots zero through eight")
    elif selected["abi"] == "keccak-loops":
        validate_transactions(case, selected)
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != keccak_loop_slots(case):
            raise Finding("unsupported-scope", "input", "Keccak-loop profile starts empty and observes slot zero and every addressed entry slot")
    elif selected["abi"] == "tuples":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != TUPLE_SLOTS:
            raise Finding("unsupported-scope", "input", "tuple-return profile starts empty and observes slots zero through two")
    elif selected["abi"] == "malformed" and encoding(selected) == "bytes":
        slots = bytes_layout(selected)[1]
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != slots:
            raise Finding("unsupported-scope", "input", "malformed-bytes profile starts empty and observes slots zero through ten")
    elif selected["abi"] == "malformed" and encoding(selected) == "nested":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != NESTED_SLOTS:
            raise Finding("unsupported-scope", "input", "malformed nested-array profile starts empty and observes slots zero through eight")
    elif selected["abi"] == "malformed":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != ARRAY_SLOTS:
            raise Finding("unsupported-scope", "input", "malformed-calldata profile starts empty and observes slots zero through four")
    elif selected["abi"] == "nested":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != NESTED_SLOTS:
            raise Finding("unsupported-scope", "input", "nested-array profile starts empty and observes slots zero through eight")
    elif selected["abi"] == "mapping":
        validate_transactions(case, selected)
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != mapping_slots(case["transactions"]):
            raise Finding("unsupported-scope", "input", "mapping profile starts empty and observes the counter and every key's and successor's entry slot")
    elif selected["abi"] == "ledger":
        validate_transactions(case, selected)
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != ledger_slots(case["transactions"]):
            raise Finding("unsupported-scope", "input", "ledger profile starts empty and observes the counter and every sender's and recipient's entry slot")
    elif selected["abi"] == "bytes":
        slots = bytes_layout(selected)[1]
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != slots:
            raise Finding("unsupported-scope", "input", f"bytes profile starts empty and observes slots 0 through {slots[-1]}")
    elif selected["abi"] == "flags":
        log_sites(case)
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != LOG_SLOTS:
            raise Finding("unsupported-scope", "input", "log profile starts empty and observes slots zero and one")
    elif selected["abi"] == "value":
        deployment_value(case)
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != VALUE_SLOTS:
            raise Finding("unsupported-scope", "input", "call-value profile starts empty and observes slots zero and one")
    elif case.get("initialState") != {"storage": []} or case.get("observedSlots") != list(SLOTS):
        raise Finding("unsupported-scope", "input", "storage profile starts empty and observes slots zero and one")
    contract = case.get("contract")
    name = selected["contract"]
    expected = {"name": name, "method": "run", "signature": selected["signature"],
        "selector": selected["selector"], "deployPath": [name + "Deploy"],
        "runtimePath": [name + "Deploy", name], "constructorCalldata": "0x"}
    if selected["abi"] == "methods":
        contract_methods(case)
    elif contract != expected:
        raise Finding("unsupported-scope", "input", "storage wrapper differs from the fixed profile")
    provenance = case.get("provenance")
    if not isinstance(provenance, dict) or any(not isinstance(provenance.get(key), str) or not provenance[key]
            for key in ("generatorVersion", "emitterVersion", "wrapperVersion")):
        raise ValueError("missing versioned storage provenance")
    validate_transactions(case, selected)


def storage(rows, slots=SLOTS) -> list[dict]:
    if not isinstance(rows, list) or len(rows) != len(slots):
        raise ValueError("committed storage requires both observed slots" if slots == SLOTS else "committed storage requires every declared slot")
    result = []
    for slot, row in zip(slots, rows):
        if not isinstance(row, dict) or row.get("slot") != slot:
            raise ValueError("committed slots must be ordered, unique and complete")
        result.append({"slot": slot, "value": common.word(row.get("value"), "storage value")})
    return result


def undeclared(rows, slots) -> list[dict]:
    """Nonzero committed values outside the declaration, strictly ordered."""
    if not isinstance(rows, list) or len(rows) > MAX_UNDECLARED_SLOTS:
        raise ValueError("undeclared storage must be a bounded list")
    result = []
    for row in rows:
        if not isinstance(row, dict) or set(row) != {"slot", "value"}:
            raise ValueError("undeclared storage rows require exactly slot and value")
        slot, value = common.word(row["slot"], "undeclared slot"), common.word(row["value"], "undeclared value")
        if slot in slots or value == "0" or (result and int(result[-1]["slot"]) >= int(slot)):
            raise ValueError("undeclared storage must contain ordered nonzero slots outside the declaration")
        result.append({"slot": slot, "value": value})
    return result


def containment(row: dict, value: dict, path, slots, key="undeclaredStorage") -> None:
    """Hull and EVM report their whole committed map; Core reports declared slots."""
    if path in CONTAINMENT_PATHS:
        value[key] = undeclared(row.get(key), slots)
    elif key in row:
        raise ValueError("original Core cannot claim storage outside the declared slots")


def account_storage(rows, roles, label="account storage") -> list[dict]:
    """Every observed account's whole committed storage, in role order: its
    bound address and strictly ordered nonzero entries. Zero is never listed,
    so a cleared slot and one never written are the same observation."""
    if not isinstance(rows, list) or len(rows) != len(roles):
        raise ValueError(f"{label} must list every observed account")
    result = []
    for role, row in zip(roles, rows):
        if not isinstance(row, dict) or set(row) != {"role", "address", "storage"} or row["role"] != role:
            raise ValueError(f"{label} must name each observed account's role, address and storage")
        address = common.word(row["address"], "observed account address")
        entries = row["storage"]
        if int(address) >= 2**160 or not isinstance(entries, list) or len(entries) > MAX_ACCOUNT_SLOTS:
            raise ValueError(f"{label} needs a 160-bit address and a bounded entry list")
        normalized = []
        for entry in entries:
            if not isinstance(entry, dict) or set(entry) != {"slot", "value"}:
                raise ValueError(f"{label} entries require exactly slot and value")
            slot, value = common.word(entry["slot"], "storage slot"), common.word(entry["value"], "storage value")
            if value == "0" or (normalized and int(normalized[-1]["slot"]) >= int(slot)):
                raise ValueError(f"{label} must contain strictly ordered nonzero entries")
            normalized.append({"slot": slot, "value": value})
        result.append({"role": role, "address": address, "storage": normalized})
    return result


def account_storage_differences(observations: dict, declared, deployment=False) -> list[dict]:
    """Classify the slots whose whole committed values differ across the paths:
    the account role, the slot if the case declares it (else `undeclared`) and
    the paths at which it is zero. After deployment the expected storage is
    empty, so every nonzero slot is a difference even if all paths agree."""
    first = observations[PATHS[0]]
    found = set()
    for position, account in enumerate(first):
        values = {path: {entry["slot"]: entry["value"] for entry in observations[path][position]["storage"]} for path in PATHS}
        for slot in set().union(*values.values()):
            if deployment or len({values[path].get(slot, "0") for path in PATHS}) > 1:
                found.add((position, slot if slot in declared else "undeclared",
                           tuple(path for path in PATHS if slot not in values[path])))
    order = lambda item: (item[0], item[1] == "undeclared", int(item[1]) if item[1] != "undeclared" else 0, item[2])
    return [{"account": first[position]["role"], "slot": slot, "zeroPaths": list(zero)}
            for position, slot, zero in sorted(found, key=order)]


def account_identities(values: dict, initial_key="initialAccountStorage", rows_key="transactions") -> list:
    """The observed accounts every path names: the same roles and bound addresses."""
    identities = {json.dumps([[account["role"], account["address"]] for account in observation])
                  for history in values.values()
                  for observation in [history[initial_key]] + [row["accountStorage"] for row in history[rows_key]]}
    if len(identities) != 1:
        raise ValueError("paths observed different accounts")
    return json.loads(identities.pop())


def normalize_history(history, case: dict, path=None) -> dict:
    selected = profile(case)
    slots = observed_slots(case)
    if not isinstance(history, dict) or history.get("schema") != selected["historySchema"]:
        raise ValueError("unsupported storage observation history")
    if selected["declared"] and history.get("observedSlots") != list(slots):
        raise ValueError("history observed slots differ from the case declaration")
    initial = storage(history.get("initialStorage"), slots)
    extra = {"initialAccountStorage": account_storage(history.get("initialAccountStorage"), (CONTRACT_ROLE,),
                                                      "initial account storage")}
    if selected["declared"]:
        containment(history, extra, path, slots, "initialUndeclaredStorage")
    if selected.get("balances"):
        extra["initialBalance"] = common.word(history.get("initialBalance"), "initial balance")
    if deployment_logs(case):
        extra["initialLogs"] = logs(history.get("initialLogs"), "deployment logs")
    if selected.get("logs"):
        if path == "rustEvm":
            chain = history.get("chainLogs")
            extra["chainLogs"] = None if chain is None else logs(chain, "chain logs")
        elif "chainLogs" in history:
            raise ValueError("only the EVM path has a chain-wide log list")
    rows = history.get("transactions")
    if not isinstance(rows, list) or len(rows) > len(case["transactions"]):
        raise ValueError("invalid storage transaction history length")
    result = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict) or row.get("id") != case["transactions"][index]["id"] or type(row.get("index")) is not int or row["index"] != index:
            raise ValueError("storage transaction order or identity changed")
        status = row.get("status")
        if not isinstance(status, str):
            raise ValueError("missing transaction status")
        value = {"id": row["id"], "index": index, "status": status,
                 "committedStorage": storage(row.get("committedStorage"), slots),
                 "accountStorage": account_storage(row.get("accountStorage"), (CONTRACT_ROLE,))}
        if selected.get("balances"):
            value["committedBalance"] = common.word(row.get("committedBalance"), "committed balance")
        if selected["declared"]:
            containment(row, value, path, slots)
        if status in {"returned", "reverted"}:
            value["output"] = "0x" + common.hex_bytes(row.get("output"), "transaction output").hex()
            if selected.get("logs"):
                value["logs"] = logs(row.get("logs"))
        else:
            value["detail"] = row.get("detail", "")
            if selected.get("logs"):
                value["logs"] = None
            if index != len(rows) - 1:
                raise ValueError("execution continued after an incomplete transaction")
        result.append(value)
    complete = len(rows) == len(case["transactions"]) and all(r["status"] in {"returned", "reverted"} for r in result)
    if history.get("status") != ("complete" if complete else "incomplete"):
        raise ValueError("history completion flag disagrees with its transactions")
    remaining = [tx["id"] for tx in case["transactions"][len(rows):]]
    unobserved = history.get("unobserved", [])
    if unobserved not in ([], remaining[:1]) or (unobserved and complete):
        raise ValueError("invalid transaction with unknown completion")
    if unobserved and any(row["status"] not in {"returned", "reverted"} for row in result):
        raise ValueError("submission continued after an incomplete transaction")
    if history.get("unexecuted") != remaining[len(unobserved):]:
        raise ValueError("incorrect unexecuted transaction identities")
    final = None if unobserved else storage(history.get("finalStorage"), slots)
    if unobserved and history.get("finalStorage") is not None:
        raise ValueError("an unobserved transaction cannot claim a final committed snapshot")
    if not unobserved and final != (result[-1]["committedStorage"] if result else initial):
        raise ValueError("final committed storage differs from the last observation")
    whole = None if unobserved else account_storage(history.get("finalAccountStorage"), (CONTRACT_ROLE,), "final account storage")
    if unobserved and history.get("finalAccountStorage") is not None:
        raise ValueError("an unobserved transaction cannot claim a final whole storage")
    if not unobserved and whole != (result[-1]["accountStorage"] if result else extra["initialAccountStorage"]):
        raise ValueError("final whole storage differs from the last observation")
    extra["finalAccountStorage"] = whole
    if unobserved and extra.get("chainLogs") is not None:
        raise ValueError("an unobserved transaction cannot claim a chain-wide log list")
    if selected.get("balances"):
        balance = None if unobserved else common.word(history.get("finalBalance"), "final balance")
        if unobserved and history.get("finalBalance") is not None:
            raise ValueError("an unobserved transaction cannot claim a final committed balance")
        if not unobserved and balance != (result[-1]["committedBalance"] if result else extra["initialBalance"]):
            raise ValueError("final committed balance differs from the last observation")
        extra["finalBalance"] = balance
    return {"initialStorage": initial, **extra, "transactions": result, "finalStorage": final,
            "status": history["status"], "unexecuted": history["unexecuted"], "unobserved": unobserved}


def without_containment(row: dict) -> dict:
    return {key: value for key, value in row.items() if key != "undeclaredStorage"}


def conforms(case: dict, tx: dict, row: dict, prior: list[dict], address=None, prior_balance=None, prior_whole=None) -> bool:
    """The fixed protocol of a completed row: polarity, a one-Word payload,
    rollback of the committed slots and, for logs, the static log shapes from
    the contract address; a reverted row commits no logs. For call value, the
    balance is the deployment value plus slot one and a revert keeps it. For
    bytes, a returned row records its payload length, last byte and sum, and for
    nested arrays its row and element counts and sum. For the ledger,
    `ledger_fields` fixes what the balance-dependent polarity leaves open. A
    returned tuple carries its arity's Words and follows `tuple_fields`."""
    expected = expected_status(case, tx)
    # A std rejection reverts with exactly its selector, after the selector rule.
    rejection = tx.get("stdRejection") if profile(case)["abi"] in ("malformed", "methods") else None
    if (expected is None and row["status"] not in ("returned", "reverted")) or (expected is not None and row["status"] != expected) or \
            (row["output"] != rejection if rejection is not None else
             len(common.hex_bytes(row["output"], "output")) != 32 * output_words(case, row)):
        return False
    if row["status"] == "reverted" and (row["committedStorage"] != prior or
                                        (prior_whole is not None and row["accountStorage"] != prior_whole)):
        return False
    if has_bytes(case) and bytes_fields(tx, row, prior, *bytes_layout(profile(case))[2:]):
        return False
    if has_nested(case) and nested_fields(tx, row, prior):
        return False
    if has_malformed_nested(case) and malformed_nested_fields(case, tx, row, prior):
        return False
    if has_malformed_bytes(case) and malformed_bytes_fields(case, tx, row, prior):
        return False
    if has_methods(case) and methods_fields(case, tx, row, prior):
        return False
    if has_loops(case) and loop_fields(case, tx, row, prior):
        return False
    if has_keccak_loops(case) and keccak_loop_fields(case, tx, row, prior):
        return False
    if has_tuples(case) and tuple_fields(case, tx, row, prior):
        return False
    if has_senders(case) and ledger_fields(tx, row, prior):
        return False
    if has_balances(case) and (row["committedBalance"] != expected_balance(case, row) or
                               (row["status"] == "reverted" and row["committedBalance"] != prior_balance)):
        return False
    if has_logs(case):
        return log_shapes(row["logs"]) == expected_log_shapes(case, tx) and (
            address is None or all(log["address"] == address for log in row["logs"]))
    return True


def log_address(histories: dict):
    """The emitter all paths share: the binding original Core executed at."""
    bindings = histories.get("directCore", {}).get("bindings") if isinstance(histories.get("directCore"), dict) else None
    return common.word(bindings.get("address"), "bound address") if isinstance(bindings, dict) else None


def undeclared_paths(values: dict, index=None) -> list[str]:
    """Paths whose own complete committed map has a nonzero undeclared slot."""
    key = "initialUndeclaredStorage" if index is None else "undeclaredStorage"
    rows = {name: values[name] if index is None else values[name]["transactions"][index] for name in values}
    return sorted(name for name, row in rows.items() if row.get(key))


def pairwise(values: dict) -> dict:
    return {f"{a}/{b}": values[a] == values[b]
            for a, b in (("directCore", "rustEvm"), ("directCore", "importedHull"), ("importedHull", "rustEvm"))}


def compare(histories: dict, case: dict) -> dict:
    """Compare every completed prefix; a later budget failure cannot erase a
    difference. For malformed calldata the result lists the rows compared by
    their std error selector, with the selector."""
    selector_rows = []
    result = compare_rows(histories, case, selector_rows)
    if uses_selector_rule(case):
        result["selectorRows"] = selector_rows
    return result


def is_malformed(case: dict) -> bool:
    return isinstance(case, dict) and any(case.get("schema") == value["caseSchema"] and value["abi"] == "malformed"
                                          for value in PROFILES.values())


def compare_rows(histories: dict, case: dict, selector_rows: list) -> dict:
    if set(histories) != set(PATHS):
        return {"category": "adapter-error", "stage": "comparison", "detail": "three histories required", "pairs": {}}
    try:
        keyed = profile(case)["declared"]
        values = {name: normalize_history(histories[name], case, name) for name in PATHS}
        bound = log_address(histories)
        address = bound if has_logs(case) else None
        # Every path observes the same contract; original Core names its binding.
        if account_identities(values) != [[CONTRACT_ROLE, bound]] and bound is not None:
            raise ValueError("observed account differs from the bound contract")
    except (ValueError, KeyError, TypeError) as error:
        return {"category": "adapter-error", "stage": "comparison", "detail": str(error), "pairs": {}}
    initial = {name: values[name]["initialStorage"] for name in PATHS}
    whole = {name: values[name]["initialAccountStorage"] for name in PATHS}
    # The empty constructor leaves the whole storage empty on every path.
    differences = account_storage_differences(whole, observed_slots(case), deployment=True)
    pairs = pairwise(initial)
    outside = undeclared_paths(values) if keyed else []
    declared = not all(pairs.values()) or any(row["value"] != "0" for state in initial.values() for row in state)
    # A fixed empty constructor commits no logs; a deployment log is a difference.
    deployed_logs = sorted(name for name in PATHS if values[name].get("initialLogs")) if deployment_logs(case) else []
    # The funded deployment holds exactly its recorded value on every path.
    funded = not has_balances(case) or all(values[name]["initialBalance"] == str(deployment_value(case)) for name in PATHS)
    if declared or outside or deployed_logs or not funded or differences:
        fields = (["committedStorage"] if declared else []) + (["undeclaredStorage"] if outside else []) + (
            ["initialLogs"] if deployed_logs else []) + ([] if funded else ["committedBalance"]) + (
            ["accountStorage"] if differences else [])
        mismatch = {"category": "semantic-mismatch", "stage": "initial-storage", "fields": fields,
            "pairs": pairwise({name: [initial[name], whole[name], values[name].get("initialLogs"), values[name].get("initialBalance")]
                               for name in PATHS})}
        if outside:
            mismatch["undeclaredPaths"] = outside
        if differences:
            mismatch["accountStorageDifferences"] = differences
        if deployed_logs:
            mismatch["logPaths"] = deployed_logs
        return mismatch
    observed = ("status", "output", "committedStorage") + (("logs",) if has_logs(case) else ()) + (
        ("committedBalance",) if has_balances(case) else ())
    for index, tx in enumerate(case["transactions"]):
        rows = {name: values[name]["transactions"][index] for name in PATHS if index < len(values[name]["transactions"])}
        where = {"stage": "transaction", "transactionId": tx["id"], "index": index}
        if len(rows) != 3:
            return {"category": "inconclusive-resource", **where, "detail": "transaction not observed on every path", "pairs": {}}
        if any(row["status"] in RESOURCE_STATUSES for row in rows.values()):
            return {"category": "inconclusive-resource", **where, "pairs": {}}
        if any(row["status"] not in {"returned", "reverted"} for row in rows.values()):
            return {"category": "execution-error", **where, "pairs": {}}
        selector = selector_rule(case, tx, rows)
        if selector is not None:
            selector_rows.append({"id": tx["id"], "index": index, "selector": selector})
        rows = comparable(case, tx, rows)
        compared = {name: without_containment(row) for name, row in rows.items()}
        pairs = pairwise(compared)
        fields = [key for key in observed if len({json.dumps(row[key], sort_keys=True) for row in rows.values()}) != 1]
        expected = expected_status(case, tx)
        # A prescribed std rejection reverts with exactly its selector on every
        # path; a returned tuple carries its arity's Words and any other row one.
        rejection = tx.get("stdRejection") if profile(case)["abi"] in ("malformed", "methods") else None
        normal = all((expected is None or row["status"] == expected) and (
            row["output"] == rejection if rejection is not None else
            len(common.hex_bytes(row["output"], "output")) == 32 * output_words(case, row))
                     for row in rows.values())
        rollback = all(row["status"] != "reverted" or row["committedStorage"] ==
            (values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])
            for name, row in rows.items())
        if not rollback and "committedStorage" not in fields:
            fields.append("committedStorage")
        if has_balances(case):
            # Every committed balance is the deployment value plus the accepted
            # value in slot one, and a revert refunds: the prior balance stays.
            refunded = all(row["committedBalance"] == expected_balance(case, row) and (row["status"] != "reverted" or
                row["committedBalance"] == (values[name]["transactions"][index - 1]["committedBalance"] if index else values[name]["initialBalance"]))
                for name, row in rows.items())
            if not refunded and "committedBalance" not in fields:
                fields.append("committedBalance")
            normal = normal and refunded
        if has_bytes(case):
            # A returned row records its payload length and last byte and returns
            # the committed sum; a revert is already covered by rollback.
            broken = sorted({field for name, row in rows.items() for field in bytes_fields(tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"],
                *bytes_layout(profile(case))[2:])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_nested(case):
            # A returned row adds its row and element counts and returns the
            # committed sum; a revert is already covered by rollback.
            broken = sorted({field for name, row in rows.items() for field in nested_fields(tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_methods(case):
            # A returned call follows the shared-slot protocol of its method.
            broken = sorted({field for name, row in rows.items() for field in methods_fields(case, tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_loops(case):
            # A returned row follows the loop protocol; a revert is already covered by rollback.
            broken = sorted({field for name, row in rows.items() for field in loop_fields(case, tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_keccak_loops(case):
            # A returned row follows the Keccak-loop protocol, its logs included;
            # a revert is already covered by rollback and the log shapes.
            broken = sorted({field for name, row in rows.items() for field in keccak_loop_fields(case, tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_tuples(case):
            # A returned tuple follows the protocol Word by Word; a revert is already covered by rollback.
            broken = sorted({field for name, row in rows.items() for field in tuple_fields(case, tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_malformed_bytes(case):
            # A returned row follows the protocol on the payload std decodes.
            broken = sorted({field for name, row in rows.items() for field in malformed_bytes_fields(case, tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_malformed_nested(case):
            # A returned row follows the protocol on the Words std decodes.
            broken = sorted({field for name, row in rows.items() for field in malformed_nested_fields(case, tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_senders(case):
            # The ledger protocol fixes the rest of each row; a revert is already covered by rollback.
            broken = sorted({field for name, row in rows.items() for field in ledger_fields(tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_logs(case):
            # Static shapes cover rollback: an expected revert commits no logs.
            shaped = all(log_shapes(row["logs"]) == expected_log_shapes(case, tx) and
                         (address is None or all(log["address"] == address for log in row["logs"])) for row in rows.values())
            if not shaped and "logs" not in fields:
                fields.append("logs")
            normal = normal and shaped
        outside = undeclared_paths(values, index) if keyed else []
        if outside:
            fields.append("undeclaredStorage")
        # The whole committed storage agrees across paths, and a revert keeps
        # each path's prior whole storage.
        differences = account_storage_differences({name: row["accountStorage"] for name, row in rows.items()}, observed_slots(case))
        rolled = sorted(name for name, row in rows.items() if row["status"] == "reverted" and row["accountStorage"] !=
                        (values[name]["transactions"][index - 1]["accountStorage"] if index else values[name]["initialAccountStorage"]))
        if (differences or rolled) and "accountStorage" not in fields:
            fields.append("accountStorage")
        if not all(pairs.values()) or not normal or not rollback or outside or rolled:
            mismatch = {"category": "semantic-mismatch", **where, "pairs": pairs, "fields": fields or ["status", "output"]}
            if outside:
                mismatch["undeclaredPaths"] = outside
            if differences:
                mismatch["accountStorageDifferences"] = differences
            if rolled:
                mismatch["accountStorageRollbackPaths"] = rolled
            return mismatch
    if has_logs(case):
        # Logs committed earlier stay: the chain's complete list for the contract
        # is the deployment logs followed by every committed receipt's logs.
        evm = values["rustEvm"]
        if evm["chainLogs"] is None:
            return {"category": "adapter-error", "stage": "committed-log-history", "detail": "EVM chain logs were not observed", "pairs": {}}
        if evm["chainLogs"] != evm["initialLogs"] + [log for row in evm["transactions"] for log in row["logs"]]:
            return {"category": "semantic-mismatch", "stage": "committed-log-history", "pairs": {}, "fields": ["chainLogs"], "logPaths": ["rustEvm"]}
    return {"category": "matched", "stage": "completed-history", "pairs": pairwise(
        {name: {key: value for key, value in values[name].items() if key not in ("initialUndeclaredStorage", "chainLogs")} | {
            "transactions": [without_containment(row) for row in values[name]["transactions"]]} for name in PATHS})}


def hull_history(stdout: str, exit_code: int, case: dict) -> dict:
    rows = [json.loads(line) for line in stdout.splitlines() if line.strip()]
    if exit_code not in (0, 1) or not rows or any(not isinstance(row, dict) for row in rows):
        raise ValueError("invalid Hull storage process result")
    if rows[-1].get("stage") == "preparation":
        detail = str(rows[-1].get("detail", "preparation rejected"))
        raise Finding("inconclusive-resource" if common.RESOURCE.search(detail) else "compilation-rejected", "core-preparation", detail)
    deployment = rows[0]
    if deployment.get("stage") != "deployment" or deployment.get("status") != "returned":
        raise Finding("inconclusive-resource" if deployment.get("status") == "out-of-fuel" else "execution-error", "core-deployment", json.dumps(deployment))
    calls = rows[1:]
    if any(row.get("stage") != "execution" for row in calls):
        raise ValueError("unexpected Hull storage output stage")
    complete = len(calls) == len(case["transactions"]) and all(row.get("status") in {"returned", "reverted"} for row in calls)
    if complete and exit_code:
        raise ValueError("unexplained Hull process failure after completed history")
    selected = profile(case)
    history = {"schema": selected["historySchema"], "initialStorage": deployment.get("committedStorage"),
        "transactions": calls, "finalStorage": calls[-1].get("committedStorage") if calls else deployment.get("committedStorage"),
        "initialAccountStorage": deployment.get("accountStorage"),
        "finalAccountStorage": calls[-1].get("accountStorage") if calls else deployment.get("accountStorage"),
        "status": "complete" if complete else "incomplete", "unexecuted": [tx["id"] for tx in case["transactions"][len(calls):]]}
    if selected["declared"]:
        history.update(observedSlots=list(observed_slots(case)), initialUndeclaredStorage=deployment.get("undeclaredStorage"))
    if deployment_logs(case):
        history["initialLogs"] = deployment.get("logs")
    if selected.get("balances"):
        history.update(initialBalance=deployment.get("committedBalance"),
                       finalBalance=calls[-1].get("committedBalance") if calls else deployment.get("committedBalance"))
    normalize_history(history, case, "importedHull")
    return history


def quantity(value, label: str) -> int:
    if not isinstance(value, str) or not re.fullmatch(r"0x(?:0|[1-9a-fA-F][0-9a-fA-F]*)", value):
        raise ValueError(f"invalid RPC quantity: {label}")
    return int(value, 16)


def receipt(rpc, tx_hash: str, runner) -> dict:
    if not isinstance(tx_hash, str) or not re.fullmatch(r"0x[0-9a-fA-F]{64}", tx_hash):
        raise ValueError("invalid submitted transaction hash")
    deadline = time.monotonic() + runner.remaining(runner.args.timeout)
    while True:
        value = rpc.call("eth_getTransactionReceipt", [tx_hash])
        if value is not None:
            if not isinstance(value, dict) or value.get("transactionHash", "").lower() != tx_hash.lower():
                raise ValueError("receipt does not identify the submitted transaction")
            quantity(value.get("blockNumber"), "receipt block")
            if value.get("status") not in ("0x0", "0x1"):
                raise ValueError("receipt has no valid execution status")
            return value
        if time.monotonic() >= deadline:
            raise Finding("inconclusive-resource", "evm-transaction", "receipt timeout; transaction not resubmitted")
        time.sleep(0.05)


def submit(rpc, request: dict, record: dict) -> str:
    record.update(request=request, submission="unknown")
    try:
        tx_hash = rpc.call("eth_sendTransaction", [request])
    except (TimeoutError, urllib.error.URLError) as error:
        record["error"] = str(error)
        raise Finding("inconclusive-resource", "evm-submission", "submission outcome unknown; transaction not resubmitted") from error
    except RpcError as error:
        record.update(submission="rejected", rpcError=error.error)
        failure = common.deployment_failure(error)
        raise Finding(failure.category, "evm-submission" if "id" in record else "evm-deployment", failure.detail) from error
    record.update(submission="submitted", transactionHash=tx_hash)
    return tx_hash


def evm_storage(rpc, address: str, block: str, slots=SLOTS) -> list[dict]:
    quantity(block, "storage block")
    result = []
    for slot in slots:
        raw = common.hex_bytes(rpc.call("eth_getStorageAt", [address, hex(int(slot)), block]), "storage bytes")
        if len(raw) != 32:
            raise ValueError("RPC storage value is not exactly one Word")
        result.append({"slot": slot, "value": str(int.from_bytes(raw, "big"))})
    return result


def evm_balance(rpc, address: str, block: str) -> str:
    """The contract's committed balance at one receipt block."""
    quantity(block, "balance block")
    return common.word(str(quantity(rpc.call("eth_getBalance", [address, block]), "contract balance")), "contract balance")


PRESTATE_DIFF = {"tracer": "prestateTracer", "tracerConfig": {"diffMode": True}}


def changed_storage(diff, addresses) -> dict[str, set[str]]:
    """Storage keys of each observed account that one mined transaction changed,
    from the client's own diff of its pre- and post-state.

    Only the deployed contracts may change storage in these profiles; any other
    account's storage change is outside the comparison scope and fails closed.
    """
    if not isinstance(diff, dict) or set(diff) != {"pre", "post"} or not all(isinstance(diff[k], dict) for k in diff):
        raise ValueError("prestate diff lacks its pre/post account maps")
    observed = {address.lower() for address in addresses}
    result = {address: set() for address in observed}
    for side in ("pre", "post"):
        for account, state in diff[side].items():
            if not isinstance(account, str) or not re.fullmatch(r"0x[0-9a-fA-F]{40}", account) or not isinstance(state, dict):
                raise ValueError("invalid prestate diff account")
            values = state.get("storage", {})
            if not isinstance(values, dict):
                raise ValueError("invalid prestate diff storage")
            if values and account.lower() not in observed:
                raise ValueError("prestate diff changed storage outside the deployed contract")
            for key in values:
                if not isinstance(key, str) or not re.fullmatch(r"0x[0-9a-fA-F]{1,64}", key):
                    raise ValueError("invalid prestate diff storage key")
                result[account.lower()].add(str(int(key, 16)))
    return result


def changed_slots(diff, address: str) -> set[str]:
    """Storage keys of the one deployed contract that a mined transaction changed."""
    return changed_storage(diff, [address])[address.lower()]


def evm_account_storage(rpc, accounts, touched: dict, block: str) -> list[dict]:
    """Each observed account's whole committed storage at one receipt block.

    `accounts` are (role, decimal address) pairs and `touched` maps each
    lowercase hexadecimal address to every slot a prestate diff has reported
    since its creation. A new contract starts empty and the diff reports every
    slot whose committed value a transaction changes, so rereading those slots
    and dropping zero values enumerates the whole storage exactly.
    """
    result = []
    for role, address in accounts:
        target = f"0x{int(address):040x}"
        rows = evm_storage(rpc, target, block, sorted(touched.get(target, set()), key=int))
        if len(rows) > MAX_ACCOUNT_SLOTS:
            raise ValueError("EVM account storage exceeds its bound")
        result.append({"role": role, "address": address, "storage": [row for row in rows if row["value"] != "0"]})
    return result


def evm_undeclared(rpc, address: str, block: str, touched: set[str], slots) -> list[dict]:
    """Every changed slot outside the declaration, reread at the receipt block."""
    outside = sorted((slot for slot in touched if slot not in slots), key=int)
    return [row for row in evm_storage(rpc, address, block, outside) if row["value"] != "0"]


def evm_log(event: dict) -> dict:
    if not isinstance(event, dict) or not isinstance(event.get("address"), str) or not re.fullmatch(r"0x[0-9a-fA-F]{40}", event["address"]) or not isinstance(event.get("topics"), list):
        raise ValueError("invalid mined log")
    if event.get("removed", False) is not False:
        raise ValueError("mined log was removed")
    topics = [common.hex_bytes(topic, "log topic") for topic in event["topics"]]
    if any(len(topic) != 32 for topic in topics):
        raise ValueError("mined log topic is not a Word")
    return {"address": str(int(event["address"], 16)), "topics": [str(int.from_bytes(topic, "big")) for topic in topics],
            "data": "0x" + common.hex_bytes(event.get("data"), "log data").hex()}


def evm_logs(mined: dict) -> list[dict]:
    """The receipt's own logs in log-index order; each names this receipt."""
    events = mined.get("logs")
    if not isinstance(events, list):
        raise ValueError("mined receipt has no log list")
    result = []
    for event in events:
        if not isinstance(event, dict) or str(event.get("transactionHash", "")).lower() != mined["transactionHash"].lower() or event.get("blockNumber") != mined["blockNumber"]:
            raise ValueError("mined log is not from the selected transaction block")
        result.append(evm_log(event))
    if [quantity(event.get("logIndex"), "log index") for event in events] != sorted(quantity(event.get("logIndex"), "log index") for event in events):
        raise ValueError("receipt logs are not in log-index order")
    return logs(result, "receipt logs")


def evm_chain_logs(rpc, address: str, receipts: list[dict]) -> list[dict]:
    """Every log of the contract on the local chain, read once after the
    sequence and ordered by block and log index. Each must come from a receipt
    of this case; the comparison requires the committed receipts' logs."""
    hashes = {mined["transactionHash"].lower() for mined in receipts}
    last = max(quantity(mined["blockNumber"], "receipt block") for mined in receipts)
    events = rpc.call("eth_getLogs", [{"address": address, "fromBlock": "0x0", "toBlock": hex(last)}])
    if not isinstance(events, list) or len(events) > MAX_LOGS:
        raise ValueError("chain logs must be a bounded list")
    keyed = []
    for event in events:
        if not isinstance(event, dict) or str(event.get("transactionHash", "")).lower() not in hashes:
            raise ValueError("chain log does not belong to a transaction of this case")
        keyed.append(((quantity(event.get("blockNumber"), "log block"), quantity(event.get("logIndex"), "log index")), evm_log(event)))
    return logs([event for _, event in sorted(keyed, key=lambda item: item[0])], "chain logs")


def trace_result(mined: dict, trace: dict) -> dict:
    if not isinstance(trace, dict) or not isinstance(trace.get("returnValue"), str) or type(trace.get("failed")) is not bool:
        raise ValueError("transaction trace lacks its actual completion")
    output = trace["returnValue"]
    output = "0x" + common.hex_bytes(output if output.startswith("0x") else "0x" + output, "trace output").hex()
    if mined["status"] == "0x1":
        if trace["failed"]:
            raise ValueError("successful receipt disagrees with failed trace")
        return {"status": "returned", "output": output}
    if not trace["failed"]:
        raise ValueError("failed receipt disagrees with successful trace")
    logs = trace.get("structLogs", [])
    last = logs[-1] if isinstance(logs, list) and logs and isinstance(logs[-1], dict) else {}
    error = str(trace.get("error", "")) + " " + str(last.get("error", ""))
    if common.RESOURCE.search(error):
        return {"status": "out-of-gas" if common.GAS_RESOURCE.search(error) else "resource-limit", "detail": error.strip()}
    if last.get("op") == "REVERT":
        return {"status": "reverted", "output": output}
    return {"status": "evm-exceptional", "detail": error.strip() or "failed transaction without a confirmed REVERT"}


def verify_archive(path: Path, report: dict) -> None:
    if not isinstance(report, dict) or report.get("schema") != REPORT_SCHEMA:
        raise ValueError("unsupported storage report schema")
    common.resolve_backend(None, report)
    common.verify_archive(path, {**report, "schema": common.REPORT_SCHEMA})


def execute(args, report: dict) -> None:
    previous = None
    if args.replay:
        previous = common.read_json(args.replay / "report.json", args.artifact_limit)
        verify_archive(args.replay, previous)
    args.backend = common.resolve_backend(getattr(args, "backend", None), previous)
    report["backend"] = args.backend
    report["pathBackends"] = common.path_backends(args.backend)
    linked = common.image_backend(args.backend)
    runner = common.Runner(args, report)
    case = common.read_json(args.replay / "case.json" if args.replay else args.case)
    validate_case(case)
    case_path, source = args.output / "case.json", args.output / "case.sol"
    save(case_path, case)
    source.write_text(case["source"])
    report.update(caseSha256=common.file_digest(case_path), sourceSha256=common.file_digest(source),
        programSha256=common.digest(common.json_bytes(case["program"])), provenance=case["provenance"],
        replayOf=str(args.replay) if args.replay else None)
    report["tools"] = {"caseTool": runner.identity(args.case_tool), "coreRunner": runner.identity(args.core_runner),
        "anvil": runner.identity(args.anvil, version=True), "runnerSha256": common.file_digest(Path(__file__)),
        "sharedRunnerSha256": common.file_digest(ROOT / "scripts/semantic-differential.py"),
        "leanToolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "python": {"path": sys.executable, "version": sys.version},
        "exporters": {name: common.file_digest(ROOT / "scripts" / name) for name in
            ("export-rust-hull.py", "export-rust-code-image.py", "rust-hull-export.rs", "rust-code-image-export.rs")}}
    if args.backend == "yul":
        report["tools"].update(solc=runner.identity(args.solc, version=True),
            yulExporterSha256=common.file_digest(ROOT / "scripts/export-rust-yul.py"),
            yulTransportSha256=common.file_digest(ROOT / "scripts/semantic-yul.py"))
    if previous:
        yul = ("yulExporterSha256", "yulTransportSha256") if args.backend == "yul" else ()
        for key in ("runnerSha256", "sharedRunnerSha256", "exporters", "leanToolchain", *yul):
            if report["tools"][key] != previous.get("tools", {}).get(key):
                raise Finding("adapter-error", "replay", f"saved tool identity changed: {key}")
        for key in ("caseTool", "coreRunner", "anvil"):
            if report["tools"][key]["sha256"] != previous.get("tools", {}).get(key, {}).get("sha256"):
                raise Finding("adapter-error", "replay", f"saved executable changed: {key}")
        for key in ("sha256", "version") if args.backend == "yul" else ():
            if report["tools"]["solc"][key] != previous.get("tools", {}).get("solc", {}).get(key):
                raise Finding("adapter-error", "replay", f"saved executable changed: solc {key}")
    revision = runner.process("repository-revision", ["git", "rev-parse", "HEAD"], 10)
    diff = runner.process("repository-diff", ["git", "diff", "--binary", "HEAD"], 10)
    if revision["returncode"] or diff["returncode"]:
        raise ValueError("cannot identify repository state")
    report["repository"] = {"revision": revision["stdout"].strip(), "trackedDiffSha256": common.digest(diff["stdout"].encode())}
    replay = common.checked_process(runner, "direct-core-replay", [str(args.case_tool), "replay", str(case_path), str(args.direct_fuel)])
    fresh = json.loads(replay["stdout"])
    selected = profile(case)
    slots = observed_slots(case)
    for key in ("program", "source", "provenance", "contract", "transactions", selected["planKey"], "initialState", "observedSlots"):
        if fresh.get(key) != case.get(key):
            raise ValueError(f"native storage replay changed {key}")
    save(args.output / "replayed-case.json", fresh)
    hull, images_path = args.output / "hull.json", args.output / "images.json"
    export_args = [str(source), "--root", str(args.output), "--upstream", str(args.upstream), "--target-dir", str(args.target_dir)]
    common.checked_process(runner, "rust-checked-source", [sys.executable, str(ROOT / "scripts/export-rust-hull.py"), *export_args, "--output", str(hull)])
    common.checked_process(runner, "rust-code-images", [sys.executable, str(ROOT / "scripts/export-rust-code-image.py"), *export_args,
        "--optimization", common.optimization_for_backend(linked),
        "--output", str(images_path), "--hull-output", str(hull), "--timeout", str(args.timeout)], args.timeout * 3)
    report["exportProvenance"] = common.validate_export(hull, images_path, source, args.artifact_limit, backend=linked)
    if previous and "exportProvenance" in previous:
        old, new = previous["exportProvenance"], report["exportProvenance"]
        if old["images"].get("toolBuild") != new["images"].get("toolBuild") or old["hull"].get("binarySha256") != new["hull"].get("binarySha256") or old["hull"].get("patches") != new["hull"].get("patches"):
            raise Finding("adapter-error", "replay", "Rust compiler/exporter build changed")
        libraries = lambda data: {k: v for k, v in data["hull"].get("sources", {}).items() if not k.endswith("/case.sol")}
        if libraries(old) != libraries(new):
            raise Finding("adapter-error", "replay", "imported library hashes changed")
    images = common.read_json(images_path, args.artifact_limit)
    init = common.image_bytes(images, case["contract"]["deployPath"])
    runtime = common.image_bytes(images, case["contract"]["runtimePath"])
    if args.backend == "yul":
        # The EVM deploys one solc compilation's bytes; Hull keeps the O0 images.
        init, runtime = common.yul_transport("execute", args, runner, case, source, hull, report, previous)
    with common.anvil(runner, args.anvil, steps_tracing=True) as rpc:
        accounts = rpc.call("eth_accounts", [])
        if not accounts or not re.fullmatch(r"0x[0-9a-fA-F]{40}", accounts[0]):
            raise ValueError("local Anvil supplied no valid sender")
        sender, gas = accounts[0], hex(args.gas)
        if has_senders(case):
            unlocked = {account.lower() for account in accounts if isinstance(account, str)}
            if sender.lower() != f"0x{int(LEDGER_SENDERS[0]):040x}" or any(f"0x{int(value):040x}" not in unlocked for value in LEDGER_SENDERS):
                raise Finding("adapter-error", "evm-senders", "local Anvil does not unlock the fixed ledger senders, the first one deploying")
        report["evmDeployment"] = {}
        tx_hash = submit(rpc, {"from": sender, "data": "0x" + init.hex(), "value": hex(deployment_value(case)), "gas": gas}, report["evmDeployment"])
        deployed = receipt(rpc, tx_hash, runner)
        report["evmDeployment"]["receipt"] = deployed
        if deployed["status"] != "0x1":
            trace = rpc.call("debug_traceTransaction", [tx_hash, {"disableStorage": True, "disableStack": True, "enableMemory": False}])
            report["evmDeployment"]["trace"] = trace
            outcome = trace_result(deployed, trace)
            raise Finding("inconclusive-resource" if outcome["status"] in RESOURCE_STATUSES else "execution-error", "evm-deployment", json.dumps(outcome))
        address = deployed.get("contractAddress")
        if not isinstance(address, str) or not re.fullmatch(r"0x[0-9a-fA-F]{40}", address):
            raise ValueError("invalid deployed contract address")
        if common.hex_bytes(rpc.call("eth_getCode", [address, deployed["blockNumber"]]), "deployed runtime") != runtime:
            raise Finding("adapter-error", "evm-deployment", "installed runtime differs from the exported " +
                          ("Yul runtime bytes" if args.backend == "yul" else "code image"))
        # Every slot a prestate diff reports from the deployment on; the whole
        # storage rereads them all at each receipt block.
        diff = rpc.call("debug_traceTransaction", [tx_hash, PRESTATE_DIFF])
        report["evmDeployment"]["storageDiff"] = diff
        touched = changed_slots(diff, address)
        bindings = {"schema": "solcore-lean.storage-bindings.v1", "caller": str(int(sender, 16)), "address": str(int(address, 16))}
        if previous and previous.get("bindings") != bindings:
            raise Finding("adapter-error", "replay", "fresh deployment changed the retained address bindings")
        report["bindings"] = bindings
        binding_path = args.output / "bindings.json"
        save(binding_path, bindings)
        observed = common.checked_process(runner, "direct-core-observe", [str(args.case_tool), "observe", str(case_path), str(binding_path), str(args.direct_fuel)])
        direct = json.loads(observed["stdout"])
        if direct.get("bindings") != bindings or direct.get("fuelPerTransaction") != args.direct_fuel:
            raise ValueError("original Core observer changed its invocation bindings or fuel")
        normalize_history(direct, case, "directCore")
        save(args.output / "direct-history.json", direct)
        report["histories"]["directCore"] = direct
        base = {"caller": bindings["caller"], "address": bindings["address"], "value": "0", "availableGas": str(args.gas)}
        scenario = {"schema": selected["scenarioSchema"], "hull": str(hull), "images": str(images_path),
            "deployPath": case["contract"]["deployPath"], "runtimePath": case["contract"]["runtimePath"], "fuel": args.core_fuel,
            "observedSlots": list(slots), "constructor": {**base, "calldata": "0x"},
            "calls": [{"id": tx["id"], "context": {**base, "calldata": tx["calldata"]}, "persist": True} for tx in case["transactions"]]}
        if has_senders(case):
            scenario["senders"] = list(LEDGER_SENDERS)
            for call, tx in zip(scenario["calls"], case["transactions"]):
                call["context"]["caller"] = tx["sender"]
        if selected.get("balances"):
            scenario["callerFunds"] = str(CALLER_FUNDS)
            scenario["constructor"]["value"] = str(deployment_value(case))
            for call, tx in zip(scenario["calls"], case["transactions"]):
                call["context"]["value"] = tx["value"]
        scenario_path = args.output / "scenario.json"
        save(scenario_path, scenario)
        result = runner.process("imported-hull", [str(args.core_runner), str(scenario_path)])
        report["histories"]["importedHull"] = hull_history(result["stdout"], result["returncode"], case)
        initial = evm_storage(rpc, address, deployed["blockNumber"], slots)
        keyed = {"observedSlots": list(slots), "initialUndeclaredStorage":
            evm_undeclared(rpc, address, deployed["blockNumber"], touched, slots)} if selected["declared"] else {}
        observed_accounts = [(CONTRACT_ROLE, bindings["address"])]
        keyed["initialAccountStorage"] = evm_account_storage(rpc, observed_accounts, {address.lower(): touched},
                                                             deployed["blockNumber"])
        if deployment_logs(case):
            keyed["initialLogs"] = evm_logs(deployed)
        if selected.get("logs"):
            keyed["chainLogs"] = None
        if selected.get("balances"):
            keyed["initialBalance"] = evm_balance(rpc, address, deployed["blockNumber"])
        evm_rows, records, mined_receipts = [], [], [deployed]
        report["evmTransactions"] = records
        def checkpoint(pending=None):
            complete = len(evm_rows) == len(case["transactions"]) and all(row["status"] in {"returned", "reverted"} for row in evm_rows)
            remaining = [tx["id"] for tx in case["transactions"][len(evm_rows):]]
            if selected.get("balances"):
                keyed["finalBalance"] = None if pending else evm_rows[-1]["committedBalance"] if evm_rows else keyed["initialBalance"]
            report["histories"]["rustEvm"] = {"schema": selected["historySchema"], **keyed, "initialStorage": initial,
                "transactions": list(evm_rows), "finalStorage": None if pending else evm_rows[-1]["committedStorage"] if evm_rows else initial,
                "finalAccountStorage": None if pending else evm_rows[-1]["accountStorage"] if evm_rows else keyed["initialAccountStorage"],
                "status": "complete" if complete else "incomplete", "unobserved": [pending] if pending else [],
                "unexecuted": remaining[1:] if pending else remaining}
        checkpoint()
        for index, tx in enumerate(case["transactions"]):
            record = {"id": tx["id"], "index": index}
            records.append(record)
            checkpoint(tx["id"])
            try:
                tx_hash = submit(rpc, {"from": f"0x{int(tx['sender']):040x}" if has_senders(case) else sender, "to": address, "data": tx["calldata"],
                                       "value": hex(int(tx["value"])), "gas": gas}, record)
            except BaseException:
                if record.get("submission") == "rejected":
                    checkpoint()
                raise
            mined = receipt(rpc, tx_hash, runner)
            record["receipt"] = mined
            mined_receipts.append(mined)
            trace = rpc.call("debug_traceTransaction", [tx_hash, {"disableStorage": True, "disableStack": True, "enableMemory": False}])
            record["trace"] = trace
            outcome = trace_result(mined, trace)
            state = evm_storage(rpc, address, mined["blockNumber"], slots)
            row = {"id": tx["id"], "index": index, **outcome, "committedStorage": state}
            if selected.get("logs") and outcome["status"] in {"returned", "reverted"}:
                row["logs"] = evm_logs(mined)
            if selected.get("balances"):
                row["committedBalance"] = evm_balance(rpc, address, mined["blockNumber"])
            diff = rpc.call("debug_traceTransaction", [tx_hash, PRESTATE_DIFF])
            record["storageDiff"] = diff
            touched |= changed_slots(diff, address)
            if selected["declared"]:
                row["undeclaredStorage"] = evm_undeclared(rpc, address, mined["blockNumber"], touched, slots)
            row["accountStorage"] = evm_account_storage(rpc, observed_accounts, {address.lower(): touched}, mined["blockNumber"])
            evm_rows.append(row)
            checkpoint()
            if outcome["status"] not in {"returned", "reverted"}:
                break
        if selected.get("logs"):
            keyed["chainLogs"] = evm_chain_logs(rpc, address, mined_receipts)
            report["evmChainLogsBlock"] = max(quantity(mined["blockNumber"], "receipt block") for mined in mined_receipts)
            checkpoint()
    report["comparison"] = compare(report["histories"], case)


def interrupted_comparison(args, report: dict, failure: dict) -> dict:
    """Keep an already established prefix difference if a later operation fails."""
    if set(report.get("histories", {})) == set(PATHS):
        try:
            case = common.read_json(args.output / "case.json")
            prefix = compare(report["histories"], case)
            if prefix["category"] == "semantic-mismatch":
                return {**prefix, "laterInterruption": failure}
        except (OSError, ValueError, KeyError, TypeError, Finding):
            pass
    return failure


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--case", type=Path)
    selection.add_argument("--replay", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--backend", choices=common.BACKENDS,
        help="default sonatina-o0; yul runs the EVM path on the pinned solc's Yul output; exact replay inherits its saved backend")
    parser.add_argument("--solc", type=Path, default=Path(shutil.which("solc") or "solc"), help="pinned solc, used only for --backend yul")
    parser.add_argument("--case-tool", type=Path)
    parser.add_argument("--core-runner", type=Path, help="default: the profile's imported-Hull scenario runner")
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    defaults = {"direct_fuel": 1000000, "core_fuel": 10000000, "gas": 10000000, "timeout": 300,
        "startup_timeout": 30, "total_timeout": 900, "output_limit": 4 * 1024 * 1024, "artifact_limit": 64 * 1024 * 1024}
    for key in defaults:
        parser.add_argument("--" + key.replace("_", "-"), type=float if "timeout" in key else int)
    args = parser.parse_args()
    try:
        selected = common.read_json(args.replay / "case.json" if args.replay else args.case)
        validate_case(selected)
        saved_report = common.read_json(args.replay / "report.json", defaults["artifact_limit"]) if args.replay else None
        if args.replay and not isinstance(saved_report, dict):
            raise ValueError("saved report must be an object")
        args.backend = common.resolve_backend(args.backend, saved_report)
        saved = saved_report.get("budgets", {}) if saved_report is not None else {}
        if not isinstance(saved, dict):
            raise ValueError("saved budgets must be an object")
        if args.case_tool is None:
            args.case_tool = ROOT / ".lake/build/bin" / profile(selected)["caseTool"]
        if args.core_runner is None:
            args.core_runner = ROOT / ".lake/build/bin" / profile(selected)["coreRunner"]
    except (ValueError, OSError, KeyError, TypeError, Finding) as error:
        parser.error(str(error))
    for key, default in defaults.items():
        explicit = getattr(args, key)
        value = saved.get(key, default) if explicit is None else explicit
        if isinstance(value, bool) or not isinstance(value, (int, float)) or ("timeout" not in key and not isinstance(value, int)) or not math.isfinite(value) or not 0 < value <= 10**9:
            parser.error(f"invalid positive bounded {key}")
        if key == "direct_fuel" and value > 10000000:
            parser.error("direct fuel exceeds native tool limit")
        if args.replay and explicit is not None and value != saved.get(key):
            parser.error("exact replay must retain every saved budget; use --case for changed budgets")
        setattr(args, key, value)
    for key in ("case", "replay", "output", "case_tool", "core_runner", "anvil", "upstream", "target_dir", "solc"):
        if getattr(args, key) is not None:
            setattr(args, key, getattr(args, key).resolve())
    args.output.mkdir(parents=True, exist_ok=False)
    report = {"schema": REPORT_SCHEMA, "backend": args.backend, "pathBackends": common.path_backends(args.backend),
        "processes": [], "histories": {}, "budgets": {key: getattr(args, key) for key in defaults},
        "scope": scope(selected)}
    previous_term = signal.getsignal(signal.SIGTERM)
    def interrupted(_signal, _frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    try:
        execute(args, report)
    except KeyboardInterrupt:
        report["comparison"] = interrupted_comparison(args, report,
            {"category": "inconclusive-resource", "stage": "runner", "detail": "interrupted", "pairs": {}})
    except Finding as error:
        report["comparison"] = interrupted_comparison(args, report,
            {"category": error.category, "stage": error.stage, "detail": error.detail, "pairs": {}})
    except (ValueError, OSError, KeyError, TypeError, RpcError, subprocess.SubprocessError) as error:
        report["comparison"] = interrupted_comparison(args, report,
            {"category": "adapter-error", "stage": "runner", "detail": str(error), "pairs": {}})
    finally:
        try:
            report["artifacts"] = {path.name: common.file_digest(path) for path in args.output.iterdir() if path.is_file()}
            save(args.output / "report.json", report)
        finally:
            signal.signal(signal.SIGTERM, previous_term)
    category = report["comparison"]["category"]
    print(json.dumps({"category": category, "report": str(args.output / "report.json")}))
    return 0 if category == "matched" else 1


if __name__ == "__main__":
    raise SystemExit(main())
