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
ASSEMBLY_LOOP_CASE_SCHEMA = "solcore-lean.semantic-assembly-storage-loop-case.v1"
ASSEMBLY_KECCAK_LOOP_CASE_SCHEMA = "solcore-lean.semantic-assembly-keccak-loop-case.v1"
ADT_CASE_SCHEMA = "solcore-lean.semantic-adt-storage-case.v1"
ADT_HISTORY_SCHEMA = "solcore-lean.adt-storage-history.v1"
TUPLE_CASE_SCHEMA = "solcore-lean.semantic-tuple-return-case.v1"
TUPLE_HISTORY_SCHEMA = "solcore-lean.tuple-return-history.v1"
BYTES_RETURN_CASE_SCHEMA = "solcore-lean.semantic-bytes-return-case.v1"
BYTES_RETURN_HISTORY_SCHEMA = "solcore-lean.bytes-return-history.v1"
ENUM_RETURN_CASE_SCHEMA = "solcore-lean.semantic-enum-return-case.v1"
ENUM_RETURN_HISTORY_SCHEMA = "solcore-lean.enum-return-history.v1"
ENUM_ARGUMENT_CASE_SCHEMA = "solcore-lean.semantic-enum-argument-case.v1"
ENUM_ARGUMENT_HISTORY_SCHEMA = "solcore-lean.enum-argument-history.v1"
ENUM_ARRAY_CASE_SCHEMA = "solcore-lean.semantic-enum-array-case.v1"
ENUM_ARRAY_HISTORY_SCHEMA = "solcore-lean.enum-array-history.v1"
ARRAY_RETURN_CASE_SCHEMA = "solcore-lean.semantic-array-return-case.v1"
ARRAY_RETURN_HISTORY_SCHEMA = "solcore-lean.array-return-history.v1"
CONSTRUCTOR_ARGUMENT_CASE_SCHEMA = "solcore-lean.semantic-constructor-argument-case.v1"
CONSTRUCTOR_ARGUMENT_HISTORY_SCHEMA = "solcore-lean.constructor-argument-history.v1"
# `declared`: per-case observed slots plus Hull/EVM containment; `abi`: calldata form;
# `logs`: ordered committed logs are part of every observation; `balances`: transactions
# carry call value and the contract's committed balance is observed; `deploymentLogs`:
# the deployment receipt must carry no logs even when transactions' logs are not compared;
# `senders`: each transaction names one of LEDGER_SENDERS, which sends it on every path.
# `encoding`: the canonical calldata a malformed-calldata profile changes, `array` by default.
# `forms`: the inline Yul forms a plan may record; the form changes only the source.
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
    # The storage-loop plan with every storage access in inline Yul blocks around
    # the Solcore step call, in the plan's form. Its Core reference, history and
    # protocol are the storage-loop profile's.
    "stateful-assembly-storage-loops": {"caseSchema": ASSEMBLY_LOOP_CASE_SCHEMA,
        "planSchema": "solcore-lean.assembly-storage-loop-plan.v1", "planKey": "storageLoopPlan",
        "corpusSchema": "solcore-lean.semantic-assembly-storage-loop-corpus.v1",
        "originKind": "assembly-storage-loop-generated", "contract": "SynthesizedAssemblyStorageLoops",
        "caseTool": "semantic-assembly-storage-loop-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": LOOP_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256)", "selector": "0x7357f5d2", "rollback": True, "keyed": False,
        "declared": True, "abi": "loops", "forms": ("split", "carried", "pipelined"), "shrinkBatch": 32},
    # The Keccak-loop plan with every storage access, entry hash and log in inline
    # Yul blocks around the Solcore step call, in the plan's form. Its Core
    # reference, history and protocol are the Keccak-loop profile's.
    "stateful-assembly-keccak-loops": {"caseSchema": ASSEMBLY_KECCAK_LOOP_CASE_SCHEMA,
        "planSchema": "solcore-lean.assembly-keccak-loop-plan.v1", "planKey": "keccakLoopPlan",
        "corpusSchema": "solcore-lean.semantic-assembly-keccak-loop-corpus.v1",
        "originKind": "assembly-keccak-loop-generated", "contract": "SynthesizedAssemblyKeccakLoops",
        "caseTool": "semantic-assembly-keccak-loop-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": KECCAK_LOOP_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256)", "selector": "0x7357f5d2", "rollback": True, "keyed": False,
        "declared": True, "abi": "keccak-loops", "logs": True, "forms": ("split", "carried", "pipelined"),
        "shrinkBatch": 16},
    # User-defined enum and struct values in contract fields and behind mapping
    # keys through std.StorageGeneric. Each case records its type shape, methods
    # and keys, and its observed slots follow from the layout. A case reaches
    # about 200 KB, so a native shrink response carries at most 16 candidates.
    "stateful-adt-storage": {"caseSchema": ADT_CASE_SCHEMA, "planSchema": "solcore-lean.adt-storage-plan.v1",
        "planKey": "adtStoragePlan", "corpusSchema": "solcore-lean.semantic-adt-storage-corpus.v1",
        "originKind": "adt-storage-generated", "contract": "SynthesizedAdtStorage",
        "caseTool": "semantic-adt-storage-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": ADT_HISTORY_SCHEMA,
        "signature": None, "selector": None, "rollback": True, "keyed": False,
        "declared": True, "abi": "adts", "shrinkBatch": 16},
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
    # One method that returns a `bytes` value of zero to 64 bytes; every path's
    # whole return data is compared. A case reaches about 70 KB, so a native
    # shrink response carries at most 32 candidates.
    "stateful-bytes-returns": {"caseSchema": BYTES_RETURN_CASE_SCHEMA, "planSchema": "solcore-lean.bytes-return-plan.v1",
        "planKey": "bytesReturnPlan", "corpusSchema": "solcore-lean.semantic-bytes-return-corpus.v1",
        "originKind": "bytes-return-generated", "contract": "SynthesizedBytesReturns",
        "caseTool": "semantic-bytes-return-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": BYTES_RETURN_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256,uint256)", "selector": "0x24b912e5", "rollback": True, "keyed": False,
        "declared": True, "abi": "bytes-returns", "shrinkBatch": 32},
    # One method that returns a value of a user enum of two to four
    # constructors; every path's whole return data is compared. A case reaches
    # about 60 KB, so a native shrink response carries at most 32 candidates.
    "stateful-enum-returns": {"caseSchema": ENUM_RETURN_CASE_SCHEMA, "planSchema": "solcore-lean.enum-return-plan.v1",
        "planKey": "enumReturnPlan", "corpusSchema": "solcore-lean.semantic-enum-return-corpus.v1",
        "originKind": "enum-return-generated", "contract": "SynthesizedEnumReturns",
        "caseTool": "semantic-enum-return-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": ENUM_RETURN_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256,uint256,uint256)", "selector": "0x15509d2b", "rollback": True, "keyed": False,
        "declared": True, "abi": "enum-returns", "shrinkBatch": 32},
    # One method that takes a value of a user enum of two to four constructors,
    # canonically or malformed. Original Core decodes the calldata itself; a std
    # rejection is compared by its selector, and an unknown tag's empty revert
    # data by the Word zero. The signature and selector follow the plan's shape.
    # A case reaches about 70 KB, so a native shrink response carries at most 32
    # candidates.
    "stateful-enum-arguments": {"caseSchema": ENUM_ARGUMENT_CASE_SCHEMA, "planSchema": "solcore-lean.enum-argument-plan.v1",
        "planKey": "enumArgumentPlan", "corpusSchema": "solcore-lean.semantic-enum-argument-corpus.v1",
        "originKind": "enum-argument-generated", "contract": "SynthesizedEnumArguments",
        "caseTool": "semantic-enum-argument-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": ENUM_ARGUMENT_HISTORY_SCHEMA,
        "signature": None, "selector": None, "rollback": True, "keyed": False,
        "declared": True, "abi": "enum-arguments", "shrinkBatch": 32},
    # One method that takes a calldata array of up to three values of a user
    # enum of two to four constructors and two indices, canonically or
    # malformed. Original Core decodes the array's head and both indexed
    # elements itself; a std rejection, ArrayOutOfBounds() among them, is
    # compared by its selector, and an unknown tag's empty revert data by the
    # Word zero. The signature and selector follow the plan's shape. A case
    # reaches about 140 KB, so a native shrink response carries at most 16
    # candidates.
    "stateful-enum-array-arguments": {"caseSchema": ENUM_ARRAY_CASE_SCHEMA, "planSchema": "solcore-lean.enum-array-plan.v1",
        "planKey": "enumArrayPlan", "corpusSchema": "solcore-lean.semantic-enum-array-corpus.v1",
        "originKind": "enum-array-generated", "contract": "SynthesizedEnumArrays",
        "caseTool": "semantic-enum-array-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": ENUM_ARRAY_HISTORY_SCHEMA,
        "signature": None, "selector": None, "rollback": True, "keyed": False,
        "declared": True, "abi": "enum-arrays", "shrinkBatch": 16},
    # One method declared to return uint256 that returns std's ABI encoding of a
    # memory array of up to three uint256, bytes4, bytes or uint256[] elements:
    # std's abi_encode, then the return_ opcode, as std's dispatcher does after
    # a method returns. The plan fixes the array's shape and every transaction
    # carries it as its choice and length; every path's whole return data is
    # compared. A case reaches about 70 KB, so a native shrink response carries
    # at most 32 candidates.
    "stateful-array-returns": {"caseSchema": ARRAY_RETURN_CASE_SCHEMA, "planSchema": "solcore-lean.array-return-plan.v1",
        "planKey": "arrayReturnPlan", "corpusSchema": "solcore-lean.semantic-array-return-corpus.v1",
        "originKind": "array-return-generated", "contract": "SynthesizedArrayReturns",
        "caseTool": "semantic-array-return-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": ARRAY_RETURN_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256,uint256,uint256)", "selector": "0x15509d2b", "rollback": True, "keyed": False,
        "declared": True, "abi": "array-returns", "shrinkBatch": 32},
    # One constructor whose parameters std decodes from the argument bytes the
    # deployment appends to the init code, canonical or with one malformation,
    # and one method over the record it writes. The deployment row is compared:
    # its status, std's revert data, which original Core gives as a Word under
    # the selector and empty-revert rules, and the whole committed storage. A
    # failed deployment ends the scenario on every path, the EVM path bound to
    # the would-be creation address.
    "stateful-constructor-arguments": {"caseSchema": CONSTRUCTOR_ARGUMENT_CASE_SCHEMA,
        "planSchema": "solcore-lean.constructor-argument-plan.v1", "planKey": "constructorArgumentsPlan",
        "corpusSchema": "solcore-lean.semantic-constructor-argument-corpus.v1",
        "originKind": "constructor-argument-generated", "contract": "SynthesizedConstructorArguments",
        "caseTool": "semantic-constructor-argument-tool", "coreRunner": "rust-hull-keyed-storage-scenario",
        "scenarioSchema": "solcore-lean.keyed-storage-contract-scenario.v1", "historySchema": CONSTRUCTOR_ARGUMENT_HISTORY_SCHEMA,
        "signature": "run(uint256,uint256)", "selector": "0x7357f5d2", "rollback": True, "keyed": False,
        "declared": True, "abi": "constructor-arguments", "shrinkBatch": 32},
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
# The enum and struct storage profile: an enum of two to four variants, each
# with zero to three Words or one two-Word struct, in at most four slots; a
# record of two Words and the enum at a drawn position; the methods in
# declaration order with their parameters; the odd multiplier of written Words
# and digests; the key bases generation draws, the last wrapping to zero.
ADT_PAYLOAD_WIDTHS = {"words0": 0, "words1": 1, "words2": 2, "words3": 3, "pair": 2}
ADT_MIN_VARIANTS, ADT_MAX_VARIANTS, ADT_MAX_CHOICE_SLOTS, ADT_RECORD_FIELDS = 2, 4, 4, 3
ADT_WORD_TYPES = ("word", "uint256")
ADT_METHODS = {
    "putChoice": ("flags", "variant", "input"), "putChoiceAt": ("flags", "key", "variant", "input"),
    "clearChoice": ("flags", "input"), "clearChoiceAt": ("flags", "key", "input"),
    "getChoice": ("flags",), "getChoiceAt": ("flags", "key"),
    "putRecord": ("flags", "variant", "input"), "putRecordAt": ("flags", "key", "variant", "input"),
    "setRecord": ("flags", "field", "variant", "input"), "setRecordAt": ("flags", "key", "field", "variant", "input"),
    "getRecord": ("flags",), "getRecordAt": ("flags", "key")}
ADT_MULTIPLIER = 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95
ADT_KEY_BASES = (0, 1, 3, 2**255, 2**256 - 1)
# The tuple-return profile: slot 0 the accumulator, slot 1 the committed call
# count, slot 2 the last committed input; plans return two to four Words.
TUPLE_SLOTS = [str(slot) for slot in range(3)]
TUPLE_ARITIES = (2, 3, 4)
# The bytes-return profile: the tuple profile's slots; a transaction requests
# zero to 64 bytes, which the contract reads modulo 65, of two data Words built
# with this odd multiplier.
BYTES_RETURN_SLOTS = [str(slot) for slot in range(3)]
MAX_RETURN_LENGTH = 64
RETURN_MULTIPLIER = 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95
# The enum-return profile: the tuple profile's slots; a plan declares two to
# four constructors named from this bank without repetition, each with the
# fields of one of these ABI signatures, whose head takes these bytes; at most
# two carry `bytes`. The returned data Words are the bytes-return profile's.
ENUM_RETURN_SLOTS = [str(slot) for slot in range(3)]
ENUM_NAMES = ("Idle", "Ready", "Pair", "Blob", "Settled", "Q", "Rejected", "OverflowedAccumulator")
ENUM_FIELD_HEADS = {"": 0, "uint256": 32, "uint256,uint256": 64, "bytes": 32}
# The enum-argument profile: slots 0 to 4, the accumulator, the decoded index
# and three decoded Words. A plan's constructors are named from the enum bank;
# each declared field type has std's signature, a struct's being its fields',
# and a head of these bytes. An unknown tag reverts with empty data.
ENUM_ARGUMENT_SLOTS = [str(slot) for slot in range(5)]
ENUM_ARGUMENT_FIELDS = {"": ("", 0), "uint256": ("uint256", 32), "uint256,uint256": ("uint256,uint256", 64),
                        "ScPair": ("uint256,uint256", 64), "bytes": ("bytes", 32)}
ENUM_ARGUMENT_KINDS = ("none", "short", "selector", "truncate", "trailing", "tag", "retag", "offset", "aliased",
                       "unused", "tail", "length", "padding")
STD_EMPTY_REVERT = "0x"
# The enum-array profile: slots 0 to 9, the accumulator, the length and both
# decoded elements' index and three Words; up to three elements of the
# enum-argument shapes, and an index past the length reverts with std's
# ArrayOutOfBounds() selector.
ENUM_ARRAY_SLOTS = [str(slot) for slot in range(10)]
ENUM_ARRAY_KINDS = ("none", "short", "selector", "truncate", "trailing", "offset", "count", "tag", "retag", "entry",
                    "share", "unused", "tail", "length", "padding")
STD_OUT_OF_BOUNDS = "0x7f52b2bf"
MAX_ARRAY_ELEMENTS = 3
# The array-return profile: the tuple profile's slots; a plan returns up to
# three elements of one of these element types, each `bytes` or `uint256[]`
# element with an inner length up to its bound, which the source reads from the
# digits of this base in `choice`. The element Words use the bytes-return
# multiplier.
ARRAY_RETURN_SLOTS = [str(slot) for slot in range(3)]
ARRAY_RETURN_ELEMENTS = {"uint256": (1, 0), "bytes4": (1, 0), "bytes": (65, 64), "uint256[]": (3, 2)}
MAX_ARRAY_RETURN_COUNT = 3
# The constructor-argument profile: slots 0 to 5, the accumulator and the record
# the constructor writes. A plan's parameters are one of these kinds, an enum's
# constructors as for the enum-argument profile. The arguments are canonical or
# carry one of these malformations.
CONSTRUCTOR_ARGUMENT_SLOTS = [str(slot) for slot in range(6)]
CONSTRUCTOR_PARAMETERS = ("none", "uint256", "uint256,uint256", "uint256,bytes", "uint256,enum")
CONSTRUCTOR_KINDS = ("none", "truncate", "trailing", "offset", "length", "tag", "tagCut", "tail", "narrow")
# std's bound on a decoded `bytes` length, ~0 - 63.
MAX_DECODED_LENGTH = 2**256 - 64
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
    if profile(case)["abi"] in ("malformed", "methods", "enum-arguments", "enum-arrays") and \
            transaction.get("stdRejection") is not None:
        return "reverted"
    if profile(case)["abi"] == "enum-arrays":
        # The decoded flags' parity, as for the enum arguments.
        return "reverted" if enum_array_decode(case, enum_array_input(case, transaction))[1][0] % 2 else "returned"
    if profile(case)["abi"] == "enum-arguments":
        # The decoded flags' parity: an aliased body takes its flags from a tag.
        return "reverted" if enum_argument_decode(case, enum_argument_input(case, transaction))[1][0] % 2 else "returned"
    if profile(case)["abi"] == "methods":
        # A call's odd input sum reverts.
        return "reverted" if sum(int(common.word(value)) for value in transaction["inputs"]) % 2 else "returned"
    if profile(case)["abi"] == "keccak-loops":
        # Odd flags revert after every logged iteration.
        return "reverted" if int(common.word(transaction["flags"])) % 2 else "returned"
    if profile(case)["abi"] == "adts":
        # Odd flags revert after the writes.
        return "reverted" if int(common.word(transaction["flags"])) % 2 else "returned"
    if profile(case)["abi"] == "bytes-returns":
        # Odd flags revert after the writes.
        return "reverted" if int(common.word(transaction["flags"])) % 2 else "returned"
    if profile(case)["abi"] == "enum-returns":
        # Odd flags revert after the writes.
        return "reverted" if int(common.word(transaction["flags"])) % 2 else "returned"
    if profile(case)["abi"] == "array-returns":
        # Odd flags revert after the writes.
        return "reverted" if int(common.word(transaction["flags"])) % 2 else "returned"
    if profile(case)["abi"] == "constructor-arguments":
        # Odd flags revert after the write.
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


def has_adts(case: dict) -> bool:
    return profile(case)["abi"] == "adts"


def adt_choice_size(widths: list[int]) -> int:
    """A right-nested sum's slots: one tag and the larger of its first variant
    and the sum of the rest; a single variant has no tag."""
    if len(widths) == 1:
        return widths[0]
    return 1 + max(widths[0], adt_choice_size(widths[1:]))


def adt_shape(case: dict) -> dict:
    """The plan's validated shape: payload widths, the clear variant, the enum
    and record sizes, the record's field offsets and the field slots."""
    shape = case.get("adtStoragePlan", {}).get("shape")
    if not isinstance(shape, dict) or set(shape) != {"variants", "position", "wordType"} or \
            not isinstance(shape["variants"], list) or any(name not in ADT_PAYLOAD_WIDTHS for name in shape["variants"]):
        raise ValueError("an enum and struct storage plan records its variants, enum position and Word type")
    widths = [ADT_PAYLOAD_WIDTHS[name] for name in shape["variants"]]
    if not ADT_MIN_VARIANTS <= len(widths) <= ADT_MAX_VARIANTS or "words0" not in shape["variants"] or \
            adt_choice_size(widths) > ADT_MAX_CHOICE_SLOTS or type(shape["position"]) is not int or \
            shape["position"] not in range(ADT_RECORD_FIELDS) or shape["wordType"] not in ADT_WORD_TYPES:
        raise ValueError("a shape has two to four variants, one payload-free, at most four enum slots, the enum at "
                         "record position 0, 1 or 2 and a Word type")
    choice = adt_choice_size(widths)
    sizes = [choice if field == shape["position"] else 1 for field in range(ADT_RECORD_FIELDS)]
    offsets = [sum(sizes[:field]) for field in range(ADT_RECORD_FIELDS)]
    record = sum(sizes)
    return {"widths": widths, "position": shape["position"], "clear": shape["variants"].index("words0"),
            "choiceSlots": choice, "recordSlots": record, "fieldOffsets": offsets,
            "choiceSlot": 1, "recordSlot": 1 + choice, "choicesSlot": 1 + choice + record, "recordsSlot": 2 + choice + record}


def adt_layout(case: dict) -> dict:
    """The layout a case's contract metadata records, recomputed from its shape."""
    shape = adt_shape(case)
    return {"accumulatorSlot": 0, "choiceSlot": shape["choiceSlot"], "choiceSlots": shape["choiceSlots"],
            "recordSlot": shape["recordSlot"], "recordSlots": shape["recordSlots"], "fieldOffsets": shape["fieldOffsets"],
            "choicesSlot": shape["choicesSlot"], "recordsSlot": shape["recordsSlot"], "clearVariant": shape["clear"]}


def adt_entry(base: int, key: int) -> int:
    """The pinned std's first slot of `m[key]` for a mapping at slot `base`."""
    return int.from_bytes(keccak256(base.to_bytes(32, "big") + (key % 2**256).to_bytes(32, "big")), "big")


def adt_keys(case: dict) -> list[int]:
    base = int(common.word(case.get("adtStoragePlan", {}).get("keyBase"), "key base"))
    return [base, (base + 1) % 2**256]


def adt_slots(case: dict) -> list[str]:
    """Every slot the protocol writes, stale payload slots included: the
    accumulator, the enum and record fields' slots, and at both keys the entry
    slots of both mappings, in increasing numeric order."""
    shape = adt_shape(case)
    values = {0} | {shape["choiceSlot"] + offset for offset in range(shape["choiceSlots"])} | \
        {shape["recordSlot"] + offset for offset in range(shape["recordSlots"])}
    for key in adt_keys(case):
        values |= {(adt_entry(shape["choicesSlot"], key) + offset) % 2**256 for offset in range(shape["choiceSlots"])}
        values |= {(adt_entry(shape["recordsSlot"], key) + offset) % 2**256 for offset in range(shape["recordSlots"])}
    return [str(value) for value in sorted(values)]


def adt_contract(case: dict) -> None:
    """The contract metadata: the plan's methods in declaration order with their
    signatures, selectors and parameters, and the layout of its shape."""
    plan, name = case.get("adtStoragePlan"), profile(case)["contract"]
    methods = plan.get("methods") if isinstance(plan, dict) else None
    if not isinstance(methods, list) or not methods or methods != [method for method in ADT_METHODS if method in methods]:
        raise ValueError("an enum and struct storage plan declares one to twelve methods in declaration order")
    rows = [{"name": method, "signature": method_signature(method, len(ADT_METHODS[method])),
             "selector": method_selector(method_signature(method, len(ADT_METHODS[method]))),
             "parameters": list(ADT_METHODS[method])} for method in methods]
    expected = {"name": name, "methods": rows, "layout": adt_layout(case), "deployPath": [name + "Deploy"],
                "runtimePath": [name + "Deploy", name], "constructorCalldata": "0x"}
    if case.get("contract") != expected:
        raise Finding("unsupported-scope", "input", "enum and struct storage contract metadata differs from its plan")


def adt_arguments(case: dict, tx: dict) -> list[int]:
    """A transaction's argument Words in its method's parameter order, each
    within the case: a key of the two, a field below three, a variant of the
    shape; it carries exactly its method's parameters."""
    method = tx.get("method")
    if method not in case["adtStoragePlan"]["methods"]:
        raise ValueError("an enum and struct storage transaction calls a declared method")
    parameters = ADT_METHODS[method]
    if set(tx) != {"id", "method", "calldata", "value", *parameters}:
        raise ValueError("an enum and struct storage transaction carries exactly its method's arguments")
    words = []
    for parameter in parameters:
        if parameter in ("field", "variant"):
            value = tx[parameter]
            bound = ADT_RECORD_FIELDS if parameter == "field" else len(adt_shape(case)["widths"])
            if type(value) is not int or not 0 <= value < bound:
                raise ValueError(f"transaction {parameter} lies outside the case")
        else:
            value = int(common.word(tx[parameter], "transaction " + parameter))
            if parameter == "key" and value not in adt_keys(case):
                raise ValueError("transaction key is not one of the case's two keys")
        words.append(value)
    return words


def adt_write_choice(state: dict, shape: dict, first: int, origin: int, variant: int, result: int) -> None:
    """Variant `variant` written at `first`: tag one at its outer levels, zero
    at its own unless it is the last, then each payload Word at offset `o` from
    the written value's first slot `origin` slots before as `result + o·K`."""
    count = len(shape["widths"])
    for level in range(min(variant, count - 1)):
        state[(first + level) % 2**256] = 1
    if variant + 1 < count:
        state[(first + variant) % 2**256] = 0
    payload = variant + 1 if variant + 1 < count else count - 1
    for index in range(shape["widths"][variant]):
        state[(first + payload + index) % 2**256] = (result + (origin + payload + index) * ADT_MULTIPLIER) % 2**256


def adt_read_choice(state: dict, shape: dict, first: int) -> list[int]:
    """The decoded variant index and payload Words: the outermost zero tag
    selects its level's variant, past every level the last."""
    count = len(shape["widths"])
    for level in range(count - 1):
        if state.get((first + level) % 2**256, 0) == 0:
            return [level] + [state.get((first + level + 1 + index) % 2**256, 0) for index in range(shape["widths"][level])]
    return [count - 1] + [state.get((first + count - 1 + index) % 2**256, 0) for index in range(shape["widths"][count - 1])]


def adt_digest(tokens: list[int]) -> int:
    value = 0
    for token in tokens:
        value = (value * ADT_MULTIPLIER + token) % 2**256
    return value


def adt_effect(case: dict, tx: dict, state: dict, result: int | None) -> int:
    """Apply one returned transaction to `state`, a map from observed slot to
    Word: a write stores its value with the step result `result` (the row's
    output), a read decodes. Returns the result the protocol fixes; a write's
    is the output itself."""
    shape = adt_shape(case)
    method = tx["method"]
    keyed, record = method.endswith("At"), "Record" in method
    if keyed:
        first = adt_entry(shape["recordsSlot" if record else "choicesSlot"], int(common.word(tx["key"], "transaction key")))
    else:
        first = shape["recordSlot" if record else "choiceSlot"]
    if method.startswith("get"):
        if record:
            tokens = []
            for field, offset in enumerate(shape["fieldOffsets"]):
                slot = (first + offset) % 2**256
                tokens += adt_read_choice(state, shape, slot) if field == shape["position"] else [state.get(slot, 0)]
        else:
            tokens = adt_read_choice(state, shape, first)
        result = adt_digest(tokens)
    elif method.startswith("clear"):
        adt_write_choice(state, shape, first, 0, shape["clear"], result)
    elif not record:
        adt_write_choice(state, shape, first, 0, tx["variant"], result)
    else:
        fields = [tx["field"]] if method.startswith("set") else range(ADT_RECORD_FIELDS)
        for field in fields:
            offset = shape["fieldOffsets"][field]
            if field == shape["position"]:
                adt_write_choice(state, shape, (first + offset) % 2**256, offset, tx["variant"], result)
            else:
                state[(first + offset) % 2**256] = (result + offset * ADT_MULTIPLIER) % 2**256
    state[0] = result
    return result


def adt_fields(case: dict, transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a returned row that break the layout protocol, from an
    independent model of the layout over the prior observed slots: a write's
    tags and payload Words `r + o·K` with `r` its output, a read's digest of the
    decoded Words as its output, the accumulator, and every other observed
    slot unchanged. A revert is checked by rollback."""
    if row["status"] != "returned":
        return []
    output = int.from_bytes(common.hex_bytes(row["output"], "output"), "big")
    state = {int(entry["slot"]): int(entry["value"]) for entry in prior}
    expected = adt_effect(case, transaction, state, output)
    after = {int(entry["slot"]): int(entry["value"]) for entry in row["committedStorage"]}
    fields = []
    if after != {slot: state[slot] for slot in after} or set(state) != set(after):
        fields.append("committedStorage")
    if output != expected:
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
    a returned `bytes` value its offset, its length and its data padded to
    whole Words, a returned enum value its encoding's Words (`enum_words`), a
    returned array its encoding's Words (`array_return_words`), every other
    row one."""
    if has_array_returns(case) and row["status"] == "returned":
        return array_return_words(case)
    if has_enum_returns(case) and row["status"] == "returned":
        return enum_words(case, case["transactions"][row["index"]])
    if has_bytes_returns(case) and row["status"] == "returned":
        return 2 + (return_length(case["transactions"][row["index"]]) + 31) // 32
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


def has_bytes_returns(case: dict) -> bool:
    return profile(case)["abi"] == "bytes-returns"


def return_length(transaction: dict) -> int:
    """The length a bytes-return transaction requests, as the contract reads it."""
    return int(common.word(transaction.get("length"), "transaction length")) % (MAX_RETURN_LENGTH + 1)


def bytes_return_fields(case: dict, transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a returned row that break the bytes-return protocol: slot one
    grows by one, slot two is the input, and the output is std's encoding of
    the first `length` bytes of the committed slot zero times the multiplier
    and the committed slot one times the multiplier xor the prior slot two:
    the offset 32, the length, those bytes, then zeros up to a whole Word. A
    revert is checked by rollback."""
    if row["status"] != "returned":
        return []
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    before = {entry["slot"]: int(entry["value"]) for entry in prior}
    fields = []
    if after["1"] != (before["1"] + 1) % 2**256 or after["2"] != int(common.word(transaction.get("input"), "transaction input")):
        fields.append("committedStorage")
    length = return_length(transaction)
    data = (after["0"] * RETURN_MULTIPLIER % 2**256).to_bytes(32, "big") + (
        (after["1"] * RETURN_MULTIPLIER % 2**256) ^ before["2"]).to_bytes(32, "big")
    expected = (32).to_bytes(32, "big") + length.to_bytes(32, "big") + data[:length] + bytes(-length % 32)
    if common.hex_bytes(row["output"], "output") != expected:
        fields.append("output")
    return fields


def has_enum_returns(case: dict) -> bool:
    return profile(case)["abi"] == "enum-returns"


def valid_enum_plan(plan: dict) -> bool:
    """Two to four constructors with distinct names from the bank and known
    fields, at most two with `bytes`."""
    constructors = plan.get("constructors")
    if not isinstance(constructors, list) or not 2 <= len(constructors) <= 4 or any(
            not isinstance(constructor, dict) or set(constructor) != {"name", "fields"} or
            constructor["name"] not in ENUM_NAMES or constructor["fields"] not in ENUM_FIELD_HEADS
            for constructor in constructors):
        return False
    names = [constructor["name"] for constructor in constructors]
    return len(set(names)) == len(names) and [constructor["fields"] for constructor in constructors].count("bytes") <= 2


def enum_constructors(case: dict) -> list[tuple[str, str]]:
    return [(constructor["name"], constructor["fields"]) for constructor in case[profile(case)["planKey"]]["constructors"]]


def enum_choice(case: dict, transaction: dict) -> tuple[str, str]:
    """The constructor a transaction chooses, as the contract reads its choice."""
    constructors = enum_constructors(case)
    return constructors[int(common.word(transaction.get("choice"), "transaction choice")) % len(constructors)]


def enum_layout(case: dict) -> tuple[bool, int]:
    """Whether the enum is static, and its body's head: the tag Word and the
    widest constructor's fields, a `bytes` field counting its offset Word."""
    fields = [fields for _, fields in enum_constructors(case)]
    return "bytes" not in fields, 32 + max(ENUM_FIELD_HEADS[field] for field in fields)


def enum_words(case: dict, transaction: dict) -> int:
    """A static enum returns its body's head; a dynamic one the offset Word and
    the head, then a `bytes` field's length Word and padded data."""
    static, head = enum_layout(case)
    if static:
        return head // 32
    tail = 1 + (return_length(transaction) + 31) // 32 if enum_choice(case, transaction)[1] == "bytes" else 0
    return 1 + head // 32 + tail


def enum_return_fields(case: dict, transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a returned row that break the enum-return protocol: slot one
    grows by one, slot two is the input, and the output is std's encoding of the
    chosen constructor: its tag `keccak256("Name(fields)")`, its fields built from
    the committed slots and the prior slot two as for bytes returns, zeros up to
    the body's head and a `bytes` field's tail, after the offset 32 for a dynamic
    enum. A revert is checked by rollback."""
    if row["status"] != "returned":
        return []
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    before = {entry["slot"]: int(entry["value"]) for entry in prior}
    fields = []
    if after["1"] != (before["1"] + 1) % 2**256 or after["2"] != int(common.word(transaction.get("input"), "transaction input")):
        fields.append("committedStorage")
    static, head = enum_layout(case)
    name, kind = enum_choice(case, transaction)
    first = (after["0"] * RETURN_MULTIPLIER % 2**256).to_bytes(32, "big")
    second = ((after["1"] * RETURN_MULTIPLIER % 2**256) ^ before["2"]).to_bytes(32, "big")
    length = return_length(transaction)
    heads = {"": b"", "uint256": first, "uint256,uint256": first + second, "bytes": head.to_bytes(32, "big")}
    tail = length.to_bytes(32, "big") + (first + second)[:length] + bytes(-length % 32) if kind == "bytes" else b""
    body = keccak256(f"{name}({kind})".encode()) + heads[kind] + bytes(head - 32 - len(heads[kind])) + tail
    if common.hex_bytes(row["output"], "output") != (body if static else (32).to_bytes(32, "big") + body):
        fields.append("output")
    return fields


def has_enum_arguments(case: dict) -> bool:
    return profile(case)["abi"] == "enum-arguments"


def valid_enum_argument_plan(plan: dict) -> bool:
    """Two to four constructors with distinct names from the bank and known
    field types, the struct among them, at most two with `bytes`."""
    constructors = plan.get("constructors")
    if not isinstance(constructors, list) or not 2 <= len(constructors) <= 4 or any(
            not isinstance(constructor, dict) or set(constructor) != {"name", "fields"} or
            constructor["name"] not in ENUM_NAMES or constructor["fields"] not in ENUM_ARGUMENT_FIELDS
            for constructor in constructors):
        return False
    names = [constructor["name"] for constructor in constructors]
    return len(set(names)) == len(names) and [constructor["fields"] for constructor in constructors].count("bytes") <= 2


def enum_argument_layout(case: dict) -> tuple[bool, int]:
    """Whether the enum is static, and its body's head: the tag Word and the
    widest constructor's fields, a `bytes` field counting its offset Word."""
    fields = [fields for _, fields in enum_constructors(case)]
    return "bytes" not in fields, 32 + max(ENUM_ARGUMENT_FIELDS[field][1] for field in fields)


def enum_argument_tag(name: str, fields: str) -> int:
    """std's variant tag, `keccak256("Name(fields)")`, with the fields' signature."""
    return int.from_bytes(keccak256(f"{name}({ENUM_ARGUMENT_FIELDS[fields][0]})".encode()), "big")


def enum_argument_signature(case: dict) -> str:
    """std's structural signature: the field signatures nested to the right in `sum(left,right)`."""
    signatures = [ENUM_ARGUMENT_FIELDS[fields][0] for _, fields in enum_constructors(case)]
    nested = signatures[-1]
    for signature in reversed(signatures[:-1]):
        nested = f"sum({signature},{nested})"
    return f"run(uint256,{nested})"


def enum_argument_contract(case: dict) -> None:
    """The contract metadata: the plan's structural signature and its selector."""
    name = profile(case)["contract"]
    signature = enum_argument_signature(case)
    expected = {"name": name, "method": "run", "signature": signature, "selector": method_selector(signature),
                "deployPath": [name + "Deploy"], "runtimePath": [name + "Deploy", name], "constructorCalldata": "0x"}
    if case.get("contract") != expected:
        raise Finding("unsupported-scope", "input", "enum-argument contract metadata differs from its plan")


def enum_argument_fields_of(tx: dict) -> tuple:
    """A transaction's flags, choice, field Words and length, type-checked."""
    choice, length = tx.get("choice"), tx.get("length")
    if type(choice) is not int or type(length) is not int or not 0 <= choice < 4 or not 0 <= length <= MAX_RETURN_LENGTH:
        raise ValueError("an enum-argument transaction records a constructor index and a length of at most 64")
    return (int(common.word(tx.get("flags"), "transaction flags")), choice,
            int(common.word(tx.get("first"), "transaction first Word")),
            int(common.word(tx.get("second"), "transaction second Word")), length)


def enum_argument_input(case: dict, tx: dict) -> bytes:
    """The calldata a transaction sends: the canonical encoding of its
    constructor, then its one malformation, which must apply to it. The body
    starts at 36 for a static enum and behind the offset 64 for a dynamic one;
    a `bytes` payload is the first `length` bytes of `first · K` and `second · K`."""
    constructors = enum_constructors(case)
    flags, choice, first, second, length = enum_argument_fields_of(tx)
    if choice >= len(constructors) or (length and constructors[choice][1] != "bytes"):
        raise ValueError("an enum-argument transaction encodes a constructor, and only a bytes constructor has a length")
    static, head = enum_argument_layout(case)
    name, fields = constructors[choice]
    word = lambda value: (value % 2**256).to_bytes(32, "big")
    payload = (word(first * RETURN_MULTIPLIER) + word(second * RETURN_MULTIPLIER))[:length]
    field_head = {"": b"", "uint256": word(first), "uint256,uint256": word(first) + word(second),
                  "ScPair": word(first) + word(second), "bytes": word(head)}[fields]
    tail = word(length) + payload + bytes(-length % 32) if fields == "bytes" else b""
    body = word(enum_argument_tag(name, fields)) + field_head + bytes(head - 32 - len(field_head)) + tail
    selector = bytes.fromhex(method_selector(enum_argument_signature(case))[2:])
    data = selector + word(flags) + (body if static else word(64) + body)
    start = 36 if static else 68
    tags = [enum_argument_tag(*constructor) for constructor in constructors]
    malformation = tx.get("malformation")
    kind = malformation.get("kind") if isinstance(malformation, dict) else None
    keys = {"none": set(), "short": {"bytes"}, "selector": {"mask"}, "truncate": {"kept"}, "trailing": {"count", "pattern"},
            "padding": {"pattern"}, "retag": {"constructor"}, "aliased": {"constructor"}}.get(kind, {"value"})
    if kind not in ENUM_ARGUMENT_KINDS or set(malformation) != {"kind"} | keys:
        raise ValueError("an enum-argument transaction carries one known malformation")
    put = lambda bytes_, position, value: bytes_[:position] + word(value) + bytes_[position + 32:]
    number = lambda key: malformation[key] if type(malformation[key]) is int else None
    value = int(common.word(malformation["value"], "malformation value")) if keys == {"value"} else None
    carries = fields == "bytes"
    padding = -length % 32
    def invalid():
        raise ValueError("an enum-argument malformation must apply to its transaction")
    if kind == "none":
        return data
    if kind == "short":
        if number("bytes") is None or not 0 <= malformation["bytes"] < 4:
            invalid()
        return data[:malformation["bytes"]]
    if kind == "selector":
        mask = int(common.word(malformation["mask"], "selector mask"))
        if not 0 < mask < 2**32:
            invalid()
        return ((int.from_bytes(data[:4], "big") ^ mask) % 2**32).to_bytes(4, "big") + data[4:]
    if kind == "truncate":
        if number("kept") is None or not 4 <= malformation["kept"] < len(data):
            invalid()
        return data[:malformation["kept"]]
    if kind == "trailing":
        count = number("count")
        pattern = TRAILING_PATTERNS.index(malformation["pattern"]) if malformation["pattern"] in TRAILING_PATTERNS else None
        if count is None or not 1 <= count <= 64 or pattern is None:
            invalid()
        return data + bytes(0 if pattern == 0 else 0xff if pattern == 1 else (position + 1) % 256 for position in range(count))
    if kind == "tag":
        if value in tags:
            invalid()
        return put(data, start, value)
    if kind in ("retag", "aliased"):
        index = number("constructor")
        if index is None or not 0 <= index < len(constructors) or (kind == "retag" and index == choice) or \
                (kind == "aliased" and static):
            invalid()
        return put(data, start, tags[index]) if kind == "retag" else put(put(data, 36, 0), 4, tags[index])
    if kind == "offset":
        if static or value == 64:
            invalid()
        return put(data, 36, value)
    if kind == "unused":
        if 32 + ENUM_ARGUMENT_FIELDS[fields][1] >= head or value == 0:
            invalid()
        return put(data, start + 32 + ENUM_ARGUMENT_FIELDS[fields][1], value)
    if kind == "tail":
        if not carries or value == head:
            invalid()
        return put(data, start + 32, value)
    if kind == "length":
        if not carries or value == length:
            invalid()
        return put(data, start + head, value)
    pattern = PADDING_PATTERNS.index(malformation["pattern"]) if malformation["pattern"] in PADDING_PATTERNS else None
    if not carries or not padding or pattern is None:
        invalid()
    last = length // 32 * 32
    fill = [0xff if pattern == 0 else (position + 1) % 256 if pattern == 1 else int(position + 1 == padding)
            for position in range(padding)]
    position = start + head + 32 + last
    return data[:position] + payload[last:length] + bytes(fill) + data[position + 32:]


def enum_argument_decode(case: dict, data: bytes) -> tuple:
    """A third reading of the pinned std's dispatcher and derived enum decoder
    for `run(uint256 flags, E value)`: the revert data of a rejection, or None
    with the flags, the one-based index and the three protocol Words. The
    fallback reverts with `0x4924aef0`, a missing or out-of-range read with
    `0x08638556` and an unknown tag with empty data; the tag is compared
    before any field is read."""
    constructors = enum_constructors(case)
    static, head = enum_argument_layout(case)
    size = len(data)
    at = lambda position: int.from_bytes(data[position:position + 32], "big")
    if size < 4 or "0x" + data[:4].hex() != method_selector(enum_argument_signature(case)):
        return STD_NO_SELECTOR, None
    if size < 4 + 32 + (head if static else 32):
        return STD_TRUNCATED, None
    start = 36
    if not static:
        if at(36) > size - 4:
            return STD_TRUNCATED, None
        start = 4 + at(36)
    if size - start < 32:
        return STD_TRUNCATED, None
    found = [index for index, constructor in enumerate(constructors) if enum_argument_tag(*constructor) == at(start)]
    if not found:
        return STD_EMPTY_REVERT, None
    fields = constructors[found[0]][1]
    words = [0, 0, 0]
    if fields in ("uint256", "uint256,uint256", "ScPair"):
        if size - start < (64 if fields == "uint256" else 96):
            return STD_TRUNCATED, None
        words = [at(start + 32), at(start + 64) if fields != "uint256" else 0, 0]
    elif fields == "bytes":
        if size - start < 64:
            return STD_TRUNCATED, None
        tail = at(start + 32)
        if tail > size - start or size - (start + tail) < 32:
            return STD_TRUNCATED, None
        length = at(start + tail)
        if length > size - (start + tail + 32) or length > MAX_DECODED_LENGTH:
            return STD_TRUNCATED, None
        payload = data[start + tail + 32:start + tail + 32 + length]
        chunk = lambda offset: int.from_bytes(payload[offset:offset + 32].ljust(32, b"\0"), "big") if length > offset else 0
        words = [length, chunk(0), chunk(32)]
    return None, (at(4), found[0] + 1, *words)


def enum_argument_fields(case: dict, transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a returned row that break the protocol on the value std
    decodes: slot 1 holds the one-based index, slots 2 to 4 the decoded Words,
    and the output is the committed slot 0. A body revert and a rejection are
    checked by rollback."""
    if row["status"] != "returned":
        return []
    rejection, decoded = enum_argument_decode(case, enum_argument_input(case, transaction))
    if rejection is not None:
        return ["status"]
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    fields = []
    if [after[slot] for slot in ("1", "2", "3", "4")] != list(decoded[1:]):
        fields.append("committedStorage")
    if int.from_bytes(common.hex_bytes(row["output"], "output"), "big") != after["0"]:
        fields.append("output")
    return fields


def has_enum_arrays(case: dict) -> bool:
    return profile(case)["abi"] == "enum-arrays"


def enum_array_signature(case: dict) -> str:
    """std's structural signature: the enum's `sum(left,right)` signature, then `[]`."""
    signatures = [ENUM_ARGUMENT_FIELDS[fields][0] for _, fields in enum_constructors(case)]
    nested = signatures[-1]
    for signature in reversed(signatures[:-1]):
        nested = f"sum({signature},{nested})"
    return f"run(uint256,{nested}[],uint256,uint256)"


def enum_array_contract(case: dict) -> None:
    """The contract metadata: the plan's structural signature and its selector."""
    name = profile(case)["contract"]
    signature = enum_array_signature(case)
    expected = {"name": name, "method": "run", "signature": signature, "selector": method_selector(signature),
                "deployPath": [name + "Deploy"], "runtimePath": [name + "Deploy", name], "constructorCalldata": "0x"}
    if case.get("contract") != expected:
        raise Finding("unsupported-scope", "input", "enum-array contract metadata differs from its plan")


def enum_array_layout(case: dict) -> tuple[bool, int, int]:
    """Whether the enum is static, its body's head, and an element's stride:
    the body head of a static enum, one offset Word of a dynamic one."""
    static, head = enum_argument_layout(case)
    return static, head, head if static else 32


def enum_array_transaction(tx: dict) -> tuple:
    """A transaction's flags, elements `(choice, a, b, length)` and indices, type-checked."""
    elements = tx.get("elements")
    if not isinstance(elements, list) or len(elements) > MAX_ARRAY_ELEMENTS or any(
            not isinstance(element, dict) or set(element) != {"choice", "a", "b", "length"} or
            type(element["choice"]) is not int or type(element["length"]) is not int or
            not 0 <= element["choice"] < 4 or not 0 <= element["length"] <= MAX_RETURN_LENGTH for element in elements):
        raise ValueError("an enum-array transaction records up to three elements, each a constructor index, two Words "
                         "and a length of at most 64")
    parsed = [(element["choice"], int(common.word(element["a"], "element Word a")),
               int(common.word(element["b"], "element Word b")), element["length"]) for element in elements]
    return (int(common.word(tx.get("flags"), "transaction flags")), parsed,
            int(common.word(tx.get("first"), "transaction first index")),
            int(common.word(tx.get("second"), "transaction second index")))


def enum_array_input(case: dict, tx: dict) -> bytes:
    """The calldata a transaction sends: the canonical encoding of its array,
    then its one malformation, which must apply to it. The head holds the
    flags, the offset 128 and both indices; the length follows, then a static
    array's bodies or a dynamic array's offset table, relative to the region
    after the length, and its bodies. A `bytes` payload is the first `length`
    bytes of `a · K` and `b · K`."""
    constructors = enum_constructors(case)
    flags, elements, first, second = enum_array_transaction(tx)
    static, head, stride = enum_array_layout(case)
    word = lambda value: (value % 2**256).to_bytes(32, "big")
    bodies = []
    for choice, a, b, length in elements:
        if choice >= len(constructors) or (length and constructors[choice][1] != "bytes"):
            raise ValueError("an enum-array element encodes a constructor, and only a bytes constructor has a length")
        name, fields = constructors[choice]
        payload = (word(a * RETURN_MULTIPLIER) + word(b * RETURN_MULTIPLIER))[:length]
        field_head = {"": b"", "uint256": word(a), "uint256,uint256": word(a) + word(b),
                      "ScPair": word(a) + word(b), "bytes": word(head)}[fields]
        tail = word(length) + payload + bytes(-length % 32) if fields == "bytes" else b""
        bodies.append(word(enum_argument_tag(name, fields)) + field_head + bytes(head - 32 - len(field_head)) + tail)
    count = len(elements)
    offsets = [32 * count + sum(len(body) for body in bodies[:index]) for index in range(count)]
    selector = bytes.fromhex(method_selector(enum_array_signature(case))[2:])
    data = (selector + word(flags) + word(128) + word(first) + word(second) + word(count) +
            (b"" if static else b"".join(word(offset) for offset in offsets)) + b"".join(bodies))
    region = 164
    starts = [region + (index * stride if static else offsets[index]) for index in range(count)]
    tags = [enum_argument_tag(*constructor) for constructor in constructors]
    malformation = tx.get("malformation")
    kind = malformation.get("kind") if isinstance(malformation, dict) else None
    keys = {"none": set(), "short": {"bytes"}, "selector": {"mask"}, "truncate": {"kept"}, "trailing": {"count", "pattern"},
            "offset": {"value"}, "count": {"value"}, "retag": {"element", "constructor"}, "share": {"element", "source"},
            "padding": {"element", "pattern"}}.get(kind, {"element", "value"})
    if kind not in ENUM_ARRAY_KINDS or set(malformation) != {"kind"} | keys:
        raise ValueError("an enum-array transaction carries one known malformation")
    put = lambda bytes_, position, value: bytes_[:position] + word(value) + bytes_[position + 32:]
    number = lambda key: malformation[key] if type(malformation[key]) is int else None
    value = int(common.word(malformation["value"], "malformation value")) if "value" in keys else None
    def invalid():
        raise ValueError("an enum-array malformation must apply to its transaction")
    target = number("element") if "element" in keys else None
    if "element" in keys and (target is None or not 0 <= target < count):
        invalid()
    choice, _, _, length = elements[target] if target is not None else (0, 0, 0, 0)
    fields = constructors[choice][1] if target is not None else ""
    if kind == "none":
        return data
    if kind == "short":
        if number("bytes") is None or not 0 <= malformation["bytes"] < 4:
            invalid()
        return data[:malformation["bytes"]]
    if kind == "selector":
        mask = int(common.word(malformation["mask"], "selector mask"))
        if not 0 < mask < 2**32:
            invalid()
        return ((int.from_bytes(data[:4], "big") ^ mask) % 2**32).to_bytes(4, "big") + data[4:]
    if kind == "truncate":
        if number("kept") is None or not 4 <= malformation["kept"] < len(data):
            invalid()
        return data[:malformation["kept"]]
    if kind == "trailing":
        extra = number("count")
        pattern = TRAILING_PATTERNS.index(malformation["pattern"]) if malformation["pattern"] in TRAILING_PATTERNS else None
        if extra is None or not 1 <= extra <= 64 or pattern is None:
            invalid()
        return data + bytes(0 if pattern == 0 else 0xff if pattern == 1 else (position + 1) % 256 for position in range(extra))
    if kind == "offset":
        if value == 128:
            invalid()
        return put(data, 36, value)
    if kind == "count":
        if value == count:
            invalid()
        return put(data, 132, value)
    if kind == "tag":
        if value in tags:
            invalid()
        return put(data, starts[target], value)
    if kind == "retag":
        index = number("constructor")
        if index is None or not 0 <= index < len(constructors) or index == choice:
            invalid()
        return put(data, starts[target], tags[index])
    if kind == "entry":
        if static or value == offsets[target]:
            invalid()
        return put(data, region + 32 * target, value)
    if kind == "share":
        source = number("source")
        if static or source is None or not 0 <= source < count or source == target:
            invalid()
        return put(data, region + 32 * target, offsets[source])
    if kind == "unused":
        if 32 + ENUM_ARGUMENT_FIELDS[fields][1] >= head or value == 0:
            invalid()
        return put(data, starts[target] + 32 + ENUM_ARGUMENT_FIELDS[fields][1], value)
    if kind == "tail":
        if fields != "bytes" or value == head:
            invalid()
        return put(data, starts[target] + 32, value)
    if kind == "length":
        if fields != "bytes" or value == length:
            invalid()
        return put(data, starts[target] + head, value)
    pattern = PADDING_PATTERNS.index(malformation["pattern"]) if malformation["pattern"] in PADDING_PATTERNS else None
    padding = -length % 32
    if fields != "bytes" or not padding or pattern is None:
        invalid()
    _, a, b, _ = elements[target]
    payload = (word(a * RETURN_MULTIPLIER) + word(b * RETURN_MULTIPLIER))[:length]
    last = length // 32 * 32
    fill = [0xff if pattern == 0 else (position + 1) % 256 if pattern == 1 else int(position + 1 == padding)
            for position in range(padding)]
    position = starts[target] + head + 32 + last
    return data[:position] + payload[last:length] + bytes(fill) + data[position + 32:]


def enum_array_element(case: dict, data: bytes, region: int, length: int, index: int) -> tuple:
    """`abiArrayGet` of element `index` once std accepted the array's head: the
    revert data of a rejection, or None with the one-based index and three
    Words. An index past the length reverts with `0x7f52b2bf`; a dynamic
    element's offset is relative to the region."""
    constructors = enum_constructors(case)
    static, _, stride = enum_array_layout(case)
    size = len(data)
    at = lambda position: int.from_bytes(data[position:position + 32], "big")
    if index >= length:
        return STD_OUT_OF_BOUNDS, None
    if static:
        start = region + index * stride
    else:
        if at(region + 32 * index) > size - region:
            return STD_TRUNCATED, None
        start = region + at(region + 32 * index)
    if size - start < 32:
        return STD_TRUNCATED, None
    found = [position for position, constructor in enumerate(constructors) if enum_argument_tag(*constructor) == at(start)]
    if not found:
        return STD_EMPTY_REVERT, None
    fields = constructors[found[0]][1]
    words = [0, 0, 0]
    if fields in ("uint256", "uint256,uint256", "ScPair"):
        if size - start < (64 if fields == "uint256" else 96):
            return STD_TRUNCATED, None
        words = [at(start + 32), at(start + 64) if fields != "uint256" else 0, 0]
    elif fields == "bytes":
        if size - start < 64:
            return STD_TRUNCATED, None
        tail = at(start + 32)
        if tail > size - start or size - (start + tail) < 32:
            return STD_TRUNCATED, None
        count = at(start + tail)
        if count > size - (start + tail + 32) or count > MAX_DECODED_LENGTH:
            return STD_TRUNCATED, None
        payload = data[start + tail + 32:start + tail + 32 + count]
        chunk = lambda offset: int.from_bytes(payload[offset:offset + 32].ljust(32, b"\0"), "big") if count > offset else 0
        words = [count, chunk(0), chunk(32)]
    return None, (found[0] + 1, *words)


def enum_array_decode(case: dict, data: bytes) -> tuple:
    """A third reading of the pinned std's dispatcher, lazy calldata-array
    decoder, `abiArrayGet` and derived enum decoder for `run(uint256 flags, E[]
    items, uint256 first, uint256 second)`: the revert data of a rejection, or
    None with the flags, the length and both elements' one-based index and
    three Words. The head is checked at dispatch, then `first` and `second`
    are decoded in turn; unread elements are never checked."""
    _, _, stride = enum_array_layout(case)
    size = len(data)
    at = lambda position: int.from_bytes(data[position:position + 32], "big")
    if size < 4 or "0x" + data[:4].hex() != method_selector(enum_array_signature(case)):
        return STD_NO_SELECTOR, None
    if size < 4 + 128:
        return STD_TRUNCATED, None
    if at(36) > size - 4:
        return STD_TRUNCATED, None
    position = 4 + at(36)
    if size - position < 32:
        return STD_TRUNCATED, None
    length = at(position)
    if length > (2**256 - 1) // stride or length * stride > size - (position + 32):
        return STD_TRUNCATED, None
    elements = []
    for index in (at(68), at(100)):
        rejection, element = enum_array_element(case, data, position + 32, length, index)
        if rejection is not None:
            return rejection, None
        elements.append(element)
    return None, (at(4), length, *elements[0], *elements[1])


def enum_array_fields(case: dict, transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a returned row that break the protocol on the array std
    decodes: slot 1 holds the length, slots 2 to 9 both elements' index and
    Words, and the output is the committed slot 0. A body revert and a
    rejection are checked by rollback."""
    if row["status"] != "returned":
        return []
    rejection, decoded = enum_array_decode(case, enum_array_input(case, transaction))
    if rejection is not None:
        return ["status"]
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    fields = []
    if [after[str(slot)] for slot in range(1, 10)] != list(decoded[1:]):
        fields.append("committedStorage")
    if int.from_bytes(common.hex_bytes(row["output"], "output"), "big") != after["0"]:
        fields.append("output")
    return fields


def has_array_returns(case: dict) -> bool:
    return profile(case)["abi"] == "array-returns"


def valid_array_return_plan(plan: dict) -> bool:
    """An element type, a count of at most three and, for `bytes` and
    `uint256[]` elements, one inner length per element within its bound."""
    element, count, lengths = plan.get("elements"), plan.get("count"), plan.get("lengths")
    if element not in ARRAY_RETURN_ELEMENTS or type(count) is not int or not 0 <= count <= MAX_ARRAY_RETURN_COUNT or \
            not isinstance(lengths, list) or any(type(length) is not int for length in lengths):
        return False
    bound = ARRAY_RETURN_ELEMENTS[element][1]
    return len(lengths) == (count if bound else 0) and all(0 <= length <= bound for length in lengths)


def array_return_arguments(case: dict) -> tuple[int, int]:
    """The plan's run-time arguments: `choice`, the inner lengths as digits of
    the element type's base, and `length`, the count."""
    plan = case[profile(case)["planKey"]]
    base = ARRAY_RETURN_ELEMENTS[plan["elements"]][0]
    return sum(length * base ** index for index, length in enumerate(plan["lengths"])), plan["count"]


def array_return_words(case: dict) -> int:
    """A returned array's Words: the offset, the length, one head Word per
    element and each `bytes` or `uint256[]` element's length Word and data."""
    plan = case[profile(case)["planKey"]]
    tail = {"bytes": lambda length: 1 + (length + 31) // 32, "uint256[]": lambda length: 1 + length}.get(plan["elements"])
    return 2 + plan["count"] + (sum(tail(length) for length in plan["lengths"]) if tail else 0)


def array_return_encoding(case: dict, result: int, calls: int, last: int) -> bytes:
    """std's encoding of the plan's array, element `i` built from
    `a = result * K + i` and `b = ((calls * K) xor last) + i`: the offset 32 and
    the length, then the inline Words of `uint256` and left-aligned `bytes4`
    elements, or one offset per element relative to the element region and then
    the element tails: a `bytes` value's length and data zero-padded to whole
    Words, an inner array's length and Words."""
    plan = case[profile(case)["planKey"]]
    element, count = plan["elements"], plan["count"]

    def word(value: int) -> bytes:
        return (value % 2**256).to_bytes(32, "big")
    a = [(result * RETURN_MULTIPLIER + index) % 2**256 for index in range(count)]
    b = [((calls * RETURN_MULTIPLIER % 2**256 ^ last) + index) % 2**256 for index in range(count)]
    head = word(32) + word(count)
    if element == "uint256":
        return head + b"".join(word(value) for value in a)
    if element == "bytes4":
        return head + b"".join(word((value % 2**32) << 224) for value in a)
    tails = []
    for index, length in enumerate(plan["lengths"]):
        if element == "bytes":
            data = (word(a[index]) + word(b[index]))[:length]
            tails.append(word(length) + data + bytes(-length % 32))
        else:
            tails.append(word(length) + b"".join(word(value) for value in (a[index], b[index])[:length]))
    offsets, position = [], 32 * count
    for tail in tails:
        offsets.append(word(position))
        position += len(tail)
    return head + b"".join(offsets) + b"".join(tails)


def array_return_fields(case: dict, transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a returned row that break the array-return protocol: slot one
    grows by one, slot two is the input, and the output is std's encoding of the
    plan's array (`array_return_encoding`) of the committed slot zero, the
    committed slot one and the prior slot two. A revert is checked by
    rollback."""
    if row["status"] != "returned":
        return []
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    before = {entry["slot"]: int(entry["value"]) for entry in prior}
    fields = []
    if after["1"] != (before["1"] + 1) % 2**256 or after["2"] != int(common.word(transaction.get("input"), "transaction input")):
        fields.append("committedStorage")
    if common.hex_bytes(row["output"], "output") != array_return_encoding(case, after["0"], after["1"], before["2"]):
        fields.append("output")
    return fields


def has_constructor_arguments(case: dict) -> bool:
    return profile(case)["abi"] == "constructor-arguments"


def valid_constructor_argument_plan(plan: dict) -> bool:
    """One parameter kind; an enum's constructors as for the enum arguments,
    and none for every other kind."""
    kind = plan.get("parameters")
    if kind not in CONSTRUCTOR_PARAMETERS:
        return False
    return valid_enum_argument_plan(plan) if kind == "uint256,enum" else plan.get("constructors") == []


def constructor_argument_record(case: dict) -> tuple:
    """The deployment record's Words `a`, `first` and `second`, its choice and
    `bytes` length, and its malformation, type-checked."""
    deployment = case.get("deployment")
    if not isinstance(deployment, dict) or set(deployment) != {"a", "choice", "first", "second", "length", "malformation",
                                                                "arguments", "stdRejection"}:
        raise ValueError("a constructor-argument case records its deployment")
    choice, length = deployment["choice"], deployment["length"]
    if type(choice) is not int or type(length) is not int or not 0 <= choice < 4 or not 0 <= length <= MAX_RETURN_LENGTH:
        raise ValueError("a constructor-argument deployment records a constructor index and a length of at most 64")
    return (int(common.word(deployment["a"], "deployment a")), choice,
            int(common.word(deployment["first"], "deployment first Word")),
            int(common.word(deployment["second"], "deployment second Word")), length, deployment["malformation"])


def constructor_argument_layout(case: dict) -> tuple:
    """The parameter kind, the enum's constructors, whether the enum is static,
    the body's head and where the body starts: inline at 32 for a static enum,
    behind the offset 64 for a dynamic one."""
    kind = case[profile(case)["planKey"]]["parameters"]
    if kind != "uint256,enum":
        return kind, [], True, 0, 32
    constructors = enum_constructors(case)
    fields = [fields for _, fields in constructors]
    static = "bytes" not in fields
    return kind, constructors, static, 32 + max(ENUM_ARGUMENT_FIELDS[field][1] for field in fields), 32 if static else 64


def constructor_argument_bytes(case: dict) -> bytes:
    """The argument bytes the deployment appends to the init code: the
    canonical encoding of the record, then its one malformation, which must
    apply. A `bytes` value is `a`, the offset 64, its length and the first
    `length` bytes of `first · K` and `second · K` zero-padded to whole Words;
    an enum's body is as for the enum arguments."""
    kind, constructors, static, head, start = constructor_argument_layout(case)
    a, choice, first, second, length, malformation = constructor_argument_record(case)
    word = lambda value: (value % 2**256).to_bytes(32, "big")
    padded = (word(first * RETURN_MULTIPLIER) + word(second * RETURN_MULTIPLIER))[:length] + bytes(-length % 32)
    if kind == "uint256,enum":
        if choice >= len(constructors):
            raise ValueError("a constructor-argument deployment encodes a constructor of its enum")
        name, fields = constructors[choice]
    else:
        name, fields = None, {"none": None, "uint256": "", "uint256,uint256": "uint256", "uint256,bytes": "bytes"}[kind]
    carries = fields == "bytes"
    sends = {None: (False, False), "": (False, False), "uint256": (True, False), "uint256,uint256": (True, True),
             "ScPair": (True, True), "bytes": (True, True)}[fields]
    if (kind == "none" and a) or (kind != "uint256,enum" and choice) or (length and not carries) or \
            (first and not sends[0]) or (second and not sends[1]):
        raise ValueError("a constructor-argument record sends only the Words of its parameters")
    if kind == "none":
        data = b""
    elif kind == "uint256":
        data = word(a)
    elif kind == "uint256,uint256":
        data = word(a) + word(first)
    elif kind == "uint256,bytes":
        data = word(a) + word(64) + word(length) + padded
    else:
        field_head = {"": b"", "uint256": word(first), "uint256,uint256": word(first) + word(second),
                      "ScPair": word(first) + word(second), "bytes": word(head)}[fields]
        tail = word(length) + padded if carries else b""
        body = word(enum_argument_tag(name, fields)) + field_head + bytes(head - 32 - len(field_head)) + tail
        data = word(a) + (body if static else word(64) + body)
    size = len(data)
    kind_name = malformation.get("kind") if isinstance(malformation, dict) else None
    keys = {"none": set(), "truncate": {"kept"}, "trailing": {"count", "pattern"}, "narrow": set()}.get(kind_name, {"value"})
    if kind_name not in CONSTRUCTOR_KINDS or set(malformation) != {"kind"} | keys:
        raise ValueError("a constructor-argument deployment carries one known malformation")
    value = int(common.word(malformation["value"], "malformation value")) if keys == {"value"} else None
    put = lambda bytes_, position, replaced: bytes_[:position] + word(replaced) + bytes_[position + 32:]
    tags = [enum_argument_tag(*constructor) for constructor in constructors]
    length_at = start + head if kind == "uint256,enum" else 64
    if kind_name == "none":
        return data
    if kind_name == "truncate" and type(malformation["kept"]) is int and 0 <= malformation["kept"] < size:
        return data[:malformation["kept"]]
    if kind_name == "trailing" and type(malformation["count"]) is int and 1 <= malformation["count"] <= 64 and \
            malformation["pattern"] in TRAILING_PATTERNS:
        count = malformation["count"]
        return data + {"zeros": bytes(count), "ones": b"\xff" * count,
                       "ramp": bytes((index + 1) % 256 for index in range(count))}[malformation["pattern"]]
    if kind_name == "offset" and (kind == "uint256,bytes" or not static) and value != 64:
        return put(data, 32, value)
    if kind_name == "length" and carries and value != length:
        return put(data, length_at, value)
    if kind_name in ("tag", "tagCut") and kind == "uint256,enum" and value not in tags:
        changed = put(data, start, value)
        return changed if kind_name == "tag" else changed[:start + 32]
    if kind_name == "tail" and kind == "uint256,enum" and not static and carries and value != head:
        return put(data, start + 32, value)
    if kind_name == "narrow" and kind == "uint256,enum" and static and 64 + ENUM_ARGUMENT_FIELDS[fields][1] < size:
        return data[:64 + ENUM_ARGUMENT_FIELDS[fields][1]]
    raise ValueError("a constructor-argument malformation must apply to its deployment")


def constructor_argument_decide(case: dict, data: bytes) -> tuple:
    """std's decision on the argument bytes, as the compiler's generated copy and
    std's `MemoryWordReader` take them: reading from 0 with no up-front head
    check, every Word read and every advance inside the arguments, else
    `ABIInputTruncated()`. `a` comes first, then the second Word, the `bytes`
    offset, length and data, or the enum's tag, compared before any field,
    and its fields; an unknown tag reverts with empty data. Returns the
    rejection or None, and the record written to slots 1 to 5."""
    kind, constructors, static, _, _ = constructor_argument_layout(case)
    if kind == "none":
        return None, [1, 0, 0, 0, 0]
    end = len(data)

    class Truncated(Exception):
        pass

    def advance(position: int, count: int) -> int:
        if not (position <= end and count <= end - position):
            raise Truncated()
        return position + count

    def read(position: int) -> tuple:
        advance(position, 32)
        return int.from_bytes(data[position:position + 32], "big"), position + 32

    def chunk(start: int, length: int, index: int) -> int:
        piece = data[start + index:start + length][:32]
        return int.from_bytes(piece + bytes(32 - len(piece)), "big")

    def bytes_value(base: int, position: int) -> list:
        offset, _ = read(position)
        length, start = read(advance(base, offset))
        advance(start, length)
        return [length, chunk(start, length, 0) if length > 0 else 0, chunk(start, length, 32) if length > 32 else 0]
    try:
        a, position = read(0)
        if kind == "uint256":
            return None, [a, 0, 0, 0, 0]
        if kind == "uint256,uint256":
            return None, [a, read(position)[0], 0, 0, 0]
        if kind == "uint256,bytes":
            return None, [a, *bytes_value(0, position), 0]
        body = position if static else advance(0, read(position)[0])
        found, position = read(body)
        index = next((index for index, constructor in enumerate(constructors)
                      if enum_argument_tag(*constructor) == found), None)
        if index is None:
            return STD_EMPTY_REVERT, [0, 0, 0, 0, 0]
        fields = constructors[index][1]
        if fields == "":
            values = [0, 0, 0]
        elif fields == "uint256":
            values = [read(position)[0], 0, 0]
        elif fields in ("uint256,uint256", "ScPair"):
            first, position = read(position)
            values = [first, read(position)[0], 0]
        else:
            values = bytes_value(body, position)
        return None, [a, index + 1, *values]
    except Truncated:
        return STD_TRUNCATED, [0, 0, 0, 0, 0]


def constructor_argument_contract(case: dict) -> None:
    """The deployment record's arguments and std's decision on them, and the
    contract metadata, whose constructor calldata is the arguments."""
    data = constructor_argument_bytes(case)
    rejection, _ = constructor_argument_decide(case, data)
    deployment = case["deployment"]
    if deployment["arguments"] != "0x" + data.hex() or deployment["stdRejection"] != rejection:
        raise ValueError("deployment arguments or std outcome differ from the record and std's decision on it")
    name = profile(case)["contract"]
    expected = {"name": name, "method": "run", "signature": profile(case)["signature"],
                "selector": profile(case)["selector"], "deployPath": [name + "Deploy"],
                "runtimePath": [name + "Deploy", name], "constructorCalldata": "0x" + data.hex()}
    if case.get("contract") != expected:
        raise Finding("unsupported-scope", "input", "constructor-argument contract metadata differs from its deployment")


def constructor_argument_expected(case: dict) -> tuple:
    """The prescribed deployment: std's rejection or None, and the committed
    slots 0 to 5, the record behind a zero accumulator or nothing."""
    rejection, record = constructor_argument_decide(case, constructor_argument_bytes(case))
    values = [0] * 6 if rejection is not None else [0, *record]
    return rejection, [{"slot": str(slot), "value": str(value % 2**256)} for slot, value in enumerate(values)]


def constructor_argument_fields(case: dict, transaction: dict, row: dict, prior: list[dict]) -> list[str]:
    """Fields of a completed runtime row that break the protocol: slots 1 to 5
    keep the record std decoded at deployment, and a returned row returns the
    committed slot zero. A revert is checked by rollback."""
    _, expected = constructor_argument_expected(case)
    fields = []
    if row["committedStorage"][1:] != expected[1:]:
        fields.append("committedStorage")
    after = {entry["slot"]: int(entry["value"]) for entry in row["committedStorage"]}
    if row["status"] == "returned" and common.hex_bytes(row["output"], "output") != after["0"].to_bytes(32, "big"):
        fields.append("output")
    return fields


def constructor_deployment_mismatch(values: dict, case: dict, selector_rows: list) -> dict | None:
    """The deployment row. Every path deploys exactly when std accepts the
    arguments and commits the record the adapter decodes, and nothing else; a
    rejection reverts with std's revert data, which original Core gives as its
    Word under the selector and empty-revert rules, and commits nothing. A
    deployment's returned data are not compared: the EVM path checks its
    installed runtime against the exported image."""
    rejection, expected = constructor_argument_expected(case)
    rows = {name: values[name]["deployment"] for name in PATHS}
    where = {"stage": "deployment", "transactionId": None, "index": None}
    if any(row["status"] in RESOURCE_STATUSES for row in rows.values()):
        return {"category": "inconclusive-resource", **where, "pairs": {}}
    if any(row["status"] not in {"returned", "reverted"} for row in rows.values()):
        return {"category": "execution-error", **where, "pairs": {}}
    outputs = {name: row["output"] if row["status"] == "reverted" else None for name, row in rows.items()}
    core = outputs["directCore"]
    word = bytes(32) if rejection == STD_EMPTY_REVERT else int(rejection, 16).to_bytes(32, "big") if rejection else None
    if rejection is not None and core == "0x" + word.hex():
        outputs["directCore"] = rejection
        selector_rows.append({"id": "deployment", "index": None, "selector": rejection})
    status = "reverted" if rejection is not None else "returned"
    whole = [entry for entry in expected if entry["value"] != "0"]
    fields = [field for field, broken in (
        ("status", any(row["status"] != status for row in rows.values())),
        ("output", any(output != rejection for output in outputs.values())),
        ("committedStorage", any(values[name]["initialStorage"] != expected for name in PATHS)),
        ("accountStorage", any([account["storage"] for account in values[name]["initialAccountStorage"]] != [whole]
                               for name in PATHS)),
        ("undeclaredStorage", any(values[name].get("initialUndeclaredStorage") for name in PATHS))) if broken]
    if not fields:
        return None
    return {"category": "semantic-mismatch", **where, "fields": fields, "pairs": pairwise(
        {name: [rows[name]["status"], outputs[name], values[name]["initialStorage"], values[name]["initialAccountStorage"]]
         for name in PATHS})}


def creation_address(sender: str, nonce: int) -> str:
    """The CREATE address of a sender's creation at a nonce: the last 20 bytes
    of `keccak256(rlp([sender, nonce]))`. Anvil reports none for a failed
    creation."""
    raw = nonce.to_bytes((nonce.bit_length() + 7) // 8, "big")
    encoded = b"\x80" if nonce == 0 else raw if nonce < 0x80 else bytes([0x80 + len(raw)]) + raw
    payload = b"\x94" + bytes.fromhex(sender[2:]) + encoded
    return "0x" + keccak256(bytes([0xc0 + len(payload)]) + payload)[12:].hex()


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
    if has_adts(case):
        return ("ordered zero-value calls of one contract's declared methods that write, clear, read and update one "
                "field of user-defined enum and struct values in contract fields and behind two keys of two mappings, "
                "through std.StorageGeneric; initially empty storage; committed values at the accumulator, the enum and "
                "record fields' slots and both keys' entry slots of both mappings, stale payload slots included, on all "
                "paths and no nonzero undeclared slot on Hull/EVM; no gas/balance/nonce or memory equivalence")
    if has_enum_arrays(case):
        return ("ordered zero-value run(uint256,E[],uint256,uint256) transactions that send a calldata array of up to "
                "three values of a user enum E of two to four constructors with no fields, one or two Words, a struct "
                "of two Words or a bytes value of zero to 64 bytes and two indices, canonically or with one "
                "malformation of its calldata, which std's dispatcher, array decoder and abiArrayGet accept or reject; "
                "a body writes the step result, the length and both indexed elements' one-based index and three "
                "decoded Words; initially empty storage; the whole return data, std's error selector or empty revert "
                "data, and committed values at slots 0..9 on all paths and no nonzero undeclared slot on Hull/EVM; no "
                "gas/balance/nonce or memory equivalence")
    if has_enum_arguments(case):
        return ("ordered zero-value run(uint256,E) transactions that send a value of a user enum E of two to four "
                "constructors with no fields, one or two Words, a struct of two Words or a bytes value of zero to 64 "
                "bytes, canonically or with one malformation of its calldata, which std's dispatcher and derived "
                "decoder accept or reject; a body writes the step result, the one-based index and three decoded Words; "
                "initially empty storage; the whole return data, std's error selector or empty revert data, and "
                "committed values at slots 0..4 on all paths and no nonzero undeclared slot on Hull/EVM; no "
                "gas/balance/nonce or memory equivalence")
    if has_constructor_arguments(case):
        return ("a zero-value deployment whose constructor takes none, one or two Words, a Word and bytes of up to 64 "
                "bytes, or a Word and a user enum of two to four constructors, decoded by std from the argument bytes "
                "appended to the init code, canonical or with one malformation, and writing the record to slots 1..5, "
                "then ordered zero-value run(uint256,uint256) transactions over those slots, none after a rejected "
                "deployment; the deployment's status, std's error selector or empty revert data, original Core's Word "
                "under the selector and empty-revert rules, and committed values at slots 0..5, then the whole return "
                "data and committed values at slots 0..5, on all paths and no nonzero undeclared slot on Hull/EVM; no "
                "gas/balance/nonce or memory equivalence")
    if has_array_returns(case):
        return ("ordered zero-value run(uint256,uint256,uint256,uint256) transactions that carry the plan's array "
                "shape as their choice and length and return std's ABI encoding of a memory array of up to three "
                "uint256, bytes4, bytes values of zero to 64 bytes or uint256[] values of zero to two Words, built from "
                "the step result and slot 1 after its write times an odd constant, the latter xor slot 2 before its "
                "write, through abi_encode and return_; initially empty storage; the whole return data and committed "
                "values at slots 0..2 on all paths and no nonzero undeclared slot on Hull/EVM; no gas/balance/nonce or "
                "memory equivalence")
    if has_enum_returns(case):
        return ("ordered zero-value run(uint256,uint256,uint256,uint256) transactions that return the chosen "
                "constructor of a user enum of two to four constructors with no fields, one or two Words or a bytes "
                "value of zero to 64 bytes, built from the step result and slot 1 after its write times an odd "
                "constant, the latter xor slot 2 before its write, in std's ABI encoding; initially empty storage; "
                "the whole return data and committed values at slots 0..2 on all paths and no nonzero undeclared slot "
                "on Hull/EVM; no gas/balance/nonce or memory equivalence")
    if has_bytes_returns(case):
        return ("ordered zero-value run(uint256,uint256,uint256) transactions that return a bytes value of the "
                "transaction's zero to 64 bytes of two Words, the step result and slot 1 after its write times an odd "
                "constant, the latter xor slot 2 before its write; initially empty storage; the whole return data and "
                "committed values at slots 0..2 on all paths and no nonzero undeclared slot on Hull/EVM; no "
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
    """Profiles whose original Core contract reverts with std's error selectors
    as a Word; the constructor arguments' initializer does so at deployment."""
    return isinstance(case, dict) and any(case.get("schema") == value["caseSchema"] and
                                          value["abi"] in ("malformed", "methods", "enum-arguments", "enum-arrays",
                                                           "constructor-arguments")
                                          for value in PROFILES.values())


def selector_rule(case: dict, tx: dict, rows: dict) -> str | None:
    """The std error selector a transaction's rows are compared by. It applies
    only when original Core reverted with exactly that selector as a Word and the
    transaction's prescribed std outcome is that rejection; every other row is
    compared exactly. A body revert whose Word equals a selector has the
    prescribed outcome acceptance, so it is compared exactly too. For enum
    arguments, original Core's Word zero likewise stands for an unknown tag's
    empty revert data, `0x`, when that is the prescribed outcome. Enum arrays
    take both rules, with `ArrayOutOfBounds()` among the selectors."""
    selector = tx.get("stdRejection")
    core = rows.get("directCore")
    if (has_enum_arguments(case) or has_enum_arrays(case)) and selector == STD_EMPTY_REVERT and isinstance(core, dict):
        # The empty-revert rule: original Core's Word zero stands for an unknown
        # tag's empty revert data, only when that is the prescribed outcome.
        return selector if core.get("status") == "reverted" and core.get("output") == "0x" + bytes(32).hex() else None
    errors = STD_ERRORS + ((STD_OUT_OF_BOUNDS,) if has_enum_arrays(case) else ())
    if profile(case)["abi"] not in ("malformed", "methods", "enum-arguments", "enum-arrays") or selector not in errors or \
            not isinstance(core, dict):
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
    if selected["abi"] == "constructor-arguments":
        # A failed deployment ends the scenario, so a rejected one keeps no
        # transactions; an accepted one keeps up to eight.
        if not isinstance(transactions, list) or len(transactions) > MAX_TRANSACTIONS or \
                (transactions and case["deployment"]["stdRejection"] is not None):
            raise ValueError(f"constructor-argument case requires up to {MAX_TRANSACTIONS} ordered transactions, "
                             "none after a rejected deployment")
    elif not isinstance(transactions, list) or not 1 <= len(transactions) <= MAX_TRANSACTIONS:
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
        if selected["abi"] == "enum-arrays":
            data = enum_array_input(case, tx)
            if len(data) > MAX_CALLDATA:
                raise ValueError("enum-array calldata exceeds 1 KiB")
            if tx.get("calldata") != "0x" + data.hex() or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its elements, indices and malformation")
            if tx.get("stdRejection") != enum_array_decode(case, data)[0]:
                raise ValueError("transaction std outcome differs from std's decision on its calldata")
            continue
        if selected["abi"] == "enum-arguments":
            data = enum_argument_input(case, tx)
            if len(data) > MAX_CALLDATA:
                raise ValueError("enum-argument calldata exceeds 1 KiB")
            if tx.get("calldata") != "0x" + data.hex() or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its constructor and malformation")
            if tx.get("stdRejection") != enum_argument_decode(case, data)[0]:
                raise ValueError("transaction std outcome differs from std's decision on its calldata")
            continue
        if selected["abi"] == "enum-returns":
            constructors = enum_constructors(case)
            choice = int(common.word(tx.get("choice"), "transaction choice"))
            length = int(common.word(tx.get("length"), "transaction length"))
            if choice >= len(constructors) or length > MAX_RETURN_LENGTH or (length and constructors[choice][1] != "bytes"):
                raise ValueError("an enum-return transaction chooses a constructor, and only a bytes constructor's "
                                 "transaction requests up to 64 bytes")
            words = [int(common.word(tx.get(field), "transaction " + field)) for field in ("flags", "input", "choice", "length")]
            if tx.get("calldata") != selected["selector"] + "".join(f"{word:064x}" for word in words) or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its four original Words")
            continue
        if selected["abi"] == "array-returns":
            choice, length = array_return_arguments(case)
            if int(common.word(tx.get("choice"), "transaction choice")) != choice or \
                    int(common.word(tx.get("length"), "transaction length")) != length:
                raise ValueError("an array-return transaction carries its plan's inner lengths as its choice and its "
                                 "count as its length")
            words = [int(common.word(tx.get(field), "transaction " + field)) for field in ("flags", "input", "choice", "length")]
            if tx.get("calldata") != selected["selector"] + "".join(f"{word:064x}" for word in words) or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its four original Words")
            continue
        if selected["abi"] == "constructor-arguments":
            words = [int(common.word(tx.get(field), "transaction " + field)) for field in ("flags", "input")]
            if tx.get("calldata") != selected["selector"] + "".join(f"{word:064x}" for word in words) or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its two original Words")
            continue
        if selected["abi"] == "bytes-returns":
            if int(common.word(tx.get("length"), "transaction length")) > MAX_RETURN_LENGTH:
                raise ValueError("a bytes-return transaction requests at most 64 bytes")
            words = [int(common.word(tx.get(field), "transaction " + field)) for field in ("flags", "input", "length")]
            if tx.get("calldata") != selected["selector"] + "".join(f"{word:064x}" for word in words) or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its three original Words")
            continue
        if selected["abi"] == "adts":
            parameters = ADT_METHODS.get(tx.get("method"), ())
            calldata = method_selector(method_signature(tx.get("method"), len(parameters))) + \
                "".join(f"{word:064x}" for word in adt_arguments(case, tx))
            if tx.get("calldata") != calldata or tx.get("value") != "0":
                raise ValueError("transaction calldata/value differs from its method call")
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
    if selected.get("forms") and plan.get("form") not in selected["forms"]:
        raise ValueError("inline Yul loop plan requires a form of split, carried or pipelined")
    if selected["abi"] == "tuples" and (type(plan.get("arity")) is not int or plan["arity"] not in TUPLE_ARITIES):
        raise ValueError("tuple-return plan requires an arity of 2, 3 or 4")
    if selected["abi"] == "enum-arrays" and not valid_enum_argument_plan(plan):
        raise ValueError("enum-array plan requires two to four constructors with distinct bank names and known "
                         "field types, at most two with bytes")
    if selected["abi"] == "enum-arguments" and not valid_enum_argument_plan(plan):
        raise ValueError("enum-argument plan requires two to four constructors with distinct bank names and known "
                         "field types, at most two with bytes")
    if selected["abi"] == "array-returns" and not valid_array_return_plan(plan):
        raise ValueError("array-return plan requires an element type of uint256, bytes4, bytes or uint256[], at most "
                         "three elements and one inner length within its bound per bytes or uint256[] element")
    if selected["abi"] == "constructor-arguments" and not valid_constructor_argument_plan(plan):
        raise ValueError("constructor-argument plan requires a parameter kind of none, uint256, uint256,uint256, "
                         "uint256,bytes or uint256,enum, an enum's two to four constructors with distinct bank names "
                         "and known field types, at most two with bytes, and no constructors otherwise")
    if selected["abi"] == "enum-returns" and not valid_enum_plan(plan):
        raise ValueError("enum-return plan requires two to four constructors with distinct bank names and known fields, "
                         "at most two with bytes")
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
    elif selected["abi"] == "adts":
        validate_transactions(case, selected)
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != adt_slots(case):
            raise Finding("unsupported-scope", "input", "enum and struct storage profile starts empty and observes "
                          "the accumulator, the enum and record fields and both keys' entry slots of both mappings")
    elif selected["abi"] == "tuples":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != TUPLE_SLOTS:
            raise Finding("unsupported-scope", "input", "tuple-return profile starts empty and observes slots zero through two")
    elif selected["abi"] == "array-returns":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != ARRAY_RETURN_SLOTS:
            raise Finding("unsupported-scope", "input", "array-return profile starts empty and observes slots zero through two")
    elif selected["abi"] == "constructor-arguments":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != CONSTRUCTOR_ARGUMENT_SLOTS:
            raise Finding("unsupported-scope", "input", "constructor-argument profile starts empty and observes slots zero through five")
    elif selected["abi"] == "bytes-returns":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != BYTES_RETURN_SLOTS:
            raise Finding("unsupported-scope", "input", "bytes-return profile starts empty and observes slots zero through two")
    elif selected["abi"] == "enum-arrays":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != ENUM_ARRAY_SLOTS:
            raise Finding("unsupported-scope", "input", "enum-array profile starts empty and observes slots zero through nine")
    elif selected["abi"] == "enum-arguments":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != ENUM_ARGUMENT_SLOTS:
            raise Finding("unsupported-scope", "input", "enum-argument profile starts empty and observes slots zero through four")
    elif selected["abi"] == "enum-returns":
        if case.get("initialState") != {"storage": []} or case.get("observedSlots") != ENUM_RETURN_SLOTS:
            raise Finding("unsupported-scope", "input", "enum-return profile starts empty and observes slots zero through two")
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
    elif selected["abi"] == "adts":
        adt_contract(case)
    elif selected["abi"] == "enum-arguments":
        enum_argument_contract(case)
    elif selected["abi"] == "enum-arrays":
        enum_array_contract(case)
    elif selected["abi"] == "constructor-arguments":
        constructor_argument_contract(case)
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
    if has_constructor_arguments(case):
        # The deployment's status and, for a revert, its whole revert data; a
        # failed deployment ends the history.
        deployment = history.get("deployment")
        if not isinstance(deployment, dict) or not isinstance(deployment.get("status"), str):
            raise ValueError("a constructor-argument history records its deployment")
        extra["deployment"] = {"status": deployment["status"], "output":
            "0x" + common.hex_bytes(deployment.get("output"), "deployment output").hex()
            if deployment["status"] == "reverted" else None}
        if deployment["status"] != "returned" and rows:
            raise ValueError("transactions ran after a failed deployment")
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
    returned tuple carries its arity's Words and follows `tuple_fields`. A
    returned `bytes` value carries its padded length and follows
    `bytes_return_fields`, a returned enum value its encoding's Words and
    `enum_return_fields`, and a returned array its encoding's Words and
    `array_return_fields`. A decoded enum argument follows
    `enum_argument_fields`, and a decoded enum array `enum_array_fields`."""
    expected = expected_status(case, tx)
    # A std rejection reverts with exactly its selector, after the selector rule.
    rejection = tx.get("stdRejection") if profile(case)["abi"] in ("malformed", "methods", "enum-arguments",
                                                                   "enum-arrays") else None
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
    if has_adts(case) and adt_fields(case, tx, row, prior):
        return False
    if has_tuples(case) and tuple_fields(case, tx, row, prior):
        return False
    if has_bytes_returns(case) and bytes_return_fields(case, tx, row, prior):
        return False
    if has_enum_returns(case) and enum_return_fields(case, tx, row, prior):
        return False
    if has_array_returns(case) and array_return_fields(case, tx, row, prior):
        return False
    if has_constructor_arguments(case) and constructor_argument_fields(case, tx, row, prior):
        return False
    if has_enum_arguments(case) and enum_argument_fields(case, tx, row, prior):
        return False
    if has_enum_arrays(case) and enum_array_fields(case, tx, row, prior):
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
    difference. For malformed calldata, several methods and enum arguments
    the result lists the rows compared by their std error selector, or by
    empty revert data, with the selector or `0x`."""
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
    if has_constructor_arguments(case):
        try:
            mismatch = constructor_deployment_mismatch(values, case, selector_rows)
        except (ValueError, KeyError, TypeError) as error:
            return {"category": "adapter-error", "stage": "comparison", "detail": str(error), "pairs": {}}
        if mismatch is not None:
            return mismatch
    # The empty constructor leaves the whole storage empty on every path.
    differences = account_storage_differences(whole, observed_slots(case), deployment=True)
    pairs = pairwise(initial)
    outside = undeclared_paths(values) if keyed else []
    declared = not all(pairs.values()) or any(row["value"] != "0" for state in initial.values() for row in state)
    # A fixed empty constructor commits no logs; a deployment log is a difference.
    deployed_logs = sorted(name for name in PATHS if values[name].get("initialLogs")) if deployment_logs(case) else []
    # The funded deployment holds exactly its recorded value on every path.
    funded = not has_balances(case) or all(values[name]["initialBalance"] == str(deployment_value(case)) for name in PATHS)
    # The constructor arguments' deployment row is compared above.
    if (declared or outside or deployed_logs or not funded or differences) and not has_constructor_arguments(case):
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
        rejection = tx.get("stdRejection") if profile(case)["abi"] in ("malformed", "methods", "enum-arguments",
                                                                       "enum-arrays") else None
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
        if has_adts(case):
            # A returned row follows the layout protocol; a revert is already covered by rollback.
            broken = sorted({field for name, row in rows.items() for field in adt_fields(case, tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_tuples(case):
            # A returned tuple follows the protocol Word by Word; a revert is already covered by rollback.
            broken = sorted({field for name, row in rows.items() for field in tuple_fields(case, tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_bytes_returns(case):
            # A returned value follows the protocol byte by byte; a revert is already covered by rollback.
            broken = sorted({field for name, row in rows.items() for field in bytes_return_fields(case, tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_enum_returns(case):
            # A returned enum value follows the protocol byte by byte; a revert is already covered by rollback.
            broken = sorted({field for name, row in rows.items() for field in enum_return_fields(case, tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_array_returns(case):
            # A returned array follows the protocol byte by byte; a revert is already covered by rollback.
            broken = sorted({field for name, row in rows.items() for field in array_return_fields(case, tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_constructor_arguments(case):
            # A completed row keeps the decoded record; a revert is already covered by rollback.
            broken = sorted({field for name, row in rows.items() for field in constructor_argument_fields(case, tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_enum_arguments(case):
            # A returned row follows the protocol on the value std decodes; a
            # body revert and a rejection are already covered by rollback.
            broken = sorted({field for name, row in rows.items() for field in enum_argument_fields(case, tx, row,
                values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])})
            fields += [field for field in broken if field not in fields]
            normal = normal and not broken
        if has_enum_arrays(case):
            # A returned row follows the protocol on the array std decodes.
            broken = sorted({field for name, row in rows.items() for field in enum_array_fields(case, tx, row,
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
        {name: {key: value for key, value in values[name].items() if key not in ("initialUndeclaredStorage", "chainLogs",
                                                                                 "deployment")} | {
            "transactions": [without_containment(row) for row in values[name]["transactions"]]} for name in PATHS})}


def hull_history(stdout: str, exit_code: int, case: dict) -> dict:
    rows = [json.loads(line) for line in stdout.splitlines() if line.strip()]
    if exit_code not in (0, 1) or not rows or any(not isinstance(row, dict) for row in rows):
        raise ValueError("invalid Hull storage process result")
    if rows[-1].get("stage") == "preparation":
        detail = str(rows[-1].get("detail", "preparation rejected"))
        raise Finding("inconclusive-resource" if common.RESOURCE.search(detail) else "compilation-rejected", "core-preparation", detail)
    deployment = rows[0]
    # A constructor-argument deployment that std rejects reverts, and the
    # runner stops after reporting it.
    rejected = has_constructor_arguments(case) and deployment.get("stage") == "deployment" and \
        deployment.get("status") == "reverted" and len(rows) == 1 and exit_code == 1
    if (deployment.get("stage") != "deployment" or deployment.get("status") != "returned") and not rejected:
        raise Finding("inconclusive-resource" if deployment.get("status") == "out-of-fuel" else "execution-error", "core-deployment", json.dumps(deployment))
    calls = rows[1:]
    if any(row.get("stage") != "execution" for row in calls):
        raise ValueError("unexpected Hull storage output stage")
    if has_constructor_arguments(case) and not case["transactions"]:
        # The runner requires a call, so a scenario without transactions sends
        # one placeholder; it runs only after an accepted deployment, and its
        # row is no part of the case.
        calls, exit_code = [], 1 if rejected else 0
    complete = len(calls) == len(case["transactions"]) and all(row.get("status") in {"returned", "reverted"} for row in calls)
    if complete and exit_code and not rejected:
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
    if has_constructor_arguments(case):
        history["deployment"] = {"status": deployment.get("status"), "output": deployment.get("output")}
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
    # A constructor-argument case also keeps its initializer and deployment record.
    for key in ("program", "source", "provenance", "contract", "transactions", selected["planKey"], "initialState", "observedSlots",
                *(("initializerProgram", "deployment") if has_constructor_arguments(case) else ())):
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
        arguments = common.hex_bytes(case["contract"]["constructorCalldata"], "constructor arguments") \
            if has_constructor_arguments(case) else b""
        tx_hash = submit(rpc, {"from": sender, "data": "0x" + (init + arguments).hex(), "value": hex(deployment_value(case)), "gas": gas}, report["evmDeployment"])
        deployed = receipt(rpc, tx_hash, runner)
        report["evmDeployment"]["receipt"] = deployed
        evm_deployment = {"status": "returned", "output": None}
        if deployed["status"] != "0x1":
            trace = rpc.call("debug_traceTransaction", [tx_hash, {"disableStorage": True, "disableStack": True, "enableMemory": False}])
            report["evmDeployment"]["trace"] = trace
            outcome = trace_result(deployed, trace)
            if not has_constructor_arguments(case) or outcome["status"] != "reverted":
                raise Finding("inconclusive-resource" if outcome["status"] in RESOURCE_STATUSES else "execution-error", "evm-deployment", json.dumps(outcome))
            # A failed deployment ends the scenario at the would-be creation
            # address, where nothing is installed.
            evm_deployment = {"status": "reverted", "output": outcome["output"]}
            created = rpc.call("eth_getTransactionByHash", [tx_hash])
            address = creation_address(sender, quantity(created.get("nonce") if isinstance(created, dict) else None, "deployment nonce"))
            if common.hex_bytes(rpc.call("eth_getCode", [address, deployed["blockNumber"]]), "failed deployment code"):
                raise Finding("adapter-error", "evm-deployment", "a reverted deployment installed code")
        else:
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
            "observedSlots": list(slots), "constructor": {**base, "calldata": case["contract"]["constructorCalldata"]
                                                          if has_constructor_arguments(case) else "0x"},
            "calls": [{"id": tx["id"], "context": {**base, "calldata": tx["calldata"]}, "persist": True} for tx in case["transactions"]]}
        if has_constructor_arguments(case) and not case["transactions"]:
            # The runner requires a call; a rejected deployment never reaches it.
            scenario["calls"] = [{"id": "placeholder", "persist": True, "context": {**base, "calldata": selected["selector"] + "00" * 64}}]
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
        if has_constructor_arguments(case):
            keyed["deployment"] = evm_deployment
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
        # A failed deployment ends the scenario before any transaction.
        for index, tx in enumerate(case["transactions"] if evm_deployment["status"] == "returned" else []):
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
