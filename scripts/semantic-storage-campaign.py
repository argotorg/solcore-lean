#!/usr/bin/env python3
"""Bounded stateful three-way campaigns with stable-transaction reduction.

Normal execution never changes observations. The explicit test adapter changes
one copied observation only after the complete actual history matches. Original
reports stay immutable and replayable; synthetic findings have their own branch.
"""
from __future__ import annotations
import argparse
import copy
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
from types import SimpleNamespace

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

adapter = load("storage_differential", ROOT / "scripts/semantic-storage-differential.py")
legacy = load("campaign_utilities", ROOT / "scripts/semantic-campaign.py")
common = adapter.common
save_json, directory_bytes, compact_report = legacy.save_json, legacy.directory_bytes, legacy.compact_report
PATHS = adapter.PATHS
SCHEMA = "solcore-lean.semantic-storage-campaign.v1"
MANIFEST_SCHEMA = "solcore-lean.semantic-storage-corpus-manifest.v1"
CORPUS_SCHEMA = "solcore-lean.semantic-storage-corpus.v1"
ANALYSIS_SCHEMA = "solcore-lean.semantic-storage-analysis.v2"
TEST_ADAPTER = "xor-one-history-word-after-matched-execution-v1"
RESOURCE = "inconclusive-resource"
SHRINKABLE = legacy.SHRINKABLE
VERSIONS = ("generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
            "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion")
LOG_VERSIONS = VERSIONS + ("framingVersion",)
DIMENSIONS = ("Features", "Inputs", "HelperCounts", "TransactionCounts", "Templates", "Outcomes", "CompletionPatterns")
KEYED_DIMENSIONS = DIMENSIONS + ("Keys", "Aliases")
ARRAY_DIMENSIONS = DIMENSIONS + ("Lengths",)
# Committed logs per transaction, their topic counts and data bytes, and the
# guarded sites of each reverted transaction, whose logs rollback discards.
LOG_EXTRA = {"LogCounts": tuple(range(4)), "TopicArities": tuple(range(5)), "DataSizes": (0, 32, 64),
             "DiscardedLogCounts": tuple(range(4))}
LOG_DIMENSIONS = DIMENSIONS + tuple(LOG_EXTRA)
# Call values, the values reverted transactions must refund, and deployment values.
VALUE_EXTRA = ("Values", "RevertedValues", "DeploymentValues")
VALUE_DIMENSIONS = DIMENSIONS + VALUE_EXTRA
# Payload lengths, and those of reverted transactions, whose slot writes rollback discards;
# each bytes profile admits lengths up to its own bound.
BYTES_EXTRA = ("PayloadLengths", "RevertedPayloadLengths")
BYTES_DIMENSIONS = DIMENSIONS + BYTES_EXTRA
# Ledger senders, recipients and amounts, distinct senders per scenario, and
# revert causes: odd flags, or an insufficient balance under even flags.
LEDGER_EXTRA = ("Senders", "Recipients", "Amounts", "SenderCounts", "RevertCauses")
LEDGER_DIMENSIONS = DIMENSIONS + LEDGER_EXTRA + ("Aliases",)
LEDGER_CAUSES = ("odd-flags", "insufficient-balance")
# Outer lengths of nested values and the lengths of their present rows.
NESTED_EXTRA = {"RowCounts": tuple(range(4)), "RowLengths": tuple(range(3))}
NESTED_DIMENSIONS = DIMENSIONS + tuple(NESTED_EXTRA)
# The canonical lengths, malformation kinds and prescribed std outcomes of
# malformed calldata: a rejecting error selector, or acceptance.
MALFORMED_EXTRA = ("Lengths", "Malformations", "Rejections")
MALFORMED_DIMENSIONS = DIMENSIONS + MALFORMED_EXTRA
MALFORMED_OUTCOMES = adapter.STD_ERRORS + ("accepted",)
# Malformed nested values: outer and row lengths, the rows that row
# malformations target, the malformation kinds and the prescribed std outcomes.
MALFORMED_NESTED_EXTRA = {"RowCounts": tuple(range(5)), "RowLengths": tuple(range(4)), "MalformedRows": tuple(range(4))}
MALFORMED_NESTED_DIMENSIONS = DIMENSIONS + tuple(MALFORMED_NESTED_EXTRA) + MALFORMED_EXTRA[1:]
# Malformed bytes: the canonical payload lengths, malformation kinds and outcomes.
MALFORMED_BYTES_DIMENSIONS = DIMENSIONS + ("PayloadLengths",) + MALFORMED_EXTRA[1:]
# Several methods: method counts, the positions transactions call, selector
# orders, arities and the prescribed outcomes, a missing selector or acceptance.
METHODS_EXTRA = {"MethodCounts": (2, 3, 4), "MethodPositions": (0, 1, 2, 3), "SelectorOrders": adapter.SELECTOR_ORDERS,
                 "Arities": (0, 1, 2), "Rejections": (adapter.STD_NO_SELECTOR, "accepted")}
METHODS_DIMENSIONS = DIMENSIONS + tuple(METHODS_EXTRA)
# Storage loops: plan masks, transactions' iteration counts, the carries
# `iteration` (an iteration read what the previous wrote) and `rollback` (a
# revert discarded loop writes), and the iteration slots a later transaction
# read after an earlier committed one wrote them.
LOOP_EXTRA = {"Masks": adapter.LOOP_MASKS, "IterationCounts": tuple(range(8)), "IterationCarries": ("iteration", "rollback"),
              "CarriedSlots": tuple(range(2, 9))}
LOOP_DIMENSIONS = DIMENSIONS + tuple(LOOP_EXTRA)
# Keccak loops: plan loop and key masks, transactions' iteration counts and the
# carries `iteration` (an iteration read the slot zero the previous one wrote),
# `entry` (two iterations of a transaction addressed one entry), `transaction`
# (an iteration read an entry an earlier committed transaction wrote) and
# `rollback` (a revert discarded logged iterations).
KECCAK_LOOP_EXTRA = {"Masks": adapter.LOOP_MASKS, "KeyMasks": adapter.LOOP_MASKS, "IterationCounts": tuple(range(8)),
                     "IterationCarries": ("entry", "iteration", "rollback", "transaction")}
KECCAK_LOOP_DIMENSIONS = DIMENSIONS + tuple(KECCAK_LOOP_EXTRA)
# Inline Yul loops: the plan's form, and each form's iteration counts as
# `form:count` and carries as `form:carry`, beside the dimensions of the loop
# profile whose plan the form renders.
FORM_EXTRA = ("Forms", "FormIterations", "FormCarries")
# Enum and struct storage: the shape's variant count, payload kinds, the
# payload-free variant's position, the enum's record position and Word type;
# the methods called; overwrites `count:old>new` of one committed variant by
# another at one location; committed field updates `target:kind`; reads whose
# decoded value's slots keep a stale payload or tag Word; both keys written in
# one mapping, or across the wrap; and the writing methods of reverts.
ADT_EXTRA = {"AdtVariantCounts": (2, 3, 4), "AdtPayloads": tuple(adapter.ADT_PAYLOAD_WIDTHS),
             "AdtClearPositions": ("first", "middle", "last"), "AdtChoicePositions": (0, 1, 2),
             "AdtWordTypes": adapter.ADT_WORD_TYPES, "AdtMethods": tuple(adapter.ADT_METHODS),
             "AdtOverwrites": tuple(f"{count}:{old}>{new}" for count in (2, 3, 4) for old in range(count)
                                    for new in range(count) if old != new),
             "AdtFieldUpdates": ("record:word", "record:choice", "entry:word", "entry:choice"),
             "AdtStaleReads": ("getChoice", "getChoiceAt", "getRecord", "getRecordAt"),
             "AdtNeighbourKeys": ("choices", "records", "wrap"),
             "AdtRevertedWrites": tuple(method for method in adapter.ADT_METHODS if not method.startswith("get"))}
ADT_DIMENSIONS = DIMENSIONS + tuple(ADT_EXTRA)
# Tuple returns: plan arities, each arity's outcomes as `arity:status`, the
# carries `committed` (a returned tuple's prior slots came from an earlier
# committed transaction) and `rollback` (a returned tuple follows a revert whose
# writes it must not read), and the node budgets of generated cases.
TUPLE_EXTRA = {"TupleArities": adapter.TUPLE_ARITIES,
               "ArityOutcomes": tuple(f"{arity}:{status}" for arity in adapter.TUPLE_ARITIES for status in ("returned", "reverted")),
               "TupleCarries": ("committed", "rollback"), "NodeBudgets": (384, 512)}
TUPLE_DIMENSIONS = DIMENSIONS + tuple(TUPLE_EXTRA)
# Bytes returns: the lengths of returned values, each length class's outcomes as
# `class:status` (empty, a partial last Word or whole Words), the carries
# `committed` and `rollback` into a returned value, and the node budgets of
# generated cases.
BYTES_RETURN_EXTRA = {"ReturnedLengths": tuple(range(adapter.MAX_RETURN_LENGTH + 1)),
                      "LengthOutcomes": tuple(f"{kind}:{status}" for kind in ("empty", "partial", "whole")
                                              for status in ("returned", "reverted")),
                      "ReturnCarries": ("committed", "rollback"), "ReturnNodeBudgets": (384, 512)}
BYTES_RETURN_DIMENSIONS = DIMENSIONS + tuple(BYTES_RETURN_EXTRA)
# Enum returns: the returned constructors as `count:position`, their fields as
# `static:kind` or `dynamic:kind`, padded (narrower than the widest
# constructor) and full-width returns of both kinds, the lengths of returned
# `bytes` fields, the shapes' counts of `bytes` constructors, the carries
# `committed` and `rollback` into a returned value, and the node budgets of
# generated cases.
ENUM_RETURN_EXTRA = {"EnumPositions": tuple(f"{count}:{position}" for count in (2, 3, 4) for position in range(count)),
                     "EnumFields": ("static:none", "static:one", "static:two", "dynamic:none", "dynamic:one",
                                    "dynamic:two", "dynamic:bytes"),
                     "EnumPadding": ("static:padded", "static:full", "dynamic:padded", "dynamic:full"),
                     "EnumBytesLengths": tuple(range(adapter.MAX_RETURN_LENGTH + 1)),
                     "EnumBytesConstructors": (0, 1, 2),
                     "EnumCarries": ("committed", "rollback"), "EnumNodeBudgets": (384, 512)}
ENUM_RETURN_DIMENSIONS = DIMENSIONS + tuple(ENUM_RETURN_EXTRA)
ENUM_FIELD_KINDS = {"": "none", "uint256": "one", "uint256,uint256": "two", "bytes": "bytes"}
ARRAY_LENGTHS = (0, 1, 2, 3)
NUMERIC_DIMENSIONS = ("Inputs", "Keys") + VALUE_EXTRA + ("Senders", "Recipients", "Amounts")
ALIASES = ("key-counter", "successor-counter", "repeated-key", "successor-key")
# Static entry aliasing of the mapping: the maximum key's successor wraps to zero.
MAPPING_ALIASES = ("repeated-key", "successor-key", "wrapped-successor")
# Static ledger aliasing: a self-transfer, a sender an earlier transaction paid, a repeated sender.
LEDGER_ALIASES = ("self-transfer", "received-then-sent", "repeated-sender")
TEST_FIELD = re.compile(r"output|log|balance|stray|storage:(?:0|[1-9][0-9]{0,77})")
# The `stray` adapter XORs one into the implicit zero Word of this undeclared
# slot in one path's whole committed storage: a stray write no other path made.
STRAY_SLOT = str(2**256 - 2)


def dimensions(profile_name):
    if adapter.PROFILES[profile_name].get("forms"):
        return {"loops": LOOP_DIMENSIONS, "keccak-loops": KECCAK_LOOP_DIMENSIONS}[adapter.PROFILES[profile_name]["abi"]] + FORM_EXTRA
    if adapter.encoding(adapter.PROFILES[profile_name]) == "nested":
        return MALFORMED_NESTED_DIMENSIONS
    if adapter.encoding(adapter.PROFILES[profile_name]) == "bytes":
        return MALFORMED_BYTES_DIMENSIONS
    if adapter.PROFILES[profile_name]["abi"] == "methods":
        return METHODS_DIMENSIONS
    if adapter.PROFILES[profile_name]["abi"] == "loops":
        return LOOP_DIMENSIONS
    if adapter.PROFILES[profile_name]["abi"] == "keccak-loops":
        return KECCAK_LOOP_DIMENSIONS
    if adapter.PROFILES[profile_name]["abi"] == "adts":
        return ADT_DIMENSIONS
    if adapter.PROFILES[profile_name]["abi"] == "tuples":
        return TUPLE_DIMENSIONS
    if adapter.PROFILES[profile_name]["abi"] == "bytes-returns":
        return BYTES_RETURN_DIMENSIONS
    if adapter.PROFILES[profile_name]["abi"] == "enum-returns":
        return ENUM_RETURN_DIMENSIONS
    return {"keyed": KEYED_DIMENSIONS, "mapping": KEYED_DIMENSIONS, "array": ARRAY_DIMENSIONS, "flags": LOG_DIMENSIONS,
            "value": VALUE_DIMENSIONS, "bytes": BYTES_DIMENSIONS, "ledger": LEDGER_DIMENSIONS, "nested": NESTED_DIMENSIONS,
            "malformed": MALFORMED_DIMENSIONS}.get(
        adapter.PROFILES[profile_name]["abi"], DIMENSIONS)


def value_coverage(case, statuses):
    """Call values, the values of reverted transactions and the deployment value."""
    return {"Values": {tx["value"] for tx in case["transactions"]},
            "RevertedValues": {tx["value"] for tx, status in zip(case["transactions"], statuses) if status == "reverted"},
            "DeploymentValues": {str(adapter.deployment_value(case))}}


def ledger_coverage(case, statuses):
    """Senders, recipients, amounts, distinct senders and the cause of each
    revert: odd flags, or an insufficient balance under even flags."""
    transactions = case["transactions"]
    return {"Senders": {tx["sender"] for tx in transactions}, "Recipients": {tx["recipient"] for tx in transactions},
            "Amounts": {tx["amount"] for tx in transactions}, "SenderCounts": {len({tx["sender"] for tx in transactions})},
            "RevertCauses": {"odd-flags" if int(tx["flags"]) % 2 else "insufficient-balance"
                             for tx, status in zip(transactions, statuses) if status == "reverted"}}


def bytes_coverage(case, statuses):
    """Payload lengths, and the lengths of reverted payloads."""
    lengths = [len(adapter.payload(tx)) for tx in case["transactions"]]
    return {"PayloadLengths": set(lengths),
            "RevertedPayloadLengths": {length for length, status in zip(lengths, statuses) if status == "reverted"}}


def malformed_coverage(case):
    """Canonical lengths, malformation kinds and prescribed std outcomes; for
    nested values, outer and row lengths and the rows row malformations target;
    for bytes, payload lengths."""
    transactions = case["transactions"]
    if adapter.has_malformed_nested(case):
        values = [adapter.malformed_nested_values(tx) for tx in transactions]
        shapes = {"RowCounts": {len(value) for value in values}, "RowLengths": {len(row) for value in values for row in value},
                  "MalformedRows": {tx["malformation"]["row"] for tx in transactions if "row" in tx["malformation"]}}
    elif adapter.has_malformed_bytes(case):
        shapes = {"PayloadLengths": {len(adapter.payload(tx)) for tx in transactions}}
    else:
        shapes = {"Lengths": {len(tx["values"]) for tx in transactions}}
    return {**shapes, "Malformations": {tx["malformation"]["kind"] for tx in transactions},
            "Rejections": {tx["stdRejection"] or "accepted" for tx in transactions}}


def methods_coverage(case):
    """Method counts, called positions, the selector order, arities and
    prescribed outcomes of a several-methods case."""
    methods, _ = adapter.contract_methods(case)
    names = [method["name"] for method in methods]
    return {"MethodCounts": {len(methods)},
            "MethodPositions": {names.index(tx["method"]) for tx in case["transactions"] if tx["method"] is not None},
            "SelectorOrders": {case["contract"]["selectorOrder"]}, "Arities": {method["arity"] for method in methods},
            "Rejections": {tx["stdRejection"] or "accepted" for tx in case["transactions"]}}


def loops_coverage(case, statuses):
    """The plan's mask, iteration counts, the in-transaction and rollback
    carries, and the iteration slots that a transaction read after an earlier
    committed transaction of the scenario wrote them."""
    counts = [adapter.loop_iterations(case, tx) for tx in case["transactions"]]
    carries = ({"iteration"} if any(count >= 2 for count in counts) else set()) | (
        {"rollback"} if any(count >= 1 and status == "reverted" for count, status in zip(counts, statuses)) else set())
    carried = {2 + iteration for index, count in enumerate(counts) for iteration in range(count)
               if any(statuses[earlier] == "returned" and counts[earlier] > iteration for earlier in range(index))}
    return {"Masks": {case[adapter.profile(case)["planKey"]]["mask"]}, "IterationCounts": set(counts),
            "IterationCarries": carries, "CarriedSlots": carried}


def keccak_loops_coverage(case, statuses):
    """The plan's loop and key masks, iteration counts, and the carries within
    a transaction, across committed transactions and through a rollback."""
    counts = [adapter.loop_iterations(case, tx) for tx in case["transactions"]]
    keys = [adapter.keccak_loop_keys(case, tx) for tx in case["transactions"]]
    carries = ({"iteration"} if any(count >= 2 for count in counts) else set()) | (
        {"entry"} if any(len(set(values)) < len(values) for values in keys) else set()) | (
        {"transaction"} if any(key in keys[earlier] for index, values in enumerate(keys) for key in values
                               for earlier in range(index) if statuses[earlier] == "returned") else set()) | (
        {"rollback"} if any(count >= 1 and status == "reverted" for count, status in zip(counts, statuses)) else set())
    plan = case[adapter.profile(case)["planKey"]]
    return {"Masks": {plan["mask"]}, "KeyMasks": {plan["keyMask"]}, "IterationCounts": set(counts),
            "IterationCarries": carries}


def form_values(selected):
    """The values each form dimension admits: the profile's forms, and each
    form paired with an iteration count or with a carry of its loop profile."""
    carries = (LOOP_EXTRA if selected["abi"] == "loops" else KECCAK_LOOP_EXTRA)["IterationCarries"]
    return {"Forms": selected["forms"],
            "FormIterations": tuple(f"{form}:{count}" for form in selected["forms"] for count in range(8)),
            "FormCarries": tuple(f"{form}:{carry}" for form in selected["forms"] for carry in carries)}


def forms_coverage(case, values):
    """The plan's form, paired with the case's iteration counts and carries."""
    form = case[adapter.profile(case)["planKey"]]["form"]
    return {"Forms": {form}, "FormIterations": {f"{form}:{count}" for count in values["IterationCounts"]},
            "FormCarries": {f"{form}:{carry}" for carry in values["IterationCarries"]}}


def adt_variant_slots(widths, variant):
    """The enum offsets variant `variant` occupies: the tags its decoding reads
    and its payload."""
    count = len(widths)
    tags = set(range(variant + 1)) if variant + 1 < count else set(range(count - 1))
    payload = variant + 1 if variant + 1 < count else count - 1
    return tags | set(range(payload, payload + widths[variant]))


def adt_coverage(case, statuses):
    """The shape's classes, the called methods, and, over the committed
    transactions in order, the overwrites at each enum location, the field
    updates, the reads of an enum whose slots keep a Word an earlier committed
    write left outside the decoded variant, both keys written in one mapping,
    and the writing methods that reverted."""
    plan = case["adtStoragePlan"]
    shape = adapter.adt_shape(case)
    widths, position, count = shape["widths"], shape["position"], len(shape["widths"])
    clear = shape["clear"]
    variants, written, overwrites, updates, stale, keyed = {}, {}, set(), set(), set(), {"choices": set(), "records": set()}
    for tx, status in zip(case["transactions"], statuses):
        method = tx["method"]
        if status != "returned":
            continue
        record, target = "Record" in method, method.endswith("At")
        location = ("records" if record else "choices", tx["key"]) if target else ("record" if record else "choice", None)
        if method.startswith("get"):
            if location in variants and written[location] - adt_variant_slots(widths, variants[location]):
                stale.add(method)
            continue
        if target:
            keyed[location[0]].add(tx["key"])
        if method.startswith("set"):
            updates.add(("entry" if target else "record") + ":" + ("choice" if tx["field"] == position else "word"))
            if tx["field"] != position:
                continue
        variant = clear if method.startswith("clear") else tx["variant"]
        if location in variants and variants[location] != variant:
            overwrites.add(f"{count}:{variants[location]}>{variant}")
        variants[location] = variant
        written[location] = written.get(location, set()) | adt_variant_slots(widths, variant)
    keys = {str(key) for key in adapter.adt_keys(case)}
    neighbours = {name for name, values in keyed.items() if values == keys}
    if neighbours and int(plan["keyBase"]) == 2**256 - 1:
        neighbours.add("wrap")
    return {"AdtVariantCounts": {count}, "AdtPayloads": set(plan["shape"]["variants"]),
            "AdtClearPositions": {"first" if clear == 0 else "last" if clear == count - 1 else "middle"},
            "AdtChoicePositions": {position}, "AdtWordTypes": {plan["shape"]["wordType"]},
            "AdtMethods": {tx["method"] for tx in case["transactions"]}, "AdtOverwrites": overwrites,
            "AdtFieldUpdates": updates, "AdtStaleReads": stale, "AdtNeighbourKeys": neighbours,
            "AdtRevertedWrites": {tx["method"] for tx, status in zip(case["transactions"], statuses)
                                  if status == "reverted" and not tx["method"].startswith("get")}}


def tuples_coverage(case, statuses):
    """The plan's arity and its outcomes, the carries into a returned tuple
    from an earlier committed transaction and past an earlier revert, and a
    generated case's node budget."""
    arity = adapter.tuple_arity(case)
    returned = [index for index, status in enumerate(statuses) if status == "returned"]
    carries = ({"committed"} if any("returned" in statuses[:index] for index in returned) else set()) | (
        {"rollback"} if any("reverted" in statuses[:index] for index in returned) else set())
    origin = case["provenance"]["origin"]
    budgets = {origin["maxProgramNodes"]} if origin.get("kind") == adapter.profile(case)["originKind"] else set()
    return {"TupleArities": {arity}, "ArityOutcomes": {f"{arity}:{status}" for status in statuses},
            "TupleCarries": carries, "NodeBudgets": budgets}


def length_class(length):
    return "empty" if length == 0 else "whole" if length % 32 == 0 else "partial"


def bytes_returns_coverage(case, statuses):
    """The returned lengths, each length class's outcomes, the carries into a
    returned value from an earlier committed transaction and past an earlier
    revert, and a generated case's node budget."""
    lengths = [adapter.return_length(tx) for tx in case["transactions"]]
    returned = [index for index, status in enumerate(statuses) if status == "returned"]
    carries = ({"committed"} if any("returned" in statuses[:index] for index in returned) else set()) | (
        {"rollback"} if any("reverted" in statuses[:index] for index in returned) else set())
    origin = case["provenance"]["origin"]
    budgets = {origin["maxProgramNodes"]} if origin.get("kind") == adapter.profile(case)["originKind"] else set()
    return {"ReturnedLengths": {lengths[index] for index in returned},
            "LengthOutcomes": {f"{length_class(length)}:{status}" for length, status in zip(lengths, statuses)},
            "ReturnCarries": carries, "ReturnNodeBudgets": budgets}


def enum_returns_coverage(case, statuses):
    """The returned constructors' positions and fields, padded and full-width
    returns, returned `bytes` lengths, the shape's `bytes` constructor count, the
    carries into a returned value from an earlier committed transaction and past
    an earlier revert, and a generated case's node budget."""
    constructors = adapter.enum_constructors(case)
    static, head = adapter.enum_layout(case)
    kind = "static" if static else "dynamic"
    returned = [index for index, status in enumerate(statuses) if status == "returned"]
    chosen = [int(common.word(case["transactions"][index]["choice"])) % len(constructors) for index in returned]
    carries = ({"committed"} if any("returned" in statuses[:index] for index in returned) else set()) | (
        {"rollback"} if any("reverted" in statuses[:index] for index in returned) else set())
    origin = case["provenance"]["origin"]
    budgets = {origin["maxProgramNodes"]} if origin.get("kind") == adapter.profile(case)["originKind"] else set()
    return {"EnumPositions": {f"{len(constructors)}:{choice}" for choice in chosen},
            "EnumFields": {f"{kind}:{ENUM_FIELD_KINDS[constructors[choice][1]]}" for choice in chosen},
            "EnumPadding": {f"{kind}:{'padded' if 32 + adapter.ENUM_FIELD_HEADS[constructors[choice][1]] < head else 'full'}"
                            for choice in chosen},
            "EnumBytesLengths": {adapter.return_length(case["transactions"][index])
                                 for index, choice in zip(returned, chosen) if constructors[choice][1] == "bytes"},
            "EnumBytesConstructors": {[fields for _, fields in constructors].count("bytes")},
            "EnumCarries": carries, "EnumNodeBudgets": budgets}


def nested_coverage(case):
    """Outer lengths, and the lengths of the rows present."""
    values = [adapter.nested_values(tx) for tx in case["transactions"]]
    return {"RowCounts": {len(value) for value in values}, "RowLengths": {len(row) for value in values for row in value}}


def versions(profile_name):
    return LOG_VERSIONS if adapter.PROFILES[profile_name].get("logs") else VERSIONS


def log_coverage(case, statuses, rows=None):
    """Static shapes from the plan and flags, or actual original-Core logs."""
    shapes = []
    for index, tx in enumerate(case["transactions"]):
        if rows is None:
            shapes.append(adapter.expected_log_shapes(case, tx))
        else:
            shapes.append(adapter.log_shapes(adapter.logs(rows[index]["logs"])))
    return {"LogCounts": {len(values) for values in shapes},
            "TopicArities": {topics for values in shapes for topics, _ in values},
            "DataSizes": {size for values in shapes for _, size in values},
            "DiscardedLogCounts": {len(adapter.guarded_sites(case, tx)) for tx, status in zip(case["transactions"], statuses)
                                   if status == "reverted"}}


def inputs(case):
    """Runtime Words: the ABI input, every element of the dynamic or nested
    arrays, or every zero-padded payload chunk the bytes step folds."""
    if adapter.has_malformed_nested(case):
        return {str(value) for tx in case["transactions"] for row in adapter.malformed_nested_values(tx) for value in row}
    if adapter.has_methods(case):
        return {value for tx in case["transactions"] for value in tx["inputs"]}
    if adapter.has_adts(case):
        return {tx["input"] for tx in case["transactions"] if "input" in tx}
    if adapter.has_malformed_bytes(case):
        return {str(chunk) for tx in case["transactions"] for chunk in adapter.payload_chunks(tx)}
    if adapter.profile(case)["abi"] in ("array", "malformed"):
        return {value for tx in case["transactions"] for value in tx["values"]}
    if adapter.has_nested(case):
        return {str(value) for tx in case["transactions"] for row in adapter.nested_values(tx) for value in row}
    if adapter.has_bytes(case):
        return {str(chunk) for tx in case["transactions"] for chunk in adapter.payload_chunks(tx)}
    return {tx["input"] for tx in case["transactions"]}


def aliases(case):
    """Static aliasing among transaction keys, independent of execution: of raw
    slots for keyed storage, of entry slots for the mapping, and of sender and
    recipient entries for the ledger."""
    if adapter.profile(case)["abi"] == "ledger":
        senders = [int(common.word(tx["sender"], "transaction sender")) for tx in case["transactions"]]
        recipients = [int(common.word(tx["recipient"], "transaction recipient")) for tx in case["transactions"]]
        found = set()
        if any(sender == recipient for sender, recipient in zip(senders, recipients)):
            found.add("self-transfer")
        if any(recipients[i] == senders[j] for i in range(len(senders)) for j in range(i + 1, len(senders))):
            found.add("received-then-sent")
        if len(set(senders)) < len(senders):
            found.add("repeated-sender")
        return found
    keys = [int(common.word(tx["key"], "transaction key")) for tx in case["transactions"]]
    found = set()
    if adapter.profile(case)["abi"] == "mapping":
        if 2**256 - 1 in keys:
            found.add("wrapped-successor")
    else:
        if int(adapter.COUNTER_SLOT) in keys:
            found.add("key-counter")
        if (int(adapter.COUNTER_SLOT) - 1) % 2**256 in keys:
            found.add("successor-counter")
    if len(set(keys)) < len(keys):
        found.add("repeated-key")
    if any((left + 1) % 2**256 == right for i, left in enumerate(keys) for j, right in enumerate(keys) if i != j):
        found.add("successor-key")
    return found


def case_hash(case):
    # Runtime inputs and sequence removals do not change the fixed contract. A
    # call-value deployment value is part of the deployed world, not the program.
    identity = {key: case[key] for key in ("program", "transactions")}
    if adapter.has_balances(case):
        identity["deploymentValue"] = str(adapter.deployment_value(case))
    return common.digest(common.json_bytes(identity))


def steps(case):
    """The case's step programs: one, or one per method of a several-methods case."""
    plan = case[adapter.profile(case)["planKey"]]
    return [method["stepProgram"] for method in plan["methods"]] if adapter.has_methods(case) else [plan["stepProgram"]]


def step_helper_count(step):
    if step.get("resultType") != {"tag": "function", "parameter": "word", "result": "word"} or step.get("dataDefinitions") != []:
        raise ValueError("storage step must be a closed Word function graph")
    return legacy.bound_helper_count(step.get("body"))


def helper_count(case):
    return step_helper_count(case[adapter.profile(case)["planKey"]]["stepProgram"])


def helper_counts(case):
    return {step_helper_count(step) for step in steps(case)}


def recipes(case):
    origin = case["provenance"].get("origin", {})
    if origin.get("kind") != adapter.profile(case)["originKind"]:
        return set()
    origins = origin.get("stepOrigins") if adapter.has_methods(case) else [origin.get("stepOrigin")]
    if not isinstance(origins, list) or not origins:
        raise ValueError("generated storage case lacks its aggregate step recipe")
    result = set()
    for step in origins:
        if not isinstance(step, dict) or step.get("kind") != "aggregate-generated":
            raise ValueError("generated storage case lacks its aggregate step recipe")
        helpers = step.get("helpers")
        if not isinstance(helpers, list) or not 1 <= len(helpers) <= 3:
            raise ValueError("invalid storage helper recipe count")
        for helper in helpers:
            value = helper.get("template") if isinstance(helper, dict) else None
            if type(value) is not int or value not in range(4):
                raise ValueError("invalid aggregate template recipe")
            result.add(value)
    return result


def validate_manifest(manifest):
    if not isinstance(manifest, dict) or manifest.get("schema") != MANIFEST_SCHEMA or manifest.get("profile") not in adapter.PROFILES:
        raise ValueError("unsupported storage corpus manifest")
    selected = adapter.PROFILES[manifest["profile"]]
    if manifest.get("coverageKind") != "step-core-ast-features":
        raise ValueError("storage corpus coverage must name the step AST")
    for key in versions(manifest["profile"]):
        if not isinstance(manifest.get(key), str) or not manifest[key]:
            raise ValueError(f"missing corpus {key}")
    for key in ("requiredFeatures", "requiredInputs"):
        values = manifest.get(key)
        if not isinstance(values, list) or any(not isinstance(value, str) for value in values) or len(set(values)) != len(values):
            raise ValueError(f"{key} must contain unique strings")
    for value in manifest["requiredInputs"]:
        common.word(value)
    for key in ("requiredHelperCounts", "requiredTransactionCounts"):
        values = manifest.get(key)
        if not isinstance(values, list) or any(type(v) is not int or v not in (1, 2, 3) for v in values) or len(set(values)) != len(values):
            raise ValueError(f"invalid {key}")
    requirements = manifest.get("generationRecipeRequirements")
    if not isinstance(requirements, dict) or set(requirements) != {"templates"}:
        raise ValueError("storage recipe requirements must contain templates only")
    values = requirements["templates"]
    if not isinstance(values, list) or any(type(v) is not int or v not in range(4) for v in values) or len(set(values)) != len(values):
        raise ValueError("invalid storage template requirements")
    outcomes = manifest.get("requiredOutcomes", [])
    patterns = manifest.get("requiredCompletionPatterns", [])
    if selected["rollback"]:
        if not isinstance(outcomes, list) or any(not isinstance(v, str) for v in outcomes) or sorted(outcomes) != ["returned", "reverted"]:
            raise ValueError("rollback coverage requires returned and reverted outcomes")
        if not isinstance(patterns, list) or not patterns or any(not isinstance(v, str) or
                not 1 <= len(v.split(",")) <= 3 or any(s not in outcomes for s in v.split(",")) for v in patterns) or len(set(patterns)) != len(patterns):
            raise ValueError("invalid rollback completion pattern requirements")
    elif outcomes or patterns:
        raise ValueError("completion requirements belong to the rollback profile")
    if selected["keyed"] or selected["abi"] == "mapping":
        catalog = MAPPING_ALIASES if selected["abi"] == "mapping" else ALIASES
        keys, kinds = manifest.get("requiredKeys"), manifest.get("requiredAliases")
        if not isinstance(keys, list) or not keys or any(not isinstance(v, str) for v in keys) or len(set(keys)) != len(keys):
            raise ValueError("keyed coverage requires unique required keys")
        for value in keys:
            common.word(value, "required key")
        if not isinstance(kinds, list) or any(v not in catalog for v in kinds) or len(set(kinds)) != len(kinds):
            raise ValueError("invalid keyed alias requirements")
    elif selected["abi"] == "ledger":
        if "requiredKeys" in manifest:
            raise ValueError("key coverage belongs to the keyed storage and mapping profiles")
        for dimension in ("Senders", "Recipients", "Amounts"):
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(not isinstance(v, str) for v in values) or len(set(values)) != len(values):
                raise ValueError(f"ledger coverage requires unique required{dimension}")
            for value in values:
                common.word(value, "required " + dimension)
        if any(value not in adapter.LEDGER_SENDERS for value in manifest["requiredSenders"]):
            raise ValueError("required senders must be fixed ledger senders")
        counts, causes, kinds = (manifest.get(key) for key in ("requiredSenderCounts", "requiredRevertCauses", "requiredAliases"))
        if not isinstance(counts, list) or not counts or any(type(v) is not int or v not in (1, 2, 3) for v in counts) or len(set(counts)) != len(counts):
            raise ValueError("ledger coverage requires unique distinct-sender counts from one to three")
        if not isinstance(causes, list) or not causes or any(v not in LEDGER_CAUSES for v in causes) or len(set(causes)) != len(causes):
            raise ValueError("invalid ledger revert-cause requirements")
        if not isinstance(kinds, list) or any(v not in LEDGER_ALIASES for v in kinds) or len(set(kinds)) != len(kinds):
            raise ValueError("invalid ledger alias requirements")
    elif "requiredKeys" in manifest or "requiredAliases" in manifest:
        raise ValueError("key coverage belongs to the keyed storage and mapping profiles")
    if selected["abi"] != "ledger" and any("required" + dimension in manifest for dimension in LEDGER_EXTRA):
        raise ValueError("sender coverage belongs to the ledger profile")
    nested_malformed = selected["abi"] == "malformed" and adapter.encoding(selected) == "nested"
    bytes_malformed = selected["abi"] == "malformed" and adapter.encoding(selected) == "bytes"
    if selected["abi"] == "array" or (selected["abi"] == "malformed" and adapter.encoding(selected) == "array"):
        lengths = manifest.get("requiredLengths")
        if not isinstance(lengths, list) or not lengths or any(type(v) is not int or v not in ARRAY_LENGTHS for v in lengths) or len(set(lengths)) != len(lengths):
            raise ValueError("dynamic-array coverage requires unique lengths from zero to three")
    elif "requiredLengths" in manifest:
        raise ValueError("length coverage belongs to the dynamic-array profiles")
    if selected["abi"] == "malformed":
        kinds = (adapter.NESTED_MALFORMATION_KINDS if nested_malformed else
                 adapter.BYTES_MALFORMATION_KINDS if bytes_malformed else adapter.MALFORMATION_KINDS)
        for dimension, allowed in (("Malformations", kinds), ("Rejections", MALFORMED_OUTCOMES)):
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(v not in allowed for v in values) or len(set(values)) != len(values):
                raise ValueError(f"malformed-calldata coverage requires unique required{dimension} from {list(allowed)}")
    elif selected["abi"] == "methods":
        for dimension, allowed in METHODS_EXTRA.items():
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(v not in allowed or type(v) is bool for v in values) or len(set(values)) != len(values):
                raise ValueError(f"several-methods coverage requires unique required{dimension} from {list(allowed)}")
        if "requiredMalformations" in manifest:
            raise ValueError("malformation coverage belongs to the malformed-calldata profiles")
    elif "requiredMalformations" in manifest or "requiredRejections" in manifest:
        raise ValueError("malformation coverage belongs to the malformed-calldata profile")
    if selected["abi"] != "methods" and any("required" + dimension in manifest for dimension in METHODS_EXTRA if dimension != "Rejections"):
        raise ValueError("method coverage belongs to the several-methods profile")
    if selected["abi"] == "loops":
        for dimension, allowed in LOOP_EXTRA.items():
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(v not in allowed or type(v) is bool for v in values) or len(set(values)) != len(values):
                raise ValueError(f"storage-loop coverage requires unique required{dimension} from {list(allowed)}")
    elif selected["abi"] == "keccak-loops":
        for dimension, allowed in KECCAK_LOOP_EXTRA.items():
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(v not in allowed or type(v) is bool for v in values) or len(set(values)) != len(values):
                raise ValueError(f"Keccak-loop coverage requires unique required{dimension} from {list(allowed)}")
        if "requiredCarriedSlots" in manifest:
            raise ValueError("carried-slot coverage belongs to the storage-loop profile")
    elif any("required" + dimension in manifest for dimension in LOOP_EXTRA):
        raise ValueError("loop coverage belongs to the storage-loop profile")
    if selected["abi"] == "adts":
        for dimension, allowed in ADT_EXTRA.items():
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(v not in allowed or type(v) is bool for v in values) or len(set(values)) != len(values):
                raise ValueError(f"enum and struct storage coverage requires unique required{dimension} from {list(allowed)}")
    elif any("required" + dimension in manifest for dimension in ADT_EXTRA):
        raise ValueError("enum and struct coverage belongs to the enum and struct storage profile")
    if selected["abi"] == "tuples":
        for dimension, allowed in TUPLE_EXTRA.items():
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(v not in allowed or type(v) is bool for v in values) or len(set(values)) != len(values):
                raise ValueError(f"tuple-return coverage requires unique required{dimension} from {list(allowed)}")
    elif any("required" + dimension in manifest for dimension in TUPLE_EXTRA):
        raise ValueError("tuple coverage belongs to the tuple-return profile")
    if selected["abi"] == "bytes-returns":
        for dimension, allowed in BYTES_RETURN_EXTRA.items():
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(v not in allowed or type(v) is bool for v in values) or len(set(values)) != len(values):
                raise ValueError(f"bytes-return coverage requires unique required{dimension} from {list(allowed)}")
    elif any("required" + dimension in manifest for dimension in BYTES_RETURN_EXTRA):
        raise ValueError("bytes-return coverage belongs to the bytes-return profile")
    if selected["abi"] == "enum-returns":
        for dimension, allowed in ENUM_RETURN_EXTRA.items():
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(v not in allowed or type(v) is bool for v in values) or len(set(values)) != len(values):
                raise ValueError(f"enum-return coverage requires unique required{dimension} from {list(allowed)}")
    elif any("required" + dimension in manifest for dimension in ENUM_RETURN_EXTRA):
        raise ValueError("enum-return coverage belongs to the enum-return profile")
    if selected["abi"] != "keccak-loops" and "requiredKeyMasks" in manifest:
        raise ValueError("key-mask coverage belongs to the Keccak-loop profile")
    if selected.get("forms"):
        for dimension, allowed in form_values(selected).items():
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(v not in allowed for v in values) or len(set(values)) != len(values):
                raise ValueError(f"inline Yul loop coverage requires unique required{dimension} from {list(allowed)}")
    elif any("required" + dimension in manifest for dimension in FORM_EXTRA):
        raise ValueError("form coverage belongs to the inline Yul loop profiles")
    # The Keccak-loop profile records the log framing, but its log shapes follow
    # from the iteration counts, not from the log profile's static sites.
    if selected["abi"] == "keccak-loops":
        if any("required" + dimension in manifest for dimension in LOG_EXTRA):
            raise ValueError("log coverage belongs to the log profile")
    elif selected.get("logs"):
        for dimension, allowed in LOG_EXTRA.items():
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(type(v) is not int or v not in allowed for v in values) or len(set(values)) != len(values):
                raise ValueError(f"log coverage requires unique required{dimension} from {list(allowed)}")
    elif any("required" + dimension in manifest for dimension in LOG_EXTRA) or "framingVersion" in manifest:
        raise ValueError("log coverage belongs to the log profile")
    if selected.get("balances"):
        for dimension in VALUE_EXTRA:
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(not isinstance(v, str) for v in values) or len(set(values)) != len(values):
                raise ValueError(f"call-value coverage requires unique required{dimension}")
            for value in values:
                common.word(value, "required " + dimension)
    elif any("required" + dimension in manifest for dimension in VALUE_EXTRA):
        raise ValueError("value coverage belongs to the call-value profile")
    if selected["abi"] == "bytes":
        bound = adapter.bytes_layout(selected)[0]
        for dimension in BYTES_EXTRA:
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(type(v) is not int or not 0 <= v <= bound for v in values) or len(set(values)) != len(values):
                raise ValueError(f"bytes coverage requires unique required{dimension} from zero to {bound}")
    elif bytes_malformed:
        values = manifest.get("requiredPayloadLengths")
        if not isinstance(values, list) or not values or any(type(v) is not int or not 0 <= v <= 256 for v in values) or len(set(values)) != len(values):
            raise ValueError("malformed-bytes coverage requires unique requiredPayloadLengths from zero to 256")
        if "requiredRevertedPayloadLengths" in manifest:
            raise ValueError("reverted payload coverage belongs to the bytes profiles")
    elif any("required" + dimension in manifest for dimension in BYTES_EXTRA):
        raise ValueError("payload coverage belongs to the bytes profile")
    if selected["abi"] == "nested" or nested_malformed:
        extra = MALFORMED_NESTED_EXTRA if nested_malformed else NESTED_EXTRA
        for dimension, allowed in extra.items():
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(type(v) is not int or v not in allowed for v in values) or len(set(values)) != len(values):
                raise ValueError(f"nested-array coverage requires unique required{dimension} from {list(allowed)}")
        if any("required" + dimension in manifest for dimension in MALFORMED_NESTED_EXTRA if dimension not in extra):
            raise ValueError("malformed-row coverage belongs to the malformed nested-array profile")
    elif any("required" + dimension in manifest for dimension in MALFORMED_NESTED_EXTRA):
        raise ValueError("row coverage belongs to the nested-array profile")
    if not isinstance(manifest.get("cases"), list):
        raise ValueError("corpus cases must be an array")
    ids = set()
    for entry in manifest["cases"]:
        if not isinstance(entry, dict) or not isinstance(entry.get("id"), str) or not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", entry["id"]) or entry["id"] in ids:
            raise ValueError("corpus IDs must be unique bounded identifiers")
        ids.add(entry["id"])
        generated = "generation" in entry
        if generated == (selected["planKey"] in entry) or ("transactions" in entry) == generated:
            raise ValueError(f"corpus entry requires generation XOR {selected['planKey']}+transactions")
        if "expectedHistory" in entry and (not selected["declared"] or not isinstance(entry["expectedHistory"], list)):
            raise ValueError("independent expected histories are declared-slot transaction lists")
        if any(key in entry for key in ("program", "loopPlan", "input")):
            raise ValueError("storage corpus uses a plan and transaction sequence")
        expected = entry.get("expectedFeatures")
        if not isinstance(expected, list) or any(not isinstance(v, str) for v in expected) or len(set(expected)) != len(expected):
            raise ValueError("expectedFeatures must contain unique strings")
        if generated:
            request = entry["generation"]
            if not isinstance(request, dict) or set(request) != {"seed", "maxProgramNodes"}:
                raise ValueError("invalid storage generation request")
            seed = common.word(request["seed"], "seed")
            nodes = request["maxProgramNodes"]
            if int(seed) >= 2**64 or type(nodes) is not int or not 1 <= nodes <= 512:
                raise ValueError("storage generation request exceeds bounds")
        else:
            if not isinstance(entry[selected["planKey"]], dict) or entry[selected["planKey"]].get("schema") != selected["planSchema"]:
                raise ValueError("invalid imported storage plan")
            # Full source/host checking and canonical ABI validation are native.
            if not isinstance(entry["transactions"], list) or not 1 <= len(entry["transactions"]) <= 3:
                raise ValueError("invalid imported transaction count")
    return manifest


def analyze(report, case, path=None, transaction_id=None, field="output"):
    actual = copy.deepcopy(report.get("comparison", {"category": "adapter-error", "stage": "missing-report", "pairs": {}}))
    histories = copy.deepcopy(report.get("histories", {}))
    synthetic = False
    selected = transaction_id or case["transactions"][0]["id"]
    if path is not None:
        if path not in PATHS or not TEST_FIELD.fullmatch(field) or (
                not adapter.profile(case)["declared"] and field not in ("output", "stray", "storage:0", "storage:1")) or (
                field == "log" and not adapter.has_logs(case)) or (field == "balance" and not adapter.has_balances(case)):
            raise ValueError("unknown synthetic history adapter")
        if actual.get("category") == "matched":
            if adapter.compare(histories, case).get("category") != "matched":
                raise ValueError("matched report has inconsistent actual histories")
            rows = histories[path]["transactions"]
            row = next((row for row in rows if row["id"] == selected), None)
            # Like a removed transaction, a candidate whose keys no longer
            # declare the selected slot cannot preserve the synthetic finding.
            declared = field in ("output", "log", "balance") or field[len("storage:"):] in adapter.observed_slots(case)
            if field == "stray":
                # A candidate that declares the slot, or already holds it on
                # this path, cannot keep a synthetic stray write.
                held = row is not None and any(entry["slot"] == STRAY_SLOT for account in row["accountStorage"] for entry in account["storage"])
                declared = STRAY_SLOT not in adapter.observed_slots(case) and not held
            if row is not None and declared:
                if field == "output":
                    # The low bit of the last Word of an output of whole Words:
                    # a one-Word output changes as it always did.
                    value = common.hex_bytes(row["output"], "test output")
                    if not value or len(value) % 32:
                        raise ValueError("test adapter requires returned Words")
                    row["output"] = "0x" + (value[:-1] + bytes([value[-1] ^ 1])).hex()
                elif field == "balance":
                    row["committedBalance"] = str(int(common.word(row["committedBalance"], "test balance")) ^ 1)
                    if rows[-1]["id"] == selected:
                        histories[path]["finalBalance"] = row["committedBalance"]
                elif field == "stray":
                    entries = row["accountStorage"][0]["storage"]
                    entries.append({"slot": STRAY_SLOT, "value": "1"})
                    entries.sort(key=lambda entry: int(entry["slot"]))
                    if rows[-1]["id"] == selected:
                        histories[path]["finalAccountStorage"] = copy.deepcopy(row["accountStorage"])
                elif field == "log":
                    # The first committed log's first topic, else its last data
                    # byte. A transaction without such a log cannot keep it.
                    log = row["logs"][0] if isinstance(row.get("logs"), list) and row["logs"] else None
                    data = common.hex_bytes(log["data"], "test log data") if log else b""
                    if log is None or not (log["topics"] or data):
                        row = None
                    elif log["topics"]:
                        log["topics"][0] = str(int(common.word(log["topics"][0])) ^ 1)
                    else:
                        log["data"] = "0x" + (data[:-1] + bytes([data[-1] ^ 1])).hex()
                else:
                    slot = next(index for index, entry in enumerate(row["committedStorage"]) if entry["slot"] == field[len("storage:"):])
                    value = row["committedStorage"][slot]["value"]
                    row["committedStorage"][slot]["value"] = str(int(common.word(value)) ^ 1)
                    if rows[-1]["id"] == selected:
                        histories[path]["finalStorage"] = copy.deepcopy(row["committedStorage"])
                synthetic = row is not None
    result = adapter.compare(histories, case) if synthetic else actual
    analysis = {"schema": ANALYSIS_SCHEMA, "backend": common.resolve_backend(None, report), "synthetic": synthetic,
            "testAdapter": {"name": TEST_ADAPTER, "path": path, "transactionId": selected, "field": field} if path else None,
            "actualComparison": actual, "comparison": result, "histories": histories}
    if adapter.uses_selector_rule(case):
        # The rows compared by their std error selector, with the selector.
        analysis["selectorRows"] = copy.deepcopy(result.get("selectorRows", []))
    return analysis


def fingerprint(analysis):
    comparison = analysis["comparison"]
    txid = comparison.get("transactionId")
    rows = {}
    shapes = {}
    for path in PATHS:
        history = analysis.get("histories", {}).get(path, {})
        history = history if isinstance(history, dict) else {}
        transactions = history.get("transactions", [])
        transactions = transactions if isinstance(transactions, list) else []
        row = next((r for r in transactions if isinstance(r, dict) and r.get("id") == txid), {}) if txid else {}
        rows[path] = row
        output = row.get("output")
        shape = "word" if isinstance(output, str) and re.fullmatch(r"0x[0-9a-f]{64}", output) else "bytes" if output is not None else "none"
        shapes[path] = {"status": row.get("status", "not-observed"), "payload": shape}
    snapshots = []
    for path in PATHS:
        history = analysis.get("histories", {}).get(path, {})
        snapshots.append(history.get("initialStorage", []) if comparison.get("stage") == "initial-storage" and isinstance(history, dict)
                         else rows[path].get("committedStorage", []))
    keyed = keyed_analysis(analysis)
    slots = []
    if keyed:
        named = [{row.get("slot"): row.get("value") for row in snapshot if isinstance(row, dict) and isinstance(row.get("slot"), str)}
                 if isinstance(snapshot, list) else {} for snapshot in snapshots]
        names = sorted({name for values in named for name in values if re.fullmatch(r"0|[1-9][0-9]{0,77}", name)}, key=int)
        for name in names:
            values = [values.get(name) if isinstance(values.get(name), str) else None for values in named]
            if len(set(values)) > 1:
                slots.append(name)
    for index, slot in enumerate(() if keyed else adapter.SLOTS):
        values = [snapshot[index].get("value") if isinstance(snapshot, list) and len(snapshot) > index and isinstance(snapshot[index], dict) else None for snapshot in snapshots]
        values = [value if isinstance(value, str) else None for value in values]
        if len(set(values)) > 1:
            slots.append(slot)
    result = {"backend": common.resolve_backend(None, analysis), "category": comparison.get("category"), "stage": comparison.get("stage"), "transactionId": txid,
            "disagreeingPairs": sorted(pair for pair, same in comparison.get("pairs", {}).items() if same is False),
            "fields": sorted(comparison.get("fields", [])), "storageSlots": slots,
            "pathShapes": shapes, "synthetic": analysis["synthetic"]}
    if keyed:
        result["undeclaredPaths"] = sorted(comparison.get("undeclaredPaths", []))
    # Whole-storage differences: account, declared slot or `undeclared`, and the
    # paths lacking the slot; and the paths whose revert changed the whole storage.
    result["accountStorageDifferences"] = copy.deepcopy(comparison.get("accountStorageDifferences", []))
    result["accountStorageRollbackPaths"] = sorted(comparison.get("accountStorageRollbackPaths", []))
    if log_analysis(analysis):
        result["logPaths"] = sorted(comparison.get("logPaths", []))
    return result


def keyed_analysis(analysis):
    histories = analysis.get("histories", {})
    return isinstance(histories, dict) and any(isinstance(history, dict) and history.get("schema") in
                                               (adapter.KEYED_HISTORY_SCHEMA, adapter.ARRAY_HISTORY_SCHEMA, adapter.LOG_HISTORY_SCHEMA,
                                                adapter.VALUE_HISTORY_SCHEMA, adapter.BYTES_HISTORY_SCHEMA, adapter.MAPPING_HISTORY_SCHEMA,
                                                adapter.LEDGER_HISTORY_SCHEMA, adapter.LONG_BYTES_HISTORY_SCHEMA,
                                                adapter.NESTED_HISTORY_SCHEMA, adapter.MALFORMED_HISTORY_SCHEMA,
                                                adapter.MALFORMED_NESTED_HISTORY_SCHEMA, adapter.MALFORMED_BYTES_HISTORY_SCHEMA,
                                                adapter.METHODS_HISTORY_SCHEMA, adapter.LOOP_HISTORY_SCHEMA,
                                                adapter.ADT_HISTORY_SCHEMA,
                                                adapter.KECCAK_LOOP_HISTORY_SCHEMA, adapter.TUPLE_HISTORY_SCHEMA,
                                                adapter.BYTES_RETURN_HISTORY_SCHEMA, adapter.ENUM_RETURN_HISTORY_SCHEMA)
                                               for history in histories.values())


def log_analysis(analysis):
    histories = analysis.get("histories", {})
    return isinstance(histories, dict) and any(isinstance(history, dict) and history.get("schema") in
                                               (adapter.LOG_HISTORY_SCHEMA, adapter.KECCAK_LOOP_HISTORY_SCHEMA)
                                               for history in histories.values())


def same_failure(expected, analysis):
    return expected["category"] in SHRINKABLE and fingerprint(analysis) == {**expected, "backend": common.resolve_backend(None, expected)}


def transaction_counts(histories, case):
    """Observed on any path; completed on all paths; equal returned prefixes."""
    result = {"executed": 0, "completed": 0, "matched": 0}
    try:
        values = {path: adapter.normalize_history(histories[path], case, path) for path in PATHS if path in histories}
        address = adapter.log_address(histories) if adapter.has_logs(case) else None
    except (ValueError, TypeError, KeyError):
        return result
    prefix = len(values) == 3 and all(all(row["value"] == "0" for row in value["initialStorage"]) and
                                      not any(account["storage"] for account in value["initialAccountStorage"]) and
                                      not value.get("initialUndeclaredStorage") and not value.get("initialLogs") and
                                      value.get("initialBalance", "0") == str(adapter.deployment_value(case)) for value in values.values())
    for index, tx in enumerate(case["transactions"]):
        by_path = {path: value["transactions"][index] for path, value in values.items() if index < len(value["transactions"])}
        rows = list(by_path.values())
        result["executed"] += bool(rows)
        complete = len(rows) == 3 and all(row["status"] in ("returned", "reverted") for row in rows)
        result["completed"] += complete
        # Malformed calldata: a std rejection is compared by its selector.
        by_path = adapter.comparable(case, tx, by_path) if complete else by_path
        rows = list(by_path.values())
        prefix = prefix and complete and all(adapter.without_containment(row) == adapter.without_containment(rows[0]) for row in rows) and not any(
            row.get("undeclaredStorage") for row in rows) and all(adapter.conforms(case, tx, by_path[path],
                value["transactions"][index - 1]["committedStorage"] if index else value["initialStorage"], address,
                (value["transactions"][index - 1].get("committedBalance") if index else value.get("initialBalance")),
                value["transactions"][index - 1]["accountStorage"] if index else value["initialAccountStorage"])
                for path, value in values.items() if path in by_path)
        result["matched"] += prefix
    return result


def compact_storage_report(report):
    result = compact_report(report)
    for record in result.get("evmTransactions", []):
        trace = record.get("trace", {})
        if "structLogs" in trace:
            logs = trace.pop("structLogs")
            trace.update(structLogsSha256=common.digest(common.json_bytes(logs)), structLogsCount=len(logs))
    return result


def count_outcome(counts, analysis, case):
    """A known prefix mismatch does not imply the entire scenario completed."""
    category = analysis["comparison"]["category"]
    counts["executed"] += 1
    counts["completed"] += transaction_counts(analysis["histories"], case)["completed"] == len(case["transactions"])
    bucket = {"matched": "matched", "semantic-mismatch": "mismatched", RESOURCE: "inconclusive"}.get(category, "errors")
    counts[bucket] += 1
    if category == "source-rejected":
        counts["sourceRejected"] += 1
    elif category == "compilation-rejected":
        counts["compilationRejected"] += 1
    counts["syntheticMismatches"] += analysis["synthetic"]


class Campaign:
    def __init__(self, args):
        self.args, self.started = args, time.monotonic()
        self.backend = common.resolve_backend(getattr(args, "backend", None))
        # The pinned solc compiles the EVM path only under --backend yul.
        self.solc = Path(getattr(args, "solc", None) or shutil.which("solc") or "solc").resolve()
        self.profile = getattr(args, "profile", "stateful-storage")
        self.specification = adapter.PROFILES[self.profile]
        self.deadline = self.started + args.seconds
        self.reserve = min(40 * 1024 * 1024, args.disk_bytes // 4)
        self.work = args.output / ".work"
        self.work.mkdir()
        self.counter = self.shrink_attempts = 0
        self.materialized = []
        self.summary = {"schema": SCHEMA, "backend": self.backend, "status": "running", "synthetic": args.test_perturb_path is not None,
            "configuration": {"profile": self.profile, "backend": self.backend, **{key: getattr(args, key) for key in ("seed", "nodes", "cases", "attempts", "seconds", "disk_bytes", "shrink_attempts", "shrink_candidates", "direct_fuel", "core_fuel", "gas", "case_timeout")}},
            "testAdapter": {"name": TEST_ADAPTER, "path": args.test_perturb_path, "transactionId": args.test_transaction_id, "field": args.test_field} if args.test_perturb_path else None,
            "tools": {"campaignSha256": common.file_digest(Path(__file__)), "differentialSha256": common.file_digest(ROOT / "scripts/semantic-storage-differential.py"), "caseTool": str(args.case_tool),
                      **({"solc": str(self.solc)} if self.backend == "yul" else {})},
            "counts": {key: 0 for key in ("generated", "excluded", "generationResourceExclusions", "executed", "completed", "matched", "mismatched", "inconclusive", "errors", "sourceRejected", "compilationRejected", "syntheticMismatches")},
            "transactionCounts": {"kind": "observed on any path; completed on all three; matched ordered prefixes; shrink executions excluded", "planned": 0, "executed": 0, "completed": 0, "matched": 0, "actualMatched": 0},
            "coverage": {"kind": "step AST features and declared helpers; native-verified generation recipes; inputs and sequence lengths of fully matched scenarios; not opcode traces",
                         **{prefix + dimension: [] for prefix in ("generated", "matched", "required", "missing") for dimension in dimensions(self.profile)}},
            "cases": [], "materializedIds": [], "findings": [], "secondaryFindings": [],
            "retention": "input cases/compact receipts; complete archives for original/final/secondary findings; matched exports removed (use --case; exact archive replay unavailable)"}
        # Random generation draws steps with G0 revision two; a corpus or a saved
        # case keeps the version it records.
        self.g0_version = getattr(args, "g0_version", None)
        if self.g0_version is None and not args.corpus and not args.case:
            self.g0_version = legacy.STATEFUL_RANDOM_G0_VERSION
        self.summary["configuration"]["g0Version"] = self.g0_version
        # Random generation requests the longest admitted sequence; a corpus or a
        # saved case keeps its own transactions.
        self.transactions = getattr(args, "transactions", None)
        if self.transactions is None and not args.corpus and not args.case:
            self.transactions = adapter.MAX_TRANSACTIONS
        self.summary["configuration"]["transactions"] = self.transactions
        self.checkpoint()

    def checkpoint(self):
        counts, coverage = self.summary["counts"], self.summary["coverage"]
        counts["unexecuted"] = counts["generated"] - counts["executed"]
        tx = self.summary["transactionCounts"]
        tx["unobserved"] = tx["planned"] - tx["executed"]
        for dimension in dimensions(self.profile):
            coverage["missing" + dimension] = sorted(set(coverage["required" + dimension]) - set(coverage["matched" + dimension]), key=int if dimension in NUMERIC_DIMENSIONS else None)
        self.summary.update(elapsedSeconds=round(time.monotonic() - self.started, 3), retainedBytes=directory_bytes(self.args.output), shrinkAttempts=self.shrink_attempts)
        save_json(self.args.output / "summary.json", self.summary)

    def guard(self):
        if time.monotonic() >= self.deadline:
            raise common.Finding(RESOURCE, "campaign-time", "campaign time limit reached")
        if directory_bytes(self.args.output) >= self.args.disk_bytes - self.reserve:
            raise common.Finding(RESOURCE, "campaign-disk", "campaign disk limit reached; metadata reserve retained")

    def tool(self, command, stage):
        self.guard()
        args = SimpleNamespace(total_timeout=max(.001, self.deadline - time.monotonic()), timeout=self.args.case_timeout,
                               output_limit=min(4 * 1024 * 1024, self.args.disk_bytes // 64), resource_guard=self.guard)
        runner = common.Runner(args, {"processes": []})
        result = runner.process(stage, [str(self.args.case_tool), *map(str, command)])
        if result["returncode"]:
            raise common.Finding("adapter-error", stage, result["stdout"] + result["stderr"])
        value = json.loads(result["stdout"])
        if not isinstance(value, dict):
            raise ValueError("native tool must return an object")
        if "caseToolSha256" not in self.summary["tools"]:
            self.summary["tools"]["caseToolSha256"] = runner.identity(self.args.case_tool)["sha256"]
        return value

    def record_coverage(self, case, prefix, histories=None):
        values = {"Features": set(case["provenance"]["features"]), "Inputs": inputs(case),
                  "HelperCounts": helper_counts(case), "TransactionCounts": {len(case["transactions"])}, "Templates": recipes(case)}
        if prefix == "matched":
            if histories is None or adapter.compare(histories, case)["category"] != "matched":
                raise ValueError("coverage requires actual matched histories")
            statuses = [row["status"] for row in histories["directCore"]["transactions"]]
        else:
            # A ledger's even flags are planned to return; only matched coverage,
            # from actual histories, can show an insufficient balance.
            statuses = [adapter.expected_status(case, tx) or "returned" for tx in case["transactions"]]
        values.update(Outcomes=set(statuses), CompletionPatterns={",".join(statuses)})
        if self.specification["abi"] in ("keyed", "mapping"):
            values.update(Keys={tx["key"] for tx in case["transactions"]}, Aliases=aliases(case))
        elif self.specification["abi"] == "array":
            values.update(Lengths={len(tx["values"]) for tx in case["transactions"]})
        elif self.specification["abi"] == "flags":
            values.update(log_coverage(case, statuses, histories["directCore"]["transactions"] if prefix == "matched" else None))
        elif self.specification["abi"] == "value":
            values.update(value_coverage(case, statuses))
        elif self.specification["abi"] == "bytes":
            values.update(bytes_coverage(case, statuses))
        elif self.specification["abi"] == "ledger":
            values.update(ledger_coverage(case, statuses), Aliases=aliases(case))
        elif self.specification["abi"] == "nested":
            values.update(nested_coverage(case))
        elif self.specification["abi"] == "malformed":
            values.update(malformed_coverage(case))
        elif self.specification["abi"] == "methods":
            values.update(methods_coverage(case))
        elif self.specification["abi"] == "loops":
            values.update(loops_coverage(case, statuses))
        elif self.specification["abi"] == "keccak-loops":
            values.update(keccak_loops_coverage(case, statuses))
        elif self.specification["abi"] == "adts":
            values.update(adt_coverage(case, statuses))
        elif self.specification["abi"] == "tuples":
            values.update(tuples_coverage(case, statuses))
        elif self.specification["abi"] == "bytes-returns":
            values.update(bytes_returns_coverage(case, statuses))
        elif self.specification["abi"] == "enum-returns":
            values.update(enum_returns_coverage(case, statuses))
        if self.specification.get("forms"):
            values.update(forms_coverage(case, values))
        for dimension, observed in values.items():
            key = prefix + dimension
            self.summary["coverage"][key] = sorted(set(self.summary["coverage"][key]) | observed, key=int if dimension in NUMERIC_DIMENSIONS else None)

    def add_case(self, case, identifier):
        adapter.validate_case(case)
        if case["schema"] != self.specification["caseSchema"]:
            raise ValueError("case differs from the selected campaign profile")
        index = len(self.materialized)
        save_json(self.args.output / "cases" / f"{index:04d}.json", case)
        self.materialized.append(case)
        self.summary["materializedIds"].append(identifier)
        self.summary["counts"]["generated"] += 1
        self.summary["transactionCounts"]["planned"] += len(case["transactions"])
        self.record_coverage(case, "generated")
        self.checkpoint()

    def recorded_g0_version(self, versions):
        """Adopt the G0 version a corpus or saved case records; generation receives it explicitly."""
        recorded = versions.get("generatorVersion") if isinstance(versions, dict) else None
        if recorded not in legacy.STATEFUL_G0_VERSIONS:
            raise ValueError("unsupported recorded G0 generator version")
        if self.g0_version is not None and self.g0_version != recorded:
            raise ValueError("G0 generator version disagrees with the supplied case or corpus")
        self.g0_version = recorded
        self.summary["configuration"]["g0Version"] = recorded
        return recorded

    def prepare_cases(self):
        if self.args.case:
            case = self.tool(["replay", self.args.case, self.args.direct_fuel], "case-replay")
            self.recorded_g0_version(case.get("provenance"))
            self.add_case(case, "saved-case")
            return
        if not self.args.corpus:
            response = self.tool(["generate", self.args.seed, self.args.nodes, self.args.cases, self.args.attempts, self.args.direct_fuel,
                                  self.g0_version, self.transactions], "generation")
            if response.get("schema") != self.specification["corpusSchema"] or not isinstance(response.get("cases"), list) or len(response["cases"]) > self.args.cases:
                raise ValueError("invalid native storage corpus")
            excluded = response.get("excluded", [])
            self.summary["counts"]["excluded"] = len(excluded)
            self.summary["counts"]["generationResourceExclusions"] = legacy.generation_resource_exclusions(excluded)
            self.summary["generation"] = {**{key: response.get(key) for key in ("requested", "attempted", "status")},
                                          "transactions": self.transactions}
            save_json(self.args.output / "generation.json", {key: value for key, value in response.items() if key != "cases"})
            for index, case in enumerate(response["cases"]):
                self.add_case(case, f"generated-{index}")
            return
        manifest = validate_manifest(common.read_json(self.args.corpus))
        if manifest["profile"] != self.profile:
            raise ValueError("manifest differs from the selected campaign profile")
        version = self.recorded_g0_version(manifest)
        save_json(self.args.output / "corpus.json", manifest)
        self.summary["corpus"] = {"path": str(self.args.corpus), "sha256": common.digest(common.json_bytes(manifest))}
        for dimension in ("Features", "Inputs", "HelperCounts", "TransactionCounts"):
            self.summary["coverage"]["required" + dimension] = manifest["required" + dimension]
        self.summary["coverage"]["requiredTemplates"] = manifest["generationRecipeRequirements"]["templates"]
        for dimension in ("Outcomes", "CompletionPatterns"):
            self.summary["coverage"]["required" + dimension] = manifest.get("required" + dimension, [])
        for dimension in {"keyed": ("Keys", "Aliases"), "mapping": ("Keys", "Aliases"), "array": ("Lengths",),
                          "flags": tuple(LOG_EXTRA), "value": VALUE_EXTRA, "bytes": BYTES_EXTRA,
                          "ledger": LEDGER_EXTRA + ("Aliases",), "nested": tuple(NESTED_EXTRA),
                          "methods": tuple(METHODS_EXTRA), "loops": tuple(LOOP_EXTRA), "tuples": tuple(TUPLE_EXTRA),
                          "keccak-loops": tuple(KECCAK_LOOP_EXTRA),
                          "adts": tuple(ADT_EXTRA),
                          "bytes-returns": tuple(BYTES_RETURN_EXTRA),
                          "enum-returns": tuple(ENUM_RETURN_EXTRA),
                          "malformed": {"nested": tuple(MALFORMED_NESTED_EXTRA) + MALFORMED_EXTRA[1:],
                                        "bytes": ("PayloadLengths",) + MALFORMED_EXTRA[1:]}.get(
                                            adapter.encoding(self.specification), MALFORMED_EXTRA)}.get(
                              self.specification["abi"], ()):
            self.summary["coverage"]["required" + dimension] = manifest["required" + dimension]
        for dimension in FORM_EXTRA if self.specification.get("forms") else ():
            self.summary["coverage"]["required" + dimension] = manifest["required" + dimension]
        self.checkpoint()
        exclusions = []
        for entry in manifest["cases"][:self.args.cases]:
            self.guard()
            if "generation" in entry:
                request = entry["generation"]
                response = self.tool(["generate", request["seed"], request["maxProgramNodes"], 1, 1, self.args.direct_fuel, version],
                                     "corpus-generation")
                if response.get("schema") != self.specification["corpusSchema"] or not isinstance(response.get("cases"), list) or len(response["cases"]) > 1:
                    raise ValueError("invalid bounded corpus generation")
                if not response["cases"]:
                    exclusions.append({"id": entry["id"], "detail": response})
                    self.summary["counts"]["excluded"] = len(exclusions)
                    self.summary["counts"]["generationResourceExclusions"] = legacy.generation_resource_exclusions(exclusions)
                    save_json(self.args.output / "generation.json", {"excluded": exclusions})
                    self.checkpoint()
                    continue
                case = response["cases"][0]
                origin = case["provenance"]["origin"]
                if origin.get("kind") != self.specification["originKind"] or any(origin.get(key) != request[key] for key in ("seed", "maxProgramNodes")):
                    raise ValueError("native generation differs from requested seed/budget")
            else:
                plan_path, tx_path = self.work / "plan.json", self.work / "transactions.json"
                save_json(plan_path, entry[self.specification["planKey"]])
                save_json(tx_path, entry["transactions"])
                try:
                    case = self.tool(["emit", plan_path, tx_path, self.args.direct_fuel], "corpus-emission")
                finally:
                    plan_path.unlink(missing_ok=True)
                    tx_path.unlink(missing_ok=True)
            if any(case["provenance"].get(key) != manifest[key] for key in versions(self.profile)) or set(case["provenance"]["features"]) != set(entry["expectedFeatures"]):
                raise ValueError("native corpus features/versions differ from manifest")
            self.add_case(case, entry["id"])
        self.summary["generation"] = {"requested": self.args.cases, "attempted": min(self.args.cases, len(manifest["cases"])), "attemptUnit": "manifest scenarios", "excluded": exclusions}
        save_json(self.args.output / "generation.json", self.summary["generation"])

    def case_args(self, case_path, folder):
        left = max(.001, self.deadline - time.monotonic())
        return SimpleNamespace(case=case_path, replay=None, backend=self.backend, solc=self.solc, output=folder, case_tool=self.args.case_tool,
            core_runner=self.args.core_runner, anvil=self.args.anvil, upstream=self.args.upstream, target_dir=self.args.target_dir,
            direct_fuel=self.args.direct_fuel, core_fuel=self.args.core_fuel, gas=self.args.gas,
            timeout=min(self.args.case_timeout, left), startup_timeout=min(30, left), total_timeout=min(self.args.case_timeout, left),
            output_limit=min(4 * 1024 * 1024, self.args.disk_bytes // 64),
            artifact_limit=min(64 * 1024 * 1024, (self.args.disk_bytes - self.reserve) // 8), resource_guard=self.guard)

    def execute_case(self, case):
        self.guard()
        self.counter += 1
        folder = self.work / f"run-{self.counter:06d}"
        folder.mkdir()
        input_path = self.work / f"input-{self.counter:06d}.json"
        save_json(input_path, case)
        args = self.case_args(input_path, folder)
        report = {"schema": adapter.REPORT_SCHEMA, "backend": self.backend, "processes": [], "histories": {},
            "budgets": {key: getattr(args, key) for key in ("direct_fuel", "core_fuel", "gas", "timeout", "startup_timeout", "total_timeout", "output_limit", "artifact_limit")},
            "scope": adapter.scope(case) if self.specification["declared"] else
                "initially empty committed slots0/1; ordered zero-value run(uint256); the contract's whole committed storage; "
                "no gas/balance/nonce equivalence"}
        interrupted = False
        try:
            adapter.execute(args, report)
        except common.Finding as error:
            report["comparison"] = adapter.interrupted_comparison(args, report, {"category": error.category, "stage": error.stage, "detail": error.detail, "pairs": {}})
        except (ValueError, OSError, KeyError, TypeError, common.RpcError, subprocess.SubprocessError) as error:
            report["comparison"] = adapter.interrupted_comparison(args, report, {"category": "adapter-error", "stage": "campaign-adapter", "detail": str(error), "pairs": {}})
        except KeyboardInterrupt:
            interrupted = True
            report["comparison"] = adapter.interrupted_comparison(args, report, {"category": RESOURCE, "stage": "campaign-interrupted", "pairs": {}})
            raise
        finally:
            report["artifacts"] = {p.name: common.file_digest(p) for p in folder.iterdir() if p.is_file()}
            save_json(folder / "report.json", report)
            input_path.unlink(missing_ok=True)
            if interrupted:
                destination = self.args.output / "interruptions" / folder.name
                destination.parent.mkdir(exist_ok=True)
                folder.rename(destination)
                self.summary.setdefault("interruptions", []).append(str(destination.relative_to(self.args.output)))
        analysis = analyze(report, case, self.args.test_perturb_path, self.args.test_transaction_id, self.args.test_field)
        save_json(folder / "analysis.json", analysis)
        return folder, report, analysis

    def retain_finding(self, index, folder, case, analysis):
        location = self.args.output / "findings" / ("synthetic" if analysis["synthetic"] else "real") / f"{index:04d}"
        location.mkdir(parents=True)
        original = location / "original"
        folder.rename(original)
        finding = {"caseIndex": index, "synthetic": analysis["synthetic"], "fingerprint": fingerprint(analysis),
            "originalCaseSha256": case_hash(case), "finalCaseSha256": case_hash(case),
            "originalArchive": str(original.relative_to(self.args.output)), "finalArchive": str(original.relative_to(self.args.output)),
            "history": str((location / "shrink.json").relative_to(self.args.output))}
        status = "not-shrinkable" if analysis["comparison"]["category"] not in SHRINKABLE else (
            "no-attempts" if self.args.shrink_attempts == 0 else "attempt-limit" if self.shrink_attempts >= self.args.shrink_attempts else "pending")
        save_json(location / "shrink.json", {"schema": "solcore-lean.semantic-storage-shrink.v1", "fingerprint": finding["fingerprint"], "steps": [], "status": status, "finalArchive": finding["finalArchive"]})
        self.summary["findings"].append(finding)
        self.checkpoint()
        return finding

    def shrink(self, original, finding):
        history_path = self.args.output / finding["history"]
        history = common.read_json(history_path)
        history["status"] = "running"
        current, current_path = original, self.args.output / finding["originalArchive"] / "case.json"
        seen = {case_hash(original)}
        try:
            while self.shrink_attempts < self.args.shrink_attempts:
                self.guard()
                # A profile may bound one native response below the requested batch.
                limit = min(self.args.shrink_candidates, self.specification.get("shrinkBatch", self.args.shrink_candidates),
                            self.args.shrink_attempts - self.shrink_attempts)
                response = self.tool(["shrink", current_path, limit, self.args.direct_fuel], "shrink-candidates")
                candidates = response.get("cases")
                if response.get("schema") != self.specification["corpusSchema"] or not isinstance(candidates, list) or len(candidates) > limit:
                    raise ValueError("invalid native bounded shrink response")
                accepted = False
                for candidate in candidates:
                    self.guard()
                    identity = case_hash(candidate)
                    if identity in seen:
                        continue
                    seen.add(identity)
                    self.shrink_attempts += 1
                    folder, report, analysis = self.execute_case(candidate)
                    keep = same_failure(finding["fingerprint"], analysis)
                    step = {"attempt": self.shrink_attempts, "caseSha256": identity,
                        "programSha256": common.digest(common.json_bytes(candidate["program"])),
                        "actualReportSha256": common.file_digest(folder / "report.json"), "fingerprint": fingerprint(analysis),
                        "accepted": keep, "actualComparison": report.get("comparison"), "comparison": analysis["comparison"]}
                    history["steps"].append(step)
                    if keep:
                        destination = history_path.parent / "reduced"
                        previous = history_path.parent / "previous-reduced"
                        if destination.exists():
                            destination.rename(previous)
                        folder.rename(destination)
                        if previous.exists():
                            shutil.rmtree(previous)
                        current, current_path = candidate, destination / "case.json"
                        finding.update(finalCaseSha256=identity, finalArchive=str(destination.relative_to(self.args.output)))
                        accepted = True
                    elif not analysis["synthetic"] and analysis["comparison"]["category"] not in ("matched", RESOURCE):
                        # A real discovery made while shrinking a synthetic test
                        # must survive independently of the synthetic branch.
                        destination = self.args.output / "findings" / "real" / f"secondary-{self.shrink_attempts:04d}"
                        destination.parent.mkdir(parents=True, exist_ok=True)
                        folder.rename(destination)
                        step["secondaryArchive"] = str(destination.relative_to(self.args.output))
                        self.summary["secondaryFindings"].append({"archive": step["secondaryArchive"], "fingerprint": fingerprint(analysis), "caseSha256": identity,
                            "synthetic": False, "parentHistory": str(history_path.relative_to(self.args.output)), "automaticReduction": False})
                    else:
                        shutil.rmtree(folder)
                    save_json(history_path, history)
                    self.checkpoint()
                    self.guard()
                    if accepted:
                        break
                if not accepted:
                    history["status"] = "attempt-limit" if self.shrink_attempts >= self.args.shrink_attempts else "no-preserving-candidate"
                    break
            else:
                history["status"] = "attempt-limit"
        except common.Finding as error:
            history.update(status="budget-exhausted" if error.category == RESOURCE else "error", stop={"category": error.category, "stage": error.stage, "detail": error.detail})
            raise
        except KeyboardInterrupt:
            history["status"] = "interrupted"
            raise
        except (ValueError, OSError, KeyError, TypeError, subprocess.SubprocessError) as error:
            history.update(status="error", stop={"category": "adapter-error", "detail": str(error)})
            raise
        finally:
            history.update(finalCaseSha256=finding["finalCaseSha256"], finalArchive=finding["finalArchive"])
            save_json(history_path, history)
            self.checkpoint()

    def run(self):
        self.prepare_cases()
        self.summary.setdefault("generation", {})["generatorVersions"] = sorted(
            {case["provenance"]["generatorVersion"] for case in self.materialized})
        self.checkpoint()
        for index, case in enumerate(self.materialized):
            self.guard()
            if self.args.test_perturb_path and self.args.test_transaction_id and self.args.test_transaction_id not in {tx["id"] for tx in case["transactions"]}:
                raise ValueError("selected synthetic transaction ID is absent from the original scenario")
            if self.args.test_perturb_path and self.args.test_field.startswith("storage:") and self.args.test_field[len("storage:"):] not in adapter.observed_slots(case):
                raise ValueError("selected synthetic slot is absent from the original scenario")
            if self.args.test_perturb_path and self.args.test_field == "stray" and STRAY_SLOT in adapter.observed_slots(case):
                raise ValueError("the synthetic stray slot is declared by the original scenario")
            folder, report, analysis = self.execute_case(case)
            category = analysis["comparison"]["category"]
            count_outcome(self.summary["counts"], analysis, case)
            for key, value in transaction_counts(analysis["histories"], case).items():
                self.summary["transactionCounts"][key] += value
            self.summary["transactionCounts"]["actualMatched"] += transaction_counts(report.get("histories", {}), case)["matched"]
            if category == "matched":
                self.record_coverage(case, "matched", report.get("histories"))
            save_json(self.args.output / "results" / f"{index:04d}.json", {"actualReport": compact_storage_report(report), "analysis": analysis})
            self.summary["cases"].append({"index": index, "id": self.summary["materializedIds"][index],
                "case": f"cases/{index:04d}.json", "result": f"results/{index:04d}.json", "caseSha256": case_hash(case),
                "category": category, "synthetic": analysis["synthetic"], "fingerprint": fingerprint(analysis)})
            if category not in ("matched", RESOURCE):
                finding = self.retain_finding(index, folder, case, analysis)
                if category in SHRINKABLE and self.shrink_attempts < self.args.shrink_attempts:
                    self.shrink(case, finding)
            else:
                shutil.rmtree(folder)
            self.checkpoint()
            print(json.dumps({"scenario": index, "category": category, "synthetic": analysis["synthetic"]}), flush=True)
        self.summary["status"] = "complete" if len(self.materialized) == self.args.cases else "generation-exhausted"


def missing_coverage(summary):
    return any(values for key, values in summary["coverage"].items() if key.startswith("missing"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--backend", choices=common.BACKENDS, default="sonatina-o0",
                        help="yul runs each scenario's EVM path on the pinned solc's Yul output; imported Hull keeps Sonatina O0")
    parser.add_argument("--solc", type=Path, default=Path(shutil.which("solc") or "solc"), help="pinned solc; used only by --backend yul")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--corpus", type=Path)
    selection.add_argument("--case", type=Path)
    parser.add_argument("--profile", choices=tuple(adapter.PROFILES))
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--nodes", type=int, default=384)
    parser.add_argument("--cases", type=int)
    parser.add_argument("--attempts", type=int, default=256)
    parser.add_argument("--g0-version", choices=legacy.STATEFUL_G0_VERSIONS,
                        help=f"G0 generator of the checked step in random generation; default {legacy.STATEFUL_RANDOM_G0_VERSION}. "
                             "A corpus or saved case uses the version it records")
    parser.add_argument("--transactions", type=int,
                        help=f"transactions per random scenario, 1 to {adapter.MAX_TRANSACTIONS}; default {adapter.MAX_TRANSACTIONS}. "
                             "A corpus or saved case keeps its own sequence")
    parser.add_argument("--seconds", type=float, default=300)
    parser.add_argument("--disk-bytes", type=int, default=256 * 1024 * 1024)
    parser.add_argument("--shrink-attempts", type=int, default=32)
    parser.add_argument("--shrink-candidates", type=int, default=64)
    parser.add_argument("--case-timeout", type=float, default=90)
    parser.add_argument("--direct-fuel", type=int, default=1000000)
    parser.add_argument("--core-fuel", type=int, default=10000000)
    parser.add_argument("--gas", type=int, default=10000000)
    parser.add_argument("--case-tool", type=Path)
    parser.add_argument("--core-runner", type=Path, help="default: the profile's imported-Hull scenario runner")
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--test-perturb-path", choices=PATHS)
    parser.add_argument("--test-transaction-id")
    parser.add_argument("--test-field", default="output",
                        help="output, storage:SLOT for an observed decimal slot, stray (whole storage), log (log profile) "
                             "or balance (call-value profile)")
    args = parser.parse_args()
    try:
        selected_profile, recorded = args.profile, None
        if args.corpus:
            manifest = validate_manifest(common.read_json(args.corpus))
            recorded = manifest.get("generatorVersion")
            if selected_profile is not None and selected_profile != manifest["profile"]:
                raise ValueError("explicit profile differs from corpus")
            selected_profile = manifest["profile"]
        if args.case:
            case = common.read_json(args.case)
            adapter.validate_case(case)
            recorded = case["provenance"].get("generatorVersion")
            case_profile = next(name for name, specification in adapter.PROFILES.items() if case["schema"] == specification["caseSchema"])
            if selected_profile is not None and selected_profile != case_profile:
                raise ValueError("explicit profile differs from saved case")
            selected_profile = case_profile
        args.profile = selected_profile or "stateful-storage"
        if args.case_tool is None:
            args.case_tool = ROOT / ".lake/build/bin" / adapter.PROFILES[args.profile]["caseTool"]
        if args.core_runner is None:
            args.core_runner = ROOT / ".lake/build/bin" / adapter.PROFILES[args.profile]["coreRunner"]
        if args.cases is None:
            args.cases = 1 if args.case else len(common.read_json(args.corpus)["cases"]) if args.corpus else 10
    except (ValueError, OSError, KeyError, TypeError, common.Finding) as error:
        parser.error(str(error))
    if args.g0_version is not None and (args.corpus or args.case) and args.g0_version != recorded:
        parser.error("--g0-version disagrees with the supplied case or corpus")
    if args.transactions is not None and (args.corpus or args.case):
        parser.error("--transactions applies only to random generation")
    if args.transactions is not None and not 1 <= args.transactions <= adapter.MAX_TRANSACTIONS:
        parser.error(f"transactions must be between 1 and {adapter.MAX_TRANSACTIONS}")
    if args.case and args.cases != 1:
        parser.error("--case requires --cases 1")
    if args.test_transaction_id and (not args.test_perturb_path or not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", args.test_transaction_id)):
        parser.error("test transaction ID requires the explicit adapter and a valid ID")
    if args.test_field != "output" and not args.test_perturb_path:
        parser.error("test field requires the explicit synthetic adapter")
    if not TEST_FIELD.fullmatch(args.test_field) or (not adapter.PROFILES[args.profile]["declared"] and args.test_field not in ("output", "stray", "storage:0", "storage:1")) or (
            args.test_field == "log" and not adapter.PROFILES[args.profile].get("logs")) or (
            args.test_field == "balance" and not adapter.PROFILES[args.profile].get("balances")):
        parser.error("test field must be output, storage:SLOT for an observed slot, stray, log for the log profile or balance for the call-value profile")
    limits = {"seed": (0, 2**64 - 1), "nodes": (1, 512), "cases": (1, 1024), "attempts": (0, 10000),
        "seconds": (.001, 86400), "disk_bytes": (16 * 1024 * 1024, 10**10), "shrink_attempts": (0, 10000),
        "shrink_candidates": (1, 4096), "case_timeout": (.001, 3600), "direct_fuel": (1, 10000000),
        "core_fuel": (1, 1000000000), "gas": (1, 1000000000)}
    for key, (lower, upper) in limits.items():
        if not math.isfinite(getattr(args, key)) or not lower <= getattr(args, key) <= upper:
            parser.error(f"{key} must be between {lower} and {upper}")
    for key in ("output", "case_tool", "core_runner", "anvil", "upstream", "target_dir", "case", "corpus", "solc"):
        if getattr(args, key) is not None:
            setattr(args, key, getattr(args, key).resolve())
    args.output.mkdir(parents=True, exist_ok=False)
    campaign = Campaign(args)
    previous = signal.getsignal(signal.SIGTERM)
    def interrupted(_signal, _frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    try:
        campaign.run()
    except common.Finding as error:
        campaign.summary.update(status="budget-exhausted" if error.category == RESOURCE else "error", stop={"category": error.category, "stage": error.stage, "detail": error.detail})
    except KeyboardInterrupt:
        campaign.summary["status"] = "interrupted"
    except (ValueError, OSError, KeyError, TypeError, subprocess.SubprocessError) as error:
        campaign.summary.update(status="error", stop={"category": "adapter-error", "detail": str(error)})
    finally:
        try:
            shutil.rmtree(campaign.work, ignore_errors=True)
            campaign.checkpoint()
            if campaign.summary["status"] == "complete" and missing_coverage(campaign.summary):
                campaign.summary["status"] = "coverage-incomplete"
                campaign.checkpoint()
        finally:
            signal.signal(signal.SIGTERM, previous)
    print(json.dumps({"status": campaign.summary["status"], "synthetic": campaign.summary["synthetic"], "counts": campaign.summary["counts"],
                      "transactionCounts": campaign.summary["transactionCounts"], "summary": str(args.output / "summary.json")}))
    return 0 if campaign.summary["status"] == "complete" and campaign.summary["counts"]["matched"] == args.cases and not missing_coverage(campaign.summary) else 1

if __name__ == "__main__":
    raise SystemExit(main())
