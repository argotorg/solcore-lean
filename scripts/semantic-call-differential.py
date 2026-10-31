#!/usr/bin/env python3
"""Compare bounded parent/child calls, committed accounts and logs on three paths.

Three profiles share this adapter: `stateful-calls` (zero-value transactions and
a fixed eight-unit parent), `stateful-forwarded-value` (payable transactions
whose parent forwards bank amounts to the child) and `stateful-call-returns`
(a parent that decodes a child method's return data with std, each contract
compiled from its own source). The original checked Core
contracts execute through the public nested runtime.
Only `stateful-call-returns` also runs with `--backend yul`: the EVM path deploys
each source's Yul through the pinned solc and imported Hull keeps Sonatina O0, as
for the storage family; the other call profiles' sources each compile both
contracts, which the Yul exporter does not admit.
Rust supplies independently compiled Hull and linked EVM images. Every EVM
observation belongs to an actual mined transaction; no Python transition model
or saved expected output supplies the reference result. Both contracts' whole
committed storage is also compared after deployment and every transaction.
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

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("storage_transport", ROOT / "scripts/semantic-storage-differential.py")
storage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(storage)
common = storage.common
Finding, RpcError = common.Finding, common.RpcError
PATHS, SLOTS, MAX_TRANSACTIONS = storage.PATHS, storage.SLOTS, storage.MAX_TRANSACTIONS
CASE_SCHEMA = "solcore-lean.semantic-call-case.v1"
REPORT_SCHEMA = "solcore-lean.semantic-call-differential.v2"
HISTORY_SCHEMA = "solcore-lean.call-history.v2"
BINDINGS_SCHEMA = "solcore-lean.call-bindings.v1"
SELECTOR = "0x7357f5d2"
ROLES = ("parent", "child")
FORWARD_CASE_SCHEMA = "solcore-lean.semantic-forward-case.v1"
FORWARD_HISTORY_SCHEMA = "solcore-lean.forward-history.v2"
FORWARD_SELECTOR = "0x24b912e5"
RETURN_CASE_SCHEMA = "solcore-lean.semantic-call-return-case.v1"
RETURN_HISTORY_SCHEMA = "solcore-lean.call-return-history.v1"
# The forwarding parent's endowment covers every generated forward: a generated
# sequence forwards at most the endowment in total. Original Core and Hull fund
# the caller with 2^80.
ENDOWMENT, CALLER_FUNDS, MAX_VALUE = 2**72, 2**80, 2**70
PROFILES = {
    "stateful-calls": {"caseSchema": CASE_SCHEMA, "historySchema": HISTORY_SCHEMA, "planKey": "callPlan",
        "planSchema": "solcore-lean.call-plan.v1", "caseTool": "semantic-call-tool", "coreRunner": "rust-hull-call-scenario",
        "scenarioSchema": "solcore-lean.call-contract-scenario.v1", "forwarding": False,
        "scope": "depth-one fixed Word calls; funded parent8/child0; both accounts' slots0/1, balances, root outcome and ordered committed logs; both accounts' whole committed storage; no gas/nonce equivalence"},
    "stateful-forwarded-value": {"caseSchema": FORWARD_CASE_SCHEMA, "historySchema": FORWARD_HISTORY_SCHEMA, "planKey": "forwardPlan",
        "planSchema": "solcore-lean.forward-plan.v1", "caseTool": "semantic-forward-tool", "coreRunner": "rust-hull-forward-scenario",
        "scenarioSchema": "solcore-lean.forward-contract-scenario.v1", "forwarding": True,
        "scope": "depth-one Word calls forwarding bank amounts; payable root values; parent endowment 2^72/child0; both accounts' slots0/1, balances, root outcome and empty logs; both accounts' whole committed storage; no sender-balance, gas or nonce equivalence"},
    "stateful-call-returns": {"caseSchema": RETURN_CASE_SCHEMA, "historySchema": RETURN_HISTORY_SCHEMA, "planKey": "callReturnPlan",
        "planSchema": "solcore-lean.call-return-plan.v1", "caseTool": "semantic-call-return-tool",
        "coreRunner": "rust-hull-call-return-scenario", "scenarioSchema": "solcore-lean.call-return-scenario.v1",
        "forwarding": False, "returns": True,
        "scope": "one depth-one call through std's raw_call to a child method whose tuple, bytes or enum return data, typed or raw with one malformation, the parent decodes with std's MemoryWordReader; zero value; the parent's slots0-6 and the child's slots0/1, balances, root outcome under the selector and empty-revert rules and empty logs; both accounts' whole committed storage; the adapter's own decoding of the child's bytes; no gas/nonce equivalence"},
}


def save(path, value):
    path.write_bytes(common.json_bytes(value))


def address(value):
    common.word(value, "address")
    if int(value) >= 2**160:
        raise ValueError("address exceeds 160 bits")
    return value


def validate_bindings(value):
    if not isinstance(value, dict) or set(value) != {"schema", "caller", "parent", "child"} or value["schema"] != BINDINGS_SCHEMA:
        raise ValueError("unsupported call bindings")
    addresses = [address(value[key]) for key in ("caller", "parent", "child")]
    # Osaka includes the BLS12-381 range and P256VERIFY at 0x100.
    if len(set(addresses)) != 3 or any(int(value[role]) <= 17 or int(value[role]) == 256 for role in ROLES):
        raise ValueError("call bindings require distinct caller and non-precompile contracts")
    return value


def profile(case):
    """The call-family profile a case schema selects."""
    if isinstance(case, dict):
        for value in PROFILES.values():
            if case.get("schema") == value["caseSchema"]:
                return value
    raise ValueError("unsupported nested-call case schema")


def forwarding(case):
    return profile(case)["forwarding"]


def endowment(forwards=False):
    return str(ENDOWMENT) if forwards else "8"


def contract_metadata(forwards=False):
    if forwards:
        parent, child = "SynthesizedForwarder", "SynthesizedRecipient"
        return {
            "parent": {"name": parent, "method": "run", "signature": "run(uint256,uint256,uint256)", "selector": FORWARD_SELECTOR,
                "payable": True, "deployPath": [parent + "Deploy"], "runtimePath": [parent + "Deploy", parent],
                "constructorCalldata": "0x", "constructorValue": str(ENDOWMENT)},
            "child": {"name": child, "entry": "fallback", "payable": True, "inputBytes": 32,
                "deployPath": [child + "Deploy"], "runtimePath": [child + "Deploy", child],
                "constructorCalldata": "0x", "constructorValue": "0"}}
    parent, child = "SynthesizedCaller", "SynthesizedCallee"
    return {
        "parent": {"name": parent, "method": "run", "signature": "run(uint256,uint256)", "selector": SELECTOR,
            "deployPath": [parent + "Deploy"], "runtimePath": [parent + "Deploy", parent],
            "constructorCalldata": "0x", "constructorValue": "8"},
        "child": {"name": child, "entry": "fallback", "payable": True, "inputBytes": 32,
            "deployPath": [child + "Deploy"], "runtimePath": [child + "Deploy", child],
            "constructorCalldata": "0x", "constructorValue": "0"}}


def validate_case(case):
    selected = profile(case)
    if selected.get("returns"):
        return validate_return_case(case)
    forwards = selected["forwarding"]
    plan = case.get(selected["planKey"])
    if not isinstance(plan, dict) or plan.get("schema") != selected["planSchema"] or not isinstance(plan.get("stepProgram"), dict):
        raise ValueError("call case requires its checked child step")
    programs = case.get("programs")
    if not isinstance(programs, dict) or set(programs) != set(ROLES) or any(not isinstance(programs[role], dict) for role in ROLES):
        raise ValueError("call case requires both original Core programs")
    if not isinstance(case.get("source"), str) or case.get("contracts") != contract_metadata(forwards):
        raise ValueError("call source or fixed ABI metadata changed")
    initial = {"accounts": [{"role": role, "balance": endowment(forwards) if role == "parent" else "0", "storage": []} for role in ROLES],
               "callerBalance": str(CALLER_FUNDS) if forwards else "0"}
    if case.get("initialState") != initial or case.get("observedSlots") != list(SLOTS):
        raise Finding("unsupported-scope", "input", "call profile requires its fixed initial accounts and observed slots")
    provenance = case.get("provenance")
    if not isinstance(provenance, dict) or any(not isinstance(provenance.get(key), str) or not provenance[key]
            for key in ("generatorVersion", "emitterVersion", "wrapperVersion")):
        raise ValueError("missing versioned call provenance")
    transactions = case.get("transactions")
    if not isinstance(transactions, list) or not 1 <= len(transactions) <= MAX_TRANSACTIONS:
        raise ValueError(f"call case requires 1 to {MAX_TRANSACTIONS} transactions")
    ids = set()
    for tx in transactions:
        keys = {"id", "input", "value", "target", "callee"} | ({"amount"} if forwards else set())
        if not isinstance(tx, dict) or set(tx) != keys:
            raise ValueError("call transactions retain symbolic roles, not invented calldata")
        identifier = tx["id"]
        if not isinstance(identifier, str) or not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", identifier) or identifier in ids:
            raise ValueError("transaction IDs must be unique bounded identifiers")
        ids.add(identifier)
        common.word(tx["input"], "transaction input")
        if forwards:
            if any(int(common.word(tx[key], "transaction " + key)) > MAX_VALUE for key in ("value", "amount")):
                raise ValueError("forwarded-value call values and amounts are at most 2^70")
            if (tx["target"], tx["callee"]) != ("parent", "child"):
                raise Finding("unsupported-scope", "input", "call transactions must use the fixed roles")
        elif (tx["target"], tx["callee"], tx["value"]) != ("parent", "child", "0"):
            raise Finding("unsupported-scope", "input", "call transactions must use the fixed roles and zero root value")


def calldata(bindings, tx):
    if "amount" in tx:
        return FORWARD_SELECTOR + f"{int(bindings['child']):064x}{int(tx['input']):064x}{int(tx['amount']):064x}"
    return SELECTOR + f"{int(bindings['child']):064x}{int(tx['input']):064x}"


def initial_accounts(bindings, forwards=False):
    return [{"role": role, "address": bindings[role], "balance": endowment(forwards) if role == "parent" else "0",
             "storage": [{"slot": slot, "value": "0"} for slot in SLOTS]} for role in ROLES]


def accounts(rows, bindings):
    if not isinstance(rows, list) or len(rows) != 2:
        raise ValueError("both committed contract accounts are required")
    result = []
    for role, row in zip(ROLES, rows):
        if not isinstance(row, dict) or row.get("role") != role or row.get("address") != bindings[role]:
            raise ValueError("committed account identity changed")
        result.append({"role": role, "address": address(row["address"]),
            "balance": common.word(row.get("balance"), "committed balance"), "storage": storage.storage(row.get("storage"))})
    return result


def logs(rows):
    if not isinstance(rows, list):
        raise ValueError("committed logs must be an ordered list")
    result = []
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get("topics"), list):
            raise ValueError("invalid committed log")
        result.append({"address": address(row.get("address")),
            "topics": [common.word(topic, "log topic") for topic in row["topics"]],
            "data": "0x" + common.hex_bytes(row.get("data"), "log data").hex()})
    return result


def whole_storage(rows, bindings, label="account storage"):
    """Both contracts' whole committed storage, bound to their actual addresses."""
    result = storage.account_storage(rows, ROLES, label)
    if any(account["address"] != bindings[account["role"]] for account in result):
        raise ValueError(f"{label} account identity changed")
    return result


def normalize_history(history, case, bindings):
    if returns(case):
        return return_normalize_history(history, case, bindings)
    if not isinstance(history, dict) or history.get("schema") != profile(case)["historySchema"]:
        raise ValueError("unsupported call history")
    initial = accounts(history.get("initialAccounts"), bindings)
    initial_whole = whole_storage(history.get("initialAccountStorage"), bindings, "initial account storage")
    rows = history.get("transactions")
    if not isinstance(rows, list) or len(rows) > len(case["transactions"]):
        raise ValueError("invalid call history length")
    result = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict) or row.get("id") != case["transactions"][index]["id"] or type(row.get("index")) is not int or row["index"] != index:
            raise ValueError("transaction identity or order changed")
        status = row.get("status")
        if not isinstance(status, str):
            raise ValueError("missing call status")
        normalized = {"id": row["id"], "index": index, "status": status,
                      "committedAccounts": accounts(row.get("committedAccounts"), bindings),
                      "accountStorage": whole_storage(row.get("accountStorage"), bindings)}
        if status in ("returned", "reverted"):
            normalized.update(output="0x" + common.hex_bytes(row.get("output"), "call output").hex(), logs=logs(row.get("logs")))
        else:
            if index != len(rows) - 1:
                raise ValueError("execution continued after an incomplete call")
            normalized.update(detail=row.get("detail", ""), logs=None)
        result.append(normalized)
    complete = len(rows) == len(case["transactions"]) and all(row["status"] in ("returned", "reverted") for row in result)
    if history.get("status") != ("complete" if complete else "incomplete"):
        raise ValueError("call history completion flag disagrees with its rows")
    remaining = [tx["id"] for tx in case["transactions"][len(rows):]]
    unobserved = history.get("unobserved", [])
    if unobserved not in ([], remaining[:1]) or unobserved and (complete or any(row["status"] not in ("returned", "reverted") for row in result)):
        raise ValueError("invalid unknown transaction completion")
    if history.get("unexecuted") != remaining[len(unobserved):]:
        raise ValueError("unexecuted transaction identities changed")
    final = None if unobserved else accounts(history.get("finalAccounts"), bindings)
    if unobserved and history.get("finalAccounts") is not None:
        raise ValueError("unknown completion cannot claim a final committed world")
    if not unobserved and final != (result[-1]["committedAccounts"] if result else initial):
        raise ValueError("final accounts differ from the last committed snapshot")
    final_whole = None if unobserved else whole_storage(history.get("finalAccountStorage"), bindings, "final account storage")
    if unobserved and history.get("finalAccountStorage") is not None:
        raise ValueError("unknown completion cannot claim a final whole storage")
    if not unobserved and final_whole != (result[-1]["accountStorage"] if result else initial_whole):
        raise ValueError("final whole storage differs from the last committed observation")
    return {"initialAccounts": initial, "initialAccountStorage": initial_whole, "transactions": result, "finalAccounts": final,
        "finalAccountStorage": final_whole, "status": history["status"], "unexecuted": history["unexecuted"], "unobserved": unobserved}


def expected_status(tx):
    if "stdRejection" in tx:
        return return_expected_status(tx)
    return "reverted" if int(tx["input"]) & 2 else "returned"


def account(rows, role):
    return next(row for row in rows if row["role"] == role)


def slot(row, name):
    return int(next(entry["value"] for entry in row["storage"] if entry["slot"] == name))


def forwarding_fields(case, rows, values, index):
    """Fields of completed forwarded-value rows that break the fixed protocol:
    committed logs must stay empty, a child revert under a committed root keeps
    the child's account, the child holds exactly its slot one, and both
    balances sum to the endowment plus every committed call value. A root
    revert is checked by the shared rollback rule."""
    fields = set()
    for path, row in rows.items():
        prior = values[path]["transactions"][index - 1]["committedAccounts"] if index else values[path]["initialAccounts"]
        accepted = sum(int(tx["value"]) for tx, earlier in zip(case["transactions"][:index + 1], values[path]["transactions"][:index + 1])
                       if earlier["status"] == "returned")
        if row["logs"]:
            fields.add("logs")
        child, parent = account(row["committedAccounts"], "child"), account(row["committedAccounts"], "parent")
        if row["status"] == "returned" and int(case["transactions"][index]["input"]) & 1 and child != account(prior, "child"):
            fields.add("committedAccounts")
        if int(child["balance"]) != slot(child, "1") or int(parent["balance"]) + int(child["balance"]) != ENDOWMENT + accepted:
            fields.add("committedAccounts")
    return sorted(fields)


def rolled_back(tx, row, prior):
    """Whether a completed row keeps the whole storage its outcome requires: a
    root revert keeps both contracts, a child revert (odd input) under a
    returned root keeps the child."""
    if row["status"] == "reverted":
        return row["accountStorage"] == prior
    child = ROLES.index("child")
    return not int(tx["input"]) & 1 or row["accountStorage"][child] == prior[child]


def compare(histories, case, bindings):
    if returns(case):
        return return_compare(histories, case, bindings)
    if set(histories) != set(PATHS):
        return {"category": "adapter-error", "stage": "comparison", "detail": "three histories required", "pairs": {}}
    try:
        validate_bindings(bindings)
        values = {path: normalize_history(histories[path], case, bindings) for path in PATHS}
    except (ValueError, KeyError, TypeError) as error:
        return {"category": "adapter-error", "stage": "comparison", "detail": str(error), "pairs": {}}
    initial = {path: values[path]["initialAccounts"] for path in PATHS}
    whole = {path: values[path]["initialAccountStorage"] for path in PATHS}
    pairs = storage.pairwise(initial)
    changed = not all(pairs.values()) or any(state != initial_accounts(bindings, forwarding(case)) for state in initial.values())
    # Both empty constructors leave the whole storage of both contracts empty.
    differences = storage.account_storage_differences(whole, SLOTS, deployment=True)
    if changed or differences:
        mismatch = {"category": "semantic-mismatch", "stage": "initial-accounts",
                    "fields": (["committedAccounts"] if changed else []) + (["accountStorage"] if differences else []),
                    "pairs": storage.pairwise({path: [initial[path], whole[path]] for path in PATHS})}
        if differences:
            mismatch["accountStorageDifferences"] = differences
        return mismatch
    for index, tx in enumerate(case["transactions"]):
        where = {"stage": "transaction", "index": index, "transactionId": tx["id"]}
        rows = {path: values[path]["transactions"][index] for path in PATHS if index < len(values[path]["transactions"])}
        if len(rows) != 3 or any(row["status"] in storage.RESOURCE_STATUSES for row in rows.values()):
            return {"category": "inconclusive-resource", **where, "pairs": {}}
        if any(row["status"] not in ("returned", "reverted") for row in rows.values()):
            return {"category": "execution-error", **where, "pairs": {}}
        pairs = storage.pairwise(rows)
        fields = [key for key in ("status", "output", "committedAccounts", "logs") if len({json.dumps(row[key], sort_keys=True) for row in rows.values()}) != 1]
        normal = all(row["status"] == expected_status(tx) and len(common.hex_bytes(row["output"], "output")) == 32 and
            all(len(log["topics"]) == 1 and len(common.hex_bytes(log["data"], "log data")) == 32 and log["address"] in (bindings["parent"], bindings["child"]) for log in row["logs"]) for row in rows.values())
        for path, row in rows.items():
            prior = values[path]["transactions"][index - 1]["committedAccounts"] if index else initial[path]
            if row["status"] == "reverted":
                for field, correct in (("committedAccounts", row["committedAccounts"] == prior), ("logs", row["logs"] == [])):
                    if not correct and field not in fields:
                        fields.append(field)
        if forwarding(case):
            fields += [field for field in forwarding_fields(case, rows, values, index) if field not in fields]
        # The whole storage agrees across paths; a root revert keeps both prior
        # contracts' whole storage and a child revert under a returned root the child's.
        differences = storage.account_storage_differences({path: row["accountStorage"] for path, row in rows.items()}, SLOTS)
        rolled = sorted(path for path, row in rows.items() if not rolled_back(tx, row,
            values[path]["transactions"][index - 1]["accountStorage"] if index else values[path]["initialAccountStorage"]))
        if (differences or rolled) and "accountStorage" not in fields:
            fields.append("accountStorage")
        if not all(pairs.values()) or not normal or fields:
            mismatch = {"category": "semantic-mismatch", **where, "pairs": pairs, "fields": fields or ["status", "output", "logs"]}
            if differences:
                mismatch["accountStorageDifferences"] = differences
            if rolled:
                mismatch["accountStorageRollbackPaths"] = rolled
            return mismatch
    return {"category": "matched", "stage": "completed-history", "pairs": storage.pairwise(values)}


def evm_accounts(rpc, bindings, block):
    storage.quantity(block, "account snapshot block")
    result = []
    for role in ROLES:
        target = "0x" + f"{int(bindings[role]):040x}"
        balance = storage.quantity(rpc.call("eth_getBalance", [target, block]), "contract balance")
        result.append({"role": role, "address": bindings[role], "balance": common.word(str(balance)),
                       "storage": storage.evm_storage(rpc, target, block)})
    return result


def evm_logs(receipt):
    events = receipt.get("logs")
    if not isinstance(events, list):
        raise ValueError("mined receipt has no committed logs")
    result = []
    for event in events:
        if not isinstance(event, dict) or not re.fullmatch(r"0x[0-9a-fA-F]{40}", event.get("address", "")) or not isinstance(event.get("topics"), list):
            raise ValueError("invalid mined log")
        if event.get("removed", False) is not False or event.get("transactionHash", "").lower() != receipt["transactionHash"].lower() or event.get("blockNumber") != receipt["blockNumber"]:
            raise ValueError("mined log is not from the selected transaction block")
        topics = [common.hex_bytes(topic, "topic") for topic in event["topics"]]
        if any(len(topic) != 32 for topic in topics):
            raise ValueError("mined log topic is not a Word")
        result.append({"address": str(int(event["address"], 16)), "topics": [str(int.from_bytes(topic, "big")) for topic in topics], "data": event["data"]})
    return logs(result)


def trace_result(mined, trace):
    # A caught child resource failure is not an ordinary handled child revert.
    for step in trace.get("structLogs", []) if isinstance(trace, dict) else []:
        detail = str(step.get("error", "")) if isinstance(step, dict) else ""
        if common.RESOURCE.search(detail):
            return {"status": "out-of-gas" if common.GAS_RESOURCE.search(detail) else "resource-limit", "detail": detail}
    return storage.trace_result(mined, trace)


def resolve_backend(case, explicit, saved_report=None):
    """Only the call-return profile, whose two sources the Yul exporter admits, runs on Yul."""
    if returns(case):
        return common.resolve_backend(explicit, saved_report)
    return common.resolve_sonatina_backend(explicit, saved_report)


def verify_archive(directory, report):
    if not isinstance(report, dict) or report.get("schema") != REPORT_SCHEMA:
        raise ValueError("unsupported call archive schema")
    if common.resolve_backend(None, report) == "yul" and report.get("scope") == PROFILES["stateful-call-returns"]["scope"]:
        return return_verify_yul_archive(directory, report)
    common.resolve_sonatina_backend(None, report)
    common.verify_archive(directory, {**report, "schema": common.REPORT_SCHEMA})


def hull_history(stdout, exit_code, case, bindings, runtimes):
    if returns(case):
        return return_hull_history(stdout, exit_code, case, bindings, runtimes)
    rows = [json.loads(line) for line in stdout.splitlines() if line.strip()]
    if exit_code not in (0, 1) or not rows or any(not isinstance(row, dict) for row in rows):
        raise ValueError("invalid linked call process result")
    if rows[-1].get("stage") == "preparation":
        detail = str(rows[-1].get("detail", "preparation rejected"))
        raise Finding("inconclusive-resource" if common.RESOURCE.search(detail) else "compilation-rejected", "core-preparation", detail)
    for index, stage in enumerate(("deployment-child", "deployment-parent")):
        row = rows[index] if index < len(rows) else {}
        if row.get("stage") != stage or row.get("status") != "returned":
            raise Finding("inconclusive-resource" if row.get("status") == "out-of-fuel" else "execution-error", "core-" + stage, json.dumps(row))
        role = "child" if index == 0 else "parent"
        if row.get("imageVerified") is not True or type(row.get("codeBytes")) is not int or row["codeBytes"] != len(runtimes[role]):
            raise ValueError("Hull constructor has no verified runtime image receipt")
        if common.hex_bytes(row.get("output"), "Hull deployed code") != runtimes[role]:
            raise ValueError("Hull constructor output differs from the linked runtime image")
    if len(rows) < 3 or rows[2].get("stage") != "initialization":
        raise ValueError("missing initialized Hull account world")
    initial = accounts(rows[2].get("committedAccounts"), bindings)
    initial_whole = rows[2].get("accountStorage")
    calls = rows[3:]
    if any(row.get("stage") != "execution" for row in calls):
        raise ValueError("unexpected linked call output stage")
    complete = len(calls) == len(case["transactions"]) and all(row.get("status") in ("returned", "reverted") for row in calls)
    if complete and exit_code:
        raise ValueError("unexplained Hull failure after complete call history")
    history = {"schema": profile(case)["historySchema"], "initialAccounts": initial, "transactions": calls,
        "finalAccounts": calls[-1].get("committedAccounts") if calls else initial,
        "initialAccountStorage": initial_whole, "finalAccountStorage": calls[-1].get("accountStorage") if calls else initial_whole,
        "status": "complete" if complete else "incomplete", "unexecuted": [tx["id"] for tx in case["transactions"][len(calls):]]}
    normalize_history(history, case, bindings)
    return history


def execute(args, report):
    previous = None
    if args.replay:
        previous = common.read_json(args.replay / "report.json", args.artifact_limit)
        verify_archive(args.replay, previous)
    case = common.read_json(args.replay / "case.json" if args.replay else args.case)
    validate_case(case)
    args.backend = resolve_backend(case, getattr(args, "backend", None), previous)
    report["backend"] = args.backend
    runner = common.Runner(args, report)
    selected = profile(case)
    if selected.get("returns"):
        return execute_returns(args, report, previous, runner, case)
    case_path, source = args.output / "case.json", args.output / "case.sol"
    save(case_path, case)
    source.write_text(case["source"])
    report.update(caseSha256=common.file_digest(case_path), sourceSha256=common.file_digest(source),
        programsSha256=common.digest(common.json_bytes(case["programs"])), provenance=case["provenance"],
        replayOf=str(args.replay) if args.replay else None)
    report["tools"] = {"caseTool": runner.identity(args.case_tool), "coreRunner": runner.identity(args.core_runner),
        "anvil": runner.identity(args.anvil, version=True), "runnerSha256": common.file_digest(Path(__file__)),
        "sharedRunnerSha256": common.file_digest(ROOT / "scripts/semantic-differential.py"),
        "storageTransportSha256": common.file_digest(ROOT / "scripts/semantic-storage-differential.py"),
        "leanToolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "python": {"path": sys.executable, "version": sys.version},
        "exporters": {name: common.file_digest(ROOT / "scripts" / name) for name in
            ("export-rust-hull.py", "export-rust-code-image.py", "rust-hull-export.rs", "rust-code-image-export.rs")}}
    if previous:
        for key in ("runnerSha256", "sharedRunnerSha256", "storageTransportSha256", "exporters", "leanToolchain"):
            if report["tools"][key] != previous.get("tools", {}).get(key):
                raise Finding("adapter-error", "replay", f"saved tool identity changed: {key}")
        for key in ("caseTool", "coreRunner", "anvil"):
            if report["tools"][key]["sha256"] != previous.get("tools", {}).get(key, {}).get("sha256"):
                raise Finding("adapter-error", "replay", f"saved executable changed: {key}")
    revision = runner.process("repository-revision", ["git", "rev-parse", "HEAD"], 10)
    diff = runner.process("repository-diff", ["git", "diff", "--binary", "HEAD"], 10)
    if revision["returncode"] or diff["returncode"]:
        raise ValueError("cannot identify repository state")
    report["repository"] = {"revision": revision["stdout"].strip(), "trackedDiffSha256": common.digest(diff["stdout"].encode())}
    refreshed = common.checked_process(runner, "direct-core-replay", [str(args.case_tool), "replay", str(case_path), str(args.direct_fuel)])
    fresh = json.loads(refreshed["stdout"])
    for key in ("programs", "source", "provenance", "contracts", "transactions", selected["planKey"], "initialState", "observedSlots"):
        if fresh.get(key) != case.get(key):
            raise ValueError(f"native call replay changed {key}")
    save(args.output / "replayed-case.json", fresh)
    hull, images_path = args.output / "hull.json", args.output / "images.json"
    export_args = [str(source), "--root", str(args.output), "--upstream", str(args.upstream), "--target-dir", str(args.target_dir)]
    common.checked_process(runner, "rust-checked-source", [sys.executable, str(ROOT / "scripts/export-rust-hull.py"), *export_args, "--output", str(hull)])
    common.checked_process(runner, "rust-code-images", [sys.executable, str(ROOT / "scripts/export-rust-code-image.py"), *export_args,
        "--optimization", common.optimization_for_backend(args.backend),
        "--output", str(images_path), "--hull-output", str(hull), "--timeout", str(args.timeout)], args.timeout * 3)
    report["exportProvenance"] = common.validate_export(hull, images_path, source, args.artifact_limit, backend=args.backend)
    if previous and "exportProvenance" in previous:
        old, new = previous["exportProvenance"], report["exportProvenance"]
        if old["images"].get("toolBuild") != new["images"].get("toolBuild") or old["hull"].get("binarySha256") != new["hull"].get("binarySha256") or old["hull"].get("patches") != new["hull"].get("patches"):
            raise Finding("adapter-error", "replay", "Rust compiler/exporter build changed")
        libraries = lambda data: {key: value for key, value in data["hull"].get("sources", {}).items() if not key.endswith("/case.sol")}
        if libraries(old) != libraries(new):
            raise Finding("adapter-error", "replay", "imported library hashes changed")
    images = common.read_json(images_path, args.artifact_limit)
    runtimes = {role: common.image_bytes(images, case["contracts"][role]["runtimePath"]) for role in ROLES}
    with common.anvil(runner, args.anvil, steps_tracing=True) as rpc:
        senders = rpc.call("eth_accounts", [])
        if not senders or not re.fullmatch(r"0x[0-9a-fA-F]{40}", senders[0]):
            raise ValueError("local Anvil supplied no valid sender")
        sender, gas = senders[0], hex(args.gas)
        bindings = {"schema": BINDINGS_SCHEMA, "caller": str(int(sender, 16))}
        report["evmDeployments"] = {}
        initial_block = None
        # Every slot a prestate diff reports for either contract from its creation on.
        touched = {}
        for role in ("child", "parent"):
            contract = case["contracts"][role]
            init = common.image_bytes(images, contract["deployPath"])
            record = report["evmDeployments"][role] = {}
            tx_hash = storage.submit(rpc, {"from": sender, "data": "0x" + init.hex(), "value": hex(int(contract["constructorValue"])), "gas": gas}, record)
            deployed = storage.receipt(rpc, tx_hash, runner)
            record["receipt"] = deployed
            if deployed["status"] != "0x1":
                trace = rpc.call("debug_traceTransaction", [tx_hash, {"disableStorage": True, "disableStack": True, "enableMemory": False}])
                record["trace"] = trace
                outcome = trace_result(deployed, trace)
                raise Finding("inconclusive-resource" if outcome["status"] in storage.RESOURCE_STATUSES else "execution-error", "evm-deployment-" + role, json.dumps(outcome))
            target = deployed.get("contractAddress")
            if not isinstance(target, str) or not re.fullmatch(r"0x[0-9a-fA-F]{40}", target):
                raise ValueError("invalid deployed contract address")
            if common.hex_bytes(rpc.call("eth_getCode", [target, deployed["blockNumber"]]), "deployed runtime") != runtimes[role]:
                raise Finding("adapter-error", "evm-deployment-" + role, "installed runtime differs from exported image")
            if evm_logs(deployed):
                raise Finding("semantic-mismatch", "evm-deployment-" + role, "fixed empty constructor emitted logs")
            diff = rpc.call("debug_traceTransaction", [tx_hash, storage.PRESTATE_DIFF])
            record["storageDiff"] = diff
            created = [target] + [f"0x{int(bindings[known]):040x}" for known in ROLES if known in bindings]
            for account, slots in storage.changed_storage(diff, created).items():
                touched.setdefault(account, set()).update(slots)
            bindings[role] = str(int(target, 16))
            initial_block = deployed["blockNumber"]
        validate_bindings(bindings)
        if previous and previous.get("bindings") != bindings:
            raise Finding("adapter-error", "replay", "fresh deployment changed retained account bindings")
        report["bindings"] = bindings
        binding_path = args.output / "bindings.json"
        save(binding_path, bindings)
        observed = common.checked_process(runner, "direct-core-observe", [str(args.case_tool), "observe", str(case_path), str(binding_path), str(args.direct_fuel)])
        direct = json.loads(observed["stdout"])
        if direct.get("bindings") != bindings or direct.get("fuelPerTransaction") != args.direct_fuel:
            raise ValueError("original Core changed account bindings or fuel")
        normalize_history(direct, case, bindings)
        save(args.output / "direct-history.json", direct)
        report["histories"]["directCore"] = direct
        scenario = {"schema": selected["scenarioSchema"], "hull": str(hull), "images": str(images_path),
            "bindings": bindings, "initialBalances": {"parent": endowment(selected["forwarding"]), "child": "0"}, "observedSlots": list(SLOTS),
            "fuel": args.core_fuel, "availableGas": str(args.gas),
            **{role + field[0].upper() + field[1:]: case["contracts"][role][field] for role in ROLES for field in ("deployPath", "runtimePath")},
            "calls": [{"id": tx["id"], "input": tx["input"], "calldata": calldata(bindings, tx), "value": "0", "persist": True} for tx in case["transactions"]]}
        if selected["forwarding"]:
            scenario["callerFunds"] = str(CALLER_FUNDS)
            scenario["calls"] = [{"id": tx["id"], "input": tx["input"], "amount": tx["amount"], "calldata": calldata(bindings, tx),
                                  "value": tx["value"], "persist": True} for tx in case["transactions"]]
        scenario_path = args.output / "scenario.json"
        save(scenario_path, scenario)
        imported = runner.process("imported-hull", [str(args.core_runner), str(scenario_path)])
        report["histories"]["importedHull"] = hull_history(imported["stdout"], imported["returncode"], case, bindings, runtimes)
        initial = evm_accounts(rpc, bindings, initial_block)
        observed_accounts = [(role, bindings[role]) for role in ROLES]
        initial_whole = storage.evm_account_storage(rpc, observed_accounts, touched, initial_block)
        report["initialBlock"] = initial_block
        evm_rows, records = [], []
        report["evmTransactions"] = records
        def checkpoint(pending=None):
            complete = len(evm_rows) == len(case["transactions"]) and all(row["status"] in ("returned", "reverted") for row in evm_rows)
            remaining = [tx["id"] for tx in case["transactions"][len(evm_rows):]]
            report["histories"]["rustEvm"] = {"schema": selected["historySchema"], "initialAccounts": initial,
                "transactions": list(evm_rows), "finalAccounts": None if pending else evm_rows[-1]["committedAccounts"] if evm_rows else initial,
                "initialAccountStorage": initial_whole,
                "finalAccountStorage": None if pending else evm_rows[-1]["accountStorage"] if evm_rows else initial_whole,
                "status": "complete" if complete else "incomplete", "unobserved": [pending] if pending else [],
                "unexecuted": remaining[1:] if pending else remaining}
        checkpoint()
        for index, tx in enumerate(case["transactions"]):
            record = {"id": tx["id"], "index": index}
            records.append(record)
            checkpoint(tx["id"])
            try:
                tx_hash = storage.submit(rpc, {"from": sender, "to": "0x" + f"{int(bindings['parent']):040x}",
                    "data": calldata(bindings, tx), "value": hex(int(tx["value"])), "gas": gas}, record)
            except BaseException:
                if record.get("submission") == "rejected":
                    checkpoint()
                raise
            mined = storage.receipt(rpc, tx_hash, runner)
            record["receipt"] = mined
            trace = rpc.call("debug_traceTransaction", [tx_hash, {"disableStorage": True, "disableStack": True, "enableMemory": False}])
            record["trace"] = trace
            outcome = trace_result(mined, trace)
            state = evm_accounts(rpc, bindings, mined["blockNumber"])
            committed_logs = evm_logs(mined) if outcome["status"] in ("returned", "reverted") else None
            diff = rpc.call("debug_traceTransaction", [tx_hash, storage.PRESTATE_DIFF])
            record["storageDiff"] = diff
            for account, slots in storage.changed_storage(diff, [f"0x{int(address):040x}" for _, address in observed_accounts]).items():
                touched.setdefault(account, set()).update(slots)
            whole = storage.evm_account_storage(rpc, observed_accounts, touched, mined["blockNumber"])
            evm_rows.append({"id": tx["id"], "index": index, **outcome, "committedAccounts": state, "logs": committed_logs,
                             "accountStorage": whole})
            checkpoint()
            if outcome["status"] not in ("returned", "reverted"):
                break
    report["comparison"] = compare(report["histories"], case, bindings)


# --- stateful-call-returns: a parent that decodes a child method's return data ---

RETURN_K = 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95
RETURN_PARENT_SLOTS = tuple(str(slot) for slot in range(7))
RETURN_CHILD_SLOTS = ("0", "1")
RETURN_TRUNCATED = "0x08638556"
RETURN_EMPTY = "0x"
RETURN_FIELDS = {"": 0, "uint256": 32, "uint256,uint256": 64, "bytes": 32}
RETURN_PATTERNS = ("zeros", "ones", "ramp")
RETURN_KINDS = ("tuple", "bytes", "static-enum", "dynamic-enum")
RETURN_MALFORMATIONS = ("truncate", "trailing", "offset", "length", "tag", "tagCut", "tail", "narrow")
RETURN_PROGRAMS = ("parentCall", "parentResume", "child")
WORD_MODULUS = 2**256


def returns(case):
    return profile(case).get("returns", False)


def return_contract_metadata():
    parent, child = "SynthesizedReturnCaller", "SynthesizedReturnCallee"
    return {
        "parent": {"name": parent, "method": "run", "signature": "run(uint256,uint256)", "selector": SELECTOR,
            "deployPath": [parent + "Deploy"], "runtimePath": [parent + "Deploy", parent],
            "constructorCalldata": "0x", "constructorValue": "0"},
        "child": {"name": child, "method": "get", "signature": "get(uint256)", "selector": "0x9507d39a",
            "deployPath": [child + "Deploy"], "runtimePath": [child + "Deploy", child],
            "constructorCalldata": "0x", "constructorValue": "0"}}


def return_words(*values):
    return b"".join((value % WORD_MODULUS).to_bytes(32, "big") for value in values)


def return_pad(data):
    return data + bytes(-len(data) % 32)


def return_word_at(data, offset):
    return int.from_bytes((data[offset:offset + 32] + bytes(32))[:32], "big")


def return_tag(name, fields):
    return int.from_bytes(storage.keccak256(f"{name}({fields})".encode()), "big")


def return_shape(plan):
    """The returned kind, the tuple's arity, the enum's constructors and the
    chosen constructor."""
    kind = plan["kind"]
    constructors = [(entry["name"], entry["fields"]) for entry in plan.get("constructors", [])]
    chosen = constructors[plan["choice"]] if kind.endswith("enum") else None
    return kind, plan.get("arity"), constructors, chosen


def return_body_head(constructors):
    return 32 + max(RETURN_FIELDS[fields] for _, fields in constructors)


def return_values(r, c, x, o):
    return {"r": r, "c": c, "x": x, "o": o, "d0": r * RETURN_K % WORD_MODULUS,
            "d1": (c * RETURN_K % WORD_MODULUS) ^ x}


def return_canonical(plan, values):
    """std's encoding of the child's value: the tuple's Words, `bytes` after
    its offset, or an enum's body inline or after the offset 32."""
    kind, arity, constructors, chosen = return_shape(plan)
    length = plan["length"]
    payload = (return_words(values["d0"], values["d1"]))[:length]
    if kind == "tuple":
        return return_words(values["r"], values["c"], values["x"], values["o"])[:32 * arity]
    if kind == "bytes":
        return return_words(32, length) + return_pad(payload)
    head = return_body_head(constructors)
    name, fields = chosen
    heads = {"": b"", "uint256": return_words(values["d0"]), "uint256,uint256": return_words(values["d0"], values["d1"]),
             "bytes": return_words(head)}
    tail = return_words(length) + return_pad(payload) if fields == "bytes" else b""
    body = return_words(return_tag(name, fields)) + heads[fields] + bytes(head - 32 - RETURN_FIELDS[fields]) + tail
    return body if kind == "static-enum" else return_words(32) + body


def return_bytes(plan, values):
    """The child's return data: the canonical encoding, or raw with its
    malformation."""
    data = return_canonical(plan, values)
    delivery = plan["delivery"]
    if delivery["kind"] == "typed":
        return data
    malformation = delivery["malformation"]
    kind, _, constructors, chosen = return_shape(plan)
    replace = lambda position, value: data[:position] + return_words(int(value)) + data[position + 32:]
    tag_position = 32 if kind == "dynamic-enum" else 0
    match malformation["kind"]:
        case "truncate":
            return data[:malformation["kept"]]
        case "trailing":
            pattern = RETURN_PATTERNS.index(malformation["pattern"])
            byte = (lambda index: 0) if pattern == 0 else (lambda index: 0xff) if pattern == 1 else (lambda index: (index + 1) % 256)
            return data + bytes(byte(index) for index in range(malformation["count"]))
        case "offset":
            return replace(0, malformation["value"])
        case "length":
            return replace(32 + return_body_head(constructors) if kind == "dynamic-enum" else 32, malformation["value"])
        case "tag":
            return replace(tag_position, malformation["value"])
        case "tagCut":
            return replace(tag_position, malformation["value"])[:tag_position + 32]
        case "tail":
            return replace(64, malformation["value"])
        case "narrow":
            return data[:32 + RETURN_FIELDS[chosen[1]]]
    raise ValueError("unsupported call-return malformation")


def return_bytes_at(data, base, head):
    """A `bytes` value whose tail offset lies at `base + head`: its length and
    two zero-padded chunks, or none past the end."""
    size = len(data)
    if base > size or size - base < head + 32:
        return None
    tail = return_word_at(data, base + head)
    if tail > size - base or size - (base + tail) < 32:
        return None
    length = return_word_at(data, base + tail)
    if length > size - (base + tail + 32):
        return None
    payload = return_pad(data[base + tail + 32:base + tail + 32 + length]) + bytes(64)
    return [length, int.from_bytes(payload[:32], "big") if length > 0 else 0,
            int.from_bytes(payload[32:64], "big") if length > 32 else 0]


def return_decide(plan, data):
    """std's decision as `MemoryWordReader` takes `raw_call`'s copy: the record
    `[index, w0, w1, w2, w3]`, or the revert data of a rejection."""
    kind, arity, constructors, _ = return_shape(plan)
    size = len(data)
    if kind == "tuple":
        if size < 32 * arity:
            return RETURN_TRUNCATED
        return [0] + [return_word_at(data, 32 * index) if index < arity else 0 for index in range(4)]
    if kind == "bytes":
        found = return_bytes_at(data, 0, 0)
        return RETURN_TRUNCATED if found is None else [0] + found + [0]
    start = 0
    if kind == "dynamic-enum":
        if size < 32:
            return RETURN_TRUNCATED
        start = return_word_at(data, 0)
        if start > size:
            return RETURN_TRUNCATED
    if size - start < 32:
        return RETURN_TRUNCATED
    tag = return_word_at(data, start)
    for index, (name, fields) in enumerate(constructors, start=1):
        if return_tag(name, fields) == tag:
            if fields == "":
                return [index, 0, 0, 0, 0]
            if fields == "uint256":
                return RETURN_TRUNCATED if size - start < 64 else [index, return_word_at(data, start + 32), 0, 0, 0]
            if fields == "uint256,uint256":
                return RETURN_TRUNCATED if size - start < 96 else \
                    [index, return_word_at(data, start + 32), return_word_at(data, start + 64), 0, 0]
            found = return_bytes_at(data, start, 32)
            return RETURN_TRUNCATED if found is None else [index] + found + [0]
    return RETURN_EMPTY


def return_prescribed(plan, tx):
    """std's prescribed rejection of a transaction: none when the child
    reverts or std accepts. No Word of the child's value decides it, so any
    values give it."""
    if int(tx["input"]) & 1:
        return None
    decision = return_decide(plan, return_bytes(plan, return_values(3, 5, int(tx["input"]), 13)))
    return decision if isinstance(decision, str) else None


def validate_return_case(case):
    plan = case.get("callReturnPlan")
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.call-return-plan.v1" or \
            not isinstance(plan.get("stepProgram"), dict) or plan.get("kind") not in RETURN_KINDS:
        raise ValueError("call-return case requires its checked plan")
    kind = plan["kind"]
    if kind == "tuple" and plan.get("arity") not in (2, 3, 4) or kind.endswith("enum") and (
            not isinstance(plan.get("constructors"), list) or not 2 <= len(plan["constructors"]) <= 4 or
            any(not isinstance(entry, dict) or set(entry) != {"name", "fields"} or entry["fields"] not in RETURN_FIELDS
                for entry in plan["constructors"])):
        raise ValueError("call-return plan has an invalid shape")
    if type(plan.get("length")) is not int or not 0 <= plan["length"] <= 64 or type(plan.get("choice")) is not int or \
            (kind.endswith("enum") and not 0 <= plan["choice"] < len(plan["constructors"])):
        raise ValueError("call-return plan has an invalid length or choice")
    delivery = plan.get("delivery")
    if not isinstance(delivery, dict) or delivery.get("kind") not in ("typed", "raw") or \
            (delivery["kind"] == "raw" and (not isinstance(delivery.get("malformation"), dict) or
                                            delivery["malformation"].get("kind") not in RETURN_MALFORMATIONS)):
        raise ValueError("call-return plan has an invalid delivery")
    programs = case.get("programs")
    if not isinstance(programs, dict) or set(programs) != set(RETURN_PROGRAMS) or \
            any(not isinstance(programs[role], dict) for role in RETURN_PROGRAMS):
        raise ValueError("call-return case requires its three original Core programs")
    sources = case.get("sources")
    if not isinstance(sources, dict) or set(sources) != set(ROLES) or any(not isinstance(sources[role], str) for role in ROLES):
        raise ValueError("call-return case requires one source per contract")
    if case.get("contracts") != return_contract_metadata():
        raise ValueError("call-return contract metadata changed")
    initial = {"accounts": [{"role": role, "balance": "0", "storage": []} for role in ROLES], "callerBalance": "0"}
    if case.get("initialState") != initial or case.get("observedSlots") != \
            {"parent": list(RETURN_PARENT_SLOTS), "child": list(RETURN_CHILD_SLOTS)}:
        raise Finding("unsupported-scope", "input", "call-return profile requires unfunded empty accounts and its observed slots")
    provenance = case.get("provenance")
    if not isinstance(provenance, dict) or any(not isinstance(provenance.get(key), str) or not provenance[key]
            for key in ("generatorVersion", "emitterVersion", "wrapperVersion")):
        raise ValueError("missing versioned call-return provenance")
    transactions = case.get("transactions")
    if not isinstance(transactions, list) or not 1 <= len(transactions) <= MAX_TRANSACTIONS:
        raise ValueError(f"call-return case requires 1 to {MAX_TRANSACTIONS} transactions")
    ids = set()
    for tx in transactions:
        if not isinstance(tx, dict) or set(tx) != {"id", "input", "value", "target", "callee", "stdRejection"}:
            raise ValueError("call-return transactions retain symbolic roles and their prescribed rejection")
        if not isinstance(tx["id"], str) or not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", tx["id"]) or tx["id"] in ids:
            raise ValueError("transaction IDs must be unique bounded identifiers")
        ids.add(tx["id"])
        common.word(tx["input"], "transaction input")
        if (tx["target"], tx["callee"], tx["value"]) != ("parent", "child", "0"):
            raise Finding("unsupported-scope", "input", "call-return transactions must use the fixed roles and zero value")
        if tx["stdRejection"] != return_prescribed(plan, tx):
            raise ValueError("a prescribed rejection differs from the adapter's own decision")


def return_initial_accounts(bindings):
    return [{"role": role, "address": bindings[role], "balance": "0",
             "storage": [{"slot": slot, "value": "0"} for slot in slots]}
            for role, slots in (("parent", RETURN_PARENT_SLOTS), ("child", RETURN_CHILD_SLOTS))]


def return_accounts(rows, bindings):
    if not isinstance(rows, list) or len(rows) != 2:
        raise ValueError("both committed contract accounts are required")
    result = []
    for (role, slots), row in zip((("parent", RETURN_PARENT_SLOTS), ("child", RETURN_CHILD_SLOTS)), rows):
        if not isinstance(row, dict) or row.get("role") != role or row.get("address") != bindings[role]:
            raise ValueError("committed account identity changed")
        result.append({"role": role, "address": address(row["address"]),
            "balance": common.word(row.get("balance"), "committed balance"), "storage": storage.storage(row.get("storage"), slots)})
    return result


def return_normalize_history(history, case, bindings):
    if not isinstance(history, dict) or history.get("schema") != RETURN_HISTORY_SCHEMA:
        raise ValueError("unsupported call-return history")
    initial = return_accounts(history.get("initialAccounts"), bindings)
    initial_whole = whole_storage(history.get("initialAccountStorage"), bindings, "initial account storage")
    rows = history.get("transactions")
    if not isinstance(rows, list) or len(rows) > len(case["transactions"]):
        raise ValueError("invalid call-return history length")
    result = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict) or row.get("id") != case["transactions"][index]["id"] or type(row.get("index")) is not int or row["index"] != index:
            raise ValueError("transaction identity or order changed")
        status = row.get("status")
        if not isinstance(status, str):
            raise ValueError("missing call-return status")
        normalized = {"id": row["id"], "index": index, "status": status,
                      "committedAccounts": return_accounts(row.get("committedAccounts"), bindings),
                      "accountStorage": whole_storage(row.get("accountStorage"), bindings)}
        if status in ("returned", "reverted"):
            normalized.update(output="0x" + common.hex_bytes(row.get("output"), "call output").hex(), logs=logs(row.get("logs")))
        else:
            if index != len(rows) - 1:
                raise ValueError("execution continued after an incomplete call")
            normalized.update(detail=row.get("detail", ""), logs=None)
        result.append(normalized)
    complete = len(rows) == len(case["transactions"]) and all(row["status"] in ("returned", "reverted") for row in result)
    if history.get("status") != ("complete" if complete else "incomplete"):
        raise ValueError("call-return history completion flag disagrees with its rows")
    remaining = [tx["id"] for tx in case["transactions"][len(rows):]]
    unobserved = history.get("unobserved", [])
    if unobserved not in ([], remaining[:1]) or unobserved and (complete or any(row["status"] not in ("returned", "reverted") for row in result)):
        raise ValueError("invalid unknown transaction completion")
    if history.get("unexecuted") != remaining[len(unobserved):]:
        raise ValueError("unexecuted transaction identities changed")
    final = None if unobserved else return_accounts(history.get("finalAccounts"), bindings)
    if unobserved and history.get("finalAccounts") is not None:
        raise ValueError("unknown completion cannot claim a final committed world")
    if not unobserved and final != (result[-1]["committedAccounts"] if result else initial):
        raise ValueError("final accounts differ from the last committed snapshot")
    final_whole = None if unobserved else whole_storage(history.get("finalAccountStorage"), bindings, "final account storage")
    if unobserved and history.get("finalAccountStorage") is not None:
        raise ValueError("unknown completion cannot claim a final whole storage")
    if not unobserved and final_whole != (result[-1]["accountStorage"] if result else initial_whole):
        raise ValueError("final whole storage differs from the last committed observation")
    return {"initialAccounts": initial, "initialAccountStorage": initial_whole, "transactions": result, "finalAccounts": final,
        "finalAccountStorage": final_whole, "status": history["status"], "unexecuted": history["unexecuted"], "unobserved": unobserved}


def return_expected_status(tx):
    return "reverted" if tx["stdRejection"] is not None or int(tx["input"]) & 2 else "returned"


def return_comparable(tx, rows):
    """Original Core's revert Word stands for std's revert data exactly when
    the transaction's prescribed rejection is that rejection: the selector
    rule for `0x08638556`, the empty-revert rule for `0x`. Hull and the EVM
    are never changed."""
    rejection, core = tx["stdRejection"], rows.get("directCore")
    if rejection is None or not isinstance(core, dict) or core.get("status") != "reverted":
        return rows
    word = int(rejection, 16).to_bytes(32, "big").hex() if rejection != RETURN_EMPTY else bytes(32).hex()
    if core.get("output") != "0x" + word:
        return rows
    return {name: {**row, "output": rejection} if name == "directCore" else row for name, row in rows.items()}


def return_slots(account):
    return [int(entry["value"]) for entry in account["storage"]]


def return_protocol_fields(case, tx, row, prior):
    """Fields that break the protocol, against the adapter's own decoding of
    the child's bytes rebuilt from its committed slots and the input."""
    plan = case["callReturnPlan"]
    parent, child = (return_slots(account) for account in row["committedAccounts"])
    before_parent, before_child = (return_slots(account) for account in prior)
    x = int(tx["input"])
    fields = []
    output = int.from_bytes(common.hex_bytes(row["output"], "output"), "big") if row["status"] == "returned" else None
    if row["status"] == "reverted":
        if row["committedAccounts"] != prior:
            fields.append("committedAccounts")
        return fields
    if tx["stdRejection"] is not None or x & 2:
        return ["status"]
    if x & 1:
        # A child revert under a returned parent keeps the child and records
        # its 32-byte revert Word.
        expected = [(before_parent[0] + x) % WORD_MODULUS, 64, 0, parent[3], 0, 0, 0]
        if child != before_child:
            fields.append("committedAccounts")
    else:
        if child[1] != (before_child[1] + 1) % WORD_MODULUS:
            fields.append("committedAccounts")
        data = return_bytes(plan, return_values(child[0], child[1], x, before_child[0]))
        record = return_decide(plan, data)
        if isinstance(record, str):
            return ["status"]
        expected = [(before_parent[0] + x) % WORD_MODULUS, 1 + 2 * len(data)] + record
    if parent != expected:
        fields.append("committedAccounts")
    if output != sum(parent[:1] + parent[2:]) % WORD_MODULUS:
        fields.append("output")
    return fields


def return_compare(histories, case, bindings):
    if set(histories) != set(PATHS):
        return {"category": "adapter-error", "stage": "comparison", "detail": "three histories required", "pairs": {}}
    try:
        validate_bindings(bindings)
        values = {path: return_normalize_history(histories[path], case, bindings) for path in PATHS}
    except (ValueError, KeyError, TypeError) as error:
        return {"category": "adapter-error", "stage": "comparison", "detail": str(error), "pairs": {}}
    initial = {path: values[path]["initialAccounts"] for path in PATHS}
    whole = {path: values[path]["initialAccountStorage"] for path in PATHS}
    changed = any(state != return_initial_accounts(bindings) for state in initial.values())
    # Both empty constructors leave the whole storage of both contracts empty.
    differences = storage.account_storage_differences(whole, RETURN_PARENT_SLOTS, deployment=True)
    if changed or differences:
        mismatch = {"category": "semantic-mismatch", "stage": "initial-accounts",
                    "fields": (["committedAccounts"] if changed else []) + (["accountStorage"] if differences else []),
                    "pairs": storage.pairwise({path: [initial[path], whole[path]] for path in PATHS})}
        if differences:
            mismatch["accountStorageDifferences"] = differences
        return mismatch
    rules = []
    for index, tx in enumerate(case["transactions"]):
        where = {"stage": "transaction", "index": index, "transactionId": tx["id"]}
        rows = {path: values[path]["transactions"][index] for path in PATHS if index < len(values[path]["transactions"])}
        if len(rows) != 3 or any(row["status"] in storage.RESOURCE_STATUSES for row in rows.values()):
            return {"category": "inconclusive-resource", **where, "pairs": {}}
        if any(row["status"] not in ("returned", "reverted") for row in rows.values()):
            return {"category": "execution-error", **where, "pairs": {}}
        compared = return_comparable(tx, rows)
        if compared is not rows:
            rules.append(tx["id"])
        pairs = storage.pairwise(compared)
        fields = [key for key in ("status", "output", "committedAccounts", "logs") if len({json.dumps(row[key], sort_keys=True) for row in compared.values()}) != 1]
        for path, row in compared.items():
            prior = values[path]["transactions"][index - 1]["committedAccounts"] if index else initial[path]
            expected = return_expected_status(tx)
            output = common.hex_bytes(row["output"], "output")
            if row["status"] != expected or row["logs"] != [] or \
                    (tx["stdRejection"] is not None and row["output"] != tx["stdRejection"]) or \
                    (tx["stdRejection"] is None and len(output) != 32):
                if "status" not in fields:
                    fields.append("status")
            for field in return_protocol_fields(case, tx, row, prior):
                if field not in fields:
                    fields.append(field)
        differences = storage.account_storage_differences({path: row["accountStorage"] for path, row in rows.items()}, RETURN_PARENT_SLOTS)
        rolled = sorted(path for path, row in rows.items() if not return_rolled_back(tx, row,
            values[path]["transactions"][index - 1]["accountStorage"] if index else values[path]["initialAccountStorage"]))
        if (differences or rolled) and "accountStorage" not in fields:
            fields.append("accountStorage")
        if not all(pairs.values()) or fields:
            mismatch = {"category": "semantic-mismatch", **where, "pairs": pairs, "fields": fields}
            if differences:
                mismatch["accountStorageDifferences"] = differences
            if rolled:
                mismatch["accountStorageRollbackPaths"] = rolled
            return mismatch
    return {"category": "matched", "stage": "completed-history", "pairs": storage.pairwise(values), "selectorRows": rules}


def return_rolled_back(tx, row, prior):
    """A parent revert keeps both contracts' whole storage, and a child revert
    under a returned parent keeps the child's."""
    if row["status"] == "reverted":
        return row["accountStorage"] == prior
    child = ROLES.index("child")
    return not int(tx["input"]) & 1 or row["accountStorage"][child] == prior[child]


def return_evm_accounts(rpc, bindings, block):
    storage.quantity(block, "account snapshot block")
    result = []
    for role, slots in (("parent", RETURN_PARENT_SLOTS), ("child", RETURN_CHILD_SLOTS)):
        target = "0x" + f"{int(bindings[role]):040x}"
        balance = storage.quantity(rpc.call("eth_getBalance", [target, block]), "contract balance")
        result.append({"role": role, "address": bindings[role], "balance": common.word(str(balance)),
                       "storage": storage.evm_storage(rpc, target, block, slots)})
    return result


def return_hull_history(stdout, exit_code, case, bindings, runtimes):
    rows = [json.loads(line) for line in stdout.splitlines() if line.strip()]
    if exit_code not in (0, 1) or not rows or any(not isinstance(row, dict) for row in rows):
        raise ValueError("invalid linked call-return process result")
    if rows[-1].get("stage") == "preparation":
        detail = str(rows[-1].get("detail", "preparation rejected"))
        raise Finding("inconclusive-resource" if common.RESOURCE.search(detail) else "compilation-rejected", "core-preparation", detail)
    for index, stage in enumerate(("deployment-child", "deployment-parent")):
        row = rows[index] if index < len(rows) else {}
        if row.get("stage") != stage or row.get("status") != "returned":
            raise Finding("inconclusive-resource" if row.get("status") == "out-of-fuel" else "execution-error", "core-" + stage, json.dumps(row))
        role = "child" if index == 0 else "parent"
        if row.get("imageVerified") is not True or type(row.get("codeBytes")) is not int or row["codeBytes"] != len(runtimes[role]):
            raise ValueError("Hull constructor has no verified runtime image receipt")
        if common.hex_bytes(row.get("output"), "Hull deployed code") != runtimes[role]:
            raise ValueError("Hull constructor output differs from the linked runtime image")
    if len(rows) < 3 or rows[2].get("stage") != "initialization":
        raise ValueError("missing initialized Hull account world")
    initial = return_accounts(rows[2].get("committedAccounts"), bindings)
    initial_whole = rows[2].get("accountStorage")
    calls = rows[3:]
    if any(row.get("stage") != "execution" for row in calls):
        raise ValueError("unexpected linked call-return output stage")
    complete = len(calls) == len(case["transactions"]) and all(row.get("status") in ("returned", "reverted") for row in calls)
    if complete and exit_code:
        raise ValueError("unexplained Hull failure after complete call-return history")
    history = {"schema": RETURN_HISTORY_SCHEMA, "initialAccounts": initial, "transactions": calls,
        "finalAccounts": calls[-1].get("committedAccounts") if calls else initial,
        "initialAccountStorage": initial_whole, "finalAccountStorage": calls[-1].get("accountStorage") if calls else initial_whole,
        "status": "complete" if complete else "incomplete", "unexecuted": [tx["id"] for tx in case["transactions"][len(calls):]]}
    return_normalize_history(history, case, bindings)
    return history


def return_used_evm(report):
    """Whether a call-return run reached the EVM, which deploys only after both exports."""
    return "evmDeployments" in report or common.yul_transport("used_yul_execution", report)


def return_yul_export(args, runner, case, role, source, report, previous):
    """One contract's Yul EVM bytes, exported beside its main checked Hull under
    its role's prefix and bound to that Hull and the reported tools."""
    contract, prefix = case["contracts"][role]["name"], role + "-"
    hull_path = args.output / (prefix + "hull.json")
    expected = report["exportProvenance"][role]["hull"]
    if common.read_json(hull_path.with_suffix(".json.provenance.json"), args.artifact_limit) != expected or \
            expected.get("sources", {}).get(source.as_uri()) != common.file_digest(source):
        raise ValueError("main Hull receipt or entry source changed before Yul export")
    runner.guard()
    command = [sys.executable, str(ROOT / "scripts/export-rust-yul.py"), str(source), "--output", str(args.output / (prefix + "yul.json")),
        "--contract", contract, "--solc", str(args.solc), "--root", str(args.output), "--upstream", str(args.upstream),
        "--target-dir", str(args.target_dir), "--timeout", str(args.timeout), "--output-limit", str(min(args.artifact_limit, 64 * 1024**2))]
    common.checked_process(runner, "rust-yul-evm-" + role, command, args.timeout * 3)
    runner.guard()
    record = common.yul_transport("validate_export", args.output, contract, expected, args.artifact_limit, prefix)
    common.yul_transport("validate_tool_record", record, report["tools"])
    if record["exporterSha256"] != common.file_digest(ROOT / "scripts/export-rust-yul.py") or \
            report["tools"]["yulTransportSha256"] != common.file_digest(ROOT / "scripts/semantic-yul.py"):
        raise ValueError("Yul tools changed during export")
    report["yulExportProvenance"][role] = record
    old = (previous or {}).get("yulExportProvenance")
    old = old.get(role) if isinstance(old, dict) else None
    if previous is not None and old is None and return_used_evm(previous):
        raise Finding("adapter-error", "replay", "saved Yul execution is missing provenance")
    if old is not None:
        if not isinstance(old, dict) or not isinstance(old.get("compiler"), dict):
            raise ValueError("malformed saved Yul compiler provenance")
        for key in ("backend", "exporterSha256", "toolBuild", "outputSha256"):
            if old.get(key) != record[key]:
                raise Finding("adapter-error", "replay", "Yul " + key + " changed since the saved run")
        if old["compiler"].get("sha256") != record["compiler"]["sha256"] or \
                str(old["compiler"].get("versionOutput", "")).strip() != record["compiler"]["versionOutput"].strip():
            raise Finding("adapter-error", "replay", "solc binary or full version changed since the saved run")
    artifact = common.read_json(args.output / (prefix + "yul.json"), args.artifact_limit)
    return common.hex_bytes(artifact["initCode"], "Yul init code"), common.hex_bytes(artifact["runtimeCode"], "Yul runtime code")


def return_verify_yul_archive(directory, report):
    """A Yul call-return archive: its inventory as the shared check reads it, then
    each contract's accepted export under its role's prefix."""
    limit = 64 * 1024 * 1024
    if report.get("pathBackends") != common.path_backends("yul"):
        raise ValueError("Yul archive relabelled an execution path")
    artifacts = report.get("artifacts")
    if not isinstance(artifacts, dict) or "case.json" not in artifacts or artifacts["case.json"] != report.get("caseSha256"):
        raise ValueError("saved artifact inventory is missing its case")
    for name, expected in artifacts.items():
        if not isinstance(name, str) or name in {"", ".", "..", "report.json"} or Path(name).name != name or \
                not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError(f"invalid saved artifact entry: {name}")
        path = directory / name
        if path.is_symlink() or not path.is_file() or common.file_digest(path) != expected:
            raise ValueError(f"saved artifact is missing or changed: {name}")
    case = common.read_json(directory / "case.json", limit)
    validate_case(case)
    if not returns(case):
        raise ValueError("only a call-return archive runs on Yul")
    saved = report.get("yulExportProvenance")
    if not isinstance(saved, dict) or not set(saved) <= set(ROLES):
        raise ValueError("malformed saved Yul export provenance")
    if set(saved) != set(ROLES) and return_used_evm(report):
        raise ValueError("Yul execution archive is missing an accepted export")
    for role, record in saved.items():
        prefix = role + "-"
        for name in common.yul_transport("evidence", prefix):
            if artifacts.get(name) != common.file_digest(directory / name):
                raise ValueError("archive omits or changes Yul evidence: " + name)
        hull = report.get("exportProvenance", {}).get(role, {}).get("hull")
        if common.yul_transport("validate_export", directory, case["contracts"][role]["name"], hull, limit, prefix) != record:
            raise ValueError("saved Yul provenance differs from its sidecar")
        common.yul_transport("validate_tool_record", record, report.get("tools"))


def execute_returns(args, report, previous, runner, case):
    """The call-return profile: each contract compiles from its own source on
    every path, the Hull runner links both, and the EVM paths deploy the
    child, then the parent, with zero value. On Yul the EVM deploys each
    source's own solc compilation and imported Hull keeps Sonatina O0 images."""
    selected = profile(case)
    yul, linked = args.backend == "yul", common.image_backend(args.backend)
    if yul:
        report["pathBackends"] = common.path_backends(args.backend)
    case_path = args.output / "case.json"
    save(case_path, case)
    sources = {role: args.output / f"{role}.sol" for role in ROLES}
    for role in ROLES:
        sources[role].write_text(case["sources"][role])
    report.update(caseSha256=common.file_digest(case_path),
        sourceSha256={role: common.file_digest(sources[role]) for role in ROLES},
        programsSha256=common.digest(common.json_bytes(case["programs"])), provenance=case["provenance"],
        replayOf=str(args.replay) if args.replay else None)
    report["tools"] = {"caseTool": runner.identity(args.case_tool), "coreRunner": runner.identity(args.core_runner),
        "anvil": runner.identity(args.anvil, version=True), "runnerSha256": common.file_digest(Path(__file__)),
        "sharedRunnerSha256": common.file_digest(ROOT / "scripts/semantic-differential.py"),
        "storageTransportSha256": common.file_digest(ROOT / "scripts/semantic-storage-differential.py"),
        "leanToolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "python": {"path": sys.executable, "version": sys.version},
        "exporters": {name: common.file_digest(ROOT / "scripts" / name) for name in
            ("export-rust-hull.py", "export-rust-code-image.py", "rust-hull-export.rs", "rust-code-image-export.rs")}}
    if yul:
        report["tools"].update(solc=runner.identity(args.solc, version=True),
            yulExporterSha256=common.file_digest(ROOT / "scripts/export-rust-yul.py"),
            yulTransportSha256=common.file_digest(ROOT / "scripts/semantic-yul.py"))
    if previous:
        transport = ("yulExporterSha256", "yulTransportSha256") if yul else ()
        for key in ("runnerSha256", "sharedRunnerSha256", "storageTransportSha256", "exporters", "leanToolchain", *transport):
            if report["tools"][key] != previous.get("tools", {}).get(key):
                raise Finding("adapter-error", "replay", f"saved tool identity changed: {key}")
        for key in ("caseTool", "coreRunner", "anvil"):
            if report["tools"][key]["sha256"] != previous.get("tools", {}).get(key, {}).get("sha256"):
                raise Finding("adapter-error", "replay", f"saved executable changed: {key}")
        for key in ("sha256", "version") if yul else ():
            if report["tools"]["solc"][key] != previous.get("tools", {}).get("solc", {}).get(key):
                raise Finding("adapter-error", "replay", f"saved executable changed: solc {key}")
    revision = runner.process("repository-revision", ["git", "rev-parse", "HEAD"], 10)
    diff = runner.process("repository-diff", ["git", "diff", "--binary", "HEAD"], 10)
    if revision["returncode"] or diff["returncode"]:
        raise ValueError("cannot identify repository state")
    report["repository"] = {"revision": revision["stdout"].strip(), "trackedDiffSha256": common.digest(diff["stdout"].encode())}
    refreshed = common.checked_process(runner, "direct-core-replay", [str(args.case_tool), "replay", str(case_path), str(args.direct_fuel)])
    fresh = json.loads(refreshed["stdout"])
    for key in ("programs", "sources", "provenance", "contracts", "transactions", selected["planKey"], "initialState", "observedSlots"):
        if fresh.get(key) != case.get(key):
            raise ValueError(f"native call-return replay changed {key}")
    save(args.output / "replayed-case.json", fresh)
    hulls = {role: args.output / f"{role}-hull.json" for role in ROLES}
    image_paths = {role: args.output / f"{role}-images.json" for role in ROLES}
    report["exportProvenance"] = {}
    for role in ROLES:
        export_args = [str(sources[role]), "--root", str(args.output), "--upstream", str(args.upstream), "--target-dir", str(args.target_dir)]
        common.checked_process(runner, f"rust-checked-source-{role}", [sys.executable, str(ROOT / "scripts/export-rust-hull.py"), *export_args,
            "--output", str(hulls[role])])
        common.checked_process(runner, f"rust-code-images-{role}", [sys.executable, str(ROOT / "scripts/export-rust-code-image.py"), *export_args,
            "--optimization", common.optimization_for_backend(linked),
            "--output", str(image_paths[role]), "--hull-output", str(hulls[role]), "--timeout", str(args.timeout)], args.timeout * 3)
        report["exportProvenance"][role] = common.validate_export(hulls[role], image_paths[role], sources[role], args.artifact_limit,
                                                                  backend=linked)
    if previous and "exportProvenance" in previous:
        for role in ROLES:
            old, new = previous["exportProvenance"].get(role, {}), report["exportProvenance"][role]
            if old.get("images", {}).get("toolBuild") != new["images"].get("toolBuild") or \
                    old.get("hull", {}).get("binarySha256") != new["hull"].get("binarySha256") or \
                    old.get("hull", {}).get("patches") != new["hull"].get("patches"):
                raise Finding("adapter-error", "replay", "Rust compiler/exporter build changed")
            libraries = lambda data: {key: value for key, value in data["hull"].get("sources", {}).items() if not key.endswith(f"/{role}.sol")}
            if libraries(old) != libraries(new):
                raise Finding("adapter-error", "replay", "imported library hashes changed")
    images = {role: common.read_json(image_paths[role], args.artifact_limit) for role in ROLES}
    runtimes = {role: common.image_bytes(images[role], case["contracts"][role]["runtimePath"]) for role in ROLES}
    # The EVM deploys each image's init code, or on Yul each source's solc bytes.
    codes = {role: (common.image_bytes(images[role], case["contracts"][role]["deployPath"]), runtimes[role]) for role in ROLES}
    if yul:
        report["yulExportProvenance"] = {}
        codes = {role: return_yul_export(args, runner, case, role, sources[role], report, previous) for role in ("child", "parent")}
    with common.anvil(runner, args.anvil, steps_tracing=True) as rpc:
        senders = rpc.call("eth_accounts", [])
        if not senders or not re.fullmatch(r"0x[0-9a-fA-F]{40}", senders[0]):
            raise ValueError("local Anvil supplied no valid sender")
        sender, gas = senders[0], hex(args.gas)
        bindings = {"schema": BINDINGS_SCHEMA, "caller": str(int(sender, 16))}
        report["evmDeployments"] = {}
        initial_block = None
        touched = {}
        for role in ("child", "parent"):
            init, runtime = codes[role]
            record = report["evmDeployments"][role] = {}
            tx_hash = storage.submit(rpc, {"from": sender, "data": "0x" + init.hex(), "value": "0x0", "gas": gas}, record)
            deployed = storage.receipt(rpc, tx_hash, runner)
            record["receipt"] = deployed
            if deployed["status"] != "0x1":
                trace = rpc.call("debug_traceTransaction", [tx_hash, {"disableStorage": True, "disableStack": True, "enableMemory": False}])
                record["trace"] = trace
                outcome = trace_result(deployed, trace)
                raise Finding("inconclusive-resource" if outcome["status"] in storage.RESOURCE_STATUSES else "execution-error", "evm-deployment-" + role, json.dumps(outcome))
            target = deployed.get("contractAddress")
            if not isinstance(target, str) or not re.fullmatch(r"0x[0-9a-fA-F]{40}", target):
                raise ValueError("invalid deployed contract address")
            if common.hex_bytes(rpc.call("eth_getCode", [target, deployed["blockNumber"]]), "deployed runtime") != runtime:
                raise Finding("adapter-error", "evm-deployment-" + role, "installed runtime differs from " +
                              ("the exported Yul runtime bytes" if yul else "exported image"))
            if evm_logs(deployed):
                raise Finding("semantic-mismatch", "evm-deployment-" + role, "fixed empty constructor emitted logs")
            diff = rpc.call("debug_traceTransaction", [tx_hash, storage.PRESTATE_DIFF])
            record["storageDiff"] = diff
            created = [target] + [f"0x{int(bindings[known]):040x}" for known in ROLES if known in bindings]
            for account, slots in storage.changed_storage(diff, created).items():
                touched.setdefault(account, set()).update(slots)
            bindings[role] = str(int(target, 16))
            initial_block = deployed["blockNumber"]
        validate_bindings(bindings)
        if previous and previous.get("bindings") != bindings:
            raise Finding("adapter-error", "replay", "fresh deployment changed retained account bindings")
        report["bindings"] = bindings
        binding_path = args.output / "bindings.json"
        save(binding_path, bindings)
        observed = common.checked_process(runner, "direct-core-observe", [str(args.case_tool), "observe", str(case_path), str(binding_path), str(args.direct_fuel)])
        direct = json.loads(observed["stdout"])
        if direct.get("bindings") != bindings or direct.get("fuelPerTransaction") != args.direct_fuel:
            raise ValueError("original Core changed account bindings or fuel")
        return_normalize_history(direct, case, bindings)
        save(args.output / "direct-history.json", direct)
        report["histories"]["directCore"] = direct
        scenario = {"schema": selected["scenarioSchema"],
            "parentHull": str(hulls["parent"]), "parentImages": str(image_paths["parent"]),
            "childHull": str(hulls["child"]), "childImages": str(image_paths["child"]),
            "bindings": bindings, "initialBalances": {"parent": "0", "child": "0"},
            "observedSlots": {"parent": list(RETURN_PARENT_SLOTS), "child": list(RETURN_CHILD_SLOTS)},
            "fuel": args.core_fuel, "availableGas": str(args.gas),
            **{role + field[0].upper() + field[1:]: case["contracts"][role][field] for role in ROLES for field in ("deployPath", "runtimePath")},
            "calls": [{"id": tx["id"], "input": tx["input"], "calldata": calldata(bindings, tx), "value": "0", "persist": True}
                      for tx in case["transactions"]]}
        scenario_path = args.output / "scenario.json"
        save(scenario_path, scenario)
        imported = runner.process("imported-hull", [str(args.core_runner), str(scenario_path)])
        report["histories"]["importedHull"] = return_hull_history(imported["stdout"], imported["returncode"], case, bindings, runtimes)
        initial = return_evm_accounts(rpc, bindings, initial_block)
        observed_accounts = [(role, bindings[role]) for role in ROLES]
        initial_whole = storage.evm_account_storage(rpc, observed_accounts, touched, initial_block)
        report["initialBlock"] = initial_block
        evm_rows, records = [], []
        report["evmTransactions"] = records
        def checkpoint(pending=None):
            complete = len(evm_rows) == len(case["transactions"]) and all(row["status"] in ("returned", "reverted") for row in evm_rows)
            remaining = [tx["id"] for tx in case["transactions"][len(evm_rows):]]
            report["histories"]["rustEvm"] = {"schema": RETURN_HISTORY_SCHEMA, "initialAccounts": initial,
                "transactions": list(evm_rows), "finalAccounts": None if pending else evm_rows[-1]["committedAccounts"] if evm_rows else initial,
                "initialAccountStorage": initial_whole,
                "finalAccountStorage": None if pending else evm_rows[-1]["accountStorage"] if evm_rows else initial_whole,
                "status": "complete" if complete else "incomplete", "unobserved": [pending] if pending else [],
                "unexecuted": remaining[1:] if pending else remaining}
        checkpoint()
        for index, tx in enumerate(case["transactions"]):
            record = {"id": tx["id"], "index": index}
            records.append(record)
            checkpoint(tx["id"])
            try:
                tx_hash = storage.submit(rpc, {"from": sender, "to": "0x" + f"{int(bindings['parent']):040x}",
                    "data": calldata(bindings, tx), "value": "0x0", "gas": gas}, record)
            except BaseException:
                if record.get("submission") == "rejected":
                    checkpoint()
                raise
            mined = storage.receipt(rpc, tx_hash, runner)
            record["receipt"] = mined
            trace = rpc.call("debug_traceTransaction", [tx_hash, {"disableStorage": True, "disableStack": True, "enableMemory": False}])
            record["trace"] = trace
            outcome = trace_result(mined, trace)
            state = return_evm_accounts(rpc, bindings, mined["blockNumber"])
            committed_logs = evm_logs(mined) if outcome["status"] in ("returned", "reverted") else None
            diff = rpc.call("debug_traceTransaction", [tx_hash, storage.PRESTATE_DIFF])
            record["storageDiff"] = diff
            for account, slots in storage.changed_storage(diff, [f"0x{int(address):040x}" for _, address in observed_accounts]).items():
                touched.setdefault(account, set()).update(slots)
            whole = storage.evm_account_storage(rpc, observed_accounts, touched, mined["blockNumber"])
            evm_rows.append({"id": tx["id"], "index": index, **outcome, "committedAccounts": state, "logs": committed_logs,
                             "accountStorage": whole})
            checkpoint()
            if outcome["status"] not in ("returned", "reverted"):
                break
    report["comparison"] = compare(report["histories"], case, bindings)


def interrupted_comparison(args, report, failure):
    if set(report.get("histories", {})) == set(PATHS) and "bindings" in report:
        try:
            prefix = compare(report["histories"], common.read_json(args.output / "case.json"), report["bindings"])
            if prefix["category"] == "semantic-mismatch":
                return {**prefix, "laterInterruption": failure}
        except (OSError, ValueError, KeyError, TypeError, Finding):
            pass
    return failure


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument("--case", type=Path)
    choice.add_argument("--replay", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--backend", choices=common.BACKENDS,
        help="default sonatina-o0; yul, for stateful-call-returns only, runs the EVM path on the pinned solc's Yul output; "
             "exact replay inherits its saved backend")
    parser.add_argument("--solc", type=Path, default=Path(shutil.which("solc") or "solc"), help="pinned solc, used only for --backend yul")
    parser.add_argument("--case-tool", type=Path, help="default: the profile's native case tool")
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
        case = common.read_json(args.replay / "case.json" if args.replay else args.case)
        selected = profile(case)
        validate_case(case)
        args.case_tool = args.case_tool or ROOT / ".lake/build/bin" / selected["caseTool"]
        args.core_runner = args.core_runner or ROOT / ".lake/build/bin" / selected["coreRunner"]
        saved_report = common.read_json(args.replay / "report.json", defaults["artifact_limit"]) if args.replay else None
        if args.replay and not isinstance(saved_report, dict):
            raise ValueError("saved report must be an object")
        args.backend = resolve_backend(case, args.backend, saved_report)
        saved = saved_report.get("budgets", {}) if saved_report is not None else {}
        if not isinstance(saved, dict):
            raise ValueError("saved budgets must be an object")
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
            parser.error("exact replay retains saved budgets; use --case for changed budgets")
        setattr(args, key, value)
    for key in ("case", "replay", "output", "case_tool", "core_runner", "anvil", "upstream", "target_dir", "solc"):
        if getattr(args, key) is not None:
            setattr(args, key, getattr(args, key).resolve())
    args.output.mkdir(parents=True, exist_ok=False)
    report = {"schema": REPORT_SCHEMA, "backend": args.backend, "processes": [], "histories": {}, "budgets": {key: getattr(args, key) for key in defaults},
        "scope": selected["scope"]}
    previous = signal.getsignal(signal.SIGTERM)
    def interrupted(_signal, _frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    try:
        execute(args, report)
    except KeyboardInterrupt:
        report["comparison"] = interrupted_comparison(args, report, {"category": "inconclusive-resource", "stage": "runner", "detail": "interrupted", "pairs": {}})
    except Finding as error:
        report["comparison"] = interrupted_comparison(args, report, {"category": error.category, "stage": error.stage, "detail": error.detail, "pairs": {}})
    except (ValueError, OSError, KeyError, TypeError, RpcError, subprocess.SubprocessError) as error:
        report["comparison"] = interrupted_comparison(args, report, {"category": "adapter-error", "stage": "runner", "detail": str(error), "pairs": {}})
    finally:
        try:
            report["artifacts"] = {path.name: common.file_digest(path) for path in args.output.iterdir() if path.is_file()}
            save(args.output / "report.json", report)
        finally:
            signal.signal(signal.SIGTERM, previous)
    print(json.dumps({"category": report["comparison"]["category"], "report": str(args.output / "report.json")}))
    return 0 if report["comparison"]["category"] == "matched" else 1


if __name__ == "__main__":
    raise SystemExit(main())
