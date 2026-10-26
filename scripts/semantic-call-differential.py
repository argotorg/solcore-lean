#!/usr/bin/env python3
"""Compare bounded parent/child calls, committed accounts and logs on three paths.

Two profiles share this adapter: `stateful-calls` (zero-value transactions and
a fixed eight-unit parent) and `stateful-forwarded-value` (payable transactions
whose parent forwards bank amounts to the child). The original checked Core
contracts execute through the public nested runtime.
Rust supplies independently compiled Hull and linked EVM images. Every EVM
observation belongs to an actual mined transaction; no Python transition model
or saved expected output supplies the reference result.
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
PATHS, SLOTS = storage.PATHS, storage.SLOTS
CASE_SCHEMA = "solcore-lean.semantic-call-case.v1"
REPORT_SCHEMA = "solcore-lean.semantic-call-differential.v1"
HISTORY_SCHEMA = "solcore-lean.call-history.v1"
BINDINGS_SCHEMA = "solcore-lean.call-bindings.v1"
SELECTOR = "0x7357f5d2"
ROLES = ("parent", "child")
FORWARD_CASE_SCHEMA = "solcore-lean.semantic-forward-case.v1"
FORWARD_HISTORY_SCHEMA = "solcore-lean.forward-history.v1"
FORWARD_SELECTOR = "0x24b912e5"
# The forwarding parent's endowment covers three forwards of the largest bank
# value; original Core and Hull fund the caller with 2^80.
ENDOWMENT, CALLER_FUNDS, MAX_VALUE = 2**72, 2**80, 2**70
PROFILES = {
    "stateful-calls": {"caseSchema": CASE_SCHEMA, "historySchema": HISTORY_SCHEMA, "planKey": "callPlan",
        "planSchema": "solcore-lean.call-plan.v1", "caseTool": "semantic-call-tool", "coreRunner": "rust-hull-call-scenario",
        "scenarioSchema": "solcore-lean.call-contract-scenario.v1", "forwarding": False,
        "scope": "depth-one fixed Word calls; funded parent8/child0; both accounts' slots0/1, balances, root outcome and ordered committed logs; no gas/nonce equivalence"},
    "stateful-forwarded-value": {"caseSchema": FORWARD_CASE_SCHEMA, "historySchema": FORWARD_HISTORY_SCHEMA, "planKey": "forwardPlan",
        "planSchema": "solcore-lean.forward-plan.v1", "caseTool": "semantic-forward-tool", "coreRunner": "rust-hull-forward-scenario",
        "scenarioSchema": "solcore-lean.forward-contract-scenario.v1", "forwarding": True,
        "scope": "depth-one Word calls forwarding bank amounts; payable root values; parent endowment 2^72/child0; both accounts' slots0/1, balances, root outcome and empty logs; no sender-balance, gas or nonce equivalence"},
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
    if not isinstance(transactions, list) or not 1 <= len(transactions) <= 3:
        raise ValueError("call case requires one to three transactions")
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


def normalize_history(history, case, bindings):
    if not isinstance(history, dict) or history.get("schema") != profile(case)["historySchema"]:
        raise ValueError("unsupported call history")
    initial = accounts(history.get("initialAccounts"), bindings)
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
                      "committedAccounts": accounts(row.get("committedAccounts"), bindings)}
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
    return {"initialAccounts": initial, "transactions": result, "finalAccounts": final,
        "status": history["status"], "unexecuted": history["unexecuted"], "unobserved": unobserved}


def expected_status(tx):
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


def compare(histories, case, bindings):
    if set(histories) != set(PATHS):
        return {"category": "adapter-error", "stage": "comparison", "detail": "three histories required", "pairs": {}}
    try:
        validate_bindings(bindings)
        values = {path: normalize_history(histories[path], case, bindings) for path in PATHS}
    except (ValueError, KeyError, TypeError) as error:
        return {"category": "adapter-error", "stage": "comparison", "detail": str(error), "pairs": {}}
    initial = {path: values[path]["initialAccounts"] for path in PATHS}
    pairs = storage.pairwise(initial)
    if not all(pairs.values()) or any(state != initial_accounts(bindings, forwarding(case)) for state in initial.values()):
        return {"category": "semantic-mismatch", "stage": "initial-accounts", "fields": ["committedAccounts"], "pairs": pairs}
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
        if not all(pairs.values()) or not normal or fields:
            return {"category": "semantic-mismatch", **where, "pairs": pairs, "fields": fields or ["status", "output", "logs"]}
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


def verify_archive(directory, report):
    if not isinstance(report, dict) or report.get("schema") != REPORT_SCHEMA:
        raise ValueError("unsupported call archive schema")
    common.resolve_sonatina_backend(None, report)
    common.verify_archive(directory, {**report, "schema": common.REPORT_SCHEMA})


def hull_history(stdout, exit_code, case, bindings, runtimes):
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
    calls = rows[3:]
    if any(row.get("stage") != "execution" for row in calls):
        raise ValueError("unexpected linked call output stage")
    complete = len(calls) == len(case["transactions"]) and all(row.get("status") in ("returned", "reverted") for row in calls)
    if complete and exit_code:
        raise ValueError("unexplained Hull failure after complete call history")
    history = {"schema": profile(case)["historySchema"], "initialAccounts": initial, "transactions": calls,
        "finalAccounts": calls[-1].get("committedAccounts") if calls else initial,
        "status": "complete" if complete else "incomplete", "unexecuted": [tx["id"] for tx in case["transactions"][len(calls):]]}
    normalize_history(history, case, bindings)
    return history


def execute(args, report):
    previous = None
    if args.replay:
        previous = common.read_json(args.replay / "report.json", args.artifact_limit)
        verify_archive(args.replay, previous)
    args.backend = common.resolve_sonatina_backend(getattr(args, "backend", None), previous)
    report["backend"] = args.backend
    runner = common.Runner(args, report)
    case = common.read_json(args.replay / "case.json" if args.replay else args.case)
    validate_case(case)
    selected = profile(case)
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
        report["initialBlock"] = initial_block
        evm_rows, records = [], []
        report["evmTransactions"] = records
        def checkpoint(pending=None):
            complete = len(evm_rows) == len(case["transactions"]) and all(row["status"] in ("returned", "reverted") for row in evm_rows)
            remaining = [tx["id"] for tx in case["transactions"][len(evm_rows):]]
            report["histories"]["rustEvm"] = {"schema": selected["historySchema"], "initialAccounts": initial,
                "transactions": list(evm_rows), "finalAccounts": None if pending else evm_rows[-1]["committedAccounts"] if evm_rows else initial,
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
            evm_rows.append({"id": tx["id"], "index": index, **outcome, "committedAccounts": state, "logs": committed_logs})
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
    parser.add_argument("--backend", choices=common.SONATINA_BACKENDS,
        help="default sonatina-o0; exact replay inherits its saved backend")
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
        selected = profile(common.read_json(args.replay / "case.json" if args.replay else args.case))
        validate_case(common.read_json(args.replay / "case.json" if args.replay else args.case))
        args.case_tool = args.case_tool or ROOT / ".lake/build/bin" / selected["caseTool"]
        args.core_runner = args.core_runner or ROOT / ".lake/build/bin" / selected["coreRunner"]
        saved_report = common.read_json(args.replay / "report.json", defaults["artifact_limit"]) if args.replay else None
        if args.replay and not isinstance(saved_report, dict):
            raise ValueError("saved report must be an object")
        args.backend = common.resolve_sonatina_backend(args.backend, saved_report)
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
    for key in ("case", "replay", "output", "case_tool", "core_runner", "anvil", "upstream", "target_dir"):
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
