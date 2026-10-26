#!/usr/bin/env python3
"""Compare ordered transactions and committed slots on three real runtimes.

The original checked host Core contract is independent of Rust Hull. The EVM
path mines transactions and reads their actual trace output and receipt-block
storage. No Python state transition or saved expected value is an oracle.
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
PROFILES = {
    "stateful-storage": {"caseSchema": CASE_SCHEMA, "planSchema": "solcore-lean.storage-plan.v1",
        "corpusSchema": "solcore-lean.semantic-storage-corpus.v1", "originKind": "storage-generated",
        "contract": "SynthesizedStorage", "caseTool": "semantic-storage-tool", "rollback": False},
    "stateful-storage-rollback": {"caseSchema": ROLLBACK_CASE_SCHEMA,
        "planSchema": "solcore-lean.storage-rollback-plan.v1",
        "corpusSchema": "solcore-lean.semantic-storage-rollback-corpus.v1", "originKind": "storage-rollback-generated",
        "contract": "SynthesizedRollback", "caseTool": "semantic-storage-rollback-tool", "rollback": True},
}
REPORT_SCHEMA = "solcore-lean.semantic-storage-differential.v1"
HISTORY_SCHEMA = "solcore-lean.storage-history.v1"
PATHS = ("directCore", "importedHull", "rustEvm")
SLOTS = ("0", "1")
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


def expected_status(case: dict, transaction: dict) -> str:
    """The profile fixes completion polarity, not the returned value or world."""
    return "reverted" if profile(case)["rollback"] and int(common.word(transaction["input"])) % 2 else "returned"


def validate_case(case) -> None:
    selected = profile(case)
    plan = case.get("storagePlan")
    if not isinstance(plan, dict) or plan.get("schema") != selected["planSchema"] or not isinstance(plan.get("stepProgram"), dict):
        raise ValueError("storage case requires its original checked step plan")
    if not isinstance(case.get("program"), dict) or not isinstance(case.get("source"), str):
        raise ValueError("storage case requires its original host Core program and source")
    if case.get("initialState") != {"storage": []} or case.get("observedSlots") != list(SLOTS):
        raise Finding("unsupported-scope", "input", "storage profile starts empty and observes slots zero and one")
    contract = case.get("contract")
    name = selected["contract"]
    expected = {"name": name, "method": "run", "signature": "run(uint256)",
        "selector": "0xa444f5e9", "deployPath": [name + "Deploy"],
        "runtimePath": [name + "Deploy", name], "constructorCalldata": "0x"}
    if contract != expected:
        raise Finding("unsupported-scope", "input", "storage wrapper differs from the fixed profile")
    provenance = case.get("provenance")
    if not isinstance(provenance, dict) or any(not isinstance(provenance.get(key), str) or not provenance[key]
            for key in ("generatorVersion", "emitterVersion", "wrapperVersion")):
        raise ValueError("missing versioned storage provenance")
    transactions = case.get("transactions")
    if not isinstance(transactions, list) or not 1 <= len(transactions) <= 3:
        raise ValueError("storage case requires one to three ordered transactions")
    ids = set()
    for tx in transactions:
        if not isinstance(tx, dict) or not isinstance(tx.get("id"), str) or not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", tx["id"]) or tx["id"] in ids:
            raise ValueError("transaction IDs must be unique bounded identifiers")
        ids.add(tx["id"])
        value = int(common.word(tx.get("input"), "transaction input"))
        if tx.get("calldata") != "0xa444f5e9" + f"{value:064x}" or tx.get("value") != "0":
            raise ValueError("transaction calldata/value differs from its original Word input")


def storage(rows) -> list[dict]:
    if not isinstance(rows, list) or len(rows) != 2:
        raise ValueError("committed storage requires both observed slots")
    result = []
    for slot, row in zip(SLOTS, rows):
        if not isinstance(row, dict) or row.get("slot") != slot:
            raise ValueError("committed slots must be ordered, unique and complete")
        result.append({"slot": slot, "value": common.word(row.get("value"), "storage value")})
    return result


def normalize_history(history, case: dict) -> dict:
    if not isinstance(history, dict) or history.get("schema") != HISTORY_SCHEMA:
        raise ValueError("unsupported storage observation history")
    initial = storage(history.get("initialStorage"))
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
                 "committedStorage": storage(row.get("committedStorage"))}
        if status in {"returned", "reverted"}:
            value["output"] = "0x" + common.hex_bytes(row.get("output"), "transaction output").hex()
        else:
            value["detail"] = row.get("detail", "")
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
    final = None if unobserved else storage(history.get("finalStorage"))
    if unobserved and history.get("finalStorage") is not None:
        raise ValueError("an unobserved transaction cannot claim a final committed snapshot")
    if not unobserved and final != (result[-1]["committedStorage"] if result else initial):
        raise ValueError("final committed storage differs from the last observation")
    return {"initialStorage": initial, "transactions": result, "finalStorage": final,
            "status": history["status"], "unexecuted": history["unexecuted"], "unobserved": unobserved}


def pairwise(values: dict) -> dict:
    return {f"{a}/{b}": values[a] == values[b]
            for a, b in (("directCore", "rustEvm"), ("directCore", "importedHull"), ("importedHull", "rustEvm"))}


def compare(histories: dict, case: dict) -> dict:
    """Compare every completed prefix; a later budget failure cannot erase a difference."""
    if set(histories) != set(PATHS):
        return {"category": "adapter-error", "stage": "comparison", "detail": "three histories required", "pairs": {}}
    try:
        profile(case)
        values = {name: normalize_history(histories[name], case) for name in PATHS}
    except (ValueError, KeyError, TypeError) as error:
        return {"category": "adapter-error", "stage": "comparison", "detail": str(error), "pairs": {}}
    initial = {name: values[name]["initialStorage"] for name in PATHS}
    pairs = pairwise(initial)
    if not all(pairs.values()) or any(row["value"] != "0" for state in initial.values() for row in state):
        return {"category": "semantic-mismatch", "stage": "initial-storage", "pairs": pairs, "fields": ["committedStorage"]}
    for index, tx in enumerate(case["transactions"]):
        rows = {name: values[name]["transactions"][index] for name in PATHS if index < len(values[name]["transactions"])}
        where = {"stage": "transaction", "transactionId": tx["id"], "index": index}
        if len(rows) != 3:
            return {"category": "inconclusive-resource", **where, "detail": "transaction not observed on every path", "pairs": {}}
        if any(row["status"] in RESOURCE_STATUSES for row in rows.values()):
            return {"category": "inconclusive-resource", **where, "pairs": {}}
        if any(row["status"] not in {"returned", "reverted"} for row in rows.values()):
            return {"category": "execution-error", **where, "pairs": {}}
        pairs = pairwise(rows)
        fields = [key for key in ("status", "output", "committedStorage") if len({json.dumps(row[key], sort_keys=True) for row in rows.values()}) != 1]
        normal = all(row["status"] == expected_status(case, tx) and len(common.hex_bytes(row["output"], "output")) == 32 for row in rows.values())
        rollback = all(row["status"] != "reverted" or row["committedStorage"] ==
            (values[name]["transactions"][index - 1]["committedStorage"] if index else values[name]["initialStorage"])
            for name, row in rows.items())
        if not rollback and "committedStorage" not in fields:
            fields.append("committedStorage")
        if not all(pairs.values()) or not normal or not rollback:
            return {"category": "semantic-mismatch", **where, "pairs": pairs, "fields": fields or ["status", "output"]}
    return {"category": "matched", "stage": "completed-history", "pairs": pairwise(values)}


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
    history = {"schema": HISTORY_SCHEMA, "initialStorage": deployment.get("committedStorage"),
        "transactions": calls, "finalStorage": calls[-1].get("committedStorage") if calls else deployment.get("committedStorage"),
        "status": "complete" if complete else "incomplete", "unexecuted": [tx["id"] for tx in case["transactions"][len(calls):]]}
    normalize_history(history, case)
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


def evm_storage(rpc, address: str, block: str) -> list[dict]:
    quantity(block, "storage block")
    result = []
    for slot in SLOTS:
        raw = common.hex_bytes(rpc.call("eth_getStorageAt", [address, hex(int(slot)), block]), "storage bytes")
        if len(raw) != 32:
            raise ValueError("RPC storage value is not exactly one Word")
        result.append({"slot": slot, "value": str(int.from_bytes(raw, "big"))})
    return result


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
    common.resolve_sonatina_backend(None, report)
    common.verify_archive(path, {**report, "schema": common.REPORT_SCHEMA})


def execute(args, report: dict) -> None:
    previous = None
    if args.replay:
        previous = common.read_json(args.replay / "report.json", args.artifact_limit)
        verify_archive(args.replay, previous)
    args.backend = common.resolve_sonatina_backend(getattr(args, "backend", None), previous)
    report["backend"] = args.backend
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
    if previous:
        for key in ("runnerSha256", "sharedRunnerSha256", "exporters", "leanToolchain"):
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
    replay = common.checked_process(runner, "direct-core-replay", [str(args.case_tool), "replay", str(case_path), str(args.direct_fuel)])
    fresh = json.loads(replay["stdout"])
    for key in ("program", "source", "provenance", "contract", "transactions", "storagePlan", "initialState", "observedSlots"):
        if fresh.get(key) != case.get(key):
            raise ValueError(f"native storage replay changed {key}")
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
        libraries = lambda data: {k: v for k, v in data["hull"].get("sources", {}).items() if not k.endswith("/case.sol")}
        if libraries(old) != libraries(new):
            raise Finding("adapter-error", "replay", "imported library hashes changed")
    images = common.read_json(images_path, args.artifact_limit)
    init = common.image_bytes(images, case["contract"]["deployPath"])
    runtime = common.image_bytes(images, case["contract"]["runtimePath"])
    with common.anvil(runner, args.anvil, steps_tracing=True) as rpc:
        accounts = rpc.call("eth_accounts", [])
        if not accounts or not re.fullmatch(r"0x[0-9a-fA-F]{40}", accounts[0]):
            raise ValueError("local Anvil supplied no valid sender")
        sender, gas = accounts[0], hex(args.gas)
        report["evmDeployment"] = {}
        tx_hash = submit(rpc, {"from": sender, "data": "0x" + init.hex(), "value": "0x0", "gas": gas}, report["evmDeployment"])
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
            raise Finding("adapter-error", "evm-deployment", "installed runtime differs from exported code image")
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
        normalize_history(direct, case)
        save(args.output / "direct-history.json", direct)
        report["histories"]["directCore"] = direct
        base = {"caller": bindings["caller"], "address": bindings["address"], "value": "0", "availableGas": str(args.gas)}
        scenario = {"schema": "solcore-lean.storage-contract-scenario.v1", "hull": str(hull), "images": str(images_path),
            "deployPath": case["contract"]["deployPath"], "runtimePath": case["contract"]["runtimePath"], "fuel": args.core_fuel,
            "observedSlots": list(SLOTS), "constructor": {**base, "calldata": "0x"},
            "calls": [{"id": tx["id"], "context": {**base, "calldata": tx["calldata"]}, "persist": True} for tx in case["transactions"]]}
        scenario_path = args.output / "scenario.json"
        save(scenario_path, scenario)
        result = runner.process("imported-hull", [str(args.core_runner), str(scenario_path)])
        report["histories"]["importedHull"] = hull_history(result["stdout"], result["returncode"], case)
        initial = evm_storage(rpc, address, deployed["blockNumber"])
        evm_rows, records = [], []
        report["evmTransactions"] = records
        def checkpoint(pending=None):
            complete = len(evm_rows) == len(case["transactions"]) and all(row["status"] in {"returned", "reverted"} for row in evm_rows)
            remaining = [tx["id"] for tx in case["transactions"][len(evm_rows):]]
            report["histories"]["rustEvm"] = {"schema": HISTORY_SCHEMA, "initialStorage": initial,
                "transactions": list(evm_rows), "finalStorage": None if pending else evm_rows[-1]["committedStorage"] if evm_rows else initial,
                "status": "complete" if complete else "incomplete", "unobserved": [pending] if pending else [],
                "unexecuted": remaining[1:] if pending else remaining}
        checkpoint()
        for index, tx in enumerate(case["transactions"]):
            record = {"id": tx["id"], "index": index}
            records.append(record)
            checkpoint(tx["id"])
            try:
                tx_hash = submit(rpc, {"from": sender, "to": address, "data": tx["calldata"], "value": "0x0", "gas": gas}, record)
            except BaseException:
                if record.get("submission") == "rejected":
                    checkpoint()
                raise
            mined = receipt(rpc, tx_hash, runner)
            record["receipt"] = mined
            trace = rpc.call("debug_traceTransaction", [tx_hash, {"disableStorage": True, "disableStack": True, "enableMemory": False}])
            record["trace"] = trace
            outcome = trace_result(mined, trace)
            state = evm_storage(rpc, address, mined["blockNumber"])
            evm_rows.append({"id": tx["id"], "index": index, **outcome, "committedStorage": state})
            checkpoint()
            if outcome["status"] not in {"returned", "reverted"}:
                break
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
    parser.add_argument("--backend", choices=common.SONATINA_BACKENDS,
        help="default sonatina-o0; exact replay inherits its saved backend")
    parser.add_argument("--case-tool", type=Path)
    parser.add_argument("--core-runner", type=Path, default=ROOT / ".lake/build/bin/rust-hull-storage-scenario")
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
        args.backend = common.resolve_sonatina_backend(args.backend, saved_report)
        saved = saved_report.get("budgets", {}) if saved_report is not None else {}
        if not isinstance(saved, dict):
            raise ValueError("saved budgets must be an object")
        if args.case_tool is None:
            args.case_tool = ROOT / ".lake/build/bin" / profile(selected)["caseTool"]
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
    for key in ("case", "replay", "output", "case_tool", "core_runner", "anvil", "upstream", "target_dir"):
        if getattr(args, key) is not None:
            setattr(args, key, getattr(args, key).resolve())
    args.output.mkdir(parents=True, exist_ok=False)
    report = {"schema": REPORT_SCHEMA, "backend": args.backend, "processes": [], "histories": {}, "budgets": {key: getattr(args, key) for key in defaults},
        "scope": "ordered zero-value run(uint256) transactions; initially empty committed slots 0/1; no gas/balance/nonce equivalence"}
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
