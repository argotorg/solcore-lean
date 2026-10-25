#!/usr/bin/env python3
"""Compare committed nested-call histories across original Core, Rust and Hull.

Ten scenarios cover child and root rollback, retained value transfers, ordered
logs, Word boundaries and private aggregate steps. The oracle is freshly run
original Core, not a Python transition model or an archived expected result.
Temporary compiler exports and local chains are removed after the bounded run.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("source_storage_regression", ROOT / "scripts/test-source-storage-rust.py")
storage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(storage)
aggregate, shared = storage.aggregate, storage.shared
CASE_SCHEMA = "solcore-lean.semantic-call-case.v1"
PLAN_SCHEMA = "solcore-lean.call-plan.v1"
ROLES = ("parent", "child")


def transactions(inputs: list[int]) -> list[dict]:
    return [{"id": f"tx-{index}", "input": str(value), "value": "0", "target": "parent", "callee": "child"}
        for index, value in enumerate(inputs)]


def fixtures() -> list[tuple[str, dict, list[dict]]]:
    identity = aggregate.function_program([storage.variable(0)])
    inherited = {label: plan["stepProgram"] for label, plan, _ in storage.fixtures()}
    return [(label, {"schema": PLAN_SCHEMA, "stepProgram": program}, transactions(inputs))
        for label, program, inputs in (
            ("identity-modes-012", identity, [0, 1, 2]),
            ("identity-modes-345", identity, [3, 4, 5]),
            ("identity-modes-67", identity, [6, 7]),
            ("child-rollback-then-value", identity, [4, 5, 4]),
            ("root-rollback-then-read", identity, [4, 6, 0]),
            ("maximum-root-rollback", identity, [storage.MAX_WORD]),
            ("high-bit-wrap", identity, [1 << 255, 4]),
            ("fresh-cell-arbitrary-entry", inherited["fresh-cell-arbitrary-entry"], [4, 5, 4]),
            ("aggregate-branch-rollback", inherited["aggregate-branch-feedback"], [4, 6, 0]),
            ("constant-zero-child", inherited["constant-zero"], [4, 5, 0]))]


def native_case(plan: dict, txs: list[dict], directory: Path, args: argparse.Namespace) -> dict:
    plan_path, tx_path = directory / "plan.json", directory / "transactions.json"
    plan_path.write_text(json.dumps(plan))
    tx_path.write_text(json.dumps(txs))
    result = shared.run([str(args.case_tool), "emit", str(plan_path), str(tx_path), str(args.fuel)], args.timeout)
    if result.returncode:
        raise ValueError(f"native call case failed: {result.stdout}{result.stderr}")
    case = json.loads(result.stdout)
    initial = {"accounts": [{"role": role, "balance": "8" if role == "parent" else "0", "storage": []}
        for role in ROLES], "callerBalance": "0"}
    if (case.get("schema") != CASE_SCHEMA or case.get("callPlan") != plan or case.get("transactions") != txs
            or case.get("initialState") != initial or case.get("observedSlots") != ["0", "1"]
            or set(case.get("programs", {})) != set(ROLES) or "directCore" in case):
        raise ValueError("native call case changed its original plan, role transactions or initial accounts")
    return case


def canonical_word(value) -> str:
    if (not isinstance(value, str) or not value.isascii() or not value.isdecimal()
            or str(int(value)) != value or not 0 <= int(value) <= storage.MAX_WORD):
        raise ValueError("history contains an invalid canonical Word")
    return value


def normalized_accounts(rows: list[dict], bindings: dict) -> list[dict]:
    if not isinstance(rows, list) or len(rows) != 2:
        raise ValueError("both committed contract accounts are required")
    result = []
    for role, row in zip(ROLES, rows):
        if row.get("role") != role or row.get("address") != bindings[role]:
            raise ValueError("committed account identity changed")
        slots = row.get("storage")
        if not isinstance(slots, list) or [item.get("slot") for item in slots] != ["0", "1"]:
            raise ValueError("committed account must contain both observed storage slots")
        result.append({"role": role, "address": bindings[role], "balance": canonical_word(row.get("balance")),
            "storage": [{"slot": item["slot"], "value": canonical_word(item.get("value"))} for item in slots]})
    return result


def word_bytes(output) -> str:
    if not isinstance(output, str) or not output.startswith("0x") or len(output) != 66:
        raise ValueError("call payload must contain exactly one ABI Word")
    if len(bytes.fromhex(output[2:])) != 32:
        raise ValueError("call payload contains invalid hexadecimal data")
    return output.lower()


def normalized_history(history: dict, case: dict, bindings: dict) -> dict:
    if history.get("schema") != "solcore-lean.call-history.v1":
        raise ValueError("unexpected call history schema")
    initial = normalized_accounts(history.get("initialAccounts"), bindings)
    if ([row["balance"] for row in initial] != ["8", "0"]
            or any(row["storage"] != storage.ZERO_STORAGE for row in initial)):
        raise ValueError("call history must begin with funded parent8/child0 and empty storage")
    rows = history.get("transactions")
    if (not isinstance(rows, list) or len(rows) != len(case["transactions"])
            or history.get("status") != "complete" or history.get("unexecuted") != []
            or history.get("unobserved", []) != []):
        raise ValueError("call history is incomplete")
    result, prior = [], initial
    for index, (row, tx) in enumerate(zip(rows, case["transactions"])):
        mode = int(tx["input"]) & 7
        status = "reverted" if mode & 2 else "returned"
        if row.get("id") != tx["id"] or row.get("index") != index or row.get("status") != status:
            raise ValueError("call history changed transaction identity, order or prescribed root completion")
        accounts = normalized_accounts(row.get("committedAccounts"), bindings)
        entries = row.get("logs")
        if not isinstance(entries, list):
            raise ValueError("committed logs must be an ordered list")
        checked_logs = []
        for item in entries:
            if item.get("address") not in (bindings["parent"], bindings["child"]):
                raise ValueError("committed log has an unexpected emitter")
            topics = item.get("topics")
            if not isinstance(topics, list) or len(topics) != 1:
                raise ValueError("committed log requires its one Word topic")
            checked_logs.append({"address": item["address"], "topics": [canonical_word(topics[0])],
                "data": word_bytes(item.get("data"))})
        expected_pattern = [] if mode & 2 else [(bindings["parent"], "1")] + (
            [] if mode & 1 else [(bindings["child"], "2")]) + [(bindings["parent"], "3")]
        if [(item["address"], item["topics"][0]) for item in checked_logs] != expected_pattern:
            raise ValueError("child/root rollback changed the committed log pattern")
        if mode & 2 and accounts != prior:
            raise ValueError("root rollback retained tentative account changes")
        if mode & 1 and accounts[1] != prior[1]:
            raise ValueError("child rollback retained tentative child storage or value")
        if sum(int(account["balance"]) for account in accounts) != 8:
            raise ValueError("bounded nested call changed the combined contract balance")
        result.append({"id": tx["id"], "index": index, "status": status,
            "output": word_bytes(row.get("output")), "committedAccounts": accounts, "logs": checked_logs})
        prior = accounts
    final = normalized_accounts(history.get("finalAccounts"), bindings)
    if final != prior:
        raise ValueError("final accounts differ from the last committed prefix")
    return {"initialAccounts": initial, "transactions": result, "finalAccounts": final}


def compact_report(report: dict) -> dict:
    result = storage.compact_report(report)
    result["histories"] = report.get("histories", {})
    result["evmDeployments"] = {role: {key: value for key, value in record.items() if key != "trace"}
        for role, record in report.get("evmDeployments", {}).items()}
    result["evmTransactions"] = [{key: record[key] for key in
        ("id", "index", "transactionHash", "receipt", "request", "submission") if key in record}
        | {"traceFailed": record.get("trace", {}).get("failed"),
           "traceLastOpcode": (record.get("trace", {}).get("structLogs") or [{}])[-1].get("op")}
        for record in report.get("evmTransactions", [])]
    return result


def validate(case: dict, directory: Path, args: argparse.Namespace, *, replay: bool = False) -> dict:
    case_path = directory / "case.json"
    case_path.write_text(json.dumps(case, indent=2) + "\n")
    output = directory / ("replay" if replay else "run")
    selection = ["--replay", str(directory / "run")] if replay else ["--case", str(case_path)]
    result = shared.run([sys.executable, str(ROOT / "scripts/semantic-call-differential.py"),
        *selection, "--output", str(output), "--case-tool", str(args.case_tool),
        "--core-runner", str(args.core_runner), "--anvil", str(args.anvil),
        "--upstream", str(args.upstream), "--target-dir", str(args.target_dir),
        "--direct-fuel", str(args.fuel), "--core-fuel", str(args.core_fuel),
        "--gas", str(args.gas), "--timeout", str(args.timeout),
        "--total-timeout", str(args.total_timeout)], args.total_timeout + 20)
    report_path = output / "report.json"
    if not report_path.is_file():
        raise ValueError(f"call runner did not save its report: {result.stdout}{result.stderr}")
    report = json.loads(report_path.read_text())
    comparison = report.get("comparison", {})
    pairs = comparison.get("pairs", {})
    matched = (result.returncode == 0 and comparison.get("category") == "matched"
        and set(pairs) == storage.PAIRS and all(value is True for value in pairs.values())
        and report.get("replayOf") == (str(directory / "run") if replay else None))
    checked = {}
    if matched:
        if set(report.get("histories", {})) != set(storage.PATHS):
            raise ValueError("three actual call histories are required")
        checked = {path: normalized_history(report["histories"][path], case, report["bindings"]) for path in storage.PATHS}
        if any(checked[path] != checked["directCore"] for path in storage.PATHS):
            raise ValueError("matched report contains unequal call prefixes")
        deployments = report.get("evmDeployments", {})
        if set(deployments) != set(ROLES):
            raise ValueError("both mined contract deployments are required")
        for role in ROLES:
            deployment = deployments[role]
            if (deployment.get("request", {}).get("value") != ("0x8" if role == "parent" else "0x0")
                    or deployment.get("receipt", {}).get("status") != "0x1"
                    or deployment.get("receipt", {}).get("logs") != []):
                raise ValueError("call fixture lacks its actual funded empty deployment")
        records = report.get("evmTransactions", [])
        if len(records) != len(case["transactions"]):
            raise ValueError("call comparison lacks mined transaction receipts")
        for record, row in zip(records, checked["rustEvm"]["transactions"]):
            reverted = row["status"] == "reverted"
            if (record.get("receipt", {}).get("status") != ("0x0" if reverted else "0x1")
                    or record.get("trace", {}).get("failed") is not reverted):
                raise ValueError("EVM receipt/trace differs from the observed completion")
            steps = record.get("trace", {}).get("structLogs", [])
            if reverted and (not isinstance(steps, list) or not steps or steps[-1].get("op") != "REVERT"):
                raise ValueError("failed transaction lacks a terminal REVERT trace")
    return {"status": "matched" if matched else "failed", "case": case,
        "checkedHistories": checked, "report": compact_report(report), "exitCode": result.returncode}


def known_examples(label: str, observation: dict) -> None:
    # These fixed vectors check fixture intent; fresh Core remains the oracle.
    expected = {"identity-modes-012": [0, 3, 5], "identity-modes-345": [7, 8, 19],
        "identity-modes-67": [12, 15], "child-rollback-then-value": [8, 19, 21],
        "root-rollback-then-read": [8, 20, 8], "maximum-root-rollback": [storage.MAX_WORD],
        "high-bit-wrap": [0, 8], "fresh-cell-arbitrary-entry": [9, 21, 23],
        "constant-zero-child": [4, 10, 9]}.get(label)
    if expected is None or observation["status"] != "matched":
        return
    rows = observation["checkedHistories"]["directCore"]["transactions"]
    if [int(row["output"], 16) for row in rows] != expected:
        raise ValueError(f"known call fixture disagrees with actual Core: {label}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-call-tool")
    parser.add_argument("--core-runner", type=Path, default=ROOT / ".lake/build/bin/rust-hull-call-scenario")
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--fuel", type=int, default=1000000)
    parser.add_argument("--core-fuel", type=int, default=10000000)
    parser.add_argument("--gas", type=int, default=10000000)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--total-timeout", type=float, default=300)
    parser.add_argument("--output", type=Path, help="save a summary of at most 2 MiB")
    args = parser.parse_args()
    for key in ("fuel", "core_fuel", "gas", "timeout", "total_timeout"):
        value = getattr(args, key)
        if not 0 < value <= 10**9 or not math.isfinite(value) or (key == "fuel" and value > 10000000):
            parser.error(f"invalid bounded {key}")
    for key in ("case_tool", "core_runner", "anvil", "upstream", "target_dir"):
        setattr(args, key, getattr(args, key).resolve())
    for executable in (args.case_tool, args.core_runner, args.anvil):
        if not executable.is_file():
            raise ValueError(f"missing executable: {executable}")
    observations, invariants, replays = [], [], []
    with tempfile.TemporaryDirectory(prefix="source-call-check-", dir=ROOT / ".upstream") as temporary:
        folder = Path(temporary)
        for label, plan, txs in fixtures():
            directory = folder / label
            directory.mkdir()
            case = native_case(plan, txs, directory, args)
            alternate = native_case(plan, transactions([0, 7]), directory, args)
            invariant = {"fixture": label, "identicalSourceAcrossSequences": case["source"] == alternate["source"],
                "identicalOriginalCoreAcrossSequences": case["programs"] == alternate["programs"]}
            invariants.append(invariant)
            if not all(value for key, value in invariant.items() if key != "fixture"):
                raise ValueError(f"transaction inputs changed a nested contract: {label}")
            observation = {"fixture": label, **validate(case, directory, args)}
            observations.append(observation)
            known_examples(label, observation)
            print(f"{label} ({len(txs)} transactions): {observation['status']}", flush=True)
            if label == "aggregate-branch-rollback" and observation["status"] == "matched":
                replay = {"fixture": label, **validate(case, directory, args, replay=True)}
                replays.append(replay)
                print(f"{label} exact replay: {replay['status']}", flush=True)
    matched = sum(row["status"] == "matched" for row in observations)
    report = {"schema": "solcore-lean.source-call-check.v1", "total": len(observations), "matched": matched,
        "transactions": sum(len(row["case"]["transactions"]) for row in observations),
        "evmExecuted": all(len(row["report"].get("evmTransactions", [])) == len(row["case"]["transactions"]) for row in observations),
        "passed": matched == 10 and len(replays) == 1 and replays[0]["status"] == "matched",
        "invariants": invariants, "observations": observations, "replays": replays}
    if args.output:
        encoded = json.dumps(report, indent=2) + "\n"
        if len(encoded.encode()) > storage.SUMMARY_LIMIT:
            raise ValueError("validation summary exceeds 2 MiB")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(f"{matched}/10 call scenarios ({report['transactions']} transactions) matched across all three paths.")
    if not report["passed"] and not args.output:
        print(json.dumps([row for row in observations + replays if row["status"] != "matched"], indent=2))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    previous_term = signal.getsignal(signal.SIGTERM)

    def interrupted(_signal, _frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupted)
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print("source-call-check: interrupted", file=sys.stderr)
        raise SystemExit(1)
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(f"source-call-check: {error}", file=sys.stderr)
        raise SystemExit(2)
    finally:
        signal.signal(signal.SIGTERM, previous_term)
