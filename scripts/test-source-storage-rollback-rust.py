#!/usr/bin/env python3
"""Compare deliberate post-write rollback on all three actual execution paths.

The fixed profile reverts odd original inputs with one Word of tentative output.
Cases retain their original Core contract; no Python state-transition evaluator
or saved observation supplies the oracle. Temporary exports and chains are owned
by the suite and removed after validation.
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
word, variable, binary = storage.word, storage.variable, storage.binary
CASE_SCHEMA = "solcore-lean.semantic-storage-rollback-case.v1"
PLAN_SCHEMA = "solcore-lean.storage-rollback-plan.v1"


def fixtures() -> list[tuple[str, dict, list[dict]]]:
    identity = aggregate.function_program([variable(0)])
    deletion = aggregate.function_program([{"tag": "if",
        "condition": binary("wordEq", variable(0), word(1)),
        "thenBranch": word(0), "elseBranch": variable(0)}])
    inherited = {label: plan["stepProgram"] for label, plan, _ in storage.fixtures()}
    return [(label, {"schema": PLAN_SCHEMA, "stepProgram": program}, storage.transactions(inputs))
        for label, program, inputs in (
            ("success-revert-success", identity, [2, 3, 4]),
            ("consecutive-reverts", identity, [1, 3, 2]),
            ("single-zero-payload-revert", identity, [storage.MAX_WORD]),
            ("tentative-deletion-rollback", deletion, [2, storage.MAX_WORD, 0]),
            ("fresh-cell-arbitrary-entry", inherited["fresh-cell-arbitrary-entry"], [0, 1, 2]),
            ("aggregate-branch-rollback", inherited["aggregate-branch-feedback"], [0, storage.MAX_WORD, 1 << 255]),
            ("first-revert-then-return", identity, [storage.MAX_WORD, 2]),
            ("zero-writes-rollback", inherited["constant-zero"], [0, 1, 0]))]


def native_case(plan: dict, txs: list[dict], directory: Path, args: argparse.Namespace) -> dict:
    plan_path, tx_path = directory / "plan.json", directory / "transactions.json"
    plan_path.write_text(json.dumps(plan))
    tx_path.write_text(json.dumps(txs))
    result = shared.run([str(args.case_tool), "emit", str(plan_path), str(tx_path), str(args.fuel)], args.timeout)
    if result.returncode:
        raise ValueError(f"native rollback case failed: {result.stdout}{result.stderr}")
    case = json.loads(result.stdout)
    if (case.get("schema") != CASE_SCHEMA or case.get("storagePlan") != plan or case.get("transactions") != txs
            or case.get("initialState") != {"storage": []} or case.get("observedSlots") != ["0", "1"]
            or "directCore" in case):
        raise ValueError("native rollback case changed its original plan, transactions or empty initial state")
    return case


def normalized_history(history: dict, case: dict) -> dict:
    if history.get("schema") != "solcore-lean.storage-history.v1" or history.get("initialStorage") != storage.ZERO_STORAGE:
        raise ValueError("rollback history must begin with two zero slots")
    rows = history.get("transactions")
    if (not isinstance(rows, list) or len(rows) != len(case["transactions"])
            or history.get("status") != "complete" or history.get("unexecuted") != []
            or history.get("unobserved", []) != []):
        raise ValueError("rollback history is incomplete")
    result, prior = [], storage.ZERO_STORAGE
    for index, (row, tx) in enumerate(zip(rows, case["transactions"])):
        expected_status = "reverted" if int(tx["input"]) % 2 else "returned"
        if row.get("id") != tx["id"] or row.get("index") != index or row.get("status") != expected_status:
            raise ValueError("rollback history changed transaction identity, order or fixed completion rule")
        output = row.get("output")
        if not isinstance(output, str) or len(output) != 66 or not output.startswith("0x"):
            raise ValueError("return/revert payload must contain exactly one ABI Word")
        int(output[2:], 16)
        state = row.get("committedStorage")
        if not isinstance(state, list) or [item.get("slot") for item in state] != ["0", "1"]:
            raise ValueError("rollback history omitted or reordered committed slots")
        for item in state:
            value = item.get("value")
            if not isinstance(value, str) or not value.isascii() or not value.isdecimal() or str(int(value)) != value or not 0 <= int(value) <= storage.MAX_WORD:
                raise ValueError("rollback history contains an invalid storage Word")
        if expected_status == "reverted" and state != prior:
            raise ValueError("revert retained tentative writes in committed storage")
        result.append({"id": tx["id"], "index": index, "status": expected_status,
            "output": output.lower(), "committedStorage": state})
        prior = state
    if history.get("finalStorage") != prior:
        raise ValueError("final storage differs from the last committed prefix")
    return {"initialStorage": storage.ZERO_STORAGE, "transactions": result, "finalStorage": prior}


def validate(case: dict, directory: Path, args: argparse.Namespace, *, replay: bool = False) -> dict:
    case_path = directory / "case.json"
    case_path.write_text(json.dumps(case, indent=2) + "\n")
    output = directory / ("replay" if replay else "run")
    selection = ["--replay", str(directory / "run")] if replay else ["--case", str(case_path)]
    result = shared.run([sys.executable, str(ROOT / "scripts/semantic-storage-differential.py"),
        *selection, "--output", str(output), "--case-tool", str(args.case_tool),
        "--core-runner", str(args.core_runner), "--anvil", str(args.anvil),
        "--upstream", str(args.upstream), "--target-dir", str(args.target_dir),
        "--direct-fuel", str(args.fuel), "--core-fuel", str(args.core_fuel),
        "--gas", str(args.gas), "--timeout", str(args.timeout),
        "--total-timeout", str(args.total_timeout)], args.total_timeout + 20)
    report_path = output / "report.json"
    if not report_path.is_file():
        raise ValueError(f"rollback runner did not save its report: {result.stdout}{result.stderr}")
    report = json.loads(report_path.read_text())
    comparison = report.get("comparison", {})
    pairs = comparison.get("pairs", {})
    matched = (result.returncode == 0 and comparison.get("category") == "matched"
        and set(pairs) == storage.PAIRS and all(value is True for value in pairs.values())
        and report.get("replayOf") == (str(directory / "run") if replay else None))
    checked = {}
    if matched:
        if set(report.get("histories", {})) != set(storage.PATHS):
            raise ValueError("three actual rollback histories are required")
        checked = {path: normalized_history(report["histories"][path], case) for path in storage.PATHS}
        if any(checked[path] != checked["directCore"] for path in storage.PATHS):
            raise ValueError("matched report contains unequal rollback prefixes")
        records = report.get("evmTransactions", [])
        if len(records) != len(case["transactions"]):
            raise ValueError("rollback comparison lacks mined transaction receipts")
        for record, row in zip(records, checked["rustEvm"]["transactions"]):
            reverted = row["status"] == "reverted"
            if (record.get("receipt", {}).get("status") != ("0x0" if reverted else "0x1")
                    or record.get("trace", {}).get("failed") is not reverted):
                raise ValueError("EVM receipt/trace differs from the observed completion")
            logs = record.get("trace", {}).get("structLogs", [])
            if reverted and (not isinstance(logs, list) or not logs or not isinstance(logs[-1], dict)
                    or logs[-1].get("op") != "REVERT"):
                raise ValueError("failed transaction lacks a terminal REVERT trace")
    return {"status": "matched" if matched else "failed", "case": case,
        "checkedHistories": checked, "report": storage.compact_report(report), "exitCode": result.returncode}


def known_examples(label: str, observation: dict) -> None:
    # Fixed vectors describe these fixtures; the comparison oracle is fresh Core.
    expected = {
        "success-revert-success": ([3, 7, 8], [[2, 1], [2, 1], [6, 2]]),
        "consecutive-reverts": ([2, 4, 3], [[0, 0], [0, 0], [2, 1]]),
        "single-zero-payload-revert": ([0], [[0, 0]]),
        "tentative-deletion-rollback": ([3, 2, 4], [[2, 1], [2, 1], [2, 2]]),
        "fresh-cell-arbitrary-entry": ([2, 5, 6], [[1, 1], [1, 1], [4, 2]]),
        "first-revert-then-return": ([0, 3], [[0, 0], [2, 1]]),
        "zero-writes-rollback": ([1, 2, 2], [[0, 1], [0, 1], [0, 2]])}.get(label)
    if expected is None or observation["status"] != "matched":
        return
    rows = observation["checkedHistories"]["directCore"]["transactions"]
    actual = ([int(row["output"], 16) for row in rows],
        [[int(slot["value"]) for slot in row["committedStorage"]] for row in rows])
    if actual != expected:
        raise ValueError(f"known rollback fixture disagrees with actual Core: {label}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-storage-rollback-tool")
    parser.add_argument("--core-runner", type=Path, default=ROOT / ".lake/build/bin/rust-hull-storage-scenario")
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
    with tempfile.TemporaryDirectory(prefix="source-storage-rollback-check-", dir=ROOT / ".upstream") as temporary:
        folder = Path(temporary)
        for label, plan, txs in fixtures():
            directory = folder / label
            directory.mkdir()
            case = native_case(plan, txs, directory, args)
            alternate = native_case(plan, storage.transactions([0, 7]), directory, args)
            invariant = {"fixture": label, "identicalSourceAcrossSequences": case["source"] == alternate["source"],
                "identicalOriginalCoreAcrossSequences": case["program"] == alternate["program"]}
            invariants.append(invariant)
            if not all(value for key, value in invariant.items() if key != "fixture"):
                raise ValueError(f"transaction inputs changed the rollback contract: {label}")
            observation = {"fixture": label, **validate(case, directory, args)}
            observations.append(observation)
            known_examples(label, observation)
            print(f"{label} ({len(txs)} transactions): {observation['status']}", flush=True)
            if label == "aggregate-branch-rollback" and observation["status"] == "matched":
                replay = {"fixture": label, **validate(case, directory, args, replay=True)}
                replays.append(replay)
                print(f"{label} exact replay: {replay['status']}", flush=True)
    matched = sum(row["status"] == "matched" for row in observations)
    report = {"schema": "solcore-lean.source-storage-rollback-check.v1", "total": len(observations), "matched": matched,
        "transactions": sum(len(row["case"]["transactions"]) for row in observations),
        "evmExecuted": all(len(row["report"].get("evmTransactions", [])) == len(row["case"]["transactions"]) for row in observations),
        "passed": matched == 8 and len(replays) == 1 and replays[0]["status"] == "matched",
        "invariants": invariants, "observations": observations, "replays": replays}
    if args.output:
        encoded = json.dumps(report, indent=2) + "\n"
        if len(encoded.encode()) > storage.SUMMARY_LIMIT:
            raise ValueError("validation summary exceeds 2 MiB")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(f"{matched}/8 rollback scenarios ({report['transactions']} transactions) matched across all three paths.")
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
        print("source-storage-rollback-check: interrupted", file=sys.stderr)
        raise SystemExit(1)
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(f"source-storage-rollback-check: {error}", file=sys.stderr)
        raise SystemExit(2)
    finally:
        signal.signal(signal.SIGTERM, previous_term)
