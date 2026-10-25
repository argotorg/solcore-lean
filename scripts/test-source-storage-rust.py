#!/usr/bin/env python3
"""Compare ordered storage transactions through original Core, Rust/EVM and Hull.

Six scenarios exercise feedback across transactions, sparse zero storage, fresh
private cells, arbitrary step entries and aggregate branches. Observations come
from actual executions; this script does not implement a state-transition oracle.
All compiler outputs and local-chain state are removed after the bounded run.
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
spec = importlib.util.spec_from_file_location("source_aggregate_regression", ROOT / "scripts/test-source-aggregate-rust.py")
aggregate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(aggregate)
shared = aggregate.shared
word, variable, binary, binding = aggregate.word, aggregate.variable, aggregate.binary, aggregate.binding
PATHS = ("directCore", "importedHull", "rustEvm")
PAIRS = {"directCore/rustEvm", "directCore/importedHull", "importedHull/rustEvm"}
ZERO_STORAGE = [{"slot": "0", "value": "0"}, {"slot": "1", "value": "0"}]
MAX_WORD = (1 << 256) - 1
SUMMARY_LIMIT = 2 * 1024 * 1024


def transactions(inputs: list[int]) -> list[dict]:
    return [{"id": f"tx-{index}", "input": str(value),
        "calldata": "0xa444f5e9" + f"{value:064x}", "value": "0"}
        for index, value in enumerate(inputs)]


def fixtures() -> list[tuple[str, dict, list[dict]]]:
    identity = aggregate.function_program([variable(0)])
    constant = aggregate.function_program([word(0)])
    # Every invocation allocates zero, increments the local cell by two, and
    # returns input+2. Its distinct entry subtracts one through a pair snapshot.
    # Replacing the entry with the helper or retaining the cell is observable.
    helper = binding(aggregate.new_cell(word(0)),
        binding(aggregate.store(0, binary("wordAdd", aggregate.load(0), word(2))),
            binary("wordAdd", variable(2), aggregate.load(1))))
    fresh = aggregate.function_program([helper])
    entry = fresh["body"]["body"]["body"]
    fresh["body"]["body"]["body"] = binding(aggregate.pair(entry, variable(0)),
        binary("wordSub", aggregate.projection(True, variable(0)), word(1)))
    branch = dict(aggregate.fixtures())["nested-payload-helper-effects"]
    return [(label, {"schema": "solcore-lean.storage-plan.v1", "stepProgram": program}, transactions(inputs))
        for label, program, inputs in (
            ("identity-feedback", identity, [1, 2, MAX_WORD]),
            ("identity-single", identity, [MAX_WORD]),
            ("identity-repeated", identity, [1, 1]),
            ("constant-zero", constant, [MAX_WORD, 0, 1 << 255]),
            ("fresh-cell-arbitrary-entry", fresh, [0, MAX_WORD - 1, 0]),
            ("aggregate-branch-feedback", branch, [0, 1 << 255, MAX_WORD]))]


def native_case(plan: dict, txs: list[dict], directory: Path, args: argparse.Namespace) -> dict:
    plan_path, tx_path = directory / "plan.json", directory / "transactions.json"
    plan_path.write_text(json.dumps(plan))
    tx_path.write_text(json.dumps(txs))
    result = shared.run([str(args.case_tool), "emit", str(plan_path), str(tx_path), str(args.fuel)], args.timeout)
    if result.returncode:
        raise ValueError(f"native storage case failed: {result.stdout}{result.stderr}")
    case = json.loads(result.stdout)
    if (case.get("schema") != "solcore-lean.semantic-storage-case.v1"
            or case.get("storagePlan") != plan or case.get("transactions") != txs
            or case.get("initialState") != {"storage": []} or case.get("observedSlots") != ["0", "1"]):
        raise ValueError("native storage case changed its plan, transaction sequence or initial state")
    if "directCore" in case:
        raise ValueError("storage case must not retain expected execution observations")
    return case


def normalized_history(history: dict, case: dict) -> dict:
    if history.get("schema") != "solcore-lean.storage-history.v1":
        raise ValueError("unexpected storage history schema")
    if history.get("initialStorage") != ZERO_STORAGE:
        raise ValueError("storage history does not begin with both slots empty")
    rows = history.get("transactions")
    if (not isinstance(rows, list) or len(rows) != len(case["transactions"])
            or history.get("status") != "complete" or history.get("unexecuted") != []):
        raise ValueError("storage history is incomplete")
    result = []
    for index, (row, tx) in enumerate(zip(rows, case["transactions"])):
        if row.get("id") != tx["id"] or row.get("index") != index or row.get("status") != "returned":
            raise ValueError("storage history changed transaction order or completion")
        output = row.get("output")
        if not isinstance(output, str) or len(output) != 66 or not output.startswith("0x"):
            raise ValueError("storage return is not one ABI Word")
        int(output[2:], 16)
        state = row.get("committedStorage")
        if not isinstance(state, list) or [item.get("slot") for item in state] != ["0", "1"]:
            raise ValueError("storage history omitted or reordered committed slots")
        for item in state:
            value = item.get("value")
            if not isinstance(value, str) or not value.isascii() or not value.isdecimal() or str(int(value)) != value or not 0 <= int(value) <= MAX_WORD:
                raise ValueError("storage history contains an invalid Word")
        result.append({"id": tx["id"], "index": index, "status": "returned",
            "output": output.lower(), "committedStorage": state})
    if history.get("finalStorage") != result[-1]["committedStorage"]:
        raise ValueError("final storage differs from the last committed prefix")
    return {"initialStorage": ZERO_STORAGE, "transactions": result, "finalStorage": history["finalStorage"]}


def compact_report(report: dict) -> dict:
    """Keep review evidence without copying opcode traces or compiler stdout."""
    retained = {key: report[key] for key in ("schema", "comparison", "bindings", "budgets", "tools",
        "provenance", "replayOf", "caseSha256", "programSha256", "sourceSha256", "artifacts") if key in report}
    retained["histories"] = {path: {key: value for key, value in history.items()
        if key != "transactions"} | {"transactions": [{key: row[key] for key in
            ("id", "index", "status", "output", "committedStorage", "detail") if key in row}
            for row in history.get("transactions", [])]} for path, history in report.get("histories", {}).items()}
    retained["evmTransactions"] = [{key: record[key] for key in ("id", "index", "transactionHash", "receipt") if key in record}
        for record in report.get("evmTransactions", [])]
    retained["processes"] = [{key: row[key] for key in ("stage", "returncode", "elapsed") if key in row}
        | ({"stderrTail": row.get("stderr", "")[-4096:]} if row.get("returncode") else {})
        for row in report.get("processes", [])]
    return retained


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
        raise ValueError(f"storage differential runner did not save its report: {result.stdout}{result.stderr}")
    report = json.loads(report_path.read_text())
    comparison = report.get("comparison", {})
    pairs = comparison.get("pairs", {})
    matched = (result.returncode == 0 and comparison.get("category") == "matched"
        and set(pairs) == PAIRS and all(value is True for value in pairs.values())
        and report.get("replayOf") == (str(directory / "run") if replay else None))
    checked = {}
    if matched:
        if set(report.get("histories", {})) != set(PATHS):
            raise ValueError("three actual execution histories are required")
        checked = {path: normalized_history(report["histories"][path], case) for path in PATHS}
        if any(checked[path] != checked["directCore"] for path in PATHS):
            raise ValueError("matched report contains unequal transaction prefixes")
        records = report.get("evmTransactions", [])
        if len(records) != len(case["transactions"]) or any(record.get("receipt", {}).get("status") != "0x1" for record in records):
            raise ValueError("storage comparison lacks successful mined transaction receipts")
    return {"status": "matched" if matched else "failed", "case": case,
        "checkedHistories": checked, "report": compact_report(report), "exitCode": result.returncode}


def known_examples(label: str, observation: dict) -> None:
    # Fixed examples check the fixture intent, never replace fresh Core execution.
    expected = {"identity-feedback": [2, 5, 5], "identity-single": [0],
        "identity-repeated": [2, 4], "constant-zero": [1, 2, 3],
        "fresh-cell-arbitrary-entry": [2, 2, 4]}.get(label)
    if expected is None or observation["status"] != "matched":
        return
    rows = observation["checkedHistories"]["directCore"]["transactions"]
    if [int(row["output"], 16) for row in rows] != expected:
        raise ValueError(f"known storage fixture disagrees with actual Core: {label}")
    if label == "constant-zero" and any(row["committedStorage"][0]["value"] != "0" for row in rows):
        raise ValueError("constant zero fixture does not normalize sparse zero storage")
    if label == "fresh-cell-arbitrary-entry" and [row["committedStorage"][0]["value"] for row in rows] != ["1", "0", "1"]:
        raise ValueError("fresh-cell fixture does not clear and then rewrite persistent slot zero")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-storage-tool")
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
    with tempfile.TemporaryDirectory(prefix="source-storage-check-", dir=ROOT / ".upstream") as temporary:
        folder = Path(temporary)
        for label, plan, txs in fixtures():
            directory = folder / label
            directory.mkdir()
            case = native_case(plan, txs, directory, args)
            alternate = native_case(plan, transactions([0, 7]), directory, args)
            invariant = {"fixture": label, "identicalSourceAcrossSequences": case["source"] == alternate["source"],
                "identicalOriginalCoreAcrossSequences": case["program"] == alternate["program"]}
            invariants.append(invariant)
            if not all(value for key, value in invariant.items() if key != "fixture"):
                raise ValueError(f"transaction inputs changed the contract: {label}")
            observation = {"fixture": label, **validate(case, directory, args)}
            observations.append(observation)
            known_examples(label, observation)
            print(f"{label} ({len(txs)} transactions): {observation['status']}", flush=True)
            if label == "aggregate-branch-feedback" and observation["status"] == "matched":
                replay = {"fixture": label, **validate(case, directory, args, replay=True)}
                replays.append(replay)
                print(f"{label} exact replay: {replay['status']}", flush=True)
    matched = sum(row["status"] == "matched" for row in observations)
    report = {"schema": "solcore-lean.source-storage-check.v1", "total": len(observations), "matched": matched,
        "transactions": sum(len(row["case"]["transactions"]) for row in observations),
        "evmExecuted": all(len(row["report"].get("evmTransactions", [])) == len(row["case"]["transactions"]) for row in observations),
        "passed": matched == 6 and len(replays) == 1 and replays[0]["status"] == "matched",
        "invariants": invariants, "observations": observations, "replays": replays}
    if args.output:
        encoded = json.dumps(report, indent=2) + "\n"
        if len(encoded.encode()) > SUMMARY_LIMIT:
            raise ValueError("validation summary exceeds 2 MiB")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(f"{matched}/6 storage scenarios ({report['transactions']} transactions) matched across all three paths.")
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
        print("source-storage-check: interrupted", file=sys.stderr)
        raise SystemExit(1)
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(f"source-storage-check: {error}", file=sys.stderr)
        raise SystemExit(2)
    finally:
        signal.signal(signal.SIGTERM, previous_term)
