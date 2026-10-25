#!/usr/bin/env python3
"""Run boundary inputs through original Core, emitted Rust/EVM and imported Hull.

Each fixture is one checked Word -> Word Core function. The native case tool
constructs and evaluates its actual application for every input; this script
does not implement a Core evaluator. The emitted function must stay identical
across inputs and produce at least two different completed results. All compiler
exports and local-chain state live in an automatically removed temporary folder.
"""

from __future__ import annotations

import argparse
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
INPUTS = (0, 1, (1 << 256) - 1, 1 << 255)
PAIRS = {"directCore/rustEvm", "directCore/importedHull", "importedHull/rustEvm"}


def word(value: int) -> dict:
    return {"tag": "word", "value": f"0x{value:064x}"}


def variable(index: int) -> dict:
    return {"tag": "var", "index": index}


def binary(operation: str, left: dict, right: dict) -> dict:
    return {"tag": "binary", "op": operation, "left": left, "right": right}


def binding(initializer: dict, body: dict) -> dict:
    return {"tag": "let", "initializer": initializer, "body": body}


def function_program(body: dict) -> dict:
    return {"schema": "solcore-semantic-core", "dataDefinitions": [],
        "resultType": {"tag": "function", "parameter": "word", "result": "word"},
        "body": {"tag": "lambda", "parameterType": "word", "resultType": "word", "body": body}}


def fixtures() -> list[tuple[str, dict]]:
    # De Bruijn variables retain the argument through an outer let and each
    # branch's local binding. The comparison crosses the unsigned high bit.
    branch = binding(binary("wordAdd", variable(0), word(1)), {
        "tag": "if",
        "condition": binary("wordGt", variable(1), word((1 << 255) - 1)),
        "thenBranch": binding(binary("wordXor", variable(0), word((1 << 256) - 1)),
            binary("wordSub", variable(0), variable(1))),
        "elseBranch": binding(word(7), binary("wordAdd", variable(2), variable(0)))})
    return [("identity", function_program(variable(0))),
            ("runtime-branch-scopes", function_program(branch))]


def run(command: list[str], timeout: float) -> subprocess.CompletedProcess:
    process = subprocess.Popen(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except BaseException:
        # The differential CLI owns further process groups. Give its SIGTERM
        # handler time to stop those groups before forcing this parent down.
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            process.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.communicate()
        raise
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


def native_case(program: Path, value: int, args: argparse.Namespace) -> dict:
    result = run([str(args.case_tool), "input-emit", str(program), str(value), str(args.fuel)], args.timeout)
    if result.returncode:
        raise ValueError(f"native input case failed: {result.stdout}{result.stderr}")
    case = json.loads(result.stdout)
    if case.get("schema") != "solcore-lean.semantic-input-case.v1" or case.get("input") != str(value):
        raise ValueError("native input case has an unexpected schema or argument")
    direct = case.get("directCore", {})
    if direct.get("stage") != "execution" or direct.get("status") != "returned":
        raise ValueError(f"original Core application did not complete: {direct}")
    return case


def validate(case: dict, directory: Path, args: argparse.Namespace, *, replay: bool = False) -> dict:
    path = directory / "case.json"
    path.write_text(json.dumps(case, indent=2) + "\n")
    output = directory / ("replay" if replay else "run")
    selection = ["--replay", str(directory / "run")] if replay else ["--case", str(path)]
    result = run([sys.executable, str(ROOT / "scripts/semantic-differential.py"),
        *selection, "--output", str(output), "--case-tool", str(args.case_tool),
        "--core-runner", str(args.core_runner), "--anvil", str(args.anvil),
        "--upstream", str(args.upstream), "--target-dir", str(args.target_dir),
        "--direct-fuel", str(args.fuel), "--core-fuel", str(args.core_fuel),
        "--gas", str(args.gas), "--timeout", str(args.timeout),
        "--total-timeout", str(args.total_timeout)], args.total_timeout + 20)
    report_path = output / "report.json"
    if not report_path.is_file():
        raise ValueError(f"differential runner did not save its report: {result.stdout}{result.stderr}")
    report = json.loads(report_path.read_text())
    comparison = report.get("comparison", {})
    pairs = comparison.get("pairs", {})
    matched = (result.returncode == 0 and comparison.get("category") == "matched"
        and set(pairs) == PAIRS and all(value is True for value in pairs.values())
        and report.get("replayOf") == (str(directory / "run") if replay else None)
        and report.get("observations", {}).get("directCore") == {
            "status": "returned", "word": case["directCore"]["word"]})
    return {"status": "matched" if matched else "failed", "case": case,
        "report": report, "exitCode": result.returncode}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--core-runner", type=Path, default=ROOT / ".lake/build/bin/rust-hull-scenario")
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--fuel", type=int, default=1000000)
    parser.add_argument("--core-fuel", type=int, default=10000000)
    parser.add_argument("--gas", type=int, default=10000000)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--total-timeout", type=float, default=300)
    parser.add_argument("--output", type=Path, help="save the validation summary with cases and reports")
    args = parser.parse_args()
    for key in ("fuel", "core_fuel", "gas", "timeout", "total_timeout"):
        value = getattr(args, key)
        if not 0 < value <= 10**9 or not math.isfinite(value):
            parser.error(f"{key} must be finite, positive and at most 1000000000")
    for key in ("case_tool", "core_runner", "anvil", "upstream", "target_dir"):
        setattr(args, key, getattr(args, key).resolve())
    for binary in (args.case_tool, args.core_runner, args.anvil):
        if not binary.is_file():
            raise ValueError(f"missing executable: {binary}")
    observations = []
    invariants = []
    replays = []
    with tempfile.TemporaryDirectory(prefix="source-input-check-", dir=ROOT / ".upstream") as temporary:
        folder = Path(temporary)
        for label, program in fixtures():
            program_path = folder / (label + ".json")
            program_path.write_text(json.dumps(program))
            cases = [native_case(program_path, value, args) for value in INPUTS]
            source_identical = len({case["source"] for case in cases}) == 1
            results_vary = len({case["directCore"]["word"] for case in cases}) >= 2
            invariants.append({"fixture": label, "identicalSource": source_identical,
                "distinctCompletedResults": results_vary})
            if not source_identical or not results_vary:
                raise ValueError(f"fixture {label} does not retain one function with varying runtime results")
            for index, case in enumerate(cases):
                directory = folder / (label + "-" + str(index))
                directory.mkdir()
                observation = {"fixture": label, "input": case["input"], **validate(case, directory, args)}
                observations.append(observation)
                print(f"{label} input {case['input']}: {observation['status']}", flush=True)
                if label == "runtime-branch-scopes" and index == len(cases) - 1 and observation["status"] == "matched":
                    replay = {"fixture": label, "input": case["input"],
                        **validate(case, directory, args, replay=True)}
                    replays.append(replay)
                    print(f"{label} exact replay: {replay['status']}", flush=True)
    matched = sum(row["status"] == "matched" for row in observations)
    report = {"schema": "solcore-lean.source-input-check.v1",
        "evmExecuted": any("rustEvm" in row["report"].get("rawObservations", {}) for row in observations),
        "passed": matched == len(observations) and len(replays) == 1 and replays[0]["status"] == "matched",
        "total": len(observations), "matched": matched,
        "invariants": invariants, "observations": observations, "replays": replays}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{matched}/{len(observations)} runtime input cases matched across all three execution paths.")
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
        print("source-input-check: interrupted", file=sys.stderr)
        raise SystemExit(1)
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(f"source-input-check: {error}", file=sys.stderr)
        raise SystemExit(2)
    finally:
        signal.signal(signal.SIGTERM, previous_term)
