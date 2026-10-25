#!/usr/bin/env python3
"""Check named helper chains and diamonds through all three execution paths.

Each original Core program binds Word -> Word helpers before its entry lambda.
The native case tool checks the function DAG and evaluates its actual application;
the Python fixtures never calculate an expected result. Runtime inputs exercise
the same emitted source through branch and let scopes, followed by exact replay.
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
spec = importlib.util.spec_from_file_location("source_input_regression", ROOT / "scripts/test-source-input-rust.py")
shared = importlib.util.module_from_spec(spec)
spec.loader.exec_module(shared)
word, variable, binary, binding = shared.word, shared.variable, shared.binary, shared.binding


def application(function: dict, argument: dict) -> dict:
    return {"tag": "apply", "function": function, "argument": argument}


def function(body: dict) -> dict:
    return {"tag": "lambda", "parameterType": "word", "resultType": "word", "body": body}


def function_program(helpers: list[dict]) -> dict:
    body = function(application(variable(1), variable(0)))
    for helper in reversed(helpers):
        body = binding(function(helper), body)
    return {"schema": "solcore-semantic-core", "dataDefinitions": [],
        "resultType": {"tag": "function", "parameter": "word", "result": "word"}, "body": body}


def fixtures() -> list[tuple[str, dict]]:
    first = binary("wordAdd", variable(0), word(1))
    # Inside this lambda: argument, first helper. Each nested let shifts both.
    second = binding(variable(0), {
        "tag": "if",
        "condition": binary("wordGt", variable(0), word((1 << 255) - 1)),
        "thenBranch": binding(application(variable(2), variable(0)),
            binary("wordSub", variable(0), word(1))),
        "elseBranch": binding(word(7),
            binary("wordAdd", application(variable(3), variable(1)), variable(0)))})
    # The third helper calls both predecessors; the second also calls the first.
    third = binding(application(variable(2), variable(0)),
        binding(application(variable(2), variable(1)), binary("wordXor", variable(1), variable(0))))
    return [("helper-chain", function_program([first, second])),
            ("helper-diamond", function_program([first, second, third]))]


def native_case(program: Path, value: int, args: argparse.Namespace) -> dict:
    result = shared.run([str(args.case_tool), "function-emit", str(program), str(value), str(args.fuel)], args.timeout)
    if result.returncode:
        raise ValueError(f"native function case failed: {result.stdout}{result.stderr}")
    case = json.loads(result.stdout)
    if case.get("schema") != "solcore-lean.semantic-function-case.v1" or case.get("input") != str(value):
        raise ValueError("native function case has an unexpected schema or argument")
    direct = case.get("directCore", {})
    if direct.get("stage") != "execution" or direct.get("status") != "returned":
        raise ValueError(f"original Core application did not complete: {direct}")
    return case


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
    for executable in (args.case_tool, args.core_runner, args.anvil):
        if not executable.is_file():
            raise ValueError(f"missing executable: {executable}")
    observations, invariants, replays = [], [], []
    with tempfile.TemporaryDirectory(prefix="source-function-check-", dir=ROOT / ".upstream") as temporary:
        folder = Path(temporary)
        for label, program in fixtures():
            program_path = folder / (label + ".json")
            program_path.write_text(json.dumps(program))
            cases = [native_case(program_path, value, args) for value in shared.INPUTS]
            source_identical = len({case["source"] for case in cases}) == 1
            results_vary = len({case["directCore"]["word"] for case in cases}) >= 2
            invariants.append({"fixture": label, "identicalSource": source_identical,
                "distinctCompletedResults": results_vary})
            if not source_identical or not results_vary:
                raise ValueError(f"fixture {label} does not retain one helper DAG with varying runtime results")
            for index, case in enumerate(cases):
                directory = folder / (label + "-" + str(index))
                directory.mkdir()
                observation = {"fixture": label, "input": case["input"], **shared.validate(case, directory, args)}
                observations.append(observation)
                print(f"{label} input {case['input']}: {observation['status']}", flush=True)
                if label == "helper-diamond" and index == len(cases) - 1 and observation["status"] == "matched":
                    replay = {"fixture": label, "input": case["input"],
                        **shared.validate(case, directory, args, replay=True)}
                    replays.append(replay)
                    print(f"{label} exact replay: {replay['status']}", flush=True)
    matched = sum(row["status"] == "matched" for row in observations)
    report = {"schema": "solcore-lean.source-function-check.v1",
        "evmExecuted": any("rustEvm" in row["report"].get("rawObservations", {}) for row in observations),
        "passed": matched == len(observations) and len(replays) == 1 and replays[0]["status"] == "matched",
        "total": len(observations), "matched": matched,
        "invariants": invariants, "observations": observations, "replays": replays}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{matched}/{len(observations)} helper DAG input cases matched across all three execution paths.")
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
        print("source-function-check: interrupted", file=sys.stderr)
        raise SystemExit(1)
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(f"source-function-check: {error}", file=sys.stderr)
        raise SystemExit(2)
    finally:
        signal.signal(signal.SIGTERM, previous_term)
