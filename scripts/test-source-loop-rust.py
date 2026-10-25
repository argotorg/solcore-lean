#!/usr/bin/env python3
"""Compare canonical Core unrolling with actual Rust while loops.

Four loop plans exercise zero iterations, aggregate step entries and private
cell reinitialization. The six fixed inputs cover zero, one, three and seven
iterations across masks. Only the native Core evaluator supplies general expected
results; a small explicitly known increment fixture checks its boundary behavior.
"""

from __future__ import annotations

import argparse
import copy
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
INPUTS = (0, 1, 3, 7, (1 << 256) - 1, 1 << 255)


def replace_entry(program: dict, transform) -> dict:
    result = copy.deepcopy(program)
    expression = result["body"]
    while expression["tag"] == "let":
        expression = expression["body"]
    if expression["tag"] != "lambda":
        raise ValueError("fixture must end in its entry lambda")
    expression["body"] = transform(expression["body"])
    return result


def fixtures() -> list[tuple[str, dict]]:
    # Each helper invocation allocates zero, stores two, and returns input+2.
    # The distinct entry projects a pair and subtracts one, making the complete
    # step input+1. Calling only the last helper or reusing its cell is observable.
    fresh_helper = binding(aggregate.new_cell(word(0)),
        binding(aggregate.store(0, binary("wordAdd", aggregate.load(0), word(2))),
            binary("wordAdd", variable(2), aggregate.load(1))))
    fresh_step = replace_entry(aggregate.function_program([fresh_helper]),
        lambda entry: binding(aggregate.pair(entry, variable(0)),
            binary("wordSub", aggregate.projection(True, variable(0)), word(1))))
    existing = dict(aggregate.fixtures())
    pair_step = replace_entry(existing["pair-snapshot"], lambda entry: binary("wordAdd", entry, word(3)))
    sum_step = replace_entry(existing["aggregate-case-joins"], lambda entry: binary("wordAdd", entry, word(1)))
    return [(label, {"schema": "solcore-lean.loop-plan.v1", "stepProgram": program, "mask": mask})
        for label, program, mask in (
            ("zero-iterations", fresh_step, 0), ("pair-entry-one-iteration", pair_step, 1),
            ("sum-entry-three-iterations", sum_step, 3), ("fresh-cell-seven-iterations", fresh_step, 7))]


def native_case(plan_path: Path, value: int, args: argparse.Namespace) -> dict:
    result = shared.run([str(args.case_tool), "loop-emit", str(plan_path), str(value), str(args.fuel)], args.timeout)
    if result.returncode:
        raise ValueError(f"native loop case failed: {result.stdout}{result.stderr}")
    case = json.loads(result.stdout)
    if case.get("schema") != "solcore-lean.semantic-loop-case.v1" or case.get("input") != str(value):
        raise ValueError("native loop case has an unexpected schema or argument")
    if case.get("loopPlan") != json.loads(plan_path.read_text()):
        raise ValueError("native loop case changed the supplied plan")
    direct = case.get("directCore", {})
    if direct.get("stage") != "execution" or direct.get("status") != "returned":
        raise ValueError(f"original Core application did not complete: {direct}")
    return case


def known_increment_results(label: str, cases: list[dict]) -> None:
    # These are fixed arithmetic examples, not a second interpreter. The loop
    # oracle used for every external comparison remains the original Core run.
    if label == "zero-iterations":
        expected = list(INPUTS)
    elif label == "fresh-cell-seven-iterations":
        expected = [0, 2, 6, 14, 6, 1 << 255]
    else:
        return
    for case, value in zip(cases, expected):
        if case["directCore"]["word"] != str(value):
            raise ValueError(f"known increment fixture disagrees at input {case['input']}: {case['directCore']}")


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
    with tempfile.TemporaryDirectory(prefix="source-loop-check-", dir=ROOT / ".upstream") as temporary:
        folder = Path(temporary)
        for label, plan in fixtures():
            plan_path = folder / (label + ".json")
            plan_path.write_text(json.dumps(plan))
            cases = [native_case(plan_path, value, args) for value in INPUTS]
            known_increment_results(label, cases)
            source_identical = len({case["source"] for case in cases}) == 1
            results_vary = len({case["directCore"]["word"] for case in cases}) >= 2
            # This is a count derived from the specified recipe, not an executed
            # statement/opcode counter or an independently evaluated loop result.
            positive_effect = any((int(case["input"]) & plan["mask"]) > 0
                and case["directCore"]["word"] != case["input"] for case in cases)
            invariants.append({"fixture": label, "mask": plan["mask"], "identicalSource": source_identical,
                "distinctCompletedResults": results_vary, "positiveTripChangesResult": positive_effect})
            if not source_identical or not results_vary or (plan["mask"] != 0 and not positive_effect):
                raise ValueError(f"fixture {label} does not retain one meaningful runtime loop source")
            for index, case in enumerate(cases):
                directory = folder / (label + "-" + str(index))
                directory.mkdir()
                observation = {"fixture": label, "input": case["input"], **shared.validate(case, directory, args)}
                observations.append(observation)
                print(f"{label} input {case['input']}: {observation['status']}", flush=True)
                if label == "fresh-cell-seven-iterations" and case["input"] == "7" and observation["status"] == "matched":
                    replay = {"fixture": label, "input": case["input"],
                        **shared.validate(case, directory, args, replay=True)}
                    replays.append(replay)
                    print(f"{label} exact replay: {replay['status']}", flush=True)
    matched = sum(row["status"] == "matched" for row in observations)
    report = {"schema": "solcore-lean.source-loop-check.v1",
        "evmExecuted": any("rustEvm" in row["report"].get("rawObservations", {}) for row in observations),
        "passed": matched == len(observations) and len(replays) == 1 and replays[0]["status"] == "matched",
        "total": len(observations), "matched": matched,
        "invariants": invariants, "observations": observations, "replays": replays}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{matched}/{len(observations)} bounded loop input cases matched across all three execution paths.")
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
        print("source-loop-check: interrupted", file=sys.stderr)
        raise SystemExit(1)
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(f"source-loop-check: {error}", file=sys.stderr)
        raise SystemExit(2)
    finally:
        signal.signal(signal.SIGTERM, previous_term)
