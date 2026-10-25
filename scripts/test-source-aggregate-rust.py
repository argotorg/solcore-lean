#!/usr/bin/env python3
"""Check local Word pairs and sums through all three execution paths.

The original Core fixtures retain pair snapshots across stores, evaluate each
projection operand once, and exercise selected sum branches with nested payload,
Unit and helper scopes. Pair/sum case results also cross typed joins. The native
tool evaluates the actual Core application; Python does not compute an oracle.
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


def new_cell(initializer: dict) -> dict:
    return {"tag": "newCell", "elementType": "word", "initializer": initializer}


def load(reference: int) -> dict:
    return {"tag": "loadCell", "reference": variable(reference)}


def store(reference: int, value: dict) -> dict:
    return {"tag": "storeCell", "reference": variable(reference), "value": value}


def pair(left: dict, right: dict) -> dict:
    return {"tag": "pair", "left": left, "right": right}


def projection(first: bool, operand: dict) -> dict:
    return {"tag": "first" if first else "second", "operand": operand}


def injection(left: bool, payload: dict) -> dict:
    return {"tag": "inLeft" if left else "inRight", "rightType" if left else "leftType": "word", "payload": payload}


def case_of(scrutinee: dict, left: dict, right: dict) -> dict:
    return {"tag": "case", "scrutinee": scrutinee, "leftBranch": left, "rightBranch": right}


def selected_sum(input_value: dict) -> dict:
    return {"tag": "if", "condition": binary("wordGt", input_value, word((1 << 255) - 1)),
        "thenBranch": injection(True, input_value), "elseBranch": injection(False, input_value)}


def fixtures() -> list[tuple[str, dict]]:
    # The tuple contains Word copies. Its first element is loaded before the
    # second operand stores; a later store must change neither saved element.
    snapshot = binding(new_cell(variable(0)),
        binding(pair(load(0), binding(store(0, word(2)), load(1))),
            binding(store(1, word(9)), binary("wordAdd",
                projection(True, variable(1)), projection(False, variable(1))))))
    # Both tuple operands have observable local effects even when only its first
    # element is selected. Reading the cell afterward detects omitted/repeated
    # operand evaluation as well as reversal of left/right evaluation order.
    once = binding(new_cell(variable(0)), binding(projection(True, pair(
        binding(store(0, binary("wordAdd", load(0), word(1))), load(1)),
        binding(store(0, binary("wordAdd", load(0), word(2))), load(1)))),
        binary("wordAdd", variable(0), load(1))))

    # Within the nested case: payload, Unit, outer payload, sum, cell, argument,
    # previous helper. The final Unit let moves the helper to index seven.
    def nested_branch(left: bool) -> dict:
        selected = binding(store(4, binary("wordAdd", variable(0), word(10 if left else 20))),
            application(variable(7), load(5)))
        unselected = binding(store(4, word(700)), word(999))
        nested = case_of(injection(not left, load(3)),
            unselected if left else selected, selected if left else unselected)
        return binding(store(2, binary("wordAdd", variable(0), word(1 if left else 2))), nested)

    nested = binding(new_cell(variable(0)), binding(selected_sum(variable(1)),
        binding(case_of(variable(0), nested_branch(True), nested_branch(False)),
            binary("wordAdd", variable(0), load(2)))))
    # A case may return a local pair or sum; neither becomes an aggregate payload
    # or ABI argument. The final payload binder shifts the saved pair to index 2.
    joins = binding(selected_sum(variable(0)),
        binding(case_of(variable(0), pair(variable(0), binary("wordAdd", variable(0), word(1))),
            pair(binary("wordAdd", variable(0), word(2)), variable(0))),
        binding(case_of(variable(1), injection(False, binary("wordAdd", variable(0), word(3))),
            injection(True, binary("wordAdd", variable(0), word(4)))),
        case_of(variable(0), binary("wordAdd", variable(0), projection(True, variable(2))),
            binary("wordAdd", variable(0), projection(False, variable(2)))))))
    return [("pair-snapshot", function_program([snapshot])),
            ("projection-evaluates-once", function_program([once])),
            ("nested-payload-helper-effects", function_program([binary("wordAdd", variable(0), word(5)), nested])),
            ("aggregate-case-joins", function_program([joins]))]


def native_case(program: Path, value: int, args: argparse.Namespace) -> dict:
    result = shared.run([str(args.case_tool), "aggregate-emit", str(program), str(value), str(args.fuel)], args.timeout)
    if result.returncode:
        raise ValueError(f"native aggregate case failed: {result.stdout}{result.stderr}")
    case = json.loads(result.stdout)
    if case.get("schema") != "solcore-lean.semantic-aggregate-case.v1" or case.get("input") != str(value):
        raise ValueError("native aggregate case has an unexpected schema or argument")
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
    with tempfile.TemporaryDirectory(prefix="source-aggregate-check-", dir=ROOT / ".upstream") as temporary:
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
                raise ValueError(f"fixture {label} does not retain one aggregate DAG with varying runtime results")
            for index, case in enumerate(cases):
                directory = folder / (label + "-" + str(index))
                directory.mkdir()
                observation = {"fixture": label, "input": case["input"], **shared.validate(case, directory, args)}
                observations.append(observation)
                print(f"{label} input {case['input']}: {observation['status']}", flush=True)
                if label == "aggregate-case-joins" and index == len(cases) - 1 and observation["status"] == "matched":
                    replay = {"fixture": label, "input": case["input"],
                        **shared.validate(case, directory, args, replay=True)}
                    replays.append(replay)
                    print(f"{label} exact replay: {replay['status']}", flush=True)
    matched = sum(row["status"] == "matched" for row in observations)
    report = {"schema": "solcore-lean.source-aggregate-check.v1",
        "evmExecuted": any("rustEvm" in row["report"].get("rawObservations", {}) for row in observations),
        "passed": matched == len(observations) and len(replays) == 1 and replays[0]["status"] == "matched",
        "total": len(observations), "matched": matched,
        "invariants": invariants, "observations": observations, "replays": replays}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{matched}/{len(observations)} local aggregate input cases matched across all three execution paths.")
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
        print("source-aggregate-check: interrupted", file=sys.stderr)
        raise SystemExit(1)
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(f"source-aggregate-check: {error}", file=sys.stderr)
        raise SystemExit(2)
    finally:
        signal.signal(signal.SIGTERM, previous_term)
