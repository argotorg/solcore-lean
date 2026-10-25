#!/usr/bin/env python3
"""Check emitted G0 source through the pinned Rust frontend and Lean Hull runtime.

This is an emitter integration check, not EVM differential testing. Explicit
mapping cases and a bounded generated corpus retain their original Core result.
Every emitted source must pass checked Rust compilation and return exactly the
same ABI Word through the imported Hull runtime. Temporary exports are removed.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
MAX_WORD = (1 << 256) - 1


def word(value: int) -> dict:
    return {"tag": "word", "value": f"0x{value:064x}"}


def boolean(value: bool) -> dict:
    return {"tag": "bool", "value": value}


def variable(index: int) -> dict:
    return {"tag": "var", "index": index}


def unary(operation: str, operand: dict) -> dict:
    return {"tag": "unary", "op": operation, "operand": operand}


def binary(operation: str, left: dict, right: dict) -> dict:
    return {"tag": "binary", "op": operation, "left": left, "right": right}


def conditional(condition: dict, yes: dict, no: dict) -> dict:
    return {"tag": "if", "condition": condition, "thenBranch": yes, "elseBranch": no}


def binding(initializer: dict, body: dict) -> dict:
    return {"tag": "let", "initializer": initializer, "body": body}


def as_word(condition: dict) -> dict:
    return conditional(condition, word(1), word(0))


def mapping_cases() -> list[tuple[str, dict, int]]:
    cases = [(f"literal-{name}", word(value), value) for name, value in [
        ("zero", 0), ("one", 1), ("maximum", MAX_WORD),
        ("high-bit", 1 << 255), ("below-high-bit", (1 << 255) - 1)]]
    for name, operation, left, right, expected in [
        ("add-wrap", "wordAdd", MAX_WORD, 1, 0),
        ("add-zero", "wordAdd", 0, 1, 1),
        ("subtract-wrap", "wordSub", 0, 1, MAX_WORD),
        ("subtract-order", "wordSub", 7, 3, 4),
        ("multiply-wrap", "wordMul", 1 << 255, 2, 0),
        ("multiply-zero", "wordMul", MAX_WORD, 0, 0),
        ("and", "wordAnd", 252, 10, 8),
        ("or", "wordOr", 252, 10, 254),
        ("xor", "wordXor", 252, 10, 246),
    ]:
        cases.append((name, binary(operation, word(left), word(right)), expected))
    for name, operation, left, right, expected in [
        ("equal-true", "wordEq", MAX_WORD, MAX_WORD, 1),
        ("equal-false", "wordEq", 0, 1, 0),
        ("greater-unsigned", "wordGt", 1 << 255, 1, 1),
        ("greater-order", "wordGt", 1, 1 << 255, 0),
        ("greater-equal", "wordGt", MAX_WORD, MAX_WORD, 0),
    ]:
        cases.append((name, as_word(binary(operation, word(left), word(right))), expected))
    cases += [
        ("word-not-zero", unary("wordNot", word(0)), MAX_WORD),
        ("word-not-maximum", unary("wordNot", word(MAX_WORD)), 0),
        ("bool-not-false", as_word(unary("boolNot", boolean(False))), 1),
        ("bool-not-true", as_word(unary("boolNot", boolean(True))), 0),
        ("nested-bindings", binding(word(7), binding(
            binary("wordAdd", variable(0), word(2)),
            binary("wordSub", variable(0), variable(1)))), 2),
        ("bool-branches", as_word(conditional(boolean(False), boolean(False),
            unary("boolNot", boolean(False)))), 1),
    ]
    for flag in [False, True]:
        body = binding(word(7), conditional(boolean(flag),
            binding(word(11), binary("wordAdd", variable(0), variable(1))),
            binding(word(3), binary("wordSub", variable(1), variable(0)))))
        cases.append((f"branch-scope-{str(flag).lower()}", body, 18 if flag else 4))
    return cases


def run(command: list[str], timeout: float) -> subprocess.CompletedProcess:
    process = subprocess.Popen(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except BaseException:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.communicate()
        raise
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


def run_json(command: list[str], timeout: float) -> dict:
    result = run(command, timeout)
    if result.returncode:
        raise ValueError(f"command failed ({result.returncode}): {command}\n{result.stdout}{result.stderr}")
    return json.loads(result.stdout)


def validate(case: dict, directory: Path, args: argparse.Namespace) -> dict:
    if case.get("schema") != "solcore-lean.semantic-case.v1":
        raise ValueError("unexpected semantic case schema")
    direct = case["directCore"]
    if direct.get("stage") != "execution" or direct.get("status") != "returned":
        raise ValueError(f"direct Core did not complete: {direct}")
    expected = f"0x{int(direct['word']):064x}"
    source = directory / "main.sol"
    source.write_text(case["source"])
    exported = directory / "hull.json"
    result = run([sys.executable, str(ROOT / "scripts/export-rust-hull.py"), str(source),
                  "--upstream", str(args.upstream), "--output", str(exported)], args.timeout)
    if result.returncode:
        return {"status": "source-rejected", "exitCode": result.returncode,
                "detail": result.stdout + result.stderr, "case": case}
    provenance = json.loads(exported.with_suffix(".json.provenance.json").read_text())
    contract = case["contract"]
    observation = run([str(args.hull_runner), str(exported),
                       "/".join(contract["runtimePath"]), contract["calldata"]], args.timeout)
    try:
        actual = json.loads(observation.stdout)
    except json.JSONDecodeError:
        actual = {"status": "adapter-error", "detail": observation.stdout + observation.stderr}
    matched = (observation.returncode == 0 and actual.get("stage") == "execution"
               and actual.get("status") == "returned" and actual.get("output") == expected
               and actual.get("storage") == [])
    return {"status": "matched" if matched else "failed", "expected": expected,
            "actual": actual, "exitCode": observation.returncode, "case": case,
            "exportProvenance": provenance}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--hull-runner", type=Path, default=ROOT / ".lake/build/bin/rust-hull-contract")
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--generated", type=int, default=12)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--nodes", type=int, default=24)
    parser.add_argument("--attempts", type=int, default=512)
    parser.add_argument("--fuel", type=int, default=1000000)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--output", type=Path, help="save the full validation report and replay cases")
    args = parser.parse_args()
    if min(args.generated, args.seed, args.nodes, args.attempts, args.fuel) < 0 or args.timeout <= 0:
        parser.error("budgets must be nonnegative and timeout must be positive")
    args.case_tool = args.case_tool.resolve()
    args.hull_runner = args.hull_runner.resolve()
    args.upstream = args.upstream.resolve()
    for binary in [args.case_tool, args.hull_runner]:
        if not binary.is_file():
            raise ValueError(f"missing {binary}; build semanticCaseTool and rustHullContract first")
    observations = []
    with tempfile.TemporaryDirectory(prefix="source-synthesis-check-", dir=ROOT / ".upstream") as name:
        temporary = Path(name)
        cases = []
        for label, body, expected in mapping_cases():
            program = {"schema": "solcore-semantic-core", "resultType": "word",
                       "dataDefinitions": [], "body": body}
            path = temporary / "program.json"
            path.write_text(json.dumps(program))
            case = run_json([str(args.case_tool), "emit", str(path), str(args.fuel)], args.timeout)
            if case.get("directCore", {}).get("word") != str(expected):
                raise ValueError(f"mapping fixture {label} disagrees with its direct Core result: {case}")
            cases.append((label, case))
        generated = (run_json([str(args.case_tool), "generate", str(args.seed), str(args.nodes),
                               str(args.generated), str(args.attempts), str(args.fuel)], args.timeout)
                     if args.generated else {"status": "complete", "cases": [], "attempted": 0, "excluded": []})
        if generated.get("status") != "complete" or len(generated["cases"]) != args.generated:
            raise ValueError(f"generated corpus was not completed: {generated}")
        cases.extend((f"generated-{index}", case) for index, case in enumerate(generated["cases"]))
        for index, (label, case) in enumerate(cases):
            directory = temporary / str(index)
            directory.mkdir()
            observation = {"id": label, **validate(case, directory, args)}
            observations.append(observation)
            print(f"{label}: {observation['status']}", flush=True)
    matched = sum(row["status"] == "matched" for row in observations)
    report = {"schema": "solcore-lean.source-emission-check.v1", "evmExecuted": False,
              "passed": matched == len(observations), "total": len(observations), "matched": matched,
              "generationAttempted": generated["attempted"], "generationExcluded": generated["excluded"],
              "observations": observations}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{matched}/{len(observations)} emitted programs passed checked Rust compilation and matched on Core.")
    if not report["passed"] and not args.output:
        print(json.dumps([row for row in observations if row["status"] != "matched"], indent=2))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(f"source-synthesis-check: {error}", file=sys.stderr)
        raise SystemExit(2)
