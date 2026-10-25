#!/usr/bin/env python3
"""Materialize and replay the fixed source corpus with the native Lean tool.

Coverage counts Core AST features and literal values. Runtime-input cases count
features in the function body, independently of the applied input literal, and
require completed observations for input coverage. This does not measure
executed EVM opcodes or prove source-emitter meaning preservation.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
MANIFEST_SCHEMA = "solcore-lean.semantic-corpus-manifest.v1"
VERSIONS = ("generatorVersion", "emitterVersion", "wrapperVersion")
INPUT_VERSIONS = ("profileVersion", "functionVersion", "abstractionVersion")
FEATURES = {"wordLiteral", "boolLiteral", "local", "let", "if"} | {
    f"unary:Solcore.Core.Wire.UnaryOp.{operation}"
    for operation in ("boolNot", "wordNot")
} | {
    f"binary:Solcore.Core.Wire.BinaryOp.{operation}"
    for operation in ("wordAdd", "wordSub", "wordMul", "wordAnd", "wordOr",
                      "wordXor", "wordEq", "wordGt")
}
LITERALS = {0, 1, (1 << 256) - 1, 1 << 255}
BOUNDARIES = (0, 1, (1 << 256) - 1, 1 << 255)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def run(tool: Path, *arguments: str) -> dict:
    result = subprocess.run([str(tool), *arguments], cwd=ROOT, text=True,
                            capture_output=True, timeout=30, check=False)
    require(result.returncode == 0,
            f"native case tool failed: {result.stdout}{result.stderr}")
    return json.loads(result.stdout)


def ast_coverage(value: object) -> tuple[set[str], set[int]]:
    features, literals = set(), set()
    if isinstance(value, dict):
        tag = value.get("tag")
        simple = {"word": "wordLiteral", "bool": "boolLiteral", "var": "local",
                  "let": "let", "if": "if"}
        if tag in simple:
            features.add(simple[tag])
        if tag == "word":
            literals.add(int(value["value"], 16))
        if tag in ("unary", "binary"):
            constructor = "UnaryOp" if tag == "unary" else "BinaryOp"
            features.add(f"{tag}:Solcore.Core.Wire.{constructor}.{value['op']}")
        children = value.values()
    elif isinstance(value, list):
        children = value
    else:
        children = []
    for child in children:
        child_features, child_literals = ast_coverage(child)
        features.update(child_features)
        literals.update(child_literals)
    return features, literals


def canonical_word(value: object) -> int:
    require(isinstance(value, str) and value.isascii() and value.isdecimal(),
            "Word must be a canonical decimal string")
    number = int(value)
    require(str(number) == value and 0 <= number < 1 << 256,
            "Word must be canonical and within 256 bits")
    return number


def scalar_body(case: dict, runtime_input: bool) -> dict:
    program = case["program"]
    if not runtime_input:
        require(case["schema"] == "solcore-lean.semantic-case.v1", "unexpected closed case schema")
        return program["body"]
    require(case["schema"] == "solcore-lean.semantic-input-case.v1", "unexpected input case schema")
    application = program["body"]
    function = application.get("function", {})
    argument = application.get("argument", {})
    require(program["resultType"] == "word" and program["dataDefinitions"] == []
            and application["tag"] == "apply" and function.get("tag") == "lambda"
            and function.get("parameterType") == "word" and function.get("resultType") == "word"
            and argument.get("tag") == "word", "input case is not a closed Word function application")
    number = canonical_word(case["input"])
    require(int(argument["value"], 16) == number, "applied Core argument differs from runtime input")
    require(case["contract"]["calldata"] == f"0xa444f5e9{number:064x}",
            "ABI argument differs from runtime input")
    return function["body"]


def materialize(entry: dict, tool: Path, directory: Path, fuel: int,
                profile: str = "closed-g0") -> dict:
    require(("generation" in entry) != ("program" in entry),
            f"{entry['id']}: choose a seed or a manual Core program")
    runtime_input = profile == "runtime-word"
    if runtime_input:
        canonical_word(entry["input"])
    if "generation" in entry:
        generation = entry["generation"]
        seed = generation["seed"]
        require(isinstance(seed, str) and str(int(seed)) == seed and 0 <= int(seed) < 1 << 64,
                f"{entry['id']}: seed must be a canonical uint64 decimal string")
        nodes = generation["maxProgramNodes"]
        require(type(nodes) is int and 3 <= nodes <= 512,
                f"{entry['id']}: invalid node budget")
        count = 4 if runtime_input else 1
        corpus = run(tool, "input-generate" if runtime_input else "generate", seed,
                     str(nodes), str(count), "1", str(fuel))
        require(corpus["status"] == "complete" and corpus["attempted"] == 1
                and not corpus["excluded"] and len(corpus["cases"]) == count,
                f"{entry['id']}: fixed seed did not emit in its single allowed attempt")
        matches = [case for case in corpus["cases"]
                   if not runtime_input or case["input"] == entry["input"]]
        require(len(matches) == 1, f"{entry['id']}: fixed seed did not emit the requested input")
        case = matches[0]
        origin = case["provenance"]["origin"]
        require(origin["seed"] == seed and origin["maxProgramNodes"] == nodes,
                f"{entry['id']}: generated provenance differs from the manifest")
        if runtime_input:
            require(origin["inputIndex"] == BOUNDARIES.index(int(entry["input"]))
                    and origin["validationFuel"] == fuel,
                    f"{entry['id']}: generated input/validation budget differs from the manifest")
        return case
    path = directory / "program.json"
    path.write_text(json.dumps(entry["program"]))
    if runtime_input:
        return run(tool, "input-emit", str(path), entry["input"], str(fuel))
    return run(tool, "emit", str(path), str(fuel))


def validate(manifest: dict, tool: Path, fuel: int) -> dict:
    require(isinstance(manifest, dict), "manifest must be an object")
    require(manifest["schema"] == MANIFEST_SCHEMA, "unexpected corpus manifest schema")
    profile = manifest.get("profile", "closed-g0")
    require(profile in ("closed-g0", "runtime-word"), "unsupported corpus profile")
    runtime_input = profile == "runtime-word"
    require(manifest["coverageKind"] == "core-ast-features", "coverage scope changed")
    for name in ("requiredFeatures", "requiredWordLiterals") + (("requiredInputs",) if runtime_input else ()):
        require(isinstance(manifest.get(name), list) and
                all(isinstance(value, str) for value in manifest[name]), f"{name} must be a string array")
    required_features = set(manifest["requiredFeatures"])
    required_literals = {canonical_word(value) for value in manifest["requiredWordLiterals"]}
    required_inputs = ({canonical_word(value) for value in manifest["requiredInputs"]}
                       if runtime_input else set())
    if runtime_input:
        require(required_features and required_features <= FEATURES, "unsupported runtime body features")
        require(required_inputs == set(BOUNDARIES), "runtime corpus must require all four boundary inputs")
    else:
        require(required_features == FEATURES,
                "required features do not cover the complete initial emitter subset")
        require(required_literals == LITERALS,
                "required literals do not cover zero, one, maximum and the high bit")
    entries = manifest["cases"]
    identifiers = [entry["id"] for entry in entries]
    require(entries and len(set(identifiers)) == len(identifiers), "empty corpus or duplicate case id")
    covered_features, covered_literals, covered_inputs = set(), set(), set()
    function_groups = {}
    with tempfile.TemporaryDirectory(prefix="semantic-corpus-") as name:
        directory = Path(name)
        for entry in entries:
            case = materialize(entry, tool, directory, fuel, profile)
            require(case == materialize(entry, tool, directory, fuel, profile),
                    f"{entry['id']}: materialization is not deterministic")
            for version in VERSIONS + (INPUT_VERSIONS if runtime_input else ()):
                require(case["provenance"][version] == manifest[version],
                        f"{entry['id']}: {version} changed")
            body = scalar_body(case, runtime_input)
            actual_features, actual_literals = ast_coverage(body)
            if runtime_input:
                # Literal inventory covers the full original program; input
                # execution coverage remains a separate obligation below.
                _, actual_literals = ast_coverage(case["program"])
            require(actual_features == set(case["provenance"]["features"])
                    == set(entry["expectedFeatures"]),
                    f"{entry['id']}: declared features differ from the actual Core AST")
            direct = case["directCore"]
            require(direct["stage"] == "execution" and direct["status"] == "returned",
                    f"{entry['id']}: original Core did not return within the test budget")
            canonical_word(direct["word"])
            if body["tag"] == "word":
                require(int(direct["word"]) == int(body["value"], 16),
                        f"{entry['id']}: literal observation disagrees with its original Core")
            path = directory / "case.json"
            path.write_text(json.dumps(case))
            require(run(tool, "replay", str(path), str(fuel)) == case,
                    f"{entry['id']}: native checked replay changed the case")
            covered_features.update(actual_features)
            covered_literals.update(actual_literals)
            if runtime_input:
                number = canonical_word(case["input"])
                require(case["input"] == entry["input"], "materialized input differs from manifest")
                covered_inputs.add(number)
                key = json.dumps(body, sort_keys=True, separators=(",", ":"))
                group = function_groups.setdefault(key, {"inputs": set(), "sources": set(), "results": set()})
                group["inputs"].add(number)
                group["sources"].add(case["source"])
                group["results"].add(direct["word"])
    require(required_features <= covered_features, "fixed corpus lost required AST feature coverage")
    require(required_literals <= covered_literals, "fixed corpus lost required Word literal coverage")
    if runtime_input:
        require(covered_features == required_features, "runtime feature requirements must name exactly this corpus's union")
        require(required_inputs <= covered_inputs, "fixed corpus lost required completed runtime inputs")
        for group in function_groups.values():
            require(set(BOUNDARIES) <= group["inputs"], "a runtime function lacks a completed boundary input")
            require(len(group["sources"]) == 1, "one runtime function emitted input-dependent source")
            require(len(group["results"]) >= 2, "a fixed runtime function returned only one boundary result")
    report = {"status": "passed", "profile": profile, "cases": len(entries),
              "coverageKind": "core-ast-features", "requiredFeatures": len(required_features),
              "requiredWordLiterals": len(required_literals), "evmExecuted": False}
    if runtime_input:
        report.update(requiredInputs=len(required_inputs), completedInputs=sorted(covered_inputs),
                      functionGroups=len(function_groups))
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=ROOT / "scripts/semantic-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    require(0 < args.fuel <= 10_000_000, "fuel must be positive and within the native tool limit")
    report = validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel)
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
