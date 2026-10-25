#!/usr/bin/env python3
"""Materialize and replay the fixed source corpus with the native Lean tool.

Coverage counts Core AST features and literal values. It does not measure
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
FEATURES = {"wordLiteral", "boolLiteral", "local", "let", "if"} | {
    f"unary:Solcore.Core.Wire.UnaryOp.{operation}"
    for operation in ("boolNot", "wordNot")
} | {
    f"binary:Solcore.Core.Wire.BinaryOp.{operation}"
    for operation in ("wordAdd", "wordSub", "wordMul", "wordAnd", "wordOr",
                      "wordXor", "wordEq", "wordGt")
}
LITERALS = {0, 1, (1 << 256) - 1, 1 << 255}


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


def materialize(entry: dict, tool: Path, directory: Path, fuel: int) -> dict:
    require(("generation" in entry) != ("program" in entry),
            f"{entry['id']}: choose a seed or a manual Core program")
    if "generation" in entry:
        generation = entry["generation"]
        seed = generation["seed"]
        require(isinstance(seed, str) and str(int(seed)) == seed and 0 <= int(seed) < 1 << 64,
                f"{entry['id']}: seed must be a canonical uint64 decimal string")
        nodes = generation["maxProgramNodes"]
        require(type(nodes) is int and 3 <= nodes <= 512,
                f"{entry['id']}: invalid node budget")
        corpus = run(tool, "generate", seed, str(nodes), "1", "1", str(fuel))
        require(corpus["status"] == "complete" and corpus["attempted"] == 1
                and not corpus["excluded"] and len(corpus["cases"]) == 1,
                f"{entry['id']}: fixed seed did not emit in its single allowed attempt")
        case = corpus["cases"][0]
        origin = case["provenance"]["origin"]
        require(origin["seed"] == seed and origin["maxProgramNodes"] == nodes,
                f"{entry['id']}: generated provenance differs from the manifest")
        return case
    path = directory / "program.json"
    path.write_text(json.dumps(entry["program"]))
    return run(tool, "emit", str(path), str(fuel))


def validate(manifest: dict, tool: Path, fuel: int) -> dict:
    require(manifest["schema"] == MANIFEST_SCHEMA, "unexpected corpus manifest schema")
    require(manifest["coverageKind"] == "core-ast-features", "coverage scope changed")
    require(set(manifest["requiredFeatures"]) == FEATURES,
            "required features do not cover the complete initial emitter subset")
    require({int(value) for value in manifest["requiredWordLiterals"]} == LITERALS,
            "required literals do not cover zero, one, maximum and the high bit")
    entries = manifest["cases"]
    identifiers = [entry["id"] for entry in entries]
    require(entries and len(set(identifiers)) == len(identifiers), "empty corpus or duplicate case id")
    covered_features, covered_literals = set(), set()
    with tempfile.TemporaryDirectory(prefix="semantic-corpus-") as name:
        directory = Path(name)
        for entry in entries:
            case = materialize(entry, tool, directory, fuel)
            require(case == materialize(entry, tool, directory, fuel),
                    f"{entry['id']}: materialization is not deterministic")
            for version in VERSIONS:
                require(case["provenance"][version] == manifest[version],
                        f"{entry['id']}: {version} changed")
            actual_features, actual_literals = ast_coverage(case["program"])
            require(actual_features == set(case["provenance"]["features"])
                    == set(entry["expectedFeatures"]),
                    f"{entry['id']}: declared features differ from the actual Core AST")
            direct = case["directCore"]
            require(direct["stage"] == "execution" and direct["status"] == "returned",
                    f"{entry['id']}: original Core did not return within the test budget")
            body = case["program"]["body"]
            if body["tag"] == "word":
                require(int(direct["word"]) == int(body["value"], 16),
                        f"{entry['id']}: literal observation disagrees with its original Core")
            path = directory / "case.json"
            path.write_text(json.dumps(case))
            require(run(tool, "replay", str(path), str(fuel)) == case,
                    f"{entry['id']}: native checked replay changed the case")
            covered_features.update(actual_features)
            covered_literals.update(actual_literals)
    require(FEATURES <= covered_features, "fixed corpus lost required AST feature coverage")
    require(LITERALS <= covered_literals, "fixed corpus lost required Word literal coverage")
    return {"status": "passed", "cases": len(entries), "coverageKind": "core-ast-features",
            "requiredFeatures": len(FEATURES), "requiredWordLiterals": len(LITERALS),
            "evmExecuted": False}


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
