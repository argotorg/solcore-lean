#!/usr/bin/env python3
"""Check the fixed generic corpus using fresh native Core executions.

Step features and helper counts are read independently from the original AST.
Variant/parity pairs describe prescribed source instantiations, not measured
runtime traces. Native replay reconstructs both the checked canonical Core and
source, and native shrinking must retain that representation. This test neither
compiles Rust nor executes an EVM and implements no arithmetic result oracle.
"""
from __future__ import annotations

import argparse
import copy
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("generic_corpus_ast", ROOT / "Tests/scripts/test-semantic-corpus.py")
pure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pure)
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
VERSIONS = pure.VERSIONS + pure.MUTATION_VERSIONS + pure.LOOP_STEP_VERSIONS
FEATURES = pure.FEATURES | pure.MUTATION_FEATURES | pure.AGGREGATE_FEATURES | {"functionCall"}
BOUNDARIES = (0, 1, (1 << 256) - 1, 1 << 255)
VARIANTS = {"word", "pair", "sum"}
INSTANTIATIONS = {variant + ":" + parity for variant in VARIANTS for parity in ("even", "odd")}
CASE_SCHEMA = "solcore-lean.semantic-generic-case.v1"
PLAN_SCHEMA = "solcore-lean.generic-plan.v1"


def strings(value, label):
    require(isinstance(value, list) and all(isinstance(item, str) for item in value)
            and len(value) == len(set(value)), f"{label} must contain unique strings")
    return set(value)


def integers(value, expected, label):
    require(isinstance(value, list) and all(type(item) is int for item in value)
            and len(value) == len(set(value)) and set(value) == expected,
            f"{label} must contain exactly {sorted(expected)}")


def check_plan(plan):
    require(isinstance(plan, dict) and set(plan) == {"schema", "variant", "stepProgram"}
            and plan["schema"] == PLAN_SCHEMA and isinstance(plan["variant"], str)
            and plan["variant"] in VARIANTS, "invalid generic plan")
    step = plan["stepProgram"]
    require(isinstance(step, dict) and set(step) == {"schema", "dataDefinitions", "resultType", "body"}
            and step["schema"] == "solcore-semantic-core" and step["dataDefinitions"] == []
            and step["resultType"] == {"tag": "function", "parameter": "word", "result": "word"},
            "generic step must retain a closed Word function DAG")
    return pure.function_parts(step["body"])


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals",
              "requiredInputs", "requiredHelperCounts", "generationRecipeRequirements",
              "genericRequirements", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == "runtime-generics", "unexpected generic manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "generic AST coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    required = strings(manifest["requiredFeatures"], "requiredFeatures")
    require(required and required <= FEATURES, "unsupported step AST features")
    for value in strings(manifest["requiredWordLiterals"], "requiredWordLiterals"):
        canonical_word(value)
    require({canonical_word(value) for value in strings(manifest["requiredInputs"], "requiredInputs")}
            == set(BOUNDARIES), "generic corpus must require all four boundary inputs")
    integers(manifest["requiredHelperCounts"], {1, 2, 3}, "requiredHelperCounts")
    recipe = manifest["generationRecipeRequirements"]
    require(isinstance(recipe, dict) and set(recipe) == {"templates", "updates"}, "invalid recipe requirements")
    integers(recipe["templates"], {0, 1, 2, 3}, "recipe templates")
    require(recipe["updates"] == [], "aggregate step has no mutable-update recipe dimension")
    generic = manifest["genericRequirements"]
    require(isinstance(generic, dict) and set(generic) == {"instantiations"}
            and strings(generic["instantiations"], "instantiations") == INSTANTIATIONS,
            "generic corpus must require every variant/parity pair")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "generic corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict), "corpus entry must be an object")
        identifier = entry.get("id")
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        canonical_word(entry.get("input"))
        expected = strings(entry.get("expectedFeatures"), "expectedFeatures")
        require(expected and expected <= FEATURES, "unsupported expected step feature")
        base = {"id", "input", "expectedFeatures"}
        if "generation" in entry:
            require(set(entry) == base | {"generation"}, "choose a seed or an imported generic plan")
            recipe = entry["generation"]
            require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
            require(canonical_word(recipe["seed"]) < 1 << 64, "seed exceeds uint64")
            require(type(recipe["maxProgramNodes"]) is int and 3 <= recipe["maxProgramNodes"] <= 512,
                    "invalid full-program node budget")
            require(int(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        else:
            require(set(entry) == base | {"genericPlan"}, "imported generic case requires exactly one plan")
            check_plan(entry["genericPlan"])
    return entries


def type_nodes(value):
    if isinstance(value, str):
        require(value in {"word", "bool", "unit"}, "unexpected type in pure generic reference")
        return 1
    require(isinstance(value, dict) and value.get("tag") in {"product", "sum", "function"}, "unexpected compound type")
    keys = ("parameter", "result") if value["tag"] == "function" else ("left", "right")
    return 1 + sum(type_nodes(value[key]) for key in keys)


def complexity(expr):
    """Count Wire nodes and literal weight; never evaluate a program operation."""
    tag = expr["tag"]
    keys = {"let": ("initializer", "body"), "apply": ("function", "argument"),
            "pair": ("left", "right"), "binary": ("left", "right"),
            "storeCell": ("reference", "value"), "first": ("operand",), "second": ("operand",),
            "unary": ("operand",), "loadCell": ("reference",), "lambda": ("body",),
            "inLeft": ("payload",), "inRight": ("payload",), "newCell": ("initializer",),
            "if": ("condition", "thenBranch", "elseBranch"),
            "case": ("scrutinee", "leftBranch", "rightBranch")}
    require(tag in keys or tag in {"word", "bool", "unit", "var"}, "unexpected expression in generic reference")
    nodes, weight = 1, int(expr["value"], 16) if tag == "word" else int(expr["value"]) if tag == "bool" else 0
    for key in keys.get(tag, ()):
        child_nodes, child_weight = complexity(expr[key])
        nodes += child_nodes
        weight += child_weight
    if tag == "lambda":
        nodes += type_nodes(expr["parameterType"]) + type_nodes(expr["resultType"])
    if tag in {"inLeft", "inRight", "newCell"}:
        nodes += type_nodes(expr[{"inLeft": "rightType", "inRight": "leftType", "newCell": "elementType"}[tag]])
    return nodes, weight


def check_case(case, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected generic case schema")
    helpers, body = check_plan(case["genericPlan"])
    number = canonical_word(case["input"])
    program = case["program"]
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == "word", "generic reference must be a closed Word program")
    application = program["body"]
    require(application.get("tag") == "apply" and application.get("argument", {}).get("tag") == "word"
            and int(application["argument"]["value"], 16) == number, "original Core argument differs from runtime input")
    require(complexity(application)[0] + 2 <= 512, "canonical applied reference exceeds node limit")
    name = "SynthesizedGenerics"
    require(case["contract"] == {"name": name, "method": "run", "signature": "run(uint256)",
            "deployPath": [name + "Deploy"], "runtimePath": [name + "Deploy", name],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "generic ABI, runtime input, or contract metadata changed")
    require(isinstance(case.get("source"), str) and case.get("executionFuel") == fuel, "invalid emitted source or fuel")
    return helpers, body


def returned(observation):
    require(isinstance(observation, dict) and observation.get("stage") == "execution"
            and observation.get("status") == "returned", "original Core did not return within the native budget")
    canonical_word(observation.get("word"))
    return observation["word"]


def materialize(entry, tool, directory, fuel):
    if "generation" in entry:
        recipe = entry["generation"]
        corpus = run(tool, "generic-generate", recipe["seed"], str(recipe["maxProgramNodes"]), "4", "1", str(fuel))
        require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
                and corpus.get("requested") == 4 and corpus.get("attempted") == 1
                and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 4,
                "fixed generic seed did not emit four cases in one attempt")
        cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
        require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
        case = cases[0]
        origin = case["provenance"]["origin"]
        require(origin.get("kind") == "generic-generated" and origin.get("seed") == recipe["seed"]
                and origin.get("maxProgramNodes") == recipe["maxProgramNodes"]
                and origin.get("inputIndex") == BOUNDARIES.index(int(entry["input"]))
                and origin.get("validationFuel") == fuel
                and origin.get("variant") == case["genericPlan"]["variant"], "generated recipe differs from manifest")
        require(complexity(case["program"]["body"])[0] + 2 <= recipe["maxProgramNodes"], "generation exceeded full-program budget")
    else:
        path = directory / "plan.json"
        path.write_text(json.dumps(entry["genericPlan"]))
        case = run(tool, "generic-emit", str(path), entry["input"], str(fuel))
        require(case["genericPlan"] == entry["genericPlan"], "emission changed the imported plan")
    check_case(case, fuel)
    require(case["input"] == entry["input"], "emission changed the recorded input")
    return case


def policy_checks(manifest, sample, tool, directory, fuel):
    count = 0

    def rejects(action, label):
        nonlocal count
        try:
            action()
        except ValueError:
            count += 1
        else:
            raise ValueError("negative check accepted " + label)

    for key, value in (("profile", "runtime-aggregates"), ("genericRequirements", {"instantiations": ["word:odd"]}),
                       ("requiredHelperCounts", [True, 2, 3]), ("requiredInputs", ["0"])):
        changed = copy.deepcopy(manifest)
        changed[key] = value
        rejects(lambda: check_manifest(changed), key)
    path = directory / "negative.json"
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("plan variant", lambda value: value["genericPlan"].update(variant="sum" if value["genericPlan"]["variant"] != "sum" else "word")),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="3")),
        ("wrapper", lambda value: value["contract"].update(name="AnotherContract")),
        ("profile version", lambda value: value["provenance"].update(profileVersion="another-version")),
    ):
        changed = copy.deepcopy(sample)
        change(changed)
        path.write_text(json.dumps(changed))
        result = subprocess.run([str(tool), "replay", str(path), str(fuel)], cwd=ROOT,
                                text=True, capture_output=True, timeout=30, check=False)
        require(result.returncode != 0, "native replay accepted altered " + label)
        count += 1
    forged = copy.deepcopy(sample)
    forged["directCore"] = {"stage": "execution", "status": "returned", "word": "999"}
    path.write_text(json.dumps(forged))
    require(run(tool, "replay", str(path), str(fuel)) == sample, "native replay trusted saved execution evidence")
    count += 1
    path.write_text(json.dumps(sample))
    lower = run(tool, "replay", str(path), "0")
    require(lower["program"] == sample["program"] and lower["source"] == sample["source"]
            and lower["directCore"].get("status") == "out-of-fuel", "zero budget changed canonical code or invented completion")
    rejects(lambda: returned(lower["directCore"]), "resource result as feature coverage")
    for args in (("generic-generate", str(1 << 64), "512", "4", "1", str(fuel)),
                 ("generic-generate", "1", "513", "4", "1", str(fuel)),
                 ("shrink", str(path), "4097", str(fuel))):
        result = subprocess.run([str(tool), *args], cwd=ROOT, text=True, capture_output=True, timeout=30, check=False)
        require(result.returncode != 0, "native CLI accepted an out-of-range budget")
        count += 1
    return count


def checked_shrinks(case, tool, directory, fuel):
    path = directory / "shrink-parent.json"
    path.write_text(json.dumps(case))
    reduced = run(tool, "shrink", str(path), "4", str(fuel))
    require(reduced == run(tool, "shrink", str(path), "4", str(fuel)), "native shrink order changed")
    candidates = reduced.get("cases")
    require(isinstance(candidates, list) and 0 < len(candidates) <= 4, "fixed generic case has no bounded shrink candidates")
    parent_helpers, _ = check_plan(case["genericPlan"])
    seen = set()
    for candidate in candidates:
        helpers, _ = check_case(candidate, fuel)
        require(len(helpers) == len(parent_helpers) and candidate["genericPlan"]["variant"] == case["genericPlan"]["variant"],
                "shrink changed declared helper count or generic instantiation")
        require(complexity(candidate["program"]["body"]) < complexity(case["program"]["body"]), "shrink did not strictly decrease")
        encoded = json.dumps(candidate["program"], sort_keys=True)
        require(encoded not in seen, "duplicate canonical shrink")
        seen.add(encoded)
        target = directory / "shrunk.json"
        target.write_text(json.dumps(candidate))
        require(run(tool, "replay", str(target), str(fuel)) == candidate, "native shrink lost canonical source/program/provenance")
        fresh = run(tool, "observe", str(target), str(fuel))
        returned(fresh)
        require(fresh == candidate["directCore"], "shrunk observation differs from fresh Core execution")
    return len(candidates)


def validate(manifest, tool, fuel):
    require(type(fuel) is int and 0 < fuel <= 10_000_000, "invalid positive execution fuel")
    entries = check_manifest(manifest)
    features, literals, inputs, helpers_seen, templates, instantiations = (set() for _ in range(6))
    groups, samples = {}, {}
    with tempfile.TemporaryDirectory(prefix="semantic-generic-corpus-") as name:
        directory = Path(name)
        for entry in entries:
            case = materialize(entry, tool, directory, fuel)
            require(case == materialize(entry, tool, directory, fuel), "materialization is not deterministic")
            for version in VERSIONS:
                require(case["provenance"][version] == manifest[version], f"{version} changed")
            helpers, body = check_case(case, fuel)
            actual, _ = pure.ast_coverage(helpers + [body], function_calls=True, mutable_cells=True, aggregates=True)
            require(actual == set(case["provenance"]["features"]) == set(entry["expectedFeatures"]), "declared features differ from the step AST")
            _, actual_literals = pure.ast_coverage(case["program"])
            path = directory / "case.json"
            path.write_text(json.dumps(case))
            before = run(tool, "observe", str(path), str(fuel))
            result = returned(before)
            require(before == case["directCore"], "saved observation differs from fresh original Core")
            replayed = run(tool, "replay", str(path), str(fuel))
            require(replayed == case, "native canonical replay changed the case")
            path.write_text(json.dumps(replayed))
            require(run(tool, "observe", str(path), str(fuel)) == before, "repeated native observation differs")
            variant = case["genericPlan"]["variant"]
            number = int(case["input"])
            key = json.dumps(case["genericPlan"], sort_keys=True)
            group = groups.setdefault(key, {"inputs": set(), "source": case["source"], "results": set()})
            require(group["source"] == case["source"], "identical generic plan emitted input-dependent source")
            group["inputs"].add(number)
            group["results"].add(result)
            if "generation" in entry:
                origin = case["provenance"]["origin"]["stepOrigin"]
                metadata = origin.get("helpers")
                require(origin.get("kind") == "aggregate-generated" and isinstance(metadata, list)
                        and origin.get("helperCount") == len(helpers) == len(metadata), "recipe helper count differs from actual declarations")
                for helper in metadata:
                    template = helper.get("template")
                    require(type(template) is int and template in {0, 1, 2, 3}, "unknown step template")
                    templates.add(template)
            elif number == 1 << 255:
                samples.setdefault(variant, case)
            # Only completed, replayed native cases contribute coverage.
            features.update(actual)
            literals.update(actual_literals)
            inputs.add(number)
            helpers_seen.add(len(helpers))
            instantiations.add(variant + (":odd" if number & 1 else ":even"))
        require(features == set(manifest["requiredFeatures"]), "lost exact step feature union")
        require({int(value) for value in manifest["requiredWordLiterals"]} <= literals, "lost required literal inventory")
        require(inputs >= set(BOUNDARIES) and helpers_seen == {1, 2, 3} and templates == {0, 1, 2, 3}, "lost completed input/helper/recipe coverage")
        require(instantiations == INSTANTIATIONS, "lost completed prescribed generic instantiation")
        for group in groups.values():
            require(group["inputs"] >= set(BOUNDARIES), "generic plan lacks a completed boundary input")
            require(len(group["results"]) >= 2, "fixed generic plan produced only a constant boundary result")
        require(set(samples) == VARIANTS, "missing imported shrink/policy fixtures")
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in samples.values())
        checks = policy_checks(manifest, samples["word"], tool, directory, fuel)
    return {"status": "passed", "profile": "runtime-generics", "cases": len(entries), "functionGroups": len(groups),
            "coverageKind": "step-core-ast-features", "requiredFeatures": len(features),
            "completedInputs": [str(value) for value in sorted(inputs)], "completedHelperCounts": sorted(helpers_seen),
            "generationRecipe": {"classification": "replayed-generator-metadata", "templates": sorted(templates), "updates": []},
            "genericCoverage": {"classification": "prescribed-variant-parity-not-execution-trace", "instantiations": sorted(instantiations)},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path, default=ROOT / "scripts/semantic-generic-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
