#!/usr/bin/env python3
"""Check the fixed recursion corpus using fresh native Core executions.

Step features and helper counts are read independently from the original AST.
Shapes and depths are prescribed by the plan and the input, not measured
traces: this test recomputes each depth `input & mask` itself. Native replay
reconstructs both the checked canonical Core and source, and native shrinking
must retain that representation. This test neither compiles Rust nor executes
an EVM and implements no arithmetic result oracle.
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
spec = importlib.util.spec_from_file_location("recursion_corpus_ast", ROOT / "Tests/scripts/test-semantic-corpus.py")
pure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pure)
generic_spec = importlib.util.spec_from_file_location("recursion_corpus_generic", ROOT / "Tests/scripts/test-semantic-generic-corpus.py")
generic = importlib.util.module_from_spec(generic_spec)
generic_spec.loader.exec_module(generic)
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
complexity, returned, strings, integers = generic.complexity, generic.returned, generic.strings, generic.integers
VERSIONS = pure.VERSIONS + pure.MUTATION_VERSIONS + pure.LOOP_STEP_VERSIONS
FEATURES = generic.FEATURES
BOUNDARIES = (0, 1, 2, 3, 7, (1 << 256) - 1, 1 << 255)
FORMS = ("tail", "nontail", "mutual")
SHAPES = {f"{mask}:{form}" for form in FORMS for mask in (1, 3, 7)}
DEPTHS = {0, 1, 2, 3, 7}
CASE_SCHEMA = "solcore-lean.semantic-recursion-case.v1"
PLAN_SCHEMA = "solcore-lean.recursion-plan.v1"


def check_plan(plan):
    require(isinstance(plan, dict) and set(plan) == {"schema", "depthMask", "form", "stepProgram"}
            and plan["schema"] == PLAN_SCHEMA and plan["form"] in FORMS
            and type(plan["depthMask"]) is int and plan["depthMask"] in (0, 1, 3, 7), "invalid recursion plan")
    step = plan["stepProgram"]
    require(isinstance(step, dict) and set(step) == {"schema", "dataDefinitions", "resultType", "body"}
            and step["schema"] == "solcore-semantic-core" and step["dataDefinitions"] == []
            and step["resultType"] == {"tag": "function", "parameter": "word", "result": "word"},
            "recursion step must retain a closed Word function DAG")
    return pure.function_parts(step["body"])


def shape(plan):
    return f"{plan['depthMask']}:{plan['form']}"


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals",
              "requiredInputs", "requiredHelperCounts", "generationRecipeRequirements",
              "recursionRequirements", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == "runtime-recursion", "unexpected recursion manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "recursion AST coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    required = strings(manifest["requiredFeatures"], "requiredFeatures")
    require(required and required <= FEATURES, "unsupported step AST features")
    for value in strings(manifest["requiredWordLiterals"], "requiredWordLiterals"):
        canonical_word(value)
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "recursion corpus must require all seven boundary inputs")
    integers(manifest["requiredHelperCounts"], {1, 2, 3}, "requiredHelperCounts")
    recipe = manifest["generationRecipeRequirements"]
    require(isinstance(recipe, dict) and set(recipe) == {"templates", "updates"}, "invalid recipe requirements")
    integers(recipe["templates"], {0, 1, 2, 3}, "recipe templates")
    require(recipe["updates"] == [], "aggregate step has no mutable-update recipe dimension")
    recursion = manifest["recursionRequirements"]
    require(isinstance(recursion, dict) and set(recursion) == {"shapes", "depths"}, "invalid recursion requirements")
    require(strings(recursion["shapes"], "shapes") == SHAPES, "recursion corpus must require every generation shape")
    integers(recursion["depths"], DEPTHS, "depths")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "recursion corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"id", "generation", "input", "expectedFeatures"},
                "a recursion corpus entry is a generation recipe with its input and features")
        identifier = entry["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        require(canonical_word(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        expected = strings(entry["expectedFeatures"], "expectedFeatures")
        require(expected and expected <= FEATURES, "unsupported expected step feature")
        recipe = entry["generation"]
        require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
        require(canonical_word(recipe["seed"]) < 1 << 64, "seed exceeds uint64")
        require(type(recipe["maxProgramNodes"]) is int and 3 <= recipe["maxProgramNodes"] <= 512,
                "invalid full-program node budget")
    return entries


def check_case(case, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected recursion case schema")
    helpers, body = check_plan(case["recursionPlan"])
    number = canonical_word(case["input"])
    program = case["program"]
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == "word", "recursion reference must be a closed Word program")
    application = program["body"]
    require(application.get("tag") == "apply" and application.get("argument", {}).get("tag") == "word"
            and int(application["argument"]["value"], 16) == number, "original Core argument differs from runtime input")
    require(complexity(application)[0] + 2 <= 512, "canonical applied reference exceeds node limit")
    name = "SynthesizedRecursion"
    require(case["contract"] == {"name": name, "method": "run", "signature": "run(uint256)",
            "deployPath": [name + "Deploy"], "runtimePath": [name + "Deploy", name],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "recursion ABI, runtime input, or contract metadata changed")
    require(isinstance(case.get("source"), str) and case.get("executionFuel") == fuel, "invalid emitted source or fuel")
    return helpers, body


def depth(case):
    """The prescribed depth, recomputed from the plan and the input."""
    return int(case["input"]) & case["recursionPlan"]["depthMask"]


def materialize(entry, tool, fuel):
    recipe = entry["generation"]
    corpus = run(tool, "recursion-generate", recipe["seed"], str(recipe["maxProgramNodes"]), "7", "1", str(fuel))
    require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
            and corpus.get("requested") == 7 and corpus.get("attempted") == 1
            and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 7,
            "fixed recursion seed did not emit seven cases in one attempt")
    cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
    require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
    case = cases[0]
    origin, plan = case["provenance"]["origin"], case["recursionPlan"]
    require(origin.get("kind") == "recursion-generated" and origin.get("seed") == recipe["seed"]
            and origin.get("maxProgramNodes") == recipe["maxProgramNodes"]
            and origin.get("inputIndex") == BOUNDARIES.index(int(entry["input"]))
            and origin.get("validationFuel") == fuel
            and (origin.get("depthMask"), origin.get("form")) == (plan["depthMask"], plan["form"]),
            "generated recipe differs from manifest")
    require(complexity(case["program"]["body"])[0] + 2 <= recipe["maxProgramNodes"], "generation exceeded full-program budget")
    check_case(case, fuel)
    return case


def checked_shrinks(case, tool, directory, fuel):
    path = directory / "shrink-parent.json"
    path.write_text(json.dumps(case))
    reduced = run(tool, "shrink", str(path), "4", str(fuel))
    require(reduced == run(tool, "shrink", str(path), "4", str(fuel)), "native shrink order changed")
    candidates = reduced.get("cases")
    require(isinstance(candidates, list) and 0 < len(candidates) <= 4, "fixed recursion case has no bounded shrink candidates")
    parent, (parent_helpers, _) = case["recursionPlan"], check_plan(case["recursionPlan"])
    seen = set()
    for candidate in candidates:
        helpers, _ = check_case(candidate, fuel)
        plan = candidate["recursionPlan"]
        require(len(helpers) == len(parent_helpers) and plan["depthMask"] <= parent["depthMask"]
                and plan["form"] in (parent["form"], "tail"),
                "shrink changed the helper count, raised the depth mask or changed the form to another than tail")
        require(complexity(candidate["program"]["body"]) < complexity(case["program"]["body"]), "shrink did not strictly decrease")
        require(candidate["provenance"]["origin"]["kind"] == "reduced", "a shrink candidate is not a reduction")
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

    for key, value in (("profile", "runtime-loops"), ("requiredHelperCounts", [True, 2, 3]), ("requiredInputs", ["0"]),
                       ("recursionRequirements", {**manifest["recursionRequirements"], "shapes": ["7:tail"]}),
                       ("recursionRequirements", {**manifest["recursionRequirements"], "depths": [0, 7]})):
        changed = copy.deepcopy(manifest)
        changed[key] = value
        rejects(lambda: check_manifest(changed), key)
    path = directory / "negative.json"
    plan = sample["recursionPlan"]
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("depth mask", lambda value: value["recursionPlan"].update(depthMask=3 if plan["depthMask"] == 7 else 7)),
        ("form", lambda value: value["recursionPlan"].update(form="tail" if plan["form"] != "tail" else "mutual")),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="3" if value["input"] != "3" else "2")),
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
    for args in (("recursion-generate", str(1 << 64), "512", "7", "1", str(fuel)),
                 ("recursion-generate", "1", "513", "7", "1", str(fuel)),
                 ("recursion-generate", "1", "384", "7", "1", str(fuel), "exclude-boundary-identity-v1"),
                 ("shrink", str(path), "4097", str(fuel))):
        result = subprocess.run([str(tool), *args], cwd=ROOT, text=True, capture_output=True, timeout=30, check=False)
        require(result.returncode != 0, "native CLI accepted an out-of-range budget or an inapplicable filter")
        count += 1
    return count


def validate(manifest, tool, fuel):
    require(type(fuel) is int and 0 < fuel <= 10_000_000, "invalid positive execution fuel")
    entries = check_manifest(manifest)
    features, literals, inputs, helpers_seen, templates = (set() for _ in range(5))
    shapes, depths = set(), set()
    groups, samples = {}, {}
    with tempfile.TemporaryDirectory(prefix="semantic-recursion-corpus-") as name:
        directory = Path(name)
        for entry in entries:
            case = materialize(entry, tool, fuel)
            require(case == materialize(entry, tool, fuel), "materialization is not deterministic")
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
            number = int(case["input"])
            key = json.dumps(case["recursionPlan"], sort_keys=True)
            group = groups.setdefault(key, {"inputs": set(), "source": case["source"], "changed": False})
            require(group["source"] == case["source"], "identical recursion plan emitted input-dependent source")
            group["inputs"].add(number)
            group["changed"] |= int(result) != number
            origin = case["provenance"]["origin"]["stepOrigin"]
            metadata = origin.get("helpers")
            require(origin.get("kind") == "aggregate-generated" and isinstance(metadata, list)
                    and origin.get("helperCount") == len(helpers) == len(metadata), "recipe helper count differs from actual declarations")
            for helper in metadata:
                template = helper.get("template")
                require(type(template) is int and template in {0, 1, 2, 3}, "unknown step template")
                templates.add(template)
            if depth(case) > 0:
                samples.setdefault(case["recursionPlan"]["form"], case)
            # Only completed, replayed native cases contribute coverage.
            features.update(actual)
            literals.update(actual_literals)
            inputs.add(number)
            helpers_seen.add(len(helpers))
            shapes.add(shape(case["recursionPlan"]))
            depths.add(depth(case))
        require(features == set(manifest["requiredFeatures"]), "lost exact step feature union")
        require({int(value) for value in manifest["requiredWordLiterals"]} <= literals, "lost required literal inventory")
        require(inputs >= set(BOUNDARIES) and helpers_seen == {1, 2, 3} and templates == {0, 1, 2, 3}, "lost completed input/helper/recipe coverage")
        recursion = manifest["recursionRequirements"]
        require(shapes == set(recursion["shapes"]) and depths >= set(recursion["depths"]),
                "lost a completed recursion shape or prescribed depth")
        for group in groups.values():
            require(group["inputs"] >= set(BOUNDARIES), "recursion plan lacks a completed boundary input")
            require(group["changed"], "fixed recursion plan returned every boundary input unchanged")
        require(set(samples) == set(FORMS), "missing shrink/policy fixtures for every recursion form")
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in samples.values())
        checks = policy_checks(manifest, samples["mutual"], tool, directory, fuel)
    return {"status": "passed", "profile": "runtime-recursion", "cases": len(entries), "functionGroups": len(groups),
            "coverageKind": "step-core-ast-features", "requiredFeatures": len(features),
            "completedInputs": [str(value) for value in sorted(inputs)], "completedHelperCounts": sorted(helpers_seen),
            "generationRecipe": {"classification": "replayed-generator-metadata", "templates": sorted(templates), "updates": []},
            "recursionCoverage": {"classification": "prescribed-depths-not-execution-trace", "shapes": sorted(shapes),
                                  "depths": sorted(depths)},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path, default=ROOT / "scripts/semantic-recursion-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
