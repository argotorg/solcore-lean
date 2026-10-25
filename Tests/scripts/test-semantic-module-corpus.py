#!/usr/bin/env python3
"""Replay checked reference ASTs and their canonical four-module source bundle.

Constant and step features are separate syntax inventories. Even/odd recipe
labels are prescribed by inputs, not measured branch traces. Native replay
reconstructs every provider and the complete original Core; this validator also
checks bundle paths, entry alias, strict shrinking and typed binder preservation.
It neither compiles Rust nor executes an EVM, and computes no arithmetic oracle.
Filesystem/export/archive transport is tested separately by the adapter suite.
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
spec = importlib.util.spec_from_file_location("module_corpus_ast", ROOT / "Tests/scripts/test-semantic-corpus.py")
pure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pure)
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
VERSIONS = pure.VERSIONS + pure.MUTATION_VERSIONS + pure.LOOP_STEP_VERSIONS
FEATURES = pure.FEATURES | pure.MUTATION_FEATURES | pure.AGGREGATE_FEATURES | {"functionCall"}
BOUNDARIES = (0, 1, (1 << 256) - 1, 1 << 255)
BRANCHES = {"even", "odd"}
SOURCE_PATHS = ["case.sol", "common.sol", "left.sol", "right.sol"]
WRAPPER_NODES = 160
CASE_SCHEMA = "solcore-lean.semantic-module-case.v1"
PLAN_SCHEMA = "solcore-lean.module-plan.v1"


def strings(value, label):
    require(isinstance(value, list) and all(isinstance(item, str) for item in value)
            and len(value) == len(set(value)), f"{label} must contain unique strings")
    return set(value)


def integers(value, expected, label):
    require(isinstance(value, list) and all(type(item) is int for item in value)
            and len(value) == len(set(value)) and set(value) == expected,
            f"{label} must contain exactly {sorted(expected)}")


def check_plan(plan):
    require(isinstance(plan, dict) and set(plan) == {"schema", "constantProgram", "stepProgram"}
            and plan["schema"] == PLAN_SCHEMA, "invalid module plan")
    constant = plan["constantProgram"]
    require(isinstance(constant, dict) and set(constant) == {"schema", "dataDefinitions", "resultType", "body"}
            and constant["schema"] == "solcore-semantic-core" and constant["dataDefinitions"] == []
            and constant["resultType"] == "word", "constant must retain its original closed Word program")
    constant_features, _ = pure.ast_coverage(constant["body"])
    require(constant_features and constant_features <= pure.FEATURES, "unsupported constant AST feature")
    step = plan["stepProgram"]
    require(isinstance(step, dict) and set(step) == {"schema", "dataDefinitions", "resultType", "body"}
            and step["schema"] == "solcore-semantic-core" and step["dataDefinitions"] == []
            and step["resultType"] == {"tag": "function", "parameter": "word", "result": "word"},
            "module step must retain a closed Word function DAG")
    return pure.function_parts(step["body"])


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals",
              "requiredInputs", "requiredHelperCounts", "generationRecipeRequirements",
              "requiredConstantFeatures", "moduleRequirements", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == "runtime-modules", "unexpected module manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "module AST coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    required = strings(manifest["requiredFeatures"], "requiredFeatures")
    require(required and required <= FEATURES, "unsupported step AST features")
    require(strings(manifest["requiredConstantFeatures"], "requiredConstantFeatures") == pure.FEATURES,
            "fixed module corpus must cover all supported constant AST features")
    for value in strings(manifest["requiredWordLiterals"], "requiredWordLiterals"):
        canonical_word(value)
    require({canonical_word(value) for value in strings(manifest["requiredInputs"], "requiredInputs")}
            == set(BOUNDARIES), "module corpus must require all four boundary inputs")
    integers(manifest["requiredHelperCounts"], {1, 2, 3}, "requiredHelperCounts")
    recipe = manifest["generationRecipeRequirements"]
    require(isinstance(recipe, dict) and set(recipe) == {"templates", "updates"}, "invalid recipe requirements")
    integers(recipe["templates"], {0, 1, 2, 3}, "recipe templates")
    require(recipe["updates"] == [], "aggregate step has no mutable-update recipe dimension")
    module = manifest["moduleRequirements"]
    require(isinstance(module, dict) and set(module) == {"branches"}
            and strings(module["branches"], "branches") == BRANCHES,
            "module corpus must require both prescribed input parities")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "module corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict), "corpus entry must be an object")
        identifier = entry.get("id")
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        canonical_word(entry.get("input"))
        expected = strings(entry.get("expectedFeatures"), "expectedFeatures")
        require(expected and expected <= FEATURES, "unsupported expected step feature")
        constant_expected = strings(entry.get("expectedConstantFeatures"), "expectedConstantFeatures")
        require(constant_expected and constant_expected <= pure.FEATURES, "unsupported expected constant feature")
        base = {"id", "input", "expectedFeatures", "expectedConstantFeatures"}
        if "generation" in entry:
            require(set(entry) == base | {"generation"}, "choose a seed or an imported module plan")
            recipe = entry["generation"]
            require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
            require(canonical_word(recipe["seed"]) < 1 << 64, "seed exceeds uint64")
            require(type(recipe["maxProgramNodes"]) is int and 3 <= recipe["maxProgramNodes"] <= 512,
                    "invalid full-program node budget")
            require(int(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        else:
            require(set(entry) == base | {"modulePlan"}, "imported module case requires exactly one plan")
            check_plan(entry["modulePlan"])
    return entries


measure_spec = importlib.util.spec_from_file_location(
    "module_corpus_measure", ROOT / "Tests/scripts/test-semantic-generic-corpus.py")
measure = importlib.util.module_from_spec(measure_spec)
measure_spec.loader.exec_module(measure)
complexity = measure.complexity


binding_spec = importlib.util.spec_from_file_location(
    "module_corpus_bindings", ROOT / "Tests/scripts/test-semantic-comptime-corpus.py")
bindings = importlib.util.module_from_spec(binding_spec)
binding_spec.loader.exec_module(bindings)
step_bindings = bindings.step_bindings


def check_bundle(case):
    bundle = case.get("sourceBundle")
    require(isinstance(bundle, dict) and set(bundle) == {"schema", "entry", "files"}
            and bundle["schema"] == "solcore-lean.source-bundle.v1" and bundle["entry"] == "case.sol",
            "module case requires its canonical source bundle and entry")
    files = bundle["files"]
    require(isinstance(files, list) and len(files) == len(SOURCE_PATHS), "module bundle requires four providers")
    for item, expected in zip(files, SOURCE_PATHS):
        require(isinstance(item, dict) and set(item) == {"path", "source"}
                and item["path"] == expected and isinstance(item["source"], str) and item["source"],
                "bundle paths must be unique, sorted, flat canonical source names")
    require(case.get("source") == files[0]["source"], "entry source alias differs from case.sol")
    return bundle


def check_case(case, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected module case schema")
    helpers, body = check_plan(case["modulePlan"])
    number = canonical_word(case["input"])
    program = case["program"]
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == "word", "module reference must be a closed Word program")
    application = program["body"]
    require(application.get("tag") == "apply" and application.get("argument", {}).get("tag") == "word"
            and int(application["argument"]["value"], 16) == number, "original Core argument differs from runtime input")
    require(complexity(application)[0] + 2 <= 512, "canonical applied reference exceeds node limit")
    # Independently check retention and binding order; native replay additionally
    # checks the entire mixed generic/closure/staging wrapper.
    constant_bind = application.get("function", {})
    step_bind = constant_bind.get("body", {})
    require(constant_bind.get("tag") == "let"
            and constant_bind.get("initializer") == case["modulePlan"]["constantProgram"]["body"]
            and step_bind.get("tag") == "let"
            and step_bind.get("initializer") == case["modulePlan"]["stepProgram"]["body"],
            "canonical reference substituted a computed constant or reordered its original bindings")
    name = "SynthesizedModules"
    require(case["contract"] == {"name": name, "method": "run", "signature": "run(uint256)",
            "deployPath": [name + "Deploy"], "runtimePath": [name + "Deploy", name],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "module ABI, runtime input, or contract metadata changed")
    require(isinstance(case.get("source"), str) and case.get("executionFuel") == fuel, "invalid emitted source or fuel")
    check_bundle(case)
    return helpers, body


def returned(observation):
    require(isinstance(observation, dict) and observation.get("stage") == "execution"
            and observation.get("status") == "returned", "original Core did not return within the native budget")
    canonical_word(observation.get("word"))
    return observation["word"]


def materialize(entry, tool, directory, fuel):
    if "generation" in entry:
        recipe = entry["generation"]
        corpus = run(tool, "module-generate", recipe["seed"], str(recipe["maxProgramNodes"]), "4", "1", str(fuel))
        require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
                and corpus.get("requested") == 4 and corpus.get("attempted") == 1
                and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 4,
                "fixed module seed did not emit four cases in one attempt")
        cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
        require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
        case = cases[0]
        origin = case["provenance"]["origin"]
        require(origin.get("kind") == "module-generated" and origin.get("seed") == recipe["seed"]
                and origin.get("maxProgramNodes") == recipe["maxProgramNodes"]
                and origin.get("inputIndex") == BOUNDARIES.index(int(entry["input"]))
                and origin.get("validationFuel") == fuel, "generated recipe differs from manifest")
        require(complexity(case["program"]["body"])[0] + 2 <= recipe["maxProgramNodes"], "generation exceeded full-program budget")
        constant_origin = origin.get("constantOrigin", {})
        # Count the retained syntax rather than assuming constant/step size is
        # included in a generator budget. Native replay checks the full wrapper.
        overhead = (complexity(case["program"]["body"])[0] + 2
                    - (complexity(case["modulePlan"]["constantProgram"]["body"])[0] + 2)
                    - (complexity(case["modulePlan"]["stepProgram"]["body"])[0] + 4))
        require(overhead == WRAPPER_NODES, "module wrapper syntax budget changed")
        available = recipe["maxProgramNodes"] - overhead
        constant_budget = min(8, available // 8)
        require(constant_origin.get("kind") == "generated"
                and constant_origin.get("seed") == str((int(recipe["seed"]) + 104729) % (1 << 64))
                and constant_origin.get("maxProgramNodes") == constant_budget,
                "constant generator recipe differs from its prescribed seed/node partition")
        constant_features, _ = pure.ast_coverage(case["modulePlan"]["constantProgram"]["body"])
        require(any(feature.startswith(("unary:", "binary:")) for feature in constant_features),
                "generated constant contains no actual operation")
        require(complexity(case["modulePlan"]["constantProgram"]["body"])[0] + 2 <= constant_budget,
                "generated constant exceeded its own node budget")
    else:
        path = directory / "plan.json"
        path.write_text(json.dumps(entry["modulePlan"]))
        case = run(tool, "module-emit", str(path), entry["input"], str(fuel))
        require(case["modulePlan"] == entry["modulePlan"], "emission changed the imported plan")
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

    for key, value in (("profile", "runtime-aggregates"), ("moduleRequirements", {"branches": ["even"]}),
                       ("requiredHelperCounts", [True, 2, 3]), ("requiredInputs", ["0"]),
                       ("requiredConstantFeatures", ["wordLiteral"])):
        changed = copy.deepcopy(manifest)
        changed[key] = value
        rejects(lambda: check_manifest(changed), key)
    path = directory / "negative.json"
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("unknown plan variant", lambda value: value["modulePlan"].update(variant="offset")),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="3")),
        ("wrapper", lambda value: value["contract"].update(name="AnotherContract")),
        ("profile version", lambda value: value["provenance"].update(profileVersion="another-version")),
        ("constant features", lambda value: value["provenance"].update(constantFeatures=["wordLiteral"])),
        ("step features", lambda value: value["provenance"].update(features=["wordLiteral"])),
        ("constant AST", lambda value: value["modulePlan"]["constantProgram"].update(body={"tag": "word", "value": "0x0"})),
        ("open constant", lambda value: value["modulePlan"]["constantProgram"].update(body={"tag": "var", "index": 0})),
        ("provider contents", lambda value: value["sourceBundle"]["files"][1].update(source="// altered common provider\n")),
        ("provider import graph", lambda value: value["sourceBundle"]["files"][2].update(source=value["sourceBundle"]["files"][2]["source"] + "\nimport * from unlisted;\n")),
        ("missing provider", lambda value: value["sourceBundle"]["files"].pop()),
        ("extra provider", lambda value: value["sourceBundle"]["files"].append({"path": "extra.sol", "source": "// unlisted\n"})),
        ("duplicate provider", lambda value: value["sourceBundle"]["files"][1].update(path="case.sol")),
        ("provider order", lambda value: value["sourceBundle"]["files"].reverse()),
        ("entry", lambda value: value["sourceBundle"].update(entry="left.sol")),
        ("path traversal", lambda value: value["sourceBundle"]["files"][1].update(path="../common.sol")),
        ("absolute provider", lambda value: value["sourceBundle"]["files"][1].update(path="/tmp/common.sol")),
        ("provider case alias", lambda value: value["sourceBundle"]["files"][1].update(path="Common.sol")),
        ("bundle schema", lambda value: value["sourceBundle"].update(schema="another-bundle")),
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
    require(lower["program"] == sample["program"] and lower["sourceBundle"] == sample["sourceBundle"]
            and lower["source"] == sample["source"]
            and lower["directCore"].get("status") == "out-of-fuel", "zero budget changed canonical code or invented completion")
    rejects(lambda: returned(lower["directCore"]), "resource result as feature coverage")
    for args in (("module-generate", str(1 << 64), "512", "4", "1", str(fuel)),
                 ("module-generate", "1", "513", "4", "1", str(fuel)),
                 ("shrink", str(path), "4097", str(fuel))):
        result = subprocess.run([str(tool), *args], cwd=ROOT, text=True, capture_output=True, timeout=30, check=False)
        require(result.returncode != 0, "native CLI accepted an out-of-range budget")
        count += 1
    return count


def checked_shrinks(case, tool, directory, fuel):
    path = directory / "shrink-parent.json"
    path.write_text(json.dumps(case))
    # Constant reductions precede runtime-step reductions. Read a bounded prefix
    # large enough to exercise both, then replay a small sample from each class.
    reduced = run(tool, "shrink", str(path), "128", str(fuel))
    require(reduced == run(tool, "shrink", str(path), "128", str(fuel)), "native shrink order changed")
    candidates = reduced.get("cases")
    require(isinstance(candidates, list) and 0 < len(candidates) <= 128, "fixed module case has no bounded shrink candidates")
    parent_helpers, _ = check_plan(case["modulePlan"])
    parent_bindings = step_bindings(case["modulePlan"]["stepProgram"])
    seen, selected = set(), {"constant": [], "step": [], "input": []}
    for candidate in candidates:
        helpers, _ = check_case(candidate, fuel)
        require(len(helpers) == len(parent_helpers), "shrink changed declared helper count")
        require(step_bindings(candidate["modulePlan"]["stepProgram"]) == parent_bindings,
                "shrink changed a typed let or case-payload binder")
        require(complexity(candidate["program"]["body"]) < complexity(case["program"]["body"]), "shrink did not strictly decrease")
        encoded = json.dumps(candidate["program"], sort_keys=True)
        require(encoded not in seen, "duplicate canonical shrink")
        seen.add(encoded)
        plan = candidate["modulePlan"]
        category = ("constant" if plan["constantProgram"] != case["modulePlan"]["constantProgram"]
                    else "step" if plan["stepProgram"] != case["modulePlan"]["stepProgram"] else "input")
        if len(selected[category]) < 2:
            selected[category].append(candidate)
    require(all(selected.values()), "fixed shrink sample did not reduce constant, step and runtime input independently")
    for candidate in [value for group in selected.values() for value in group]:
        target = directory / "shrunk.json"
        target.write_text(json.dumps(candidate))
        require(run(tool, "replay", str(target), str(fuel)) == candidate, "native shrink lost canonical source/program/provenance")
        fresh = run(tool, "observe", str(target), str(fuel))
        returned(fresh)
        require(fresh == candidate["directCore"], "shrunk observation differs from fresh Core execution")
    return sum(map(len, selected.values()))


def validate(manifest, tool, fuel):
    require(type(fuel) is int and 0 < fuel <= 10_000_000, "invalid positive execution fuel")
    entries = check_manifest(manifest)
    features, constants, literals, inputs, helpers_seen, templates, branches = (set() for _ in range(7))
    groups, samples = {}, {}
    with tempfile.TemporaryDirectory(prefix="semantic-module-corpus-") as name:
        directory = Path(name)
        for entry in entries:
            case = materialize(entry, tool, directory, fuel)
            require(case == materialize(entry, tool, directory, fuel), "materialization is not deterministic")
            for version in VERSIONS:
                require(case["provenance"][version] == manifest[version], f"{version} changed")
            helpers, body = check_case(case, fuel)
            actual, _ = pure.ast_coverage(helpers + [body], function_calls=True, mutable_cells=True, aggregates=True)
            require(actual == set(case["provenance"]["features"]) == set(entry["expectedFeatures"]), "declared features differ from the step AST")
            actual_constants, _ = pure.ast_coverage(case["modulePlan"]["constantProgram"]["body"])
            require(actual_constants == set(case["provenance"]["constantFeatures"]) == set(entry["expectedConstantFeatures"]),
                    "declared constant features differ from the original closed AST")
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
            key = json.dumps(case["modulePlan"], sort_keys=True)
            group = groups.setdefault(key, {"inputs": set(), "sourceBundle": case["sourceBundle"], "results": set()})
            require(group["sourceBundle"] == case["sourceBundle"], "identical module plan emitted input-dependent source bundle")
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
                samples[key] = case
            # Only completed, replayed native cases contribute coverage.
            features.update(actual)
            constants.update(actual_constants)
            literals.update(actual_literals)
            inputs.add(number)
            helpers_seen.add(len(helpers))
            branches.add("odd" if number % 2 else "even")
        require(features == set(manifest["requiredFeatures"]), "lost exact step feature union")
        require(constants == set(manifest["requiredConstantFeatures"]), "lost exact constant feature union")
        require({int(value) for value in manifest["requiredWordLiterals"]} <= literals, "lost required literal inventory")
        require(inputs >= set(BOUNDARIES) and helpers_seen == {1, 2, 3} and templates == {0, 1, 2, 3}, "lost completed input/helper/recipe coverage")
        require(branches == BRANCHES, "lost completed prescribed module input parity")
        for group in groups.values():
            require(group["inputs"] >= set(BOUNDARIES), "module plan lacks a completed boundary input")
            require(len(group["results"]) >= 2, "fixed module plan produced only a constant boundary result")
        selected = sorted(samples.values(), key=lambda case: complexity(case["modulePlan"]["constantProgram"]["body"]), reverse=True)[:2]
        require(len(selected) == 2, "missing imported shrink/policy fixtures")
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in selected)
        checks = policy_checks(manifest, selected[0], tool, directory, fuel)
    return {"status": "passed", "profile": "runtime-modules", "cases": len(entries), "functionGroups": len(groups),
            "coverageKind": "step-core-ast-features", "requiredFeatures": len(features),
            "completedInputs": [str(value) for value in sorted(inputs)], "completedHelperCounts": sorted(helpers_seen),
            "generationRecipe": {"classification": "replayed-generator-metadata", "templates": sorted(templates), "updates": []},
            "moduleCoverage": {"classification": "prescribed-input-parity-not-execution-trace", "branches": sorted(branches)},
            "sourceBundle": {"entry": "case.sol", "files": SOURCE_PATHS},
            "constantCoverage": {"classification": "original-constant-core-ast-features", "features": sorted(constants)},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path, default=ROOT / "scripts/semantic-module-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
