#!/usr/bin/env python3
"""Replay original constant and runtime ASTs with the native Core machine.

Constant features and runtime step features are separate syntax inventories;
neither is an execution trace. Every plan retains its original closed constant
expression and is exercised with four runtime boundary inputs. Native replay
reconstructs both the checked canonical Core and source, and native shrinking
must preserve that representation. This test neither compiles Rust nor executes
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
spec = importlib.util.spec_from_file_location("comptime_corpus_ast", ROOT / "Tests/scripts/test-semantic-corpus.py")
pure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pure)
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
VERSIONS = pure.VERSIONS + pure.MUTATION_VERSIONS + pure.LOOP_STEP_VERSIONS
FEATURES = pure.FEATURES | pure.MUTATION_FEATURES | pure.AGGREGATE_FEATURES | {"functionCall"}
BOUNDARIES = (0, 1, (1 << 256) - 1, 1 << 255)
VARIANTS = {"offset", "scale"}
CASE_SCHEMA = "solcore-lean.semantic-comptime-case.v1"
PLAN_SCHEMA = "solcore-lean.comptime-plan.v1"


def strings(value, label):
    require(isinstance(value, list) and all(isinstance(item, str) for item in value)
            and len(value) == len(set(value)), f"{label} must contain unique strings")
    return set(value)


def integers(value, expected, label):
    require(isinstance(value, list) and all(type(item) is int for item in value)
            and len(value) == len(set(value)) and set(value) == expected,
            f"{label} must contain exactly {sorted(expected)}")


def check_plan(plan):
    require(isinstance(plan, dict) and set(plan) == {"schema", "variant", "constantProgram", "stepProgram"}
            and plan["schema"] == PLAN_SCHEMA and isinstance(plan["variant"], str)
            and plan["variant"] in VARIANTS, "invalid comptime plan")
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
            "comptime step must retain a closed Word function DAG")
    return pure.function_parts(step["body"])


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals",
              "requiredInputs", "requiredHelperCounts", "generationRecipeRequirements",
              "requiredConstantFeatures", "comptimeRequirements", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == "runtime-comptime", "unexpected comptime manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "comptime AST coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    required = strings(manifest["requiredFeatures"], "requiredFeatures")
    require(required and required <= FEATURES, "unsupported step AST features")
    require(strings(manifest["requiredConstantFeatures"], "requiredConstantFeatures") == pure.FEATURES,
            "fixed comptime corpus must cover all supported constant AST features")
    for value in strings(manifest["requiredWordLiterals"], "requiredWordLiterals"):
        canonical_word(value)
    require({canonical_word(value) for value in strings(manifest["requiredInputs"], "requiredInputs")}
            == set(BOUNDARIES), "comptime corpus must require all four boundary inputs")
    integers(manifest["requiredHelperCounts"], {1, 2, 3}, "requiredHelperCounts")
    recipe = manifest["generationRecipeRequirements"]
    require(isinstance(recipe, dict) and set(recipe) == {"templates", "updates"}, "invalid recipe requirements")
    integers(recipe["templates"], {0, 1, 2, 3}, "recipe templates")
    require(recipe["updates"] == [], "aggregate step has no mutable-update recipe dimension")
    comptime = manifest["comptimeRequirements"]
    require(isinstance(comptime, dict) and set(comptime) == {"variants"}
            and strings(comptime["variants"], "variants") == VARIANTS,
            "comptime corpus must require both comptime variants")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "comptime corpus must contain cases")
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
            require(set(entry) == base | {"generation"}, "choose a seed or an imported comptime plan")
            recipe = entry["generation"]
            require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
            require(canonical_word(recipe["seed"]) < 1 << 64, "seed exceeds uint64")
            require(type(recipe["maxProgramNodes"]) is int and 3 <= recipe["maxProgramNodes"] <= 512,
                    "invalid full-program node budget")
            require(int(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        else:
            require(set(entry) == base | {"comptimePlan"}, "imported comptime case requires exactly one plan")
            check_plan(entry["comptimePlan"])
    return entries


measure_spec = importlib.util.spec_from_file_location(
    "comptime_corpus_measure", ROOT / "Tests/scripts/test-semantic-generic-corpus.py")
measure = importlib.util.module_from_spec(measure_spec)
measure_spec.loader.exec_module(measure)
complexity = measure.complexity


def step_bindings(program):
    """Read typed binder kinds without evaluating any arithmetic operation."""
    def walk(expr, locals_):
        tag = expr["tag"]
        if tag in {"word", "bool", "unit"}:
            return tag, []
        if tag == "var":
            index = expr["index"]
            require(type(index) is int and 0 <= index < len(locals_), "open step variable")
            return locals_[index], []
        if tag == "let":
            kind, initial = walk(expr["initializer"], locals_)
            require(kind != "function", "step helper escaped into an ordinary let")
            result, body = walk(expr["body"], [kind, *locals_])
            return result, initial + ["let:" + kind] + body
        if tag == "case":
            kind, scrutinee = walk(expr["scrutinee"], locals_)
            left, left_bindings = walk(expr["leftBranch"], ["word", *locals_])
            right, right_bindings = walk(expr["rightBranch"], ["word", *locals_])
            require(kind == "sum" and left == right, "invalid case payload/branch types")
            return left, scrutinee + ["leftPayload"] + left_bindings + ["rightPayload"] + right_bindings
        keys = {"if": ("condition", "thenBranch", "elseBranch"),
                "binary": ("left", "right"), "pair": ("left", "right"),
                "apply": ("function", "argument"), "storeCell": ("reference", "value"),
                "unary": ("operand",), "first": ("operand",), "second": ("operand",),
                "newCell": ("initializer",), "loadCell": ("reference",),
                "inLeft": ("payload",), "inRight": ("payload",)}
        require(tag in keys, "unsupported step constructor")
        values = [walk(expr[key], locals_) for key in keys[tag]]
        kinds = [kind for kind, _ in values]
        bindings = [binding for _, group in values for binding in group]
        if tag == "if":
            require(kinds[0] == "bool" and kinds[1] == kinds[2], "invalid conditional types")
            return kinds[1], bindings
        if tag == "binary":
            require(kinds == ["word", "word"], "invalid scalar binary operands")
            return ("bool" if expr["op"] in {"wordEq", "wordGt"} else "word"), bindings
        if tag == "unary":
            kind = "bool" if expr["op"] == "boolNot" else "word"
            require(kinds == [kind], "invalid scalar unary operand")
            return kind, bindings
        expected, result = {
            "pair": (["word", "word"], "pair"), "first": (["pair"], "word"),
            "second": (["pair"], "word"), "inLeft": (["word"], "sum"),
            "inRight": (["word"], "sum"), "newCell": (["word"], "cell"),
            "loadCell": (["cell"], "word"), "storeCell": (["cell", "word"], "unit"),
            "apply": (["function", "word"], "word")}[tag]
        require(kinds == expected, "invalid typed step operands")
        return result, bindings

    helpers, entry = pure.function_parts(program["body"])
    inventory = []
    for index, body in [*enumerate(helpers), (len(helpers), entry)]:
        result, bindings = walk(body, ["word"] + ["function"] * index)
        require(result == "word", "step helper or entry does not return a Word")
        inventory.extend(bindings)
    return inventory


def check_case(case, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected comptime case schema")
    helpers, body = check_plan(case["comptimePlan"])
    number = canonical_word(case["input"])
    program = case["program"]
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == "word", "comptime reference must be a closed Word program")
    application = program["body"]
    require(application.get("tag") == "apply" and application.get("argument", {}).get("tag") == "word"
            and int(application["argument"]["value"], 16) == number, "original Core argument differs from runtime input")
    require(complexity(application)[0] + 2 <= 512, "canonical applied reference exceeds node limit")
    # Independently check retention and binding order; native replay additionally
    # checks the entire wrapper, including the selected offset/scale body.
    constant_bind = application.get("function", {})
    step_bind = constant_bind.get("body", {})
    require(constant_bind.get("tag") == "let"
            and constant_bind.get("initializer") == case["comptimePlan"]["constantProgram"]["body"]
            and step_bind.get("tag") == "let"
            and step_bind.get("initializer") == case["comptimePlan"]["stepProgram"]["body"],
            "canonical reference substituted a computed constant or reordered its original bindings")
    name = "SynthesizedComptime"
    require(case["contract"] == {"name": name, "method": "run", "signature": "run(uint256)",
            "deployPath": [name + "Deploy"], "runtimePath": [name + "Deploy", name],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "comptime ABI, runtime input, or contract metadata changed")
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
        corpus = run(tool, "comptime-generate", recipe["seed"], str(recipe["maxProgramNodes"]), "4", "1", str(fuel))
        require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
                and corpus.get("requested") == 4 and corpus.get("attempted") == 1
                and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 4,
                "fixed comptime seed did not emit four cases in one attempt")
        cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
        require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
        case = cases[0]
        origin = case["provenance"]["origin"]
        require(origin.get("kind") == "comptime-generated" and origin.get("seed") == recipe["seed"]
                and origin.get("maxProgramNodes") == recipe["maxProgramNodes"]
                and origin.get("inputIndex") == BOUNDARIES.index(int(entry["input"]))
                and origin.get("validationFuel") == fuel
                and origin.get("variant") == case["comptimePlan"]["variant"], "generated recipe differs from manifest")
        require(complexity(case["program"]["body"])[0] + 2 <= recipe["maxProgramNodes"], "generation exceeded full-program budget")
        constant_origin = origin.get("constantOrigin", {})
        overhead = {"offset": 10, "scale": 12}[case["comptimePlan"]["variant"]]
        available = recipe["maxProgramNodes"] - overhead
        constant_budget = min(8, available // 8)
        require(constant_origin.get("kind") == "generated"
                and constant_origin.get("seed") == str((int(recipe["seed"]) + 104729) % (1 << 64))
                and constant_origin.get("maxProgramNodes") == constant_budget,
                "constant generator recipe differs from its prescribed seed/node partition")
        constant_features, _ = pure.ast_coverage(case["comptimePlan"]["constantProgram"]["body"])
        require(any(feature.startswith(("unary:", "binary:")) for feature in constant_features),
                "generated constant contains no actual operation")
        require(complexity(case["comptimePlan"]["constantProgram"]["body"])[0] + 2 <= constant_budget,
                "generated constant exceeded its own node budget")
    else:
        path = directory / "plan.json"
        path.write_text(json.dumps(entry["comptimePlan"]))
        case = run(tool, "comptime-emit", str(path), entry["input"], str(fuel))
        require(case["comptimePlan"] == entry["comptimePlan"], "emission changed the imported plan")
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

    for key, value in (("profile", "runtime-aggregates"), ("comptimeRequirements", {"variants": ["offset"]}),
                       ("requiredHelperCounts", [True, 2, 3]), ("requiredInputs", ["0"]),
                       ("requiredConstantFeatures", ["wordLiteral"])):
        changed = copy.deepcopy(manifest)
        changed[key] = value
        rejects(lambda: check_manifest(changed), key)
    path = directory / "negative.json"
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("plan variant", lambda value: value["comptimePlan"].update(variant="scale" if value["comptimePlan"]["variant"] == "offset" else "offset")),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="3")),
        ("wrapper", lambda value: value["contract"].update(name="AnotherContract")),
        ("profile version", lambda value: value["provenance"].update(profileVersion="another-version")),
        ("constant features", lambda value: value["provenance"].update(constantFeatures=["wordLiteral"])),
        ("step features", lambda value: value["provenance"].update(features=["wordLiteral"])),
        ("constant AST", lambda value: value["comptimePlan"]["constantProgram"].update(body={"tag": "word", "value": "0x0"})),
        ("open constant", lambda value: value["comptimePlan"]["constantProgram"].update(body={"tag": "var", "index": 0})),
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
    for args in (("comptime-generate", str(1 << 64), "512", "4", "1", str(fuel)),
                 ("comptime-generate", "1", "513", "4", "1", str(fuel)),
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
    require(isinstance(candidates, list) and 0 < len(candidates) <= 128, "fixed comptime case has no bounded shrink candidates")
    parent_helpers, _ = check_plan(case["comptimePlan"])
    parent_bindings = step_bindings(case["comptimePlan"]["stepProgram"])
    seen, selected = set(), {"constant": [], "step": [], "input": []}
    for candidate in candidates:
        helpers, _ = check_case(candidate, fuel)
        require(len(helpers) == len(parent_helpers) and candidate["comptimePlan"]["variant"] == case["comptimePlan"]["variant"],
                "shrink changed declared helper count or comptime instantiation")
        require(step_bindings(candidate["comptimePlan"]["stepProgram"]) == parent_bindings,
                "shrink changed a typed let or case-payload binder")
        require(complexity(candidate["program"]["body"]) < complexity(case["program"]["body"]), "shrink did not strictly decrease")
        encoded = json.dumps(candidate["program"], sort_keys=True)
        require(encoded not in seen, "duplicate canonical shrink")
        seen.add(encoded)
        plan = candidate["comptimePlan"]
        category = ("constant" if plan["constantProgram"] != case["comptimePlan"]["constantProgram"]
                    else "step" if plan["stepProgram"] != case["comptimePlan"]["stepProgram"] else "input")
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
    features, constants, literals, inputs, helpers_seen, templates, variants = (set() for _ in range(7))
    groups, samples = {}, {}
    with tempfile.TemporaryDirectory(prefix="semantic-comptime-corpus-") as name:
        directory = Path(name)
        for entry in entries:
            case = materialize(entry, tool, directory, fuel)
            require(case == materialize(entry, tool, directory, fuel), "materialization is not deterministic")
            for version in VERSIONS:
                require(case["provenance"][version] == manifest[version], f"{version} changed")
            helpers, body = check_case(case, fuel)
            actual, _ = pure.ast_coverage(helpers + [body], function_calls=True, mutable_cells=True, aggregates=True)
            require(actual == set(case["provenance"]["features"]) == set(entry["expectedFeatures"]), "declared features differ from the step AST")
            actual_constants, _ = pure.ast_coverage(case["comptimePlan"]["constantProgram"]["body"])
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
            variant = case["comptimePlan"]["variant"]
            number = int(case["input"])
            key = json.dumps(case["comptimePlan"], sort_keys=True)
            group = groups.setdefault(key, {"inputs": set(), "source": case["source"], "results": set()})
            require(group["source"] == case["source"], "identical comptime plan emitted input-dependent source")
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
                previous = samples.get(variant)
                if previous is None or complexity(case["comptimePlan"]["constantProgram"]["body"]) > complexity(previous["comptimePlan"]["constantProgram"]["body"]):
                    samples[variant] = case
            # Only completed, replayed native cases contribute coverage.
            features.update(actual)
            constants.update(actual_constants)
            literals.update(actual_literals)
            inputs.add(number)
            helpers_seen.add(len(helpers))
            variants.add(variant)
        require(features == set(manifest["requiredFeatures"]), "lost exact step feature union")
        require(constants == set(manifest["requiredConstantFeatures"]), "lost exact constant feature union")
        require({int(value) for value in manifest["requiredWordLiterals"]} <= literals, "lost required literal inventory")
        require(inputs >= set(BOUNDARIES) and helpers_seen == {1, 2, 3} and templates == {0, 1, 2, 3}, "lost completed input/helper/recipe coverage")
        require(variants == VARIANTS, "lost completed prescribed comptime instantiation")
        for group in groups.values():
            require(group["inputs"] >= set(BOUNDARIES), "comptime plan lacks a completed boundary input")
            require(len(group["results"]) >= 2, "fixed comptime plan produced only a constant boundary result")
        require(set(samples) == VARIANTS, "missing imported shrink/policy fixtures")
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in samples.values())
        checks = policy_checks(manifest, samples["offset"], tool, directory, fuel)
    return {"status": "passed", "profile": "runtime-comptime", "cases": len(entries), "functionGroups": len(groups),
            "coverageKind": "step-core-ast-features", "requiredFeatures": len(features),
            "completedInputs": [str(value) for value in sorted(inputs)], "completedHelperCounts": sorted(helpers_seen),
            "generationRecipe": {"classification": "replayed-generator-metadata", "templates": sorted(templates), "updates": []},
            "comptimeCoverage": {"classification": "prescribed-comptime-variant-not-execution-trace", "variants": sorted(variants)},
            "constantCoverage": {"classification": "original-constant-core-ast-features", "features": sorted(constants)},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path, default=ROOT / "scripts/semantic-comptime-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
