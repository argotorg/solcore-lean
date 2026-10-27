#!/usr/bin/env python3
"""Check the fixed inline Yul corpus using fresh native Core executions.

The corpus is built from the primitive corpus: its distinct hand-specified
functions, in corpus order, in three consecutive groups, each group combined by
a balanced XOR tree into one function, rendered in each form at the eight
boundary inputs. Those functions read the input in the operand positions they
test and shift only by the input or by a literal count below 2^64, unlike the
generated functions whose constant counts of at least 2^64 crash Sonatina
code-image export (recorded locally), so the corpus does not track that known
upstream defect; random campaigns still generate them. This test rebuilds the construction, emits and replays every entry
natively, reads the features independently from the original AST, recomputes
each form's coverage, and checks reductions and tampering. It neither compiles
Rust nor executes an EVM and implements no arithmetic result oracle; the
primitive corpus's goldens check the same Core operations.
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
spec = importlib.util.spec_from_file_location("assembly_corpus_ast", ROOT / "Tests/scripts/test-semantic-corpus.py")
pure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pure)
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
VERSIONS = (*pure.VERSIONS, *pure.INPUT_VERSIONS, "functionProfileVersion", "baseGeneratorVersion", "boundaryVersion")
FEATURES = pure.FEATURES | pure.PRIMITIVE_FEATURES
BOUNDARIES = (0, 1, 2, 255, 256, (1 << 256) - 1, 1 << 255, (1 << 255) - 1)
FORMS = ("switch", "if", "operations")
GROUPS = 3
CASE_SCHEMA = "solcore-lean.semantic-assembly-case.v1"
PLAN_SCHEMA = "solcore-lean.assembly-plan.v1"
NAME = "SynthesizedAssembly"
SHIFTS = {"wordShl", "wordShr", "wordSar"}
CHILDREN = {"word": (), "bool": (), "var": (), "if": ("condition", "thenBranch", "elseBranch"),
            "unary": ("operand",), "binary": ("left", "right"), "ternary": ("first", "second", "third")}


def reads_input(expression, scope):
    """Whether a G0 expression reads the input; `scope` says, nearest binding
    first, whether each local reads it."""
    tag = expression["tag"]
    if tag == "var":
        return scope[expression["index"]]
    if tag == "let":
        return reads_input(expression["body"], [reads_input(expression["initializer"], scope), *scope])
    return any(reads_input(expression[key], scope) for key in CHILDREN[tag])


def large_constant_shift(expression, scope):
    """Whether some shift's count neither reads the input nor is a literal below
    2^64. Core `wordShl(v, n)` shifts `v` by `n`."""
    tag = expression["tag"]
    if tag == "binary" and expression["op"] in SHIFTS:
        count = expression["right"]
        if not reads_input(count, scope) and not (count["tag"] == "word" and int(count["value"], 16) < 1 << 64):
            return True
    if tag == "let":
        return (large_constant_shift(expression["initializer"], scope)
                or large_constant_shift(expression["body"], [reads_input(expression["initializer"], scope), *scope]))
    return any(large_constant_shift(expression[key], scope) for key in CHILDREN[tag])


def xor_tree(bodies):
    if len(bodies) == 1:
        return bodies[0]
    middle = (len(bodies) + 1) // 2
    return {"tag": "binary", "op": "wordXor", "left": xor_tree(bodies[:middle]), "right": xor_tree(bodies[middle:])}


def construction(primitive):
    """The plans by form and group in corpus order, and the boundary inputs."""
    bodies, seen = [], set()
    for entry in primitive["cases"]:
        key = json.dumps(entry["program"], sort_keys=True)
        if key not in seen:
            seen.add(key)
            bodies.append(entry["program"]["body"]["body"])
    inputs = [str(value) for value in BOUNDARIES]
    size, extra = divmod(len(bodies), GROUPS)
    groups, start = [], 0
    for index in range(GROUPS):
        end = start + size + (index < extra)
        groups.append(bodies[start:end])
        start = end
    template = primitive["cases"][0]["program"]
    plans = {(form, index): {"schema": PLAN_SCHEMA, "form": form, "functionProgram": {
                 **template, "body": {**template["body"], "body": xor_tree(group)}}}
             for form in FORMS for index, group in enumerate(groups)}
    return plans, inputs


def check_plan(plan):
    require(isinstance(plan, dict) and set(plan) == {"schema", "functionProgram", "form"}
            and plan["schema"] == PLAN_SCHEMA and plan["form"] in FORMS, "invalid assembly plan")
    program = plan["functionProgram"]
    require(isinstance(program, dict) and set(program) == {"schema", "dataDefinitions", "resultType", "body"}
            and program["schema"] == "solcore-semantic-core" and program["dataDefinitions"] == []
            and program["resultType"] == {"tag": "function", "parameter": "word", "result": "word"}
            and program["body"].get("tag") == "lambda", "assembly plan must retain a closed Word function")
    return program["body"]["body"]


def check_manifest(manifest, primitive):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals", "requiredInputs",
              "assemblyRequirements", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == "runtime-assembly", "unexpected assembly manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "assembly AST coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    for version in ("functionVersion", "abstractionVersion", "generatorVersion", "baseGeneratorVersion",
                    "boundaryVersion"):
        require(manifest[version] == primitive[version], f"{version} differs from the primitive corpus")
    require(manifest["functionProfileVersion"] == primitive["profileVersion"], "the function profile changed")
    require(set(manifest["requiredFeatures"]) == FEATURES == set(primitive["requiredFeatures"]),
            "assembly corpus must require every primitive AST feature")
    require(manifest["requiredWordLiterals"] == [], "assembly corpus requires no literal inventory")
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "assembly corpus must require all eight boundary inputs")
    requirements = manifest["assemblyRequirements"]
    require(isinstance(requirements, dict) and set(requirements) == {"forms", "formFeatures"}
            and requirements["forms"] == list(FORMS)
            and set(requirements["formFeatures"]) == {f"{form}:{feature}" for form in FORMS for feature in FEATURES}
            and len(requirements["formFeatures"]) == len(FORMS) * len(FEATURES),
            "assembly corpus must require every feature in every form")
    plans, inputs = construction(primitive)
    expected = [(f"{form}-group-{group}-input-{index}", plan, value)
                for (form, group), plan in plans.items() for index, value in enumerate(inputs)]
    entries = manifest["cases"]
    require(isinstance(entries, list) and len(entries) == len(expected), "the corpus is not the primitive construction")
    for entry, (identifier, plan, value) in zip(entries, expected):
        require(isinstance(entry, dict) and set(entry) == {"id", "assemblyPlan", "input", "expectedFeatures"},
                "an assembly corpus entry is a plan with its input and features")
        require(entry["id"] == identifier and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and entry["assemblyPlan"] == plan and entry["input"] == value,
                "an entry differs from the primitive construction")
        check_plan(entry["assemblyPlan"])
        canonical_word(entry["input"])
        features = entry["expectedFeatures"]
        require(isinstance(features, list) and features == sorted(set(features)) and set(features) <= FEATURES,
                "expected features must be a sorted set of primitive features")
    return entries


def check_case(case, entry, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected assembly case schema")
    body = check_plan(case["assemblyPlan"])
    require(case["assemblyPlan"] == entry["assemblyPlan"] and case["input"] == entry["input"],
            "emission changed the plan or the input")
    number = canonical_word(case["input"])
    program = case["program"]
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == "word", "assembly reference must be a closed Word program")
    application = program["body"]
    require(application.get("tag") == "apply" and application.get("function") == entry["assemblyPlan"]["functionProgram"]["body"]
            and application.get("argument", {}).get("tag") == "word"
            and int(application["argument"]["value"], 16) == number, "original Core application differs from the plan and input")
    require(case["contract"] == {"name": NAME, "method": "run", "signature": "run(uint256)",
            "deployPath": [NAME + "Deploy"], "runtimePath": [NAME + "Deploy", NAME],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "assembly ABI, runtime input, or contract metadata changed")
    require(isinstance(case.get("source"), str) and case.get("executionFuel") == fuel, "invalid emitted source or fuel")
    source, form = case["source"], case["assemblyPlan"]["form"]
    conditional = "if" in case["provenance"]["features"]
    switches, branches = "switch " in source, "if iszero(" in source
    if form == "operations":
        require(not switches and not branches and ("if (" in source) == conditional,
                "the operations form does not keep Solcore control flow")
    else:
        require(source.count("assembly {") == 1 and "tobool(" not in source and "if (" not in source
                and switches == (form == "switch" and conditional) and branches == (form == "if" and conditional),
                "a whole-body form is not one Yul block with its own control flow")
    return body


def checked_shrinks(case, tool, directory, fuel):
    path = directory / "shrink-parent.json"
    path.write_text(json.dumps(case))
    reduced = run(tool, "shrink", str(path), "4", str(fuel))
    require(reduced == run(tool, "shrink", str(path), "4", str(fuel)), "native shrink order changed")
    candidates = reduced.get("cases")
    require(isinstance(candidates, list) and 0 < len(candidates) <= 4, "fixed assembly case has no bounded shrink candidates")
    seen = set()
    for candidate in candidates:
        require(candidate.get("schema") == CASE_SCHEMA and candidate["assemblyPlan"]["form"] == case["assemblyPlan"]["form"],
                "shrink changed the form")
        origin = candidate["provenance"]["origin"]
        require(origin.get("kind") == "reduced" and origin.get("parentPlan") == case["assemblyPlan"]
                and origin.get("parentProgram") == case["program"] and origin.get("parentInput") == case["input"],
                "a shrink candidate does not record its parent")
        encoded = json.dumps(candidate["program"], sort_keys=True)
        require(encoded not in seen, "duplicate canonical shrink")
        seen.add(encoded)
        target = directory / "shrunk.json"
        target.write_text(json.dumps(candidate))
        require(run(tool, "replay", str(target), str(fuel)) == candidate, "native shrink lost canonical source/program/provenance")
        fresh = run(tool, "observe", str(target), str(fuel))
        require(fresh == candidate["directCore"], "shrunk observation differs from fresh Core execution")
    return len(candidates)


def policy_checks(manifest, primitive, sample, tool, directory, fuel):
    count = 0

    def rejects(action, label):
        nonlocal count
        try:
            action()
        except ValueError:
            count += 1
        else:
            raise ValueError("negative check accepted " + label)

    entry = manifest["cases"][0]
    for key, value in (("profile", "runtime-primitives"), ("requiredInputs", ["0"]),
                       ("assemblyRequirements", {**manifest["assemblyRequirements"], "forms": ["switch"]}),
                       ("assemblyRequirements", {**manifest["assemblyRequirements"],
                                                 "formFeatures": manifest["assemblyRequirements"]["formFeatures"][1:]}),
                       ("cases", manifest["cases"][1:]),
                       ("cases", [{**entry, "input": "3"}, *manifest["cases"][1:]]),
                       ("cases", [{**entry, "assemblyPlan": {**entry["assemblyPlan"], "form": "if"}}, *manifest["cases"][1:]])):
        changed = copy.deepcopy(manifest)
        changed[key] = value
        rejects(lambda: check_manifest(changed, primitive), key)
    path = directory / "negative.json"
    # Without an `if`, the two whole-body forms emit the same source.
    other = "operations" if sample["assemblyPlan"]["form"] != "operations" else "switch"
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("form", lambda value: value["assemblyPlan"].update(form=other)),
        ("function", lambda value: value["assemblyPlan"]["functionProgram"]["body"].update(
            body={"tag": "var", "index": 0})),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="3" if value["input"] != "3" else "2")),
        ("wrapper", lambda value: value["contract"].update(name="AnotherContract")),
        ("origin", lambda value: value["provenance"].update(origin={"kind": "assembly-generated"})),
        ("profile version", lambda value: value["provenance"].update(profileVersion="another-version")),
        ("function profile", lambda value: value["provenance"].update(functionProfileVersion="another-version")),
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
    count += 1
    for args in (("assembly-generate", str(1 << 64), "96", "8", "1", str(fuel)),
                 ("assembly-generate", "1", "513", "8", "1", str(fuel)),
                 ("assembly-generate", "1", "96", "8", "1", str(fuel), "exclude-boundary-identity-v1",
                  "exclude-boundary-identity-v1"),
                 ("shrink", str(path), "4097", str(fuel))):
        result = subprocess.run([str(tool), *args], cwd=ROOT, text=True, capture_output=True, timeout=30, check=False)
        require(result.returncode != 0, "native CLI accepted an out-of-range budget or a repeated filter")
        count += 1
    return count


def validate(manifest, primitive, tool, fuel):
    require(type(fuel) is int and 0 < fuel <= 10_000_000, "invalid positive execution fuel")
    entries = check_manifest(manifest, primitive)
    coverage = {form: {"features": set(), "inputs": set()} for form in FORMS}
    sources, samples = {}, {}
    with tempfile.TemporaryDirectory(prefix="semantic-assembly-corpus-") as name:
        directory = Path(name)
        plan = directory / "plan.json"
        for entry in entries:
            plan.write_text(json.dumps(entry["assemblyPlan"]))
            case = run(tool, "assembly-emit", str(plan), entry["input"], str(fuel))
            require(case == run(tool, "assembly-emit", str(plan), entry["input"], str(fuel)), "emission is not deterministic")
            require(case["provenance"]["origin"] == {"kind": "imported"}, "a fixed entry is not an imported plan")
            for version in VERSIONS:
                require(case["provenance"][version] == manifest[version], f"{version} changed")
            body = check_case(case, entry, fuel)
            require(not large_constant_shift(body, [True]), "a fixed function shifts by a large constant count")
            actual, _ = pure.ast_coverage(body)
            require(actual == set(case["provenance"]["features"]) == set(entry["expectedFeatures"]),
                    "declared features differ from the function AST")
            path = directory / "case.json"
            path.write_text(json.dumps(case))
            before = run(tool, "observe", str(path), str(fuel))
            require(before == case["directCore"] and before.get("status") == "returned",
                    "saved observation differs from fresh original Core")
            canonical_word(before["word"])
            require(run(tool, "replay", str(path), str(fuel)) == case, "native canonical replay changed the case")
            key = json.dumps(entry["assemblyPlan"], sort_keys=True)
            require(sources.setdefault(key, case["source"]) == case["source"], "one plan emitted input-dependent source")
            form = entry["assemblyPlan"]["form"]
            samples.setdefault(form, case)
            # Only completed, replayed native cases contribute coverage.
            coverage[form]["features"].update(actual)
            coverage[form]["inputs"].add(canonical_word(entry["input"]))
        for form in FORMS:
            require(coverage[form]["features"] == FEATURES, f"the {form} form lost a feature")
            require(coverage[form]["inputs"] == set(BOUNDARIES), f"the {form} form lost a boundary input")
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in samples.values())
        checks = policy_checks(manifest, primitive, samples["switch"], tool, directory, fuel)
    return {"status": "passed", "profile": "runtime-assembly", "cases": len(entries), "plans": len(sources),
            "coverageKind": "core-ast-features-per-form", "requiredFeatures": len(FEATURES),
            "forms": {form: {"features": len(values["features"]), "inputs": len(values["inputs"])}
                      for form, values in coverage.items()},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path, default=ROOT / "scripts/semantic-assembly-corpus.json")
    parser.add_argument("--primitive", type=Path, default=ROOT / "scripts/semantic-primitive-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), json.loads(args.primitive.read_text()),
                              args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
