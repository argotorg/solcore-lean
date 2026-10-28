#!/usr/bin/env python3
"""Check the fixed enum corpus using fresh native Core executions.

The corpus takes, from seed 1 upwards at the default budget, every generated
plan that covers a missing enum shape, each at the eight primitive boundary
inputs. This test rebuilds that selection, recomputes every shape from the
plan alone, checks the emitted source's declarations, views and builders
against the plan, and replays, observes and shrinks natively. It neither
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
spec = importlib.util.spec_from_file_location("enum_corpus_pure", ROOT / "Tests/scripts/test-semantic-corpus.py")
pure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pure)
generic_spec = importlib.util.spec_from_file_location("enum_corpus_generic", ROOT / "Tests/scripts/test-semantic-generic-corpus.py")
generic = importlib.util.module_from_spec(generic_spec)
generic_spec.loader.exec_module(generic)
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
returned = generic.returned
VERSIONS = pure.VERSIONS + ("profileVersion", "boundaryVersion")
BOUNDARIES = (0, 1, 2, 255, 256, (1 << 256) - 1, 1 << 255, (1 << 255) - 1)
CASE_SCHEMA = "solcore-lean.semantic-enum-case.v1"
PLAN_SCHEMA = "solcore-lean.enum-plan.v1"
NAME = "SynthesizedEnums"
NODES = 2048
CASE_LIMIT = 4096
SHRINK_BYTES = 1_500_000
NAMES = ("sc_a", "sc_b", "sc_c", "sc_d", "sc_w")
SHAPES = {
    "constructors": ["2", "3", "4"],
    "fields": ["count:0", "count:1", "count:2", "type:applied", "type:enum", "type:param", "type:tuple", "type:word"],
    "declarations": ["argument:enum", "argument:param", "argument:tuple", "argument:word", "generic", "plain", "same-name"],
    "views": ["generic", "pair", "single"],
    "patterns": ["default", "dot", "exhaustive", "nested", "nullary", "qualified", "rebound", "repeated", "same-name",
                 "shadow", "tuple", "variable", "wildcard"],
    "wildcards": ["arm", "column", "component", "deep", "field"],
    "depths": ["1", "2", "3"]}
FORMS = {"qualified", "dot", "same-name"}


def ty_kind(ty):
    if ty in ("word", "param"):
        return ty
    if "tuple" in ty:
        return "tuple"
    return "applied" if "argument" in ty else "enum"


def ty_arguments(ty):
    """The arguments of every generic instance inside a type."""
    if ty in ("word", "param"):
        return []
    if "tuple" in ty:
        return [argument for part in ty["tuple"] for argument in ty_arguments(part)]
    if "argument" in ty:
        return [ty["argument"], *ty_arguments(ty["argument"])]
    return []


def argument_kind(ty):
    return ty if ty in ("word", "param") else "tuple" if "tuple" in ty else "enum"


def substitute(ty, argument):
    if ty == "param":
        return argument
    if ty == "word":
        return ty
    if "tuple" in ty:
        return {"tuple": [substitute(part, argument) for part in ty["tuple"]]}
    if "argument" in ty:
        return {"enum": ty["enum"], "argument": substitute(ty["argument"], argument)}
    return ty


def is_wild(pattern):
    return pattern == "_"


def is_leaf(pattern):
    return pattern == "_" or "var" in pattern


def variables(pattern):
    if pattern == "_":
        return []
    if "var" in pattern:
        return [pattern["var"]]
    parts = pattern["tuple"] if "tuple" in pattern else pattern["fields"]
    return [name for part in parts for name in variables(part)]


def depth(pattern):
    if is_leaf(pattern):
        return 0
    parts = pattern["tuple"] if "tuple" in pattern else pattern["fields"]
    return 1 + max([depth(part) for part in parts], default=0)


def forms(pattern, level):
    """Forms, nullary, tuple, variable and wildcard patterns, and wildcard
    positions below their parent: field, component, deep."""
    if pattern == "_":
        return ["wildcard"]
    if "var" in pattern:
        return ["variable"]

    def inside(part, position):
        found = []
        if part == "_":
            found += ["wildcard:" + position] + (["wildcard:deep"] if level >= 1 else [])
        return found + forms(part, level + 1)

    if "tuple" in pattern:
        return ["tuple"] + [value for part in pattern["tuple"] for value in inside(part, "component")]
    require(pattern["form"] in FORMS, "unknown constructor form")
    if not pattern["fields"]:
        return ["nullary", pattern["form"]]
    return [pattern["form"]] + [value for part in pattern["fields"] for value in inside(part, "field")]


def row_forms(rows):
    found = []
    for row in rows:
        if not row:
            found.append("default")
        elif row == ["_"]:
            found += ["wildcard:arm", "wildcard"]
        else:
            catch_all = all(is_leaf(pattern) for pattern in row)
            if len(row) > 1 and not catch_all and "_" in row:
                found.append("wildcard:column")
            if len(row) > 1 and all(is_wild(pattern) for pattern in row):
                found.append("wildcard:arm")
            for pattern in row:
                found += forms(pattern, 0)
            if "sc_w" in [name for pattern in row for name in variables(pattern)]:
                found.append("shadow")
    if not any(all(is_leaf(pattern) for pattern in row) for row in rows):
        found.append("exhaustive")
    names = [name for row in rows for name in sorted(set(v for pattern in row for v in variables(pattern)))]
    if len(names) != len(set(names)):
        found.append("repeated")
    return found


def shapes(plan):
    """Every shape value from the plan alone."""
    declarations = plan["declarations"]
    field_types = [ty for declaration in declarations for fields in declaration["constructors"] for ty in fields]
    use_types = []
    for view in plan["views"]:
        use_types += view["scrutinees"]
        if view["kind"] == "generic":
            use_types += [substitute(view["scrutinees"][0], argument) for argument in view["instances"]]
    tables, nested, rebound = [], False, False
    for view in plan["views"]:
        tables.append([arm["patterns"] for arm in view["arms"]])
        for arm in view["arms"]:
            if "match" in arm:
                nested = True
                tables.append([inner["patterns"] for inner in arm["arms"]])
                outer = {name for pattern in arm["patterns"] for name in variables(pattern)}
                if any(name in outer for inner in arm["arms"] for pattern in inner["patterns"] for name in variables(pattern)):
                    rebound = True
    found = [value for rows in tables for value in row_forms(rows)] + (["nested"] if nested else []) + \
        (["rebound"] if rebound else [])
    return {
        "constructors": {str(len(declaration["constructors"])) for declaration in declarations},
        "fields": {f"count:{len(fields)}" for declaration in declarations for fields in declaration["constructors"]}
        | {"type:" + ty_kind(ty) for ty in field_types},
        "declarations": {"generic" if declaration["generic"] else "plain" for declaration in declarations}
        | {"same-name" for declaration in declarations if declaration["sameName"]}
        | {"argument:" + argument_kind(argument) for ty in field_types + use_types for argument in ty_arguments(ty)},
        "views": {view["kind"] for view in plan["views"]},
        "patterns": {value for value in found if not value.startswith("wildcard:")},
        "wildcards": {value[len("wildcard:"):] for value in found if value.startswith("wildcard:")},
        "depths": {str(min(depth(pattern), 3)) for rows in tables for row in rows for pattern in row if depth(pattern)}}


def type_text(ty):
    if ty in ("word", "param"):
        return "word" if ty == "word" else "a"
    if "tuple" in ty:
        return "(" + ", ".join(type_text(part) for part in ty["tuple"]) + ")"
    name = f"Sc_T{ty['enum']}"
    return name + (f"<{type_text(ty['argument'])}>" if "argument" in ty else "")


def check_plan(plan):
    require(isinstance(plan, dict) and set(plan) == {"schema", "declarations", "views"} and plan["schema"] == PLAN_SCHEMA,
            "unexpected enum plan schema")
    declarations = plan["declarations"]
    require(isinstance(declarations, list) and 1 <= len(declarations) <= 3, "one to three declarations")
    for declaration in declarations:
        require(set(declaration) == {"generic", "sameName", "constructors"}
                and 2 <= len(declaration["constructors"]) <= 4
                and all(len(fields) <= 2 for fields in declaration["constructors"])
                and (not declaration["sameName"] or len(declaration["constructors"][0]) > 0),
                "declarations have two to four constructors of at most two fields")
    views = plan["views"]
    require(isinstance(views, list) and 1 <= len(views) <= 3, "one to three views")
    for view in views:
        require(view["kind"] in ("single", "pair", "generic") and 1 <= len(view["arms"]) <= 8
                and len(view["builders"]) == (2 if view["kind"] != "single" else 1)
                and len(view["scrutinees"]) == (2 if view["kind"] == "pair" else 1)
                and len(view["instances"]) == (2 if view["kind"] == "generic" else 0),
                "views are single, pair or generic with their builders and instances")
        for builder in view["builders"]:
            require(0 <= builder["offset"] < 4 and 1 <= len(builder["values"]) <= 4, "builders hold one to four values")
        canonical_word(view["wordOffset"])
    return plan


def check_source(case):
    """The source declares the plan's enums and one function per view and
    builder, and run calls every view."""
    plan, source = case["enumPlan"], case["source"]
    for index, declaration in enumerate(plan["declarations"]):
        header = f"enum Sc_T{index}{'<a>' if declaration['generic'] else ''} {{"
        require(source.count(header + "\n") == 1, "a declaration is missing from the source")
        for ctor, fields in enumerate(declaration["constructors"]):
            name = f"Sc_T{index}" if ctor == 0 and declaration["sameName"] else f"Sc_T{index}_{ctor}"
            text = name + ("(" + ", ".join(type_text(ty) for ty in fields) + ")" if fields else "")
            require(f"\n    {text}" in source, "a constructor is missing from its declaration")
    calls = 0
    for index, view in enumerate(plan["views"]):
        require(source.count(f"function sc_view{index}{'<a>' if view['kind'] == 'generic' else ''}(") == 1,
                "a view function is missing")
        require(source.count("\n    match (") >= len(plan["views"]), "a view has no match")
        for builder in range(len(view["builders"])):
            require(source.count(f"function sc_make{index}_{builder}(sc_x: word)") == 1, "a builder is missing")
        calls += 2 if view["kind"] == "generic" else 1
    require(source.count("let sc_r") == calls and "contract SynthesizedEnums {" in source, "run does not call every view")


def check_case(case, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected enum case schema")
    plan = check_plan(case["enumPlan"])
    number = canonical_word(case["input"])
    program = case["program"]
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == "word", "enum reference must be a closed Word program")
    require(generic.complexity(program["body"])[0] <= CASE_LIMIT, "reference exceeds the case limit")
    require(case["provenance"]["referenceNodes"] <= CASE_LIMIT, "recorded reference size exceeds the case limit")
    require(case["contract"] == {"name": NAME, "method": "run", "signature": "run(uint256)",
            "deployPath": [NAME + "Deploy"], "runtimePath": [NAME + "Deploy", NAME],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "enum ABI, runtime input, or contract metadata changed")
    require(isinstance(case.get("source"), str) and case.get("executionFuel") == fuel, "invalid emitted source or fuel")
    check_source(case)
    recorded = case["provenance"]["enumShapes"]
    require({key: set(values) for key, values in recorded.items()} == shapes(plan),
            "recorded enum shapes differ from the plan")
    require(case["provenance"]["features"] == [], "the enum profile records no G0 step features")
    return plan


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals", "requiredInputs",
              "enumRequirements", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == "runtime-enums", "unexpected enum manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "enum coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    require(manifest["requiredFeatures"] == [] and manifest["requiredWordLiterals"] == [],
            "the enum corpus requires enum shapes, not step features or literals")
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "the enum corpus must require all eight boundary inputs")
    require(manifest["enumRequirements"] == SHAPES, "the enum corpus must require every shape value")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "the enum corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"id", "generation", "input", "expectedFeatures"},
                "an enum corpus entry is a generation recipe with its input")
        identifier = entry["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        require(canonical_word(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        require(entry["expectedFeatures"] == [], "enum entries expect no step features")
        recipe = entry["generation"]
        require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
        require(canonical_word(recipe["seed"]) < 1 << 64 and recipe["maxProgramNodes"] == NODES,
                "fixed recipes use a uint64 seed and the default budget")
    return entries


def generated_shapes(tool, seed, fuel):
    """The seed's plan shapes, or None for an excluded seed."""
    corpus = run(tool, "enum-generate", str(seed), str(NODES), "1", "1", str(fuel))
    cases = corpus.get("cases")
    require(isinstance(cases, list) and len(cases) <= 1, "invalid generation response")
    return shapes(check_plan(cases[0]["enumPlan"])) if cases else None


def selection(tool, fuel, last):
    """The roadmap's construction: from seed 1 upwards, every accepted seed
    whose plan covers a missing value, until nothing is missing."""
    missing = {key: set(values) for key, values in SHAPES.items()}
    chosen = []
    for seed in range(1, last + 1):
        if not any(missing.values()):
            break
        found = generated_shapes(tool, seed, fuel)
        if found is None:
            continue
        if any(missing[key] & found[key] for key in missing):
            chosen.append(seed)
            for key in missing:
                missing[key] -= found[key]
    require(not any(missing.values()), "seeds up to the last chosen one leave a requirement missing")
    return chosen


def materialize(entry, tool, fuel):
    recipe = entry["generation"]
    corpus = run(tool, "enum-generate", recipe["seed"], str(recipe["maxProgramNodes"]), "8", "1", str(fuel))
    require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
            and corpus.get("requested") == 8 and corpus.get("attempted") == 1
            and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 8,
            "fixed enum seed did not emit eight cases in one attempt")
    cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
    require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
    case = cases[0]
    origin = case["provenance"]["origin"]
    require(origin == {"kind": "enum-generated", "seed": recipe["seed"], "maxProgramNodes": recipe["maxProgramNodes"],
                       "inputIndex": BOUNDARIES.index(int(entry["input"])), "validationFuel": fuel},
            "generated recipe differs from manifest")
    check_case(case, fuel)
    return case


def plan_size(plan):
    """The shrink measure's plan size, independently: constructors and
    field-type weights, views, arms, pattern nodes, body terms, inner arms and
    value nodes."""
    def weight(ty):
        if ty in ("word", "param"):
            return 1
        if "tuple" in ty:
            return 1 + sum(weight(part) for part in ty["tuple"])
        return 2 + (weight(ty["argument"]) if "argument" in ty else 0)

    def nodes(pattern):
        if is_leaf(pattern):
            return 1
        parts = pattern["tuple"] if "tuple" in pattern else pattern["fields"]
        return 1 + sum(nodes(part) for part in parts)

    def value_nodes(value):
        if "leaf" in value:
            return 1
        parts = value["tuple"] if "tuple" in value else value["fields"]
        return 1 + sum(value_nodes(part) for part in parts)

    def body(arm):
        return len(arm["return"]["terms"])

    total = sum(1 + sum(weight(ty) for ty in fields) for declaration in plan["declarations"]
                for fields in declaration["constructors"])
    for view in plan["views"]:
        total += 1 + sum(value_nodes(value) for builder in view["builders"] for value in builder["values"])
        for arm in view["arms"]:
            total += 1 + sum(nodes(pattern) for pattern in arm["patterns"])
            if "match" in arm:
                total += 1 + sum(1 + sum(nodes(pattern) for pattern in inner["patterns"]) + body(inner)
                                 for inner in arm["arms"])
            else:
                total += body(arm)
    return total


def checked_shrinks(case, tool, directory, fuel):
    path = directory / "shrink-parent.json"
    path.write_text(json.dumps(case))
    reduced = run(tool, "shrink", str(path), "64", str(fuel))
    require(reduced == run(tool, "shrink", str(path), "64", str(fuel)), "native shrink order changed")
    candidates = reduced.get("cases")
    require(isinstance(candidates, list) and candidates, "fixed enum case has no shrink candidate")
    require(sum(len(json.dumps(candidate, separators=(",", ":"))) for candidate in candidates) <= SHRINK_BYTES,
            "a shrink response exceeds its byte cap")
    parent = (plan_size(case["enumPlan"]), int(case["input"]))
    seen = set()
    for candidate in candidates:
        check_case(candidate, fuel)
        require(candidate["provenance"]["origin"] == {"kind": "reduced", "parentPlan": case["enumPlan"],
                                                      "parentInput": case["input"]},
                "a shrink candidate is not a reduction of its parent")
        require((plan_size(candidate["enumPlan"]), int(candidate["input"])) < parent,
                "a shrink candidate is not strictly smaller")
        encoded = json.dumps([candidate["enumPlan"], candidate["input"]], sort_keys=True)
        require(encoded not in seen, "duplicate canonical shrink")
        seen.add(encoded)
        target = directory / "shrunk.json"
        target.write_text(json.dumps(candidate))
        require(run(tool, "replay", str(target), str(fuel)) == candidate, "native shrink lost canonical source/program/provenance")
        fresh = run(tool, "observe", str(target), str(fuel))
        returned(fresh)
        require(fresh == candidate["directCore"], "shrunk observation differs from fresh Core execution")
    return len(candidates)


def first_arm_pattern(plan):
    for view_index, view in enumerate(plan["views"]):
        for arm_index, arm in enumerate(view["arms"]):
            if arm["patterns"] and not is_leaf(arm["patterns"][0]):
                return view_index, arm_index
    raise ValueError("no constructor pattern in the sample")


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

    for key, value in (("profile", "runtime-assembly"), ("requiredInputs", ["0"]), ("requiredFeatures", ["let"]),
                       *(("enumRequirements", {**SHAPES, key: SHAPES[key][1:]}) for key in SHAPES)):
        changed = copy.deepcopy(manifest)
        changed[key] = value
        rejects(lambda: check_manifest(changed), key)
    plan = sample["enumPlan"]
    for label, broken in (("no views", {**plan, "views": []}),
                          ("five constructors", {**plan, "declarations": [{**plan["declarations"][0], "constructors":
                              plan["declarations"][0]["constructors"] + [[]] * (5 - len(plan["declarations"][0]["constructors"]))}]
                              + plan["declarations"][1:]})):
        rejects(lambda: check_plan(broken), label)
    view, arm = first_arm_pattern(plan)
    path = directory / "negative.json"
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("an unreachable arm", lambda value: value["enumPlan"]["views"][view]["arms"].insert(
            arm + 1, copy.deepcopy(value["enumPlan"]["views"][view]["arms"][arm]))),
        ("a removed catch-all", lambda value: value["enumPlan"]["views"][view]["arms"].pop()),
        ("a constructor index", lambda value: value["enumPlan"]["views"][view]["arms"][arm]["patterns"].__setitem__(
            0, {"constructor": 7, "form": "qualified", "fields": []})),
        ("a leaf value at an enum type", lambda value: value["enumPlan"]["views"][0]["builders"][0]["values"].__setitem__(
            0, {"leaf": "add", "constant": "1"})),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="1" if value["input"] != "1" else "2")),
        ("wrapper", lambda value: value["contract"].update(name="AnotherContract")),
        ("enum shapes", lambda value: value["provenance"]["enumShapes"].update(views=[])),
        ("generator version", lambda value: value["provenance"].update(generatorVersion="another-version")),
    ):
        changed = copy.deepcopy(sample)
        change(changed)
        path.write_text(json.dumps(changed))
        result = subprocess.run([str(tool), "replay", str(path), str(fuel)], cwd=ROOT,
                                text=True, capture_output=True, timeout=60, check=False)
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
    rejects(lambda: returned(lower["directCore"]), "resource result as shape coverage")
    for args in (("enum-generate", str(1 << 64), "2048", "8", "1", str(fuel)),
                 ("enum-generate", "1", "4097", "8", "1", str(fuel)),
                 ("enum-generate", "1", "255", "8", "1", str(fuel)),
                 ("shrink", str(path), "4097", str(fuel))):
        result = subprocess.run([str(tool), *args], cwd=ROOT, text=True, capture_output=True, timeout=60, check=False)
        generated = result.returncode == 0 and json.loads(result.stdout).get("cases")
        require(result.returncode != 0 or not generated, "native CLI accepted an out-of-range budget")
        count += 1
    return count


def validate(manifest, tool, fuel):
    require(type(fuel) is int and 0 < fuel <= 10_000_000, "invalid positive execution fuel")
    entries = check_manifest(manifest)
    groups, seeds, inputs, samples = {}, [], set(), []
    found = {key: set() for key in SHAPES}
    with tempfile.TemporaryDirectory(prefix="enum-corpus-") as name:
        directory = Path(name)
        for entry in entries:
            case = materialize(entry, tool, fuel)
            require(case == materialize(entry, tool, fuel), "materialization is not deterministic")
            for version in VERSIONS:
                require(case["provenance"][version] == manifest[version], f"{version} changed")
            plan = check_case(case, fuel)
            path = directory / "case.json"
            path.write_text(json.dumps(case))
            before = run(tool, "observe", str(path), str(fuel))
            result = returned(before)
            require(before == case["directCore"], "saved observation differs from fresh original Core")
            replayed = run(tool, "replay", str(path), str(fuel))
            require(replayed == case, "native canonical replay changed the case")
            key = json.dumps(plan, sort_keys=True)
            if key not in groups:
                seeds.append(int(entry["generation"]["seed"]))
                samples.append(case)
            group = groups.setdefault(key, {"inputs": set(), "source": case["source"], "results": set()})
            require(group["source"] == case["source"], "identical enum plan emitted input-dependent source")
            group["inputs"].add(int(case["input"]))
            group["results"].add(result)
            # Only completed, replayed native cases contribute coverage.
            inputs.add(int(case["input"]))
            for dimension, values in shapes(plan).items():
                found[dimension] |= values
        require(inputs == set(BOUNDARIES), "lost completed input coverage")
        for dimension, values in SHAPES.items():
            require(set(values) <= found[dimension], f"lost completed {dimension} coverage")
        for group in groups.values():
            require(group["inputs"] == set(BOUNDARIES), "enum plan lacks a completed boundary input")
            require(len(group["results"]) > 1, "fixed enum plan returned one Word for every boundary input")
        require(seeds == selection(tool, fuel, max(seeds)), "the corpus is not every covering seed in order")
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in samples[:2])
        checks = policy_checks(manifest, samples[0], tool, directory, fuel)
    return {"status": "passed", "profile": "runtime-enums", "cases": len(entries), "plans": len(groups),
            "seeds": seeds, "completedInputs": [str(value) for value in sorted(inputs)],
            "enumCoverage": {"classification": "specified-by-the-plan-not-measured-match-compilation",
                             **{key: sorted(values) for key, values in found.items()}},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path, default=ROOT / "scripts/semantic-enum-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
