#!/usr/bin/env python3
"""Check the fixed trait corpus using fresh native Core executions.

The corpus takes, from seed 1 upwards at the default budget, every generated
plan that covers a missing trait shape, each at the eight primitive boundary
inputs. This test rebuilds that selection, recomputes every shape from the
plan alone with its own walk over the instances the uses reach, checks the
emitted source's trait, impls, helpers and builders against the plan, and
replays, observes and shrinks natively. It neither compiles Rust nor executes
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
spec = importlib.util.spec_from_file_location("trait_corpus_pure", ROOT / "Tests/scripts/test-semantic-corpus.py")
pure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pure)
generic_spec = importlib.util.spec_from_file_location("trait_corpus_generic", ROOT / "Tests/scripts/test-semantic-generic-corpus.py")
generic = importlib.util.module_from_spec(generic_spec)
generic_spec.loader.exec_module(generic)
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
returned = generic.returned
VERSIONS = pure.VERSIONS + ("profileVersion", "boundaryVersion")
BOUNDARIES = (0, 1, 2, 255, 256, (1 << 256) - 1, 1 << 255, (1 << 255) - 1)
CASE_SCHEMA = "solcore-lean.semantic-trait-case.v1"
PLAN_SCHEMA = "solcore-lean.trait-plan.v1"
NAME = "SynthesizedTraits"
NODES = 2048
CASE_LIMIT = 4096
SHRINK_BYTES = 1_500_000
SHAPES = {
    "instances": ["generic:binary", "generic:unary", "plain:binary", "plain:unary", "sum:binary", "sum:unary",
                  "tuple:binary", "tuple:unary", "word:binary", "word:unary"],
    "calls": ["binary:direct", "binary:generic", "binary:lifted", "unary:direct", "unary:generic", "unary:lifted"],
    "depths": ["0", "1", "2", "3"],
    "arguments": ["generic", "plain", "sum", "tuple", "word"],
    "forms": ["enum:columns", "enum:nested", "tuple:columns", "tuple:nested"],
    "shapes": ["sum-of-product"]}
HELPERS = {("generic", "unary"): "sc_once", ("generic", "binary"): "sc_twice",
           ("lifted", "unary"): "sc_lift", ("lifted", "binary"): "sc_lift2"}


def key(ty):
    return json.dumps(ty, sort_keys=True)


def kind(ty):
    if ty == "word":
        return "word"
    if "tuple" in ty:
        return "tuple"
    if "sum" in ty:
        return "sum"
    return "generic" if "argument" in ty else "plain"


def depth(ty):
    if ty == "word":
        return 0
    if "tuple" in ty or "sum" in ty:
        return 1 + max(depth(part) for part in ty.get("tuple", ty.get("sum")))
    return 1 + depth(ty["argument"]) if "argument" in ty else 1


def substitute(field, argument):
    """A declaration's field type at an instance argument."""
    if field == "word":
        return "word"
    if field == "param":
        return argument
    if "tuple" in field:
        return {"tuple": [substitute(part, argument) for part in field["tuple"]]}
    if "argument" in field:
        return {"enum": field["enum"], "argument": substitute(field["argument"], argument)}
    return {"enum": field["enum"]}


def children(plan, ty):
    """The types an impl's arms call the method at."""
    if ty == "word":
        return []
    if "tuple" in ty or "sum" in ty:
        return list(ty.get("tuple", ty.get("sum")))
    declaration = plan["declarations"][ty["enum"]]
    argument = ty.get("argument", "word")
    return [substitute(field, argument) for fields in declaration["constructors"] for field in fields]


def reached(plan):
    """Every instance type and method the uses reach, as (key, type, method)."""
    seen, found = set(), []
    pending = [({"tuple": [use["type"], use["type"]]} if use["call"] == "lifted" else use["type"], use["method"])
               for use in plan["uses"]]
    while pending:
        ty, method = pending.pop()
        if (key(ty), method) in seen:
            continue
        seen.add((key(ty), method))
        found.append((ty, method))
        pending.extend((child, method) for child in children(plan, ty))
    return found


def impl_form(plan, head):
    impls = [impl for impl in plan["impls"] if impl["head"] == head]
    require(len(impls) == 1, "a reached instance has no impl")
    return impls[0]["form"]


def shapes(plan):
    """The trait shapes from the plan alone."""
    found = {dimension: set() for dimension in SHAPES}
    for ty, method in reached(plan):
        found["instances"].add(f"{kind(ty)}:{method}")
        if "argument" in ty:
            found["arguments"].add(kind(ty["argument"]))
        if method == "binary" and "tuple" in ty:
            found["forms"].add("tuple:" + impl_form(plan, "tuple"))
        if method == "binary" and "enum" in ty:
            found["forms"].add("enum:" + impl_form(plan, {"enum": ty["enum"]}))
        if method == "binary" and "sum" in ty and [kind(part) for part in ty["sum"]].count("tuple") == 1:
            found["shapes"].add("sum-of-product")
    for use in plan["uses"]:
        found["calls"].add(f"{use['method']}:{use['call']}")
        found["depths"].add(str(depth(use["type"])))
    return found


def type_text(ty):
    if ty == "word":
        return "word"
    if "tuple" in ty:
        return "(" + ", ".join(type_text(part) for part in ty["tuple"]) + ")"
    if "sum" in ty:
        return "sum<" + ", ".join(type_text(part) for part in ty["sum"]) + ">"
    return f"Sc_T{ty['enum']}" + (f"<{type_text(ty['argument'])}>" if "argument" in ty else "")


def impl_header(plan, head):
    if head == "word":
        return "impl Sc_Fold<word> {"
    if head in ("tuple", "sum"):
        shape = "(f, g)" if head == "tuple" else "sum<f, g>"
        return f"impl<f, g> Sc_Fold<{shape}> where f: Sc_Fold, g: Sc_Fold {{"
    index = head["enum"]
    if plan["declarations"][index]["generic"]:
        return f"impl<a> Sc_Fold<Sc_T{index}<a>> where a: Sc_Fold {{"
    return f"impl Sc_Fold<Sc_T{index}> {{"


def check_plan(plan):
    require(isinstance(plan, dict) and set(plan) == {"schema", "declarations", "methods", "impls", "helpers", "uses"}
            and plan["schema"] == PLAN_SCHEMA, "unexpected trait plan schema")
    declarations = plan["declarations"]
    require(isinstance(declarations, list) and 1 <= len(declarations) <= 3, "one to three declarations")
    for declaration in declarations:
        require(set(declaration) == {"generic", "sameName", "constructors"}
                and 2 <= len(declaration["constructors"]) <= 4
                and all(len(fields) <= 2 for fields in declaration["constructors"]),
                "declarations have two to four constructors of at most two fields")
    require(plan["methods"] in (["unary"], ["binary"], ["unary", "binary"]), "trait methods are unary, binary or both")
    heads = ["word", "tuple", "sum", *({"enum": index} for index in range(len(declarations)))]
    order = [heads.index(impl["head"]) for impl in plan["impls"]]
    require(order == sorted(set(order)), "impls are distinct, in the order Word, tuple, sum, declarations")
    for impl in plan["impls"]:
        head = impl["head"]
        arms = (1 if head in ("word", "tuple") else 2 if head == "sum"
                else len(declarations[head["enum"]]["constructors"]))
        for method in ("unary", "binary"):
            require(len(impl[method]) == (arms if method in plan["methods"] else 0), "an impl lacks an arm per constructor")
        mismatch = 2 if head == "sum" else 1 if isinstance(head, dict) else 0
        require(len(impl["mismatch"]) == (mismatch if "binary" in plan["methods"] else 0), "mismatch constants changed")
        require(impl["form"] == "nested" or (isinstance(head, dict) or head == "tuple"), "only tuples and enums have columns")
    uses = plan["uses"]
    require(isinstance(uses, list) and 1 <= len(uses) <= 6, "one to six uses")
    for use in uses:
        require(use["method"] in plan["methods"] and depth(use["type"]) <= 3
                and use["shift"] == (0 if use["method"] == "unary" else use["shift"])
                and (use["method"] == "unary" or 1 <= use["shift"] <= 4), "uses call a present method at depth 3 or less")
        builder = use["builder"]
        require(0 <= builder["offset"] < 4 and 1 <= len(builder["values"]) <= 4, "builders hold one to four values")
    needed = [pair for pair in HELPERS if any((use["call"], use["method"]) == pair for use in uses)]
    require([(helper["call"], helper["method"]) for helper in plan["helpers"]] == needed,
            "helpers are exactly those the uses need, in order")
    return plan


def check_source(case):
    """The source declares the trait and every impl, helper and builder of the
    plan, and run calls every use."""
    plan, source = case["traitPlan"], case["source"]
    for index, declaration in enumerate(plan["declarations"]):
        require(source.count(f"enum Sc_T{index}{'<a>' if declaration['generic'] else ''} {{\n") == 1,
                "a declaration is missing from the source")
    require(source.count("trait Sc_Fold<a> {\n") == 1, "the trait is missing")
    for method, signature in (("unary", "function sc_fold(sc_x: a) returns (word);"),
                              ("binary", "function sc_both(sc_x: a, sc_y: a) returns (word);")):
        require((f"    {signature}\n" in source) == (method in plan["methods"]), "the trait's methods differ from the plan")
    for impl in plan["impls"]:
        require(source.count(impl_header(plan, impl["head"]) + "\n") == 1, "an impl is missing")
    require(source.count("\nimpl") == len(plan["impls"]), "the source has an impl the plan lacks")
    for helper in plan["helpers"]:
        require(source.count(f"function {HELPERS[(helper['call'], helper['method'])]}<t>(") == 1, "a helper is missing")
    require(source.count("<t>(") == len(plan["helpers"]), "the source has a helper the plan lacks")
    for index, use in enumerate(plan["uses"]):
        require(source.count(f"function sc_u{index}(sc_x: word) returns ({type_text(use['type'])}) {{\n") == 1,
                "a builder is missing")
    require(source.count("let sc_r") == len(plan["uses"]) and "contract SynthesizedTraits {" in source,
            "run does not call every use")
    if any(use["method"] == "binary" and "sum" in use["type"] for use in plan["uses"]):
        require("match (sc_y) {" in source, "the sum impl's binary method does not match its second argument")


def check_case(case, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected trait case schema")
    plan = check_plan(case["traitPlan"])
    number = canonical_word(case["input"])
    program = case["program"]
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == "word", "trait reference must be a closed Word program")
    require(generic.complexity(program["body"])[0] <= CASE_LIMIT, "reference exceeds the case limit")
    require(case["provenance"]["referenceNodes"] <= CASE_LIMIT, "recorded reference size exceeds the case limit")
    require(case["contract"] == {"name": NAME, "method": "run", "signature": "run(uint256)",
            "deployPath": [NAME + "Deploy"], "runtimePath": [NAME + "Deploy", NAME],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "trait ABI, runtime input, or contract metadata changed")
    require(isinstance(case.get("source"), str) and case.get("executionFuel") == fuel, "invalid emitted source or fuel")
    check_source(case)
    recorded = case["provenance"]["traitShapes"]
    require({dimension: set(values) for dimension, values in recorded.items()} == shapes(plan),
            "recorded trait shapes differ from the plan")
    require(all(values == sorted(set(values)) for values in recorded.values()), "trait shapes are not sorted inventories")
    require(case["provenance"]["features"] == [], "the trait profile records no G0 step features")
    return plan


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals", "requiredInputs",
              "traitRequirements", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == "runtime-traits", "unexpected trait manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "trait coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    require(manifest["requiredFeatures"] == [] and manifest["requiredWordLiterals"] == [],
            "the trait corpus requires trait shapes, not step features or literals")
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "the trait corpus must require all eight boundary inputs")
    require(manifest["traitRequirements"] == SHAPES, "the trait corpus must require every shape value")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "the trait corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"id", "generation", "input", "expectedFeatures"},
                "a trait corpus entry is a generation recipe with its input")
        identifier = entry["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        require(canonical_word(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        require(entry["expectedFeatures"] == [], "trait entries expect no step features")
        recipe = entry["generation"]
        require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
        require(canonical_word(recipe["seed"]) < 1 << 64 and recipe["maxProgramNodes"] == NODES,
                "fixed recipes use a uint64 seed and the default budget")
    return entries


def generated_shapes(tool, seed, fuel):
    """The seed's plan shapes, or None for an excluded seed."""
    corpus = run(tool, "trait-generate", str(seed), str(NODES), "1", "1", str(fuel))
    cases = corpus.get("cases")
    require(isinstance(cases, list) and len(cases) <= 1, "invalid generation response")
    return shapes(check_plan(cases[0]["traitPlan"])) if cases else None


def selection(tool, fuel, last):
    """The roadmap's construction: from seed 1 upwards, every accepted seed
    whose plan covers a missing value, until nothing is missing."""
    missing = {dimension: set(values) for dimension, values in SHAPES.items()}
    chosen = []
    for seed in range(1, last + 1):
        if not any(missing.values()):
            break
        found = generated_shapes(tool, seed, fuel)
        if found is None:
            continue
        if any(missing[dimension] & found[dimension] for dimension in missing):
            chosen.append(seed)
            for dimension in missing:
                missing[dimension] -= found[dimension]
    require(not any(missing.values()), "seeds up to the last chosen one leave a requirement missing")
    return chosen


def materialize(entry, tool, fuel):
    recipe = entry["generation"]
    corpus = run(tool, "trait-generate", recipe["seed"], str(recipe["maxProgramNodes"]), "8", "1", str(fuel))
    require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
            and corpus.get("requested") == 8 and corpus.get("attempted") == 1
            and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 8,
            "fixed trait seed did not emit eight cases in one attempt")
    cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
    require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
    case = cases[0]
    origin = case["provenance"]["origin"]
    require(origin == {"kind": "trait-generated", "seed": recipe["seed"], "maxProgramNodes": recipe["maxProgramNodes"],
                       "inputIndex": BOUNDARIES.index(int(entry["input"])), "validationFuel": fuel},
            "generated recipe differs from manifest")
    check_case(case, fuel)
    return case


def plan_size(plan):
    """The shrink measure's plan size, independently: declarations, methods,
    impl arms, helpers, call forms, type nodes and value weights."""
    def weight(field):
        if field in ("word", "param"):
            return 1
        if "tuple" in field:
            return 1 + sum(weight(part) for part in field["tuple"])
        return 2 + (weight(field["argument"]) if "argument" in field else 0)

    def nodes(ty):
        if ty == "word" or ("enum" in ty and "argument" not in ty):
            return 1
        if "argument" in ty:
            return 1 + nodes(ty["argument"])
        return 1 + sum(nodes(part) for part in ty.get("tuple", ty.get("sum")))

    def value(tree):
        if "leaf" in tree:
            return 1 if tree["leaf"] == "input" else 2
        if "tuple" in tree:
            return 1 + sum(value(part) for part in tree["tuple"])
        if "inl" in tree or "inr" in tree:
            return 1 + value(tree.get("inl", tree.get("inr")))
        return 1 + sum(value(part) for part in tree["fields"])

    total = sum(1 + sum(weight(field) for field in fields) for declaration in plan["declarations"]
                for fields in declaration["constructors"])
    total += len(plan["methods"]) + sum(1 + len(impl["unary"]) + len(impl["binary"]) + len(impl["mismatch"])
                                        for impl in plan["impls"])
    total += len(plan["helpers"])
    for use in plan["uses"]:
        total += 1 + {"direct": 0, "generic": 1, "lifted": 2}[use["call"]] + nodes(use["type"])
        total += sum(value(tree) for tree in use["builder"]["values"])
    return total


def checked_shrinks(case, tool, directory, fuel):
    path = directory / "shrink-parent.json"
    path.write_text(json.dumps(case))
    reduced = run(tool, "shrink", str(path), "64", str(fuel))
    require(reduced == run(tool, "shrink", str(path), "64", str(fuel)), "native shrink order changed")
    candidates = reduced.get("cases")
    require(isinstance(candidates, list) and candidates, "fixed trait case has no shrink candidate")
    require(sum(len(json.dumps(candidate, separators=(",", ":"))) for candidate in candidates) <= SHRINK_BYTES,
            "a shrink response exceeds its byte cap")
    parent = (plan_size(case["traitPlan"]), int(case["input"]))
    seen = set()
    for candidate in candidates:
        check_case(candidate, fuel)
        require(candidate["provenance"]["origin"] == {"kind": "reduced", "parentPlan": case["traitPlan"],
                                                      "parentInput": case["input"]},
                "a shrink candidate is not a reduction of its parent")
        require((plan_size(candidate["traitPlan"]), int(candidate["input"])) < parent,
                "a shrink candidate is not strictly smaller")
        encoded = json.dumps([candidate["traitPlan"], candidate["input"]], sort_keys=True)
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

    for field, value in (("profile", "runtime-enums"), ("requiredInputs", ["0"]), ("requiredFeatures", ["let"]),
                         *(("traitRequirements", {**SHAPES, dimension: SHAPES[dimension][1:]}) for dimension in SHAPES)):
        changed = copy.deepcopy(manifest)
        changed[field] = value
        rejects(lambda: check_manifest(changed), field)
    plan = sample["traitPlan"]
    for label, broken in (("no uses", {**plan, "uses": []}), ("seven uses", {**plan, "uses": plan["uses"] * 7}),
                          ("reversed impls", {**plan, "impls": plan["impls"][::-1]}),
                          ("an extra helper", {**plan, "helpers": plan["helpers"] + [{"call": "lifted", "method": "unary",
                                                                                      "op": "add", "constant": "0"}] * 5})):
        rejects(lambda: check_plan(broken), label)
    path = directory / "negative.json"
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("a missing impl", lambda value: value["traitPlan"]["impls"].pop(0)),
        ("impls out of order", lambda value: value["traitPlan"]["impls"].reverse()),
        ("an arm constant", lambda value: value["traitPlan"]["impls"][0]["unary"][0].update(constant="07")),
        ("a binary match form", lambda value: value["traitPlan"]["impls"][2].update(form="columns")),
        ("a helper", lambda value: value["traitPlan"]["helpers"].append({"call": "generic", "method": "unary",
                                                                         "op": "add", "constant": "1"})),
        ("a use's shift", lambda value: value["traitPlan"]["uses"][0].update(shift=9)),
        ("an unknown declaration", lambda value: value["traitPlan"]["uses"][0].update(type={"enum": 7})),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="1" if value["input"] != "1" else "2")),
        ("wrapper", lambda value: value["contract"].update(name="AnotherContract")),
        ("trait shapes", lambda value: value["provenance"]["traitShapes"].update(calls=[])),
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
    for args in (("trait-generate", str(1 << 64), "2048", "8", "1", str(fuel)),
                 ("trait-generate", "1", "4097", "8", "1", str(fuel)),
                 ("trait-generate", "1", "255", "8", "1", str(fuel)),
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
    found = {dimension: set() for dimension in SHAPES}
    with tempfile.TemporaryDirectory(prefix="trait-corpus-") as name:
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
            plan_key = json.dumps(plan, sort_keys=True)
            if plan_key not in groups:
                seeds.append(int(entry["generation"]["seed"]))
                samples.append(case)
            group = groups.setdefault(plan_key, {"inputs": set(), "source": case["source"], "results": set()})
            require(group["source"] == case["source"], "identical trait plan emitted input-dependent source")
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
            require(group["inputs"] == set(BOUNDARIES), "trait plan lacks a completed boundary input")
            require(len(group["results"]) > 1, "fixed trait plan returned one Word for every boundary input")
        require(seeds == selection(tool, fuel, max(seeds)), "the corpus is not every covering seed in order")
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in samples[:2])
        checks = policy_checks(manifest, samples[0], tool, directory, fuel)
    return {"status": "passed", "profile": "runtime-traits", "cases": len(entries), "plans": len(groups),
            "seeds": seeds, "completedInputs": [str(value) for value in sorted(inputs)],
            "traitCoverage": {"classification": "specified-by-the-plan-not-measured-specialization",
                              **{dimension: sorted(values) for dimension, values in found.items()}},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path, default=ROOT / "scripts/semantic-trait-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
