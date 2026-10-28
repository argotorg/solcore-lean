#!/usr/bin/env python3
"""Check the fixed trait hierarchy corpus using fresh native Core executions.

The corpus takes, from seed 1 upwards at the default budget, every generated
plan that covers a missing trait hierarchy shape, each at the eight primitive
boundary inputs, except a plan with a base-method `top` use at a tuple, std
sum or generic declaration, which the checked frontend rejects. This test
rebuilds that selection, recomputes every shape from the plan alone with its
own walk over the closures the uses reach, checks the emitted source's traits,
impls, helpers and builders against the plan, and replays, observes and
shrinks natively. It neither compiles Rust nor executes an EVM and implements
no arithmetic result oracle.
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
spec = importlib.util.spec_from_file_location("hierarchy_corpus_pure", ROOT / "Tests/scripts/test-semantic-corpus.py")
pure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pure)
generic_spec = importlib.util.spec_from_file_location("hierarchy_corpus_generic",
                                                      ROOT / "Tests/scripts/test-semantic-generic-corpus.py")
generic = importlib.util.module_from_spec(generic_spec)
generic_spec.loader.exec_module(generic)
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
returned = generic.returned
VERSIONS = pure.VERSIONS + ("profileVersion", "boundaryVersion")
BOUNDARIES = (0, 1, 2, 255, 256, (1 << 256) - 1, 1 << 255, (1 << 255) - 1)
CASE_SCHEMA = "solcore-lean.semantic-trait-hierarchy-case.v1"
PLAN_SCHEMA = "solcore-lean.trait-hierarchy-plan.v1"
PROFILE = "runtime-trait-hierarchies"
NAME = "SynthesizedTraitHierarchies"
NODES = 2048
CASE_LIMIT = 4096
SHRINK_BYTES = 1_500_000
SHAPES = {
    "instances": ["generic:binary", "generic:mix", "generic:unary", "plain:binary", "plain:mix", "plain:unary",
                  "sum:binary", "sum:mix", "sum:unary", "tuple:binary", "tuple:mix", "tuple:unary", "word:binary",
                  "word:mix", "word:unary"],
    "calls": ["binary:direct", "binary:function", "binary:sub", "binary:top", "binary:value", "mix:direct", "mix:top",
              "mix:value", "unary:direct", "unary:function", "unary:sub", "unary:top", "unary:value"],
    "depths": ["0", "1", "2", "3"],
    "arguments": ["generic", "plain", "sum", "tuple", "word"],
    "parameters": ["generic", "plain", "sum", "tuple", "word"],
    "forms": ["enum:columns", "enum:nested", "tuple:columns", "tuple:nested"],
    "subclass": ["marker", "mix", "shadow"]}
# Helper keys in plan order, and their source names.
HELPERS = {("sub", "unary"): "sc_up", ("sub", "binary"): "sc_up2", ("top", "unary"): "sc_top",
           ("top", "binary"): "sc_top2", ("value", "unary"): "sc_val", ("value", "binary"): "sc_val2",
           ("function", "unary"): "sc_fun", ("function", "binary"): "sc_fun2", ("top", "mix"): "sc_mixt",
           ("value", "mix"): "sc_mixv"}
CALLS = {"unary": ("direct", "sub", "top", "value", "function"), "binary": ("direct", "sub", "top", "value", "function"),
         "mix": ("direct", "top", "value")}


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
    """The types an impl's arms call its method at."""
    if ty == "word":
        return []
    if "tuple" in ty or "sum" in ty:
        return list(ty.get("tuple", ty.get("sum")))
    declaration = plan["declarations"][ty["enum"]]
    argument = ty.get("argument", "word")
    return [substitute(field, argument) for fields in declaration["constructors"] for field in fields]


def reached(plan):
    """The base closures, as (type, method), and the subclass closures, as
    (receiver, argument), the uses reach; a subclass closure at a Word also
    reaches the argument's unary base closure."""
    base, base_seen, mixes, mix_seen = [], set(), [], set()

    def visit(pending, seen, found, step):
        while pending:
            item = pending.pop()
            identity = json.dumps(item, sort_keys=True)
            if identity in seen:
                continue
            seen.add(identity)
            found.append(item)
            pending.extend(step(item))

    visit([(use["type"], argument["type"]) for use in plan["uses"] if use["method"] == "mix"
           for argument in use["arguments"]], mix_seen, mixes,
          lambda item: [(child, item[1]) for child in children(plan, item[0])])
    roots = [(use["type"], use["method"]) for use in plan["uses"] if use["method"] != "mix"]
    roots += [(argument, "unary") for receiver, argument in mixes if receiver == "word"]
    visit(roots, base_seen, base, lambda item: [(child, item[1]) for child in children(plan, item[0])])
    return base, mixes


def impl_form(plan, head):
    impls = [impl for impl in plan["impls"] if impl["head"] == head]
    require(len(impls) == 1, "a reached instance has no base impl")
    return impls[0]["form"]


def shapes(plan):
    """The trait hierarchy shapes from the plan alone."""
    found = {dimension: set() for dimension in SHAPES}
    base, mixes = reached(plan)
    for ty, method in base:
        found["instances"].add(f"{kind(ty)}:{method}")
        if method == "binary" and "tuple" in ty:
            found["forms"].add("tuple:" + impl_form(plan, "tuple"))
        if method == "binary" and "enum" in ty:
            found["forms"].add("enum:" + impl_form(plan, {"enum": ty["enum"]}))
    for ty, _ in mixes:
        found["instances"].add(f"{kind(ty)}:mix")
    for ty in [ty for ty, _ in base] + [ty for ty, _ in mixes]:
        if "argument" in ty:
            found["arguments"].add(kind(ty["argument"]))
    for use in plan["uses"]:
        found["calls"].add(f"{use['method']}:{use['call']}")
        found["depths"].add(str(depth(use["type"])))
        for argument in use["arguments"]:
            found["parameters"].add(kind(argument["type"]))
    found["subclass"].add(plan["subclass"])
    return found


def type_text(ty):
    if ty == "word":
        return "word"
    if "tuple" in ty:
        return "(" + ", ".join(type_text(part) for part in ty["tuple"]) + ")"
    if "sum" in ty:
        return "sum<" + ", ".join(type_text(part) for part in ty["sum"]) + ">"
    return f"Sc_T{ty['enum']}" + (f"<{type_text(ty['argument'])}>" if "argument" in ty else "")


def impl_header(plan, trait, head):
    if head == "word":
        return f"impl {trait}<word>"
    if head in ("tuple", "sum"):
        shape = "(f, g)" if head == "tuple" else "sum<f, g>"
        return f"impl<f, g> {trait}<{shape}> where f: {trait}, g: {trait}"
    index = head["enum"]
    if plan["declarations"][index]["generic"]:
        return f"impl<a> {trait}<Sc_T{index}<a>> where a: {trait}"
    return f"impl {trait}<Sc_T{index}>"


def arms(plan, head):
    return 1 if head in ("word", "tuple") else 2 if head == "sum" else len(plan["declarations"][head["enum"]]["constructors"])


def needed_helpers(uses):
    return [pair for pair in HELPERS if any(use["method"] == pair[1] and (use["call"] == pair[0] or (
        pair[0] == "sub" and use["call"] == "function")) for use in uses)]


def check_plan(plan):
    require(isinstance(plan, dict) and set(plan) == {"schema", "declarations", "methods", "impls", "subclass",
                                                     "subImpls", "tops", "helpers", "uses"}
            and plan["schema"] == PLAN_SCHEMA, "unexpected trait hierarchy plan schema")
    declarations = plan["declarations"]
    require(isinstance(declarations, list) and 1 <= len(declarations) <= 3, "one to three declarations")
    for declaration in declarations:
        require(set(declaration) == {"generic", "sameName", "constructors"}
                and 2 <= len(declaration["constructors"]) <= 4
                and all(len(fields) <= 2 for fields in declaration["constructors"]),
                "declarations have two to four constructors of at most two fields")
    require(plan["methods"] in (["unary"], ["binary"], ["unary", "binary"]), "base methods are unary, binary or both")
    require(plan["subclass"] in SHAPES["subclass"], "the subclass is a marker, mix or shadow")
    method = plan["subclass"] != "marker"
    require(not method or "unary" in plan["methods"], "the subclass method needs the unary base method")
    heads = ["word", "tuple", "sum", *({"enum": index} for index in range(len(declarations)))]
    for label, found in (("base", [impl["head"] for impl in plan["impls"]]),
                         ("subclass", [impl["head"] for impl in plan["subImpls"]]), ("chain", plan["tops"])):
        order = [heads.index(head) for head in found]
        require(order == sorted(set(order)), f"{label} impls are distinct, in the order Word, tuple, sum, declarations")
    base_heads = [impl["head"] for impl in plan["impls"]]
    sub_heads = [impl["head"] for impl in plan["subImpls"]]
    require(all(head in base_heads for head in sub_heads) and all(head in sub_heads for head in plan["tops"]),
            "every subclass and chain impl is over an impl of its superclass")
    for impl in plan["impls"]:
        head = impl["head"]
        for name in ("unary", "binary"):
            require(len(impl[name]) == (arms(plan, head) if name in plan["methods"] else 0),
                    "a base impl lacks an arm per constructor")
        mismatch = 2 if head == "sum" else 1 if isinstance(head, dict) else 0
        require(len(impl["mismatch"]) == (mismatch if "binary" in plan["methods"] else 0), "mismatch constants changed")
        require(impl["form"] == "nested" or (isinstance(head, dict) or head == "tuple"), "only tuples and enums have columns")
    for impl in plan["subImpls"]:
        require(len(impl["steps"]) == (arms(plan, impl["head"]) if method else 0),
                "a subclass impl lacks an arm per constructor, or a marker has one")
    uses = plan["uses"]
    require(isinstance(uses, list) and 1 <= len(uses) <= 6, "one to six uses")
    for use in uses:
        require(use["call"] in CALLS[use["method"]], "a use's call form does not fit its method")
        require(depth(use["type"]) <= 3, "uses call at depth 3 or less")
        if use["method"] == "mix":
            types = [argument["type"] for argument in use["arguments"]]
            require(method and use["shift"] == 0 and len(types) == 2 and key(types[0]) != key(types[1])
                    and all(depth(ty) <= 3 for ty in types), "a mix use calls a subclass method at two distinct types")
        else:
            require(use["method"] in plan["methods"] and use["arguments"] == []
                    and (use["shift"] == 0 if use["method"] == "unary" else 1 <= use["shift"] <= 4),
                    "a base use calls a present method with its shift")
        for builder in [use["builder"]] + [argument["builder"] for argument in use["arguments"]]:
            require(0 <= builder["offset"] < 4 and 1 <= len(builder["values"]) <= 4, "builders hold one to four values")
    require([(helper["call"], helper["method"]) for helper in plan["helpers"]] == needed_helpers(uses),
            "helpers are exactly those the uses need, in order")
    return plan


def check_source(case):
    """The source declares the three traits and every impl, helper and builder
    of the plan, and run calls every use."""
    plan, source = case["hierarchyPlan"], case["source"]
    for index, declaration in enumerate(plan["declarations"]):
        require(source.count(f"enum Sc_T{index}{'<a>' if declaration['generic'] else ''} {{\n") == 1,
                "a declaration is missing from the source")
    require(source.count("trait Sc_Fold<a> {\n") == 1, "the base trait is missing")
    for method, signature in (("unary", "function sc_fold(sc_x: a) returns (word);"),
                              ("binary", "function sc_both(sc_x: a, sc_y: a) returns (word);")):
        require((f"    {signature}\n" in source) == (method in plan["methods"]), "the base methods differ from the plan")
    name = "sc_fold" if plan["subclass"] == "shadow" else "sc_mix"
    if plan["subclass"] == "marker":
        require(source.count("trait Sc_Sub<a> where a: Sc_Fold {}\n") == 1, "the marker subclass is missing")
    else:
        require(source.count("trait Sc_Sub<a> where a: Sc_Fold {\n    function " + name +
                             "<u>(sc_x: a, sc_y: u) returns (word) where u: Sc_Fold;\n}\n") == 1,
                "the subclass method is missing or misnamed")
    require(source.count("trait Sc_Top<a> where a: Sc_Sub {}\n") == 1, "the chain is missing")
    for trait, heads, empty in (("Sc_Fold", [impl["head"] for impl in plan["impls"]], False),
                                ("Sc_Sub", [impl["head"] for impl in plan["subImpls"]], plan["subclass"] == "marker"),
                                ("Sc_Top", plan["tops"], True)):
        for head in heads:
            require(source.count(impl_header(plan, trait, head) + (" {}\n" if empty else " {\n")) == 1,
                    f"an impl of {trait} is missing")
    require(source.count("\nimpl") == len(plan["impls"]) + len(plan["subImpls"]) + len(plan["tops"]),
            "the source has an impl the plan lacks")
    for helper in plan["helpers"]:
        require(source.count(f"function {HELPERS[(helper['call'], helper['method'])]}<t") == 1, "a helper is missing")
    require(len(re.findall(r"^function sc_\w+<t", source, re.M)) == len(plan["helpers"]),
            "the source has a helper the plan lacks")
    for index, use in enumerate(plan["uses"]):
        require(source.count(f"function sc_u{index}(sc_x: word) returns ({type_text(use['type'])}) {{\n") == 1,
                "a receiver builder is missing")
        for prefix, argument in zip(("sc_v", "sc_w"), use["arguments"]):
            require(source.count(f"function {prefix}{index}(sc_x: word) returns ({type_text(argument['type'])}) {{\n") == 1,
                    "an argument builder is missing")
    require(source.count("let sc_r") == len(plan["uses"]) and f"contract {NAME} {{" in source,
            "run does not call every use")


def check_case(case, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected trait hierarchy case schema")
    plan = check_plan(case["hierarchyPlan"])
    number = canonical_word(case["input"])
    program = case["program"]
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == "word", "trait hierarchy reference must be a closed Word program")
    require(generic.complexity(program["body"])[0] <= CASE_LIMIT, "reference exceeds the case limit")
    require(case["provenance"]["referenceNodes"] <= CASE_LIMIT, "recorded reference size exceeds the case limit")
    require(case["contract"] == {"name": NAME, "method": "run", "signature": "run(uint256)",
            "deployPath": [NAME + "Deploy"], "runtimePath": [NAME + "Deploy", NAME],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "trait hierarchy ABI, runtime input, or contract metadata changed")
    require(isinstance(case.get("source"), str) and case.get("executionFuel") == fuel, "invalid emitted source or fuel")
    check_source(case)
    recorded = case["provenance"]["hierarchyShapes"]
    require({dimension: set(values) for dimension, values in recorded.items()} == shapes(plan),
            "recorded trait hierarchy shapes differ from the plan")
    require(all(values == sorted(set(values)) for values in recorded.values()),
            "trait hierarchy shapes are not sorted inventories")
    require(case["provenance"]["features"] == [], "the trait hierarchy profile records no G0 step features")
    return plan


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals", "requiredInputs",
              "hierarchyRequirements", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == PROFILE, "unexpected trait hierarchy manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "trait hierarchy coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    require(manifest["requiredFeatures"] == [] and manifest["requiredWordLiterals"] == [],
            "the trait hierarchy corpus requires shapes, not step features or literals")
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "the trait hierarchy corpus must require all eight boundary inputs")
    require(manifest["hierarchyRequirements"] == SHAPES, "the trait hierarchy corpus must require every shape value")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "the trait hierarchy corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"id", "generation", "input", "expectedFeatures"},
                "a trait hierarchy corpus entry is a generation recipe with its input")
        identifier = entry["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        require(canonical_word(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        require(entry["expectedFeatures"] == [], "trait hierarchy entries expect no step features")
        recipe = entry["generation"]
        require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
        require(canonical_word(recipe["seed"]) < 1 << 64 and recipe["maxProgramNodes"] == NODES,
                "fixed recipes use a uint64 seed and the default budget")
    return entries


def frontend_rejected(plan):
    """A base-method `top` use at a tuple, std sum or generic declaration, which
    the checked frontend rejects; the fixed corpus skips such plans."""
    return any(use["call"] == "top" and use["method"] != "mix" and kind(use["type"]) in ("tuple", "sum", "generic")
               for use in plan["uses"])


def generated_plan(tool, seed, fuel):
    """The seed's plan, or None for an excluded seed."""
    corpus = run(tool, "hierarchy-generate", str(seed), str(NODES), "1", "1", str(fuel))
    cases = corpus.get("cases")
    require(isinstance(cases, list) and len(cases) <= 1, "invalid generation response")
    return check_plan(cases[0]["hierarchyPlan"]) if cases else None


def selection(tool, fuel, last):
    """The roadmap's construction: from seed 1 upwards, every accepted seed
    whose plan covers a missing value and is not rejected by the frontend,
    until nothing is missing."""
    missing = {dimension: set(values) for dimension, values in SHAPES.items()}
    chosen = []
    for seed in range(1, last + 1):
        if not any(missing.values()):
            break
        plan = generated_plan(tool, seed, fuel)
        if plan is None or frontend_rejected(plan):
            continue
        found = shapes(plan)
        if any(missing[dimension] & found[dimension] for dimension in missing):
            chosen.append(seed)
            for dimension in missing:
                missing[dimension] -= found[dimension]
    require(not any(missing.values()), "seeds up to the last chosen one leave a requirement missing")
    return chosen


def materialize(entry, tool, fuel):
    recipe = entry["generation"]
    corpus = run(tool, "hierarchy-generate", recipe["seed"], str(recipe["maxProgramNodes"]), "8", "1", str(fuel))
    require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
            and corpus.get("requested") == 8 and corpus.get("attempted") == 1
            and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 8,
            "fixed trait hierarchy seed did not emit eight cases in one attempt")
    cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
    require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
    case = cases[0]
    origin = case["provenance"]["origin"]
    require(origin == {"kind": "hierarchy-generated", "seed": recipe["seed"],
                       "maxProgramNodes": recipe["maxProgramNodes"],
                       "inputIndex": BOUNDARIES.index(int(entry["input"])), "validationFuel": fuel},
            "generated recipe differs from manifest")
    check_case(case, fuel)
    require(not frontend_rejected(case["hierarchyPlan"]), "a fixed plan has a frontend-rejected top use")
    return case


def plan_size(plan):
    """The shrink measure's plan size, independently: declarations, base
    methods, impl arms, the subclass form, its impls' steps, the chain's
    impls, helpers, call forms, type nodes and value weights."""
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
    total += {"marker": 0, "mix": 1, "shadow": 2}[plan["subclass"]]
    total += sum(1 + len(impl["steps"]) for impl in plan["subImpls"]) + len(plan["tops"]) + len(plan["helpers"])
    for use in plan["uses"]:
        total += 1 + {"direct": 0, "sub": 1, "top": 2, "value": 2, "function": 2}[use["call"]] + nodes(use["type"])
        total += sum(value(tree) for tree in use["builder"]["values"])
        total += sum(nodes(argument["type"]) + sum(value(tree) for tree in argument["builder"]["values"])
                     for argument in use["arguments"])
    return total


def checked_shrinks(case, tool, directory, fuel):
    path = directory / "shrink-parent.json"
    path.write_text(json.dumps(case))
    reduced = run(tool, "shrink", str(path), "64", str(fuel))
    require(reduced == run(tool, "shrink", str(path), "64", str(fuel)), "native shrink order changed")
    candidates = reduced.get("cases")
    require(isinstance(candidates, list) and candidates, "fixed trait hierarchy case has no shrink candidate")
    require(sum(len(json.dumps(candidate, separators=(",", ":"))) for candidate in candidates) <= SHRINK_BYTES,
            "a shrink response exceeds its byte cap")
    parent = (plan_size(case["hierarchyPlan"]), int(case["input"]))
    seen = set()
    for candidate in candidates:
        check_case(candidate, fuel)
        require(candidate["provenance"]["origin"] == {"kind": "reduced", "parentPlan": case["hierarchyPlan"],
                                                      "parentInput": case["input"]},
                "a shrink candidate is not a reduction of its parent")
        require((plan_size(candidate["hierarchyPlan"]), int(candidate["input"])) < parent,
                "a shrink candidate is not strictly smaller")
        encoded = json.dumps([candidate["hierarchyPlan"], candidate["input"]], sort_keys=True)
        require(encoded not in seen, "duplicate canonical shrink")
        seen.add(encoded)
        target = directory / "shrunk.json"
        target.write_text(json.dumps(candidate))
        require(run(tool, "replay", str(target), str(fuel)) == candidate,
                "native shrink lost canonical source/program/provenance")
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

    for field, value in (("profile", "runtime-traits"), ("requiredInputs", ["0"]), ("requiredFeatures", ["let"]),
                         *(("hierarchyRequirements", {**SHAPES, dimension: SHAPES[dimension][1:]})
                           for dimension in SHAPES)):
        changed = copy.deepcopy(manifest)
        changed[field] = value
        rejects(lambda: check_manifest(changed), field)
    plan = sample["hierarchyPlan"]
    extra = {"call": "top", "method": "unary", "op": "add", "constant": "0"}
    for label, broken in (("no uses", {**plan, "uses": []}), ("seven uses", {**plan, "uses": plan["uses"] * 7}),
                          ("reversed impls", {**plan, "impls": plan["impls"][::-1]}),
                          ("reversed subclass impls", {**plan, "subImpls": plan["subImpls"][::-1]}),
                          ("a chain impl over no subclass impl", {**plan, "subImpls": plan["subImpls"][1:]}),
                          ("an unknown subclass", {**plan, "subclass": "deep"}),
                          ("an extra helper", {**plan, "helpers": plan["helpers"] + [extra] * 5})):
        rejects(lambda: check_plan(broken), label)
    path = directory / "negative.json"
    sub_index = 0 if sample["hierarchyPlan"]["subImpls"] else None
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("a missing base impl", lambda value: value["hierarchyPlan"]["impls"].pop(0)),
        ("base impls out of order", lambda value: value["hierarchyPlan"]["impls"].reverse()),
        ("a missing chain impl", lambda value: value["hierarchyPlan"]["tops"].pop(0)),
        ("subclass impls out of order", lambda value: value["hierarchyPlan"]["subImpls"].reverse()),
        ("an arm constant", lambda value: value["hierarchyPlan"]["impls"][0]["unary"][0].update(constant="07")),
        ("a subclass form", lambda value: value["hierarchyPlan"].update(
            subclass="marker" if value["hierarchyPlan"]["subclass"] != "marker" else "mix")),
        ("a helper", lambda value: value["hierarchyPlan"]["helpers"].append(extra)),
        ("a use's shift", lambda value: value["hierarchyPlan"]["uses"][0].update(shift=9)),
        ("an unknown declaration", lambda value: value["hierarchyPlan"]["uses"][0].update(type={"enum": 7})),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="1" if value["input"] != "1" else "2")),
        ("wrapper", lambda value: value["contract"].update(name="AnotherContract")),
        ("hierarchy shapes", lambda value: value["provenance"]["hierarchyShapes"].update(calls=[])),
        ("generator version", lambda value: value["provenance"].update(generatorVersion="another-version")),
    ):
        changed = copy.deepcopy(sample)
        change(changed)
        path.write_text(json.dumps(changed))
        result = subprocess.run([str(tool), "replay", str(path), str(fuel)], cwd=ROOT,
                                text=True, capture_output=True, timeout=60, check=False)
        require(result.returncode != 0, "native replay accepted altered " + label)
        count += 1
    require(sub_index is not None, "the sample plan has no subclass impl")
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
    for args in (("hierarchy-generate", str(1 << 64), "2048", "8", "1", str(fuel)),
                 ("hierarchy-generate", "1", "4097", "8", "1", str(fuel)),
                 ("hierarchy-generate", "1", "255", "8", "1", str(fuel)),
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
    with tempfile.TemporaryDirectory(prefix="trait-hierarchy-corpus-") as name:
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
            require(group["source"] == case["source"], "identical trait hierarchy plan emitted input-dependent source")
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
            require(group["inputs"] == set(BOUNDARIES), "trait hierarchy plan lacks a completed boundary input")
            require(len(group["results"]) > 1, "fixed trait hierarchy plan returned one Word for every boundary input")
        require(seeds == selection(tool, fuel, max(seeds)), "the corpus is not every covering seed in order")
        with_method = next(case for case in samples if case["hierarchyPlan"]["subclass"] != "marker")
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in [samples[0], with_method])
        checks = policy_checks(manifest, with_method, tool, directory, fuel)
    return {"status": "passed", "profile": PROFILE, "cases": len(entries), "plans": len(groups),
            "seeds": seeds, "completedInputs": [str(value) for value in sorted(inputs)],
            "hierarchyCoverage": {"classification": "specified-by-the-plan-not-measured-specialization",
                                  **{dimension: sorted(values) for dimension, values in found.items()}},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path,
                        default=ROOT / "scripts/semantic-trait-hierarchy-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
