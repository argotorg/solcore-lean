#!/usr/bin/env python3
"""Check the fixed inline Yul loop corpus using fresh native Core executions.

The corpus is the first generated plan of each of the fifteen shapes (mask and
form) from seed 1 upwards at the default budget, each at the six loop boundary
inputs, skipping steps that shift by a count that may fold to a constant of at
least 2^64, through lets, conditionals or calls: such counts crash Sonatina
code-image export (recorded locally), so the corpus does not track that known
upstream defect; random campaigns still generate them. This test rebuilds that selection, reads
features, helper counts and call shapes independently from the original AST,
recomputes each prescribed iteration count `input & mask`, and replays,
observes and shrinks natively. It neither compiles Rust nor executes an EVM and
implements no arithmetic result oracle.
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
spec = importlib.util.spec_from_file_location("assembly_loop_corpus_ast", ROOT / "Tests/scripts/test-semantic-corpus.py")
pure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pure)
generic_spec = importlib.util.spec_from_file_location("assembly_loop_corpus_generic", ROOT / "Tests/scripts/test-semantic-generic-corpus.py")
generic = importlib.util.module_from_spec(generic_spec)
generic_spec.loader.exec_module(generic)
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
complexity, returned, strings, integers = generic.complexity, generic.returned, generic.strings, generic.integers
VERSIONS = pure.VERSIONS + ("profileVersion", "functionVersion", "loopVersion", "stepFunctionVersion", "aggregateVersion",
                            "boundaryVersion", "stepBoundaryVersion", "callShapeVersion", "loopProfileVersion")
FEATURES = pure.FEATURES | pure.PRIMITIVE_FEATURES | {"functionCall"}
BOUNDARIES = (0, 1, 3, 7, (1 << 256) - 1, 1 << 255)
FORMS = ("for", "break", "continue", "leave", "pair")
SHAPES = [f"{mask}:{form}" for form in FORMS for mask in (1, 3, 7)]
FORM_ITERATIONS = [f"{form}:{count}" for form in FORMS for count in (0, 1, 3, 7)]
CALL_SHAPES = ["skipped-helper", "multiple-callees", "shared-callee", "nested-call", "branch-call", "local-call",
               "diamond", "predicate-call", "primitive-operand-call"]
CASE_SCHEMA = "solcore-lean.semantic-assembly-loop-case.v1"
PLAN_SCHEMA = "solcore-lean.assembly-loop-plan.v1"
NAME = "SynthesizedAssemblyLoops"
NODES = 256
# The line that only each form's loop has.
MARKERS = {"for": "            for { let sc_i := 0 } lt(sc_i, sc_limit) { sc_i := add(sc_i, 1) } {",
           "break": "                if iszero(lt(sc_i, sc_limit)) { break }",
           "continue": "                if iszero(lt(sc_i, sc_limit)) { continue }",
           "leave": "                    if iszero(lt(sc_i, sc_limit)) { leave }",
           "pair": "                sc_acc, sc_i := sc_iterate(sc_acc, sc_i)"}
SHIFTS = {"wordShl", "wordShr", "wordSar"}
CHILDREN = {"word": (), "bool": (), "var": (), "let": ("initializer", "body"),
            "if": ("condition", "thenBranch", "elseBranch"), "unary": ("operand",), "binary": ("left", "right"),
            "ternary": ("first", "second", "third"), "apply": ("argument",)}


def constant(expression, scope, helpers):
    """Whether an expression may fold to a compile-time constant: a literal, a
    local bound to one, an operation on such values, a conditional whose
    branches may both fold or whose condition and either branch may fold, or a
    call to a helper whose result may fold for such an argument. `scope` gives
    each Word local's answer, nearest first, and `helpers` the facts of each
    earlier helper, nearest first."""
    tag = expression["tag"]
    if tag in ("word", "bool"):
        return True
    if tag == "var":
        return scope[expression["index"]]
    if tag == "let":
        return constant(expression["body"], [constant(expression["initializer"], scope, helpers), *scope], helpers)
    if tag == "if":
        condition, yes, no = (constant(expression[key], scope, helpers) for key in CHILDREN["if"])
        return (yes and no) or (condition and (yes or no))
    if tag == "apply":
        callee = helpers[expression["function"]["index"] - len(scope)]
        return callee["folds"] or (callee["foldsFromConstant"] and constant(expression["argument"], scope, helpers))
    return all(constant(expression[key], scope, helpers) for key in CHILDREN[tag])


def constant_shift(expression, scope, helpers):
    """Whether some shift's count may fold to a constant other than a literal
    below 2^64, here or in a helper this expression calls with an argument that
    may fold. Core `wordShl(v, n)` shifts `v` by `n`."""
    tag = expression["tag"]
    if tag == "binary" and expression["op"] in SHIFTS:
        count = expression["right"]
        if constant(count, scope, helpers) and not (count["tag"] == "word" and int(count["value"], 16) < 1 << 64):
            return True
    if tag == "apply":
        callee = helpers[expression["function"]["index"] - len(scope)]
        if callee["shiftsFromConstant"] and constant(expression["argument"], scope, helpers):
            return True
    if tag == "let":
        return (constant_shift(expression["initializer"], scope, helpers)
                or constant_shift(expression["body"], [constant(expression["initializer"], scope, helpers), *scope], helpers))
    return any(constant_shift(expression[key], scope, helpers) for key in CHILDREN[tag])


def safe(bodies, entry):
    """No helper shifts by a count that may fold as compiled on its own, no
    call passes a helper an argument that makes one fold, and neither does the
    entry, whose argument is the loop-carried accumulator."""
    helpers = []
    for body in bodies:
        facts = {"folds": constant(body, [False], helpers), "foldsFromConstant": constant(body, [True], helpers),
                 "shiftsFromConstant": constant_shift(body, [True], helpers)}
        if constant_shift(body, [False], helpers):
            return False
        helpers = [facts, *helpers]
    return not constant_shift(entry, [False], helpers)


def check_plan(plan):
    require(isinstance(plan, dict) and set(plan) == {"schema", "stepProgram", "mask", "form"}
            and plan["schema"] == PLAN_SCHEMA and plan["form"] in FORMS
            and type(plan["mask"]) is int and plan["mask"] in (0, 1, 3, 7), "invalid assembly loop plan")
    step = plan["stepProgram"]
    require(isinstance(step, dict) and set(step) == {"schema", "dataDefinitions", "resultType", "body"}
            and step["schema"] == "solcore-semantic-core" and step["dataDefinitions"] == []
            and step["resultType"] == {"tag": "function", "parameter": "word", "result": "word"},
            "assembly loop step must retain a closed Word function DAG")
    return pure.function_parts(step["body"])


def shape(plan):
    return f"{plan['mask']}:{plan['form']}"


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals", "requiredInputs",
              "requiredHelperCounts", "requiredCallShapes", "loopRequirements", "assemblyLoopRequirements",
              "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == "runtime-assembly-loops", "unexpected assembly loop manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "assembly loop AST coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    required = strings(manifest["requiredFeatures"], "requiredFeatures")
    loop = json.loads((ROOT / "scripts/semantic-call-graph-loop-corpus.json").read_text())
    require(required <= FEATURES and required == set(loop["requiredFeatures"]),
            "assembly loop corpus must require every step AST feature of the call-graph loop corpus")
    require(manifest["requiredWordLiterals"] == [], "assembly loop corpus requires no literal")
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "assembly loop corpus must require all six boundary inputs")
    integers(manifest["requiredHelperCounts"], {1, 2, 3}, "requiredHelperCounts")
    require(manifest["requiredCallShapes"] == CALL_SHAPES, "assembly loop corpus must require every call shape")
    require(manifest["loopRequirements"] == {"masks": [1, 3, 7], "iterations": [0, 1, 3, 7]},
            "assembly loop corpus must require the generated masks and iterations 0, 1, 3 and 7")
    require(manifest["assemblyLoopRequirements"] == {"shapes": SHAPES, "formIterations": FORM_ITERATIONS},
            "assembly loop corpus must require every shape and every form at 0, 1, 3 and 7 iterations")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "assembly loop corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"id", "generation", "input", "expectedFeatures",
                                                           "expectedCallShapes", "expectedHelperCount"},
                "an assembly loop corpus entry is a generation recipe with its input, features, call shapes and helpers")
        identifier = entry["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        require(canonical_word(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        expected = strings(entry["expectedFeatures"], "expectedFeatures")
        require(expected and expected <= FEATURES, "unsupported expected step feature")
        require(isinstance(entry["expectedCallShapes"], list) and set(entry["expectedCallShapes"]) <= set(CALL_SHAPES)
                and type(entry["expectedHelperCount"]) is int and 1 <= entry["expectedHelperCount"] <= 3,
                "invalid expected call shapes or helper count")
        recipe = entry["generation"]
        require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
        require(canonical_word(recipe["seed"]) < 1 << 64 and recipe["maxProgramNodes"] == NODES,
                "fixed recipes use a uint64 seed and the default budget")
    return entries


def check_case(case, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected assembly loop case schema")
    plan = case["assemblyLoopPlan"]
    helpers, body = check_plan(plan)
    number = canonical_word(case["input"])
    program = case["program"]
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == "word", "assembly loop reference must be a closed Word program")
    application = program["body"]
    require(application.get("tag") == "apply" and application.get("argument", {}).get("tag") == "word"
            and int(application["argument"]["value"], 16) == number, "original Core argument differs from runtime input")
    require(complexity(application)[0] + 2 <= 512, "canonical applied reference exceeds node limit")
    require(case["contract"] == {"name": NAME, "method": "run", "signature": "run(uint256)",
            "deployPath": [NAME + "Deploy"], "runtimePath": [NAME + "Deploy", NAME],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "assembly loop ABI, runtime input, or contract metadata changed")
    require(isinstance(case.get("source"), str) and case.get("executionFuel") == fuel, "invalid emitted source or fuel")
    source = case["source"]
    require(source.count("assembly {") == 1 and source.count("            function sc_fn") == len(helpers),
            "the source does not render one assembly block with one Yul function per helper")
    require(all(source.count(marker) == (form == plan["form"]) for form, marker in MARKERS.items()),
            "the source lacks its form's loop or has another form's")
    return helpers, body


def iterations(case):
    """The prescribed iteration count, recomputed from the plan and the input."""
    return int(case["input"]) & case["assemblyLoopPlan"]["mask"]


def generated_plan(tool, seed, fuel):
    """The seed's first accepted case, or None for an excluded seed."""
    corpus = run(tool, "assembly-loop-generate", str(seed), str(NODES), "1", "1", str(fuel))
    cases = corpus.get("cases")
    require(isinstance(cases, list) and len(cases) <= 1, "invalid generation response")
    if not cases:
        return None
    helpers, body = check_plan(cases[0]["assemblyLoopPlan"])
    return shape(cases[0]["assemblyLoopPlan"]), safe(helpers, body)


def selection(tool, fuel, last):
    """The roadmap's construction: from seed 1 upwards, the first seed of each
    shape whose step shifts by no count that may fold to a constant of at
    least 2^64."""
    chosen = {}
    for seed in range(1, last + 1):
        result = generated_plan(tool, seed, fuel)
        if result is not None and result[1] and result[0] not in chosen:
            chosen[result[0]] = seed
    return chosen


def materialize(entry, tool, fuel):
    recipe = entry["generation"]
    corpus = run(tool, "assembly-loop-generate", recipe["seed"], str(recipe["maxProgramNodes"]), "6", "1", str(fuel))
    require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
            and corpus.get("requested") == 6 and corpus.get("attempted") == 1
            and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 6,
            "fixed assembly loop seed did not emit six cases in one attempt")
    cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
    require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
    case = cases[0]
    origin, plan = case["provenance"]["origin"], case["assemblyLoopPlan"]
    require(origin.get("kind") == "assembly-loop-generated" and origin.get("seed") == recipe["seed"]
            and origin.get("maxProgramNodes") == recipe["maxProgramNodes"]
            and origin.get("inputIndex") == BOUNDARIES.index(int(entry["input"]))
            and origin.get("validationFuel") == fuel
            and (origin.get("mask"), origin.get("form")) == (plan["mask"], plan["form"]),
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
    require(isinstance(candidates, list) and 0 < len(candidates) <= 4, "fixed assembly loop case has no bounded shrink candidates")
    parent, (parent_helpers, _) = case["assemblyLoopPlan"], check_plan(case["assemblyLoopPlan"])
    seen = set()
    for candidate in candidates:
        helpers, _ = check_case(candidate, fuel)
        plan = candidate["assemblyLoopPlan"]
        require(len(helpers) == len(parent_helpers) and plan["mask"] <= parent["mask"] and plan["form"] == parent["form"],
                "shrink changed the helper count, raised the mask or changed the form")
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

    for key, value in (("profile", "runtime-call-graph-loops"), ("requiredHelperCounts", [True, 2, 3]),
                       ("requiredInputs", ["0"]), ("requiredCallShapes", CALL_SHAPES[1:]),
                       ("loopRequirements", {"masks": [0, 1, 3, 7], "iterations": [0, 1, 3, 7]}),
                       ("assemblyLoopRequirements", {"shapes": SHAPES[1:], "formIterations": FORM_ITERATIONS}),
                       ("assemblyLoopRequirements", {"shapes": SHAPES, "formIterations": FORM_ITERATIONS[1:]})):
        changed = copy.deepcopy(manifest)
        changed[key] = value
        rejects(lambda: check_manifest(changed), key)
    path = directory / "negative.json"
    plan = sample["assemblyLoopPlan"]
    other = FORMS[(FORMS.index(plan["form"]) + 1) % len(FORMS)]
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("mask", lambda value: value["assemblyLoopPlan"].update(mask=3 if plan["mask"] == 7 else 7)),
        ("form", lambda value: value["assemblyLoopPlan"].update(form=other)),
        ("origin form", lambda value: value["provenance"]["origin"].update(form=other)),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="3" if value["input"] != "3" else "7")),
        ("wrapper", lambda value: value["contract"].update(name="AnotherContract")),
        ("profile version", lambda value: value["provenance"].update(loopProfileVersion="another-version")),
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
    for args in (("assembly-loop-generate", str(1 << 64), "256", "6", "1", str(fuel)),
                 ("assembly-loop-generate", "1", "513", "6", "1", str(fuel)),
                 ("assembly-loop-generate", "1", "256", "6", "1", str(fuel), "exclude-boundary-identity-v1"),
                 ("assembly-loop-generate", "1", "256", "6", "1", str(fuel), "core-g0-v4/lcg64-v1"),
                 ("shrink", str(path), "4097", str(fuel))):
        result = subprocess.run([str(tool), *args], cwd=ROOT, text=True, capture_output=True, timeout=30, check=False)
        require(result.returncode != 0, "native CLI accepted an out-of-range budget or an inapplicable option")
        count += 1
    return count


def validate(manifest, tool, fuel):
    require(type(fuel) is int and 0 < fuel <= 10_000_000, "invalid positive execution fuel")
    entries = check_manifest(manifest)
    features, inputs, helpers_seen, call_shapes = set(), set(), set(), set()
    shapes, counts, masks, form_iterations = set(), set(), set(), set()
    groups, samples, seeds = {}, {}, []
    with tempfile.TemporaryDirectory(prefix="semantic-assembly-loop-corpus-") as name:
        directory = Path(name)
        for entry in entries:
            case = materialize(entry, tool, fuel)
            require(case == materialize(entry, tool, fuel), "materialization is not deterministic")
            for version in VERSIONS:
                require(case["provenance"][version] == manifest[version], f"{version} changed")
            helpers, body = check_case(case, fuel)
            require(safe(helpers, body), "a fixed step shifts by a count that may fold to a constant of at least 2^64")
            actual, _ = pure.ast_coverage(helpers + [body], function_calls=True)
            require(actual == set(case["provenance"]["features"]) == set(entry["expectedFeatures"]),
                    "declared features differ from the step AST")
            require(case["provenance"]["helperCount"] == len(helpers) == entry["expectedHelperCount"],
                    "declared helper count differs from the step declarations")
            require(case["provenance"]["callShapes"] == entry["expectedCallShapes"], "declared call shapes changed")
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
            plan = case["assemblyLoopPlan"]
            key = json.dumps(plan, sort_keys=True)
            if key not in groups:
                seeds.append((shape(plan), int(entry["generation"]["seed"])))
            group = groups.setdefault(key, {"inputs": set(), "source": case["source"], "changed": False})
            require(group["source"] == case["source"], "identical assembly loop plan emitted input-dependent source")
            group["inputs"].add(number)
            group["changed"] |= iterations(case) > 0 and int(result) != number
            if iterations(case) > 0:
                samples.setdefault(plan["form"], case)
            # Only completed, replayed native cases contribute coverage.
            features.update(actual)
            inputs.add(number)
            helpers_seen.add(len(helpers))
            call_shapes.update(case["provenance"]["callShapes"])
            shapes.add(shape(plan))
            masks.add(plan["mask"])
            counts.add(iterations(case))
            form_iterations.add(f"{plan['form']}:{iterations(case)}")
        require(features == set(manifest["requiredFeatures"]), "lost exact step feature union")
        require(inputs == set(BOUNDARIES) and helpers_seen == {1, 2, 3} and call_shapes == set(CALL_SHAPES),
                "lost completed input, helper or call-shape coverage")
        require(shapes == set(SHAPES) and masks == {1, 3, 7} and counts == {0, 1, 3, 7}
                and form_iterations == set(FORM_ITERATIONS), "lost a completed shape, mask or prescribed iteration count")
        for group in groups.values():
            require(group["inputs"] == set(BOUNDARIES), "assembly loop plan lacks a completed boundary input")
            require(group["changed"], "fixed assembly loop plan returned every positive-trip boundary input unchanged")
        # The construction: the first seed of each shape, in shape order, and no other function.
        expected = selection(tool, fuel, max(seed for _, seed in seeds))
        require(seeds == [(name, expected[name]) for name in SHAPES],
                "the corpus is not the first seed of each shape without a constant shift count")
        require(set(samples) == set(FORMS), "missing shrink/policy fixtures for every form")
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in samples.values())
        checks = policy_checks(manifest, samples["leave"], tool, directory, fuel)
    return {"status": "passed", "profile": "runtime-assembly-loops", "cases": len(entries), "functionGroups": len(groups),
            "coverageKind": "step-core-ast-features", "requiredFeatures": len(features),
            "completedInputs": [str(value) for value in sorted(inputs)], "completedHelperCounts": sorted(helpers_seen),
            "callShapes": sorted(call_shapes),
            "assemblyLoopCoverage": {"classification": "prescribed-iterations-not-execution-trace", "shapes": sorted(shapes),
                                     "formIterations": sorted(form_iterations)},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path, default=ROOT / "scripts/semantic-assembly-loop-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
