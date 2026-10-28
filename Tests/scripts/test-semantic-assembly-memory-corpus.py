#!/usr/bin/env python3
"""Check the fixed inline Yul memory corpus using fresh native Core executions.

The corpus takes, from seed 1 upwards at the default budget, every generated
plan that covers a missing memory shape, each at the eight primitive boundary
inputs, skipping plans whose step may compile to a shift by a count that folds
to a constant of at least 2^64, through lets, conditionals or memory: such
counts crash Sonatina code-image export (recorded locally), so the corpus does
not track that known upstream defect; random campaigns still generate them.
This test rebuilds that selection, recomputes every memory shape from the
schedule alone and the step's features from its original AST, and replays,
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
spec = importlib.util.spec_from_file_location("assembly_memory_corpus_ast", ROOT / "Tests/scripts/test-semantic-corpus.py")
pure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pure)
generic_spec = importlib.util.spec_from_file_location("assembly_memory_corpus_generic", ROOT / "Tests/scripts/test-semantic-generic-corpus.py")
generic = importlib.util.module_from_spec(generic_spec)
generic_spec.loader.exec_module(generic)
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
returned, strings = generic.returned, generic.strings
VERSIONS = pure.VERSIONS + ("profileVersion", "functionVersion", "abstractionVersion", "baseGeneratorVersion",
                            "boundaryVersion", "functionProfileVersion", "memoryVersion")
FEATURES = pure.FEATURES | pure.PRIMITIVE_FEATURES
BOUNDARIES = (0, 1, 2, 255, 256, (1 << 256) - 1, 1 << 255, (1 << 255) - 1)
CASE_SCHEMA = "solcore-lean.semantic-assembly-memory-case.v1"
PLAN_SCHEMA = "solcore-lean.assembly-memory-plan.v1"
NAME = "SynthesizedAssemblyMemory"
NODES = 96
CASE_LIMIT = 3282
HASH_LENGTHS = (0, 1, 31, 32, 33, 64)
DELTA_CLASSES = (("0", 0, 0), ("1", 1, 1), ("2-15", 2, 15), ("16", 16, 16), ("17-30", 17, 30), ("31", 31, 31))
SHAPES = {
    "stages": ["1", "2", "3"],
    "accesses": [f"{kind}:{name}" for kind in ("read", "word", "byte") for name, _, _ in DELTA_CLASSES],
    "hazards": ["waw:word-word", "waw:word-byte", "waw:byte-word", "waw:byte-byte",
                "raw:same", "raw:overlap", "raw:byte", "raw:hash"],
    "hashes": ["none", *(str(length) for length in HASH_LENGTHS)]}
# Generated but not required: two byte writes at one byte.
REQUIRED = {**SHAPES, "hazards": [value for value in SHAPES["hazards"] if value != "waw:byte-byte"]}
SHIFTS = {"wordShl", "wordShr", "wordSar"}
CHILDREN = {"word": (), "bool": (), "var": (), "let": ("initializer", "body"),
            "if": ("condition", "thenBranch", "elseBranch"), "unary": ("operand",), "binary": ("left", "right"),
            "ternary": ("first", "second", "third")}


def delta_class(offset):
    return next(name for name, low, high in DELTA_CLASSES if low <= offset % 32 <= high)


def shapes(plan):
    """Every specified memory shape from the schedule alone. Each byte's last
    writer is a prologue Word or a stage; an overwrite of an earlier stage's
    byte counts when a later read or the hash reads it before it is written
    again."""
    owner = [None] * 96
    writes, pending = [], {}
    found = {"stages": {str(len(plan["stages"]))}, "accesses": set(), "hazards": set(),
             "hashes": {"none" if plan["hash"] is None else str(plan["hash"]["length"])}}

    def read(offset, length, word):
        for index in range(offset, offset + length):
            if index in pending:
                found["hazards"].add("waw:" + pending[index])
        stages = [owner[index] for index in range(offset, offset + length) if owner[index] is not None]
        if not word:
            if stages:
                found["hazards"].add("raw:hash")
            return
        if len(stages) == 32 and len(set(stages)) == 1 and writes[stages[0]] == ("word", offset):
            found["hazards"].add("raw:same")
        if any(writes[stage][0] == "word" and writes[stage][1] != offset for stage in stages):
            found["hazards"].add("raw:overlap")
        if any(writes[stage][0] == "byte" for stage in stages):
            found["hazards"].add("raw:byte")

    for index, stage in enumerate(plan["stages"]):
        found["accesses"].add("read:" + delta_class(stage["read"]))
        read(stage["read"], 32, True)
        width, offset = stage["width"], stage["write"]
        found["accesses"].add(f"{width}:{delta_class(offset)}")
        for byte in range(offset, offset + (32 if width == "word" else 1)):
            if owner[byte] is not None:
                pending[byte] = f"{writes[owner[byte]][0]}-{width}"
            owner[byte] = index
        writes.append((width, offset))
    found["accesses"].add("read:" + delta_class(plan["finalRead"]))
    read(plan["finalRead"], 32, True)
    if plan["hash"] is not None:
        read(plan["hash"]["offset"], plan["hash"]["length"], False)
    return found


def constant(expression, scope):
    """Whether an expression may fold to a compile-time constant: a literal, a
    local bound to one, an operation on such values, or a conditional whose
    branches may both fold or whose condition and either branch may fold."""
    tag = expression["tag"]
    if tag in ("word", "bool"):
        return True
    if tag == "var":
        return scope[expression["index"]]
    if tag == "let":
        return constant(expression["body"], [constant(expression["initializer"], scope), *scope])
    if tag == "if":
        condition, yes, no = (constant(expression[key], scope) for key in CHILDREN["if"])
        return (yes and no) or (condition and (yes or no))
    return all(constant(expression[key], scope) for key in CHILDREN[tag])


def constant_shift(expression, scope):
    """Whether some shift's count may fold to a constant other than a literal
    below 2^64. Core `wordShl(v, n)` shifts `v` by `n`."""
    tag = expression["tag"]
    if tag == "binary" and expression["op"] in SHIFTS:
        count = expression["right"]
        if constant(count, scope) and not (count["tag"] == "word" and int(count["value"], 16) < 1 << 64):
            return True
    if tag == "let":
        return (constant_shift(expression["initializer"], scope)
                or constant_shift(expression["body"], [constant(expression["initializer"], scope), *scope]))
    return any(constant_shift(expression[key], scope) for key in CHILDREN[tag])


def safe(body, plan):
    """The step compiled on its own shifts by no count that may fold, and no
    application passes it a read that may fold and makes one fold. A read may
    fold when every byte it reads was last written by a value that may: the
    input and its complement never do, and the step's result does when it may
    fold for its argument."""
    if constant_shift(body, [False]):
        return False
    folds, from_constant, shifts_from_constant = constant(body, [False]), constant(body, [True]), constant_shift(body, [True])
    foldable = [False] * 32 + [folds] * 32 + [False] * 32

    def apply(argument):
        if argument and shifts_from_constant:
            return None
        return folds or (from_constant and argument)

    for stage in plan["stages"]:
        value = apply(all(foldable[stage["read"]:stage["read"] + 32]))
        if value is None:
            return False
        width = 32 if stage["width"] == "word" else 1
        foldable[stage["write"]:stage["write"] + width] = [value] * width
    return apply(all(foldable[plan["finalRead"]:plan["finalRead"] + 32])) is not None


def check_plan(plan):
    require(isinstance(plan, dict) and set(plan) == {"schema", "functionProgram", "stages", "finalRead", "hash"}
            and plan["schema"] == PLAN_SCHEMA, "invalid assembly memory plan")
    stages = plan["stages"]
    require(isinstance(stages, list) and 1 <= len(stages) <= 3, "a plan has one to three stages")
    for stage in stages:
        require(isinstance(stage, dict) and set(stage) == {"read", "width", "write"} and stage["width"] in ("word", "byte")
                and type(stage["read"]) is int and 0 <= stage["read"] <= 64 and type(stage["write"]) is int
                and 0 <= stage["write"] <= (64 if stage["width"] == "word" else 95), "a stage leaves the window")
    require(type(plan["finalRead"]) is int and 0 <= plan["finalRead"] <= 64, "the final read leaves the window")
    hash_ = plan["hash"]
    require(hash_ is None or (isinstance(hash_, dict) and set(hash_) == {"offset", "length"}
            and hash_["length"] in HASH_LENGTHS and type(hash_["offset"]) is int
            and 0 <= hash_["offset"] <= 96 - hash_["length"]), "the hash leaves the window or has another length")
    step = plan["functionProgram"]
    require(isinstance(step, dict) and step.get("schema") == "solcore-semantic-core" and step.get("dataDefinitions") == []
            and step.get("resultType") == {"tag": "function", "parameter": "word", "result": "word"}
            and step["body"].get("tag") == "lambda", "the step must stay a closed Word function")
    return step["body"]["body"]


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals", "requiredInputs",
              "assemblyMemoryRequirements", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == "runtime-assembly-memory", "unexpected assembly memory manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "assembly memory AST coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    require(manifest["requiredFeatures"] == [] and manifest["requiredWordLiterals"] == [],
            "assembly memory corpus requires memory shapes, not step features or literals")
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "assembly memory corpus must require all eight boundary inputs")
    require(manifest["assemblyMemoryRequirements"] == REQUIRED,
            "assembly memory corpus must require every stage count, access, required hazard and hash option")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "assembly memory corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"id", "generation", "input", "expectedFeatures"},
                "an assembly memory corpus entry is a generation recipe with its input and features")
        identifier = entry["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        require(canonical_word(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        expected = strings(entry["expectedFeatures"], "expectedFeatures")
        require(expected <= FEATURES, "unsupported expected step feature")
        recipe = entry["generation"]
        require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
        require(canonical_word(recipe["seed"]) < 1 << 64 and recipe["maxProgramNodes"] == NODES,
                "fixed recipes use a uint64 seed and the default budget")
    return entries


def check_case(case, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected assembly memory case schema")
    plan = case["assemblyMemoryPlan"]
    body = check_plan(plan)
    number = canonical_word(case["input"])
    program = case["program"]
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == "word", "assembly memory reference must be a closed Word program")
    require(generic.complexity(program["body"])[0] <= CASE_LIMIT, "reference exceeds the case limit")
    require(case["contract"] == {"name": NAME, "method": "run", "signature": "run(uint256)",
            "deployPath": [NAME + "Deploy"], "runtimePath": [NAME + "Deploy", NAME],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "assembly memory ABI, runtime input, or contract metadata changed")
    require(isinstance(case.get("source"), str) and case.get("executionFuel") == fuel, "invalid emitted source or fuel")
    source = case["source"]
    require(source.count("assembly {") == 1 and source.count("            function sc_step(sc_arg) -> sc_ret {") == 1
            and source.count("let sc_base := mload(64)") == 1 and "mstore(64" not in source,
            "the source does not take one base from the free-memory pointer in one block with one step function")
    stores = sum(source.count(f"{'mstore' if stage['width'] == 'word' else 'mstore8'}({address(stage['write'])}, sc_step(sc_m{index}))")
                 for index, stage in enumerate(plan["stages"]))
    require(stores == len(plan["stages"]) and source.count("keccak256(") == (plan["hash"] is not None),
            "the source does not render each stage's write and the hash")
    return body


def address(offset):
    return "sc_base" if offset == 0 else f"add(sc_base, {offset})"


def generated_plan(tool, seed, fuel):
    """The seed's first accepted case, or None for an excluded seed."""
    corpus = run(tool, "assembly-memory-generate", str(seed), str(NODES), "1", "1", str(fuel), "core-g0-v1/lcg64-v1")
    cases = corpus.get("cases")
    require(isinstance(cases, list) and len(cases) <= 1, "invalid generation response")
    if not cases:
        return None
    plan = cases[0]["assemblyMemoryPlan"]
    return shapes(plan), safe(check_plan(plan), plan)


def selection(tool, fuel, last):
    """The roadmap's construction: from seed 1 upwards, every accepted seed
    whose plan passes the shift rule and covers a missing required value,
    until nothing is missing."""
    missing = {key: set(values) for key, values in REQUIRED.items()}
    chosen = []
    for seed in range(1, last + 1):
        if not any(missing.values()):
            break
        result = generated_plan(tool, seed, fuel)
        if result is None or not result[1]:
            continue
        if any(missing[key] & result[0][key] for key in missing):
            chosen.append(seed)
            for key in missing:
                missing[key] -= result[0][key]
    require(not any(missing.values()), "seeds up to the last chosen one leave a requirement missing")
    return chosen


def materialize(entry, tool, fuel):
    recipe = entry["generation"]
    corpus = run(tool, "assembly-memory-generate", recipe["seed"], str(recipe["maxProgramNodes"]), "8", "1", str(fuel),
                 "core-g0-v1/lcg64-v1")
    require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
            and corpus.get("requested") == 8 and corpus.get("attempted") == 1
            and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 8,
            "fixed assembly memory seed did not emit eight cases in one attempt")
    cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
    require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
    case = cases[0]
    origin = case["provenance"]["origin"]
    require(origin.get("kind") == "assembly-memory-generated" and origin.get("seed") == recipe["seed"]
            and origin.get("maxProgramNodes") == recipe["maxProgramNodes"]
            and origin.get("inputIndex") == BOUNDARIES.index(int(entry["input"]))
            and origin.get("validationFuel") == fuel, "generated recipe differs from manifest")
    check_case(case, fuel)
    return case


def checked_shrinks(case, tool, directory, fuel):
    path = directory / "shrink-parent.json"
    path.write_text(json.dumps(case))
    reduced = run(tool, "shrink", str(path), "64", str(fuel))
    require(reduced == run(tool, "shrink", str(path), "64", str(fuel)), "native shrink order changed")
    candidates = reduced.get("cases")
    limit = 8 if case["assemblyMemoryPlan"]["hash"] is not None else 64
    require(isinstance(candidates, list) and 0 < len(candidates) <= limit,
            "fixed assembly memory case has no shrink candidate or exceeds its batch")
    seen = set()
    for candidate in candidates:
        check_case(candidate, fuel)
        require(candidate["provenance"]["origin"]["kind"] == "reduced"
                and candidate["provenance"]["origin"]["parentPlan"] == case["assemblyMemoryPlan"],
                "a shrink candidate is not a reduction of its parent")
        encoded = json.dumps([candidate["assemblyMemoryPlan"], candidate["input"]], sort_keys=True)
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

    for key, value in (("profile", "runtime-assembly"), ("requiredInputs", ["0"]),
                       ("requiredFeatures", ["let"]),
                       *(("assemblyMemoryRequirements", {**REQUIRED, key: REQUIRED[key][1:]}) for key in REQUIRED)):
        changed = copy.deepcopy(manifest)
        changed[key] = value
        rejects(lambda: check_manifest(changed), key)
    for label, plan in (("hash length", {**sample["assemblyMemoryPlan"], "hash": {"offset": 0, "length": 2}}),
                        ("final read", {**sample["assemblyMemoryPlan"], "finalRead": 65}),
                        ("stage count", {**sample["assemblyMemoryPlan"], "stages": []})):
        rejects(lambda: check_plan(plan), label)
    path = directory / "negative.json"
    plan = sample["assemblyMemoryPlan"]
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("final read", lambda value: value["assemblyMemoryPlan"].update(finalRead=(plan["finalRead"] + 1) % 65)),
        ("width", lambda value: value["assemblyMemoryPlan"]["stages"][0].update(
            width="byte" if plan["stages"][0]["width"] == "word" else "word")),
        ("hash", lambda value: value["assemblyMemoryPlan"].update(
            hash=None if plan["hash"] is not None else {"offset": 0, "length": 32})),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="1" if value["input"] != "1" else "2")),
        ("wrapper", lambda value: value["contract"].update(name="AnotherContract")),
        ("memory version", lambda value: value["provenance"].update(memoryVersion="another-version")),
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
    rejects(lambda: returned(lower["directCore"]), "resource result as feature coverage")
    for args in (("assembly-memory-generate", str(1 << 64), "96", "8", "1", str(fuel)),
                 ("assembly-memory-generate", "1", "513", "8", "1", str(fuel)),
                 ("shrink", str(path), "4097", str(fuel))):
        result = subprocess.run([str(tool), *args], cwd=ROOT, text=True, capture_output=True, timeout=60, check=False)
        require(result.returncode != 0, "native CLI accepted an out-of-range budget")
        count += 1
    return count


def validate(manifest, tool, fuel):
    require(type(fuel) is int and 0 < fuel <= 10_000_000, "invalid positive execution fuel")
    entries = check_manifest(manifest)
    inputs, found = set(), {key: set() for key in SHAPES}
    groups, seeds, samples = {}, [], {}
    with tempfile.TemporaryDirectory(prefix="semantic-assembly-memory-corpus-") as name:
        directory = Path(name)
        for entry in entries:
            case = materialize(entry, tool, fuel)
            require(case == materialize(entry, tool, fuel), "materialization is not deterministic")
            for version in VERSIONS:
                require(case["provenance"][version] == manifest[version], f"{version} changed")
            body = check_case(case, fuel)
            plan = case["assemblyMemoryPlan"]
            require(safe(body, plan), "a fixed plan may compile to a shift by a constant of at least 2^64")
            actual, _ = pure.ast_coverage([body])
            require(actual == set(case["provenance"]["features"]) == set(entry["expectedFeatures"]),
                    "declared features differ from the step AST")
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
            group = groups.setdefault(key, {"inputs": set(), "source": case["source"], "results": set()})
            require(group["source"] == case["source"], "identical assembly memory plan emitted input-dependent source")
            group["inputs"].add(int(case["input"]))
            group["results"].add(result)
            samples.setdefault("hash" if plan["hash"] is not None else "none", case)
            # Only completed, replayed native cases contribute coverage.
            inputs.add(int(case["input"]))
            for dimension, values in shapes(plan).items():
                found[dimension] |= values
        require(inputs == set(BOUNDARIES), "lost completed input coverage")
        for dimension, values in REQUIRED.items():
            require(set(values) <= found[dimension], f"lost completed {dimension} coverage")
        for group in groups.values():
            require(group["inputs"] == set(BOUNDARIES), "assembly memory plan lacks a completed boundary input")
            require(len(group["results"]) > 1, "fixed assembly memory plan returned one Word for every boundary input")
        require(seeds == selection(tool, fuel, max(seeds)),
                "the corpus is not every covering seed in order without a constant shift count")
        require(set(samples) == {"hash", "none"}, "missing shrink fixtures with and without a hash")
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in samples.values())
        checks = policy_checks(manifest, samples["hash"], tool, directory, fuel)
    return {"status": "passed", "profile": "runtime-assembly-memory", "cases": len(entries), "functionGroups": len(groups),
            "seeds": seeds, "completedInputs": [str(value) for value in sorted(inputs)],
            "assemblyMemoryCoverage": {"classification": "specified-by-the-schedule-not-a-memory-trace",
                                       **{key: sorted(values) for key, values in found.items()}},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path, default=ROOT / "scripts/semantic-assembly-memory-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
