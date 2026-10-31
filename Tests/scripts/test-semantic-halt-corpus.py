#!/usr/bin/env python3
"""Check the fixed halt corpus using fresh native Core executions.

The corpus takes, from seed 1 upwards at the default budget, every generated
plan that covers a missing halt shape, each at the eight primitive boundary
inputs; every shape value is required. This test rebuilds that selection,
admits every plan with the revert data corpus checker's walk over the helpers,
sites and scope, which admits halt sites only here and requires one the plan
reaches, recomputes every halt shape and the shrink measure from the plan
alone, re-emits the source and compares it exactly, evaluates every case's plan
with that checker's model, which runs each helper and closure as a function
over byte lists, raises each site's revert data and stops at a halt, against
the recorded Core outcome, and replays, observes and shrinks natively. It
neither compiles Rust nor executes an EVM.
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


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


rd = load("halt_corpus_revert_data", "Tests/scripts/test-semantic-revert-data-corpus.py")
pure, generic, m2 = rd.pure, rd.generic, rd.m2
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
VERSIONS = rd.VERSIONS
BOUNDARIES = rd.BOUNDARIES
CASE_SCHEMA = "solcore-lean.semantic-halt-case.v1"
PROFILE = "runtime-halts"
NAME = "SynthesizedHalts"
OPCODES = "import { mload, mstore, mstore8, shr, mod, invalid } from std.opcodes;"
NODES = rd.NODES
CASE_LIMIT = rd.CASE_LIMIT
SHRINK_BYTES = rd.SHRINK_BYTES
SHAPES = rd.HALT_SHAPES
REQUIRED = SHAPES


def check_plan(plan):
    return rd.check_plan(plan, halts=True)


def outcome(observation):
    """A completed Core outcome: a returned Word, revert data of at most 64 bytes, or a halt."""
    require(isinstance(observation, dict) and observation.get("stage") == "execution", "missing Core outcome")
    if observation.get("status") == "invalid":
        require(set(observation) == {"stage", "status"}, "a halt has no data")
        return "invalid"
    return rd.outcome(observation)


def check_case(case, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected halt case schema")
    plan = check_plan(case["haltPlan"])
    number = canonical_word(case["input"])
    program = case["program"]
    payload = {"tag": "product", "left": "word", "right": {"tag": "product", "left": "word", "right": "word"}}
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == {"tag": "sum", "left": "word", "right": payload},
            "the halt reference is a closed program returning a Word, revert data or a halt")
    require(generic.complexity(program["body"])[0] <= CASE_LIMIT, "reference exceeds the case limit")
    require(1 <= case["provenance"]["referenceNodes"] <= CASE_LIMIT, "recorded reference size exceeds the case limit")
    require(case["contract"] == {"name": NAME, "method": "run", "signature": "run(uint256)",
            "deployPath": [NAME + "Deploy"], "runtimePath": [NAME + "Deploy", NAME],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "halt ABI, runtime input, or contract metadata changed")
    require(case.get("executionFuel") == fuel, "invalid execution fuel")
    require(case.get("source") == rd.emitted_source(plan, NAME, OPCODES), "the emitted source differs from the plan's re-emission")
    recorded = case["provenance"]["haltShapes"]
    require(set(recorded) == set(SHAPES) and {dimension: set(values) for dimension, values in recorded.items()}
            == rd.halt_shapes(plan), "recorded halt shapes differ from the plan")
    require(all(values == sorted(set(values)) for values in recorded.values()), "halt shapes are not sorted")
    require(case["provenance"]["features"] == [], "the halt profile records no G0 step features")
    require(rd.model_outcome(plan, number) == case["directCore"], "the halt model differs from the recorded Core outcome")
    return plan


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals", "requiredInputs",
              "haltRequirements", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == PROFILE, "unexpected halt manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "halt coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    require(manifest["requiredFeatures"] == [] and manifest["requiredWordLiterals"] == [],
            "the halt corpus requires shapes, not step features or literals")
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "the halt corpus must require all eight boundary inputs")
    require(manifest["haltRequirements"] == REQUIRED, "the halt corpus must require every shape value")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "the halt corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"id", "generation", "input", "expectedFeatures"},
                "a halt corpus entry is a generation recipe with its input")
        identifier = entry["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        require(canonical_word(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        require(entry["expectedFeatures"] == [], "halt entries expect no step features")
        recipe = entry["generation"]
        require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
        require(canonical_word(recipe["seed"]) < 1 << 64 and recipe["maxProgramNodes"] == NODES,
                "fixed recipes use a uint64 seed and the default budget")
    return entries


def generated_plan(tool, seed, fuel):
    """The seed's plan, or None for an excluded seed."""
    corpus = run(tool, "halt-generate", str(seed), str(NODES), "1", "1", str(fuel))
    cases = corpus.get("cases")
    require(isinstance(cases, list) and len(cases) <= 1, "invalid generation response")
    return check_plan(cases[0]["haltPlan"]) if cases else None


def selection(tool, fuel, last):
    """The roadmap's construction: from seed 1 upwards, every accepted seed
    whose plan covers a missing value, until nothing is missing."""
    missing = {dimension: set(values) for dimension, values in REQUIRED.items()}
    chosen = []
    for seed in range(1, last + 1):
        if not any(missing.values()):
            break
        plan = generated_plan(tool, seed, fuel)
        if plan is None:
            continue
        found = rd.halt_shapes(plan)
        if any(missing[dimension] & found[dimension] for dimension in missing):
            chosen.append(seed)
            for dimension in missing:
                missing[dimension] -= found[dimension]
    require(not any(missing.values()), "seeds up to the last chosen one leave a requirement missing")
    return chosen


def materialize(entry, tool, fuel):
    recipe = entry["generation"]
    corpus = run(tool, "halt-generate", recipe["seed"], str(recipe["maxProgramNodes"]), "8", "1", str(fuel))
    require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
            and corpus.get("requested") == 8 and corpus.get("attempted") == 1
            and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 8,
            "fixed halt seed did not emit eight cases in one attempt")
    cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
    require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
    case = cases[0]
    origin = case["provenance"]["origin"]
    require(origin == {"kind": "halt-generated", "seed": recipe["seed"],
                       "maxProgramNodes": recipe["maxProgramNodes"],
                       "inputIndex": BOUNDARIES.index(int(entry["input"])), "validationFuel": fuel},
            "generated recipe differs from manifest")
    check_case(case, fuel)
    return case


def checked_shrinks(case, tool, directory, fuel):
    path = directory / "shrink-parent.json"
    path.write_text(json.dumps(case))
    reduced = run(tool, "shrink", str(path), "64", str(fuel))
    require(reduced == run(tool, "shrink", str(path), "64", str(fuel)), "native shrink order changed")
    candidates = reduced.get("cases")
    require(isinstance(candidates, list) and candidates, "fixed halt case has no shrink candidate")
    require(sum(len(json.dumps(candidate, separators=(",", ":"))) for candidate in candidates) <= SHRINK_BYTES,
            "a shrink response exceeds its byte cap")
    parent = (rd.plan_size(case["haltPlan"]), int(case["input"]))
    seen = set()
    for candidate in candidates:
        check_case(candidate, fuel)
        require(candidate["provenance"]["origin"] == {"kind": "reduced", "parentPlan": case["haltPlan"],
                                                      "parentInput": case["input"]},
                "a shrink candidate is not a reduction of its parent")
        require((rd.plan_size(candidate["haltPlan"]), int(candidate["input"])) < parent,
                "a shrink candidate is not strictly smaller")
        encoded = json.dumps([candidate["haltPlan"], candidate["input"]], sort_keys=True)
        require(encoded not in seen, "duplicate canonical shrink")
        seen.add(encoded)
        target = directory / "shrunk.json"
        target.write_text(json.dumps(candidate))
        require(run(tool, "replay", str(target), str(fuel)) == candidate,
                "native shrink lost canonical source/program/provenance")
        fresh = run(tool, "observe", str(target), str(fuel))
        outcome(fresh)
        require(fresh == candidate["directCore"], "shrunk observation differs from fresh Core execution")
    return len(candidates)


def policy_checks(manifest, sample, tool, directory, fuel):
    count = 0

    def rejects(action, label):
        nonlocal count
        try:
            action()
        except (ValueError, KeyError, TypeError, IndexError):
            count += 1
        else:
            raise ValueError("negative check accepted " + label)

    for field, value in (("profile", "runtime-revert-data"), ("requiredInputs", ["0"]), ("requiredFeatures", ["let"]),
                         *(("haltRequirements", {**REQUIRED, dimension: REQUIRED[dimension][1:]})
                           for dimension in REQUIRED)):
        changed = copy.deepcopy(manifest)
        changed[field] = value
        rejects(lambda: check_manifest(changed), field)
    plan = sample["haltPlan"]
    observe = {"action": {"kind": "observe", "fold": "add", "constant": 3, "value": "sc_b0", "access": {"access": "length"}}}
    bytes_value = {"action": {"kind": "bytes", "build": "to_bytes", "parts": [{"part": "word", "operand": {"operand": "input"}}]}}
    cond = {"word": {"operand": "input"}, "test": {"test": "eq", "constant": 0}}
    quiet = {"form": "when", "cond": cond, "payload": {"payload": "none"}}
    halting = {"form": "when", "cond": cond, "payload": {"payload": "halt", "halt": "inline"}}
    for label, broken in (
            ("no halt", {**plan, "helpers": [], "steps": [bytes_value, {"site": quiet}, observe]}),
            ("an assert under if", {**plan, "helpers": [], "steps": [bytes_value, {"site": {**halting,
                "payload": {"payload": "halt", "halt": "assert"}}}, observe]}),
            ("inline Yul through require", {**plan, "helpers": [], "steps": [bytes_value, {"site": {**halting,
                "form": "require"}}, observe]}),
            ("an unknown halt", {**plan, "helpers": [], "steps": [bytes_value, {"site": {**halting,
                "payload": {"payload": "halt", "halt": "stop"}}}, observe]}),
            ("a halt only in a closure never applied", {**plan, "helpers": [], "steps": [bytes_value,
                {"closure": {"site": halting, "fold": "add", "constant": 3}}, {"site": quiet}, observe]}),
            ("a halt only in a helper nothing calls", {**plan, "helpers": [{"kind": "raise", "site": halting, "fold": "add",
                "constant": 3}], "steps": [bytes_value, {"site": quiet}, observe]}),
            ("the revert data plan schema", {**plan, "schema": rd.PLAN_SCHEMA})):
        rejects(lambda: check_plan(broken), label)
    rejects(lambda: rd.check_plan({**plan, "schema": rd.PLAN_SCHEMA}), "a halt in a revert data plan")
    path = directory / "negative.json"
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("a removed step", lambda value: value["haltPlan"]["steps"].pop(0)),
        ("a halt under the wrong form", lambda value: value["haltPlan"]["steps"].append(
            {"site": {**halting, "form": "require"}})),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="1" if value["input"] != "1" else "2")),
        ("wrapper", lambda value: value["contract"].update(name="SynthesizedRevertData")),
        ("halt shapes", lambda value: value["provenance"]["haltShapes"].update(halts=[])),
        ("generator version", lambda value: value["provenance"].update(generatorVersion="core-revert-data-v1")),
    ):
        changed = copy.deepcopy(sample)
        change(changed)
        path.write_text(json.dumps(changed))
        result = subprocess.run([str(tool), "replay", str(path), str(fuel)], cwd=ROOT,
                                text=True, capture_output=True, timeout=60, check=False)
        require(result.returncode != 0, "native replay accepted altered " + label)
        count += 1
    forged = copy.deepcopy(sample)
    forged["directCore"] = {"stage": "execution", "status": "invalid"}
    path.write_text(json.dumps(forged))
    require(run(tool, "replay", str(path), str(fuel)) == sample, "native replay trusted saved execution evidence")
    count += 1
    path.write_text(json.dumps(sample))
    lower = run(tool, "replay", str(path), "0")
    require(lower["program"] == sample["program"] and lower["source"] == sample["source"]
            and lower["directCore"].get("status") == "out-of-fuel", "zero budget changed canonical code or invented completion")
    rejects(lambda: outcome(lower["directCore"]), "resource result as shape coverage")
    for args in (("halt-generate", str(1 << 64), "1024", "8", "1", str(fuel)),
                 ("halt-generate", "1", "2049", "8", "1", str(fuel)),
                 ("halt-generate", "1", "255", "8", "1", str(fuel)),
                 ("halt-generate", "1", "1024", "8", "1", str(fuel), "exclude-boundary-identity-v1"),
                 ("shrink", str(path), "4097", str(fuel))):
        result = subprocess.run([str(tool), *args], cwd=ROOT, text=True, capture_output=True, timeout=60, check=False)
        generated = result.returncode == 0 and json.loads(result.stdout).get("cases")
        require(result.returncode != 0 or not generated, "native CLI accepted an out-of-range budget or a filter")
        count += 1
    return count


def validate(manifest, tool, fuel):
    require(type(fuel) is int and 0 < fuel <= 10_000_000, "invalid positive execution fuel")
    entries = check_manifest(manifest)
    groups, seeds, inputs, samples = {}, [], set(), []
    found = {dimension: set() for dimension in SHAPES}
    halted = reverted = 0
    with tempfile.TemporaryDirectory(prefix="halt-corpus-") as name:
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
            result = outcome(before)
            require(before == case["directCore"], "saved observation differs from fresh original Core")
            replayed = run(tool, "replay", str(path), str(fuel))
            require(replayed == case, "native canonical replay changed the case")
            halted += result == "invalid"
            reverted += result.startswith("reverted:")
            plan_key = json.dumps(plan, sort_keys=True)
            if plan_key not in groups:
                seeds.append(int(entry["generation"]["seed"]))
                samples.append(case)
            group = groups.setdefault(plan_key, {"inputs": set(), "source": case["source"], "results": set()})
            require(group["source"] == case["source"], "identical halt plan emitted input-dependent source")
            group["inputs"].add(int(case["input"]))
            group["results"].add(result)
            # Only completed, replayed native cases contribute coverage.
            inputs.add(int(case["input"]))
            for dimension, values in rd.halt_shapes(plan).items():
                found[dimension] |= values
        require(inputs == set(BOUNDARIES), "lost completed input coverage")
        for dimension, values in REQUIRED.items():
            require(set(values) <= found[dimension], f"lost completed {dimension} coverage")
        for group in groups.values():
            require(group["inputs"] == set(BOUNDARIES), "halt plan lacks a completed boundary input")
            require("invalid" in group["results"], "fixed halt plan halted at no boundary input")
            require(len(group["results"]) > 1, "fixed halt plan had one outcome for every boundary input")
        require(seeds == selection(tool, fuel, max(seeds)), "the corpus is not every covering seed in order")
        looped = next(case for case in samples if any("loop" in step for step in case["haltPlan"]["steps"]))
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in [samples[0], looped])
        checks = policy_checks(manifest, samples[0], tool, directory, fuel)
    return {"status": "passed", "profile": PROFILE, "cases": len(entries), "plans": len(groups),
            "seeds": seeds, "halted": halted, "reverted": reverted,
            "completedInputs": [str(value) for value in sorted(inputs)],
            "haltCoverage": {"classification": "specified-by-the-plan-not-measured-halts",
                             **{dimension: sorted(values) for dimension, values in found.items()}},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path,
                        default=ROOT / "scripts/semantic-halt-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
