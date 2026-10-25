#!/usr/bin/env python3
"""Bounded pure-program differential campaigns and failure-preserving reduction.

Normal execution never changes observations. --test-perturb-path is an explicit
synthetic test adapter: after all real paths match, it flips one observed Word
bit in a separate analysis. The actual M2 report and observations are retained.
"""
from __future__ import annotations

import argparse
import copy
import importlib.util
import json
import math
from pathlib import Path
import shutil
import signal
import sys
import time
from types import SimpleNamespace

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
_spec = importlib.util.spec_from_file_location("semantic_differential", ROOT / "scripts/semantic-differential.py")
assert _spec and _spec.loader
m2 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(m2)
SCHEMA = "solcore-lean.semantic-campaign.v1"
ANALYSIS_SCHEMA = "solcore-lean.semantic-analysis.v1"
TEST_ADAPTER = "xor-low-bit-after-matched-execution-v1"
PATHS = ("directCore", "importedHull", "rustEvm")
PROFILES = tuple(m2.CASE_PROFILES.values())
PROFILE_SCHEMAS = {profile: schema for schema, profile in m2.CASE_PROFILES.items()}
PROFILE_COMMANDS = {"closed-g0": ("generate", "emit", "generated"),
                    "runtime-word": ("input-generate", "input-emit", "input-generated"),
                    "runtime-functions": ("function-generate", "function-emit", "function-generated"),
                    "runtime-mutation": ("mutation-generate", "mutation-emit", "mutation-generated"),
                    "runtime-aggregates": ("aggregate-generate", "aggregate-emit", "aggregate-generated"),
                    "runtime-loops": ("loop-generate", "loop-emit", "loop-generated"),
                    "runtime-generics": ("generic-generate", "generic-emit", "generic-generated"),
                    "runtime-closures": ("closure-generate", "closure-emit", "closure-generated"),
                    "runtime-comptime": ("comptime-generate", "comptime-emit", "comptime-generated"),
                    "runtime-modules": ("module-generate", "module-emit", "module-generated")}
HELPER_PROFILES = ("runtime-functions", "runtime-mutation", "runtime-aggregates", "runtime-loops", "runtime-generics", "runtime-closures", "runtime-comptime", "runtime-modules")
INPUT_BOUNDARIES = ("0", "1", str(2**256 - 1), str(2**255))
LOOP_INPUTS = ("0", "1", "3", "7", str(2**256 - 1), str(2**255))
INPUT_VERSIONS = ("profileVersion", "functionVersion", "abstractionVersion")
PROFILE_VERSION_FIELDS = {"closed-g0": (), "runtime-word": INPUT_VERSIONS,
                          "runtime-functions": INPUT_VERSIONS,
                          "runtime-mutation": ("profileVersion", "functionVersion", "templateVersion"),
                          "runtime-aggregates": ("profileVersion", "functionVersion", "templateVersion"),
                          "runtime-loops": ("profileVersion", "functionVersion", "templateVersion",
                                            "stepProfileVersion", "stepTemplateVersion", "stepFunctionVersion"),
                          "runtime-generics": ("profileVersion", "functionVersion", "templateVersion",
                                               "stepProfileVersion", "stepTemplateVersion", "stepFunctionVersion"),
                          "runtime-closures": ("profileVersion", "functionVersion", "templateVersion",
                                               "stepProfileVersion", "stepTemplateVersion", "stepFunctionVersion"),
                          "runtime-comptime": ("profileVersion", "functionVersion", "templateVersion",
                                               "stepProfileVersion", "stepTemplateVersion", "stepFunctionVersion"),
                          "runtime-modules": ("profileVersion", "functionVersion", "templateVersion",
                                               "stepProfileVersion", "stepTemplateVersion", "stepFunctionVersion")}
RESOURCE = "inconclusive-resource"
SHRINKABLE = {"semantic-mismatch", "source-rejected", "compilation-rejected", "compiler-crash", "execution-error"}


def save_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".writing")
    temporary.write_bytes(m2.json_bytes(value))
    temporary.replace(path)


def directory_bytes(path: Path) -> int:
    return sum(item.stat().st_size for item in path.rglob("*") if item.is_file())


def program_hash(case: dict) -> str:
    return m2.digest(m2.json_bytes(case["program"]))


def word_literals(program: dict) -> set[str]:
    result = set()
    pending = [program]
    while pending:
        value = pending.pop()
        if isinstance(value, dict):
            if value.get("tag") == "word":
                literal = value.get("value")
                if not isinstance(literal, str) or not literal.startswith("0x"):
                    raise ValueError("invalid Core Word literal")
                result.add(m2.word(str(int(literal, 16))))
            pending.extend(value.values())
        elif isinstance(value, list):
            pending.extend(value)
    return result


def bound_helper_count(body) -> int:
    """Count actual declaration lambdas, excluding the entry and ABI wrapper."""
    def word_function(value) -> bool:
        return (isinstance(value, dict) and value.get("tag") == "lambda"
            and value.get("parameterType") == "word" and value.get("resultType") == "word"
            and isinstance(value.get("body"), dict))

    count = 0
    while isinstance(body, dict) and body.get("tag") == "let":
        if not word_function(body.get("initializer")):
            raise ValueError("function helper declaration must bind a Word function")
        count += 1
        if count > 3:
            raise ValueError("function case declares more than three helpers")
        body = body.get("body")
    if not 1 <= count <= 3 or not word_function(body):
        raise ValueError("function case requires one to three helpers followed by its entry lambda")
    return count


def declared_helper_count(program: dict) -> int:
    """Check the outer shape; native replay checks types, bodies and scopes."""
    if not isinstance(program, dict) or program.get("resultType") != "word":
        raise ValueError("function case requires an original Core Word application")
    application = program.get("body")
    if not isinstance(application, dict) or application.get("tag") != "apply":
        raise ValueError("function case requires an original Core application")
    argument = application.get("argument")
    if not isinstance(argument, dict) or argument.get("tag") != "word" or len(m2.hex_bytes(argument.get("value"), "Core input")) != 32:
        raise ValueError("function case application requires a Word input")
    return bound_helper_count(application.get("function"))


def helper_counts(case: dict) -> set[int]:
    plans = {m2.LOOP_CASE_SCHEMA: ("loopPlan", m2.validate_loop_plan),
             m2.GENERIC_CASE_SCHEMA: ("genericPlan", m2.validate_generic_plan),
             m2.CLOSURE_CASE_SCHEMA: ("closurePlan", m2.validate_closure_plan),
             m2.COMPTIME_CASE_SCHEMA: ("comptimePlan", m2.validate_comptime_plan),
             m2.MODULE_CASE_SCHEMA: ("modulePlan", m2.validate_module_plan)}
    if case.get("schema") in plans:
        key, validate = plans[case["schema"]]
        step = validate(case.get(key))["stepProgram"]
        if step.get("resultType") != {"tag": "function", "parameter": "word", "result": "word"} or step.get("dataDefinitions") != []:
            raise ValueError("plan step must be a closed Word function graph")
        return {bound_helper_count(step.get("body"))}
    return {declared_helper_count(case["program"])} if m2.CASE_PROFILES.get(case.get("schema")) in HELPER_PROFILES else set()


def loop_requirements(manifest: dict) -> dict:
    requirements = manifest.get("loopRequirements", {"masks": [], "iterations": []})
    if not isinstance(requirements, dict) or set(requirements) != {"masks", "iterations"}:
        raise ValueError("loopRequirements requires masks and iterations arrays")
    for key, allowed in (("masks", {0, 1, 3, 7}), ("iterations", set(range(8)))):
        values = requirements[key]
        if not isinstance(values, list) or any(type(v) is not int or v not in allowed for v in values) or len(values) != len(set(values)):
            raise ValueError(f"invalid loop {key} requirements")
    if manifest.get("profile", "closed-g0") != "runtime-loops" and any(requirements.values()):
        raise ValueError("only loop corpora can require masks and specified iterations")
    return requirements


def specified_loops(case: dict) -> dict[str, set[int]]:
    """Prescribed iteration counts, never a claim of measured execution traces."""
    if case.get("schema") != m2.LOOP_CASE_SCHEMA:
        return {"Masks": set(), "Iterations": set()}
    plan = m2.validate_loop_plan(case.get("loopPlan"))
    return {"Masks": {plan["mask"]}, "Iterations": {int(m2.word(case.get("input"))) & plan["mask"]}}


def generic_requirements(manifest: dict) -> dict:
    requirements = manifest.get("genericRequirements", {"instantiations": []})
    if not isinstance(requirements, dict) or set(requirements) != {"instantiations"}:
        raise ValueError("genericRequirements requires an instantiations array")
    values = requirements["instantiations"]
    allowed = {variant + ":" + branch for variant in ("word", "pair", "sum") for branch in ("even", "odd")}
    if (not isinstance(values, list) or any(not isinstance(v, str) or v not in allowed for v in values)
            or len(values) != len(set(values))):
        raise ValueError("invalid generic instantiation requirements")
    if manifest.get("profile", "closed-g0") != "runtime-generics" and values:
        raise ValueError("only generic corpora can require instantiations")
    return requirements


def specified_generics(case: dict) -> set[str]:
    if case.get("schema") != m2.GENERIC_CASE_SCHEMA:
        return set()
    plan = m2.validate_generic_plan(case.get("genericPlan"))
    branch = "odd" if int(m2.word(case.get("input"))) & 1 else "even"
    return {plan["variant"] + ":" + branch}


def closure_requirements(manifest: dict) -> dict:
    requirements = manifest.get("closureRequirements", {"variants": []})
    if not isinstance(requirements, dict) or set(requirements) != {"variants"}:
        raise ValueError("closureRequirements requires a variants array")
    values = requirements["variants"]
    if (not isinstance(values, list) or any(not isinstance(v, str) or v not in ("snapshot", "independent") for v in values)
            or len(values) != len(set(values))):
        raise ValueError("invalid closure variant requirements")
    if manifest.get("profile", "closed-g0") != "runtime-closures" and values:
        raise ValueError("only closure corpora can require capture variants")
    return requirements


def specified_closures(case: dict) -> set[str]:
    if case.get("schema") != m2.CLOSURE_CASE_SCHEMA:
        return set()
    return {m2.validate_closure_plan(case.get("closurePlan"))["variant"]}


def comptime_requirements(manifest: dict) -> dict:
    requirements = manifest.get("comptimeRequirements", {"variants": []})
    if not isinstance(requirements, dict) or set(requirements) != {"variants"}:
        raise ValueError("comptimeRequirements requires a variants array")
    values = requirements["variants"]
    if (not isinstance(values, list) or any(not isinstance(v, str) or v not in ("offset", "scale") for v in values)
            or len(values) != len(set(values))):
        raise ValueError("invalid comptime variant requirements")
    if manifest.get("profile", "closed-g0") != "runtime-comptime" and values:
        raise ValueError("only comptime corpora can require constant variants")
    return requirements


def module_requirements(manifest: dict) -> dict:
    requirements = manifest.get("moduleRequirements", {"branches": []})
    if not isinstance(requirements, dict) or set(requirements) != {"branches"}:
        raise ValueError("moduleRequirements requires a branches array")
    values = requirements["branches"]
    if (not isinstance(values, list) or any(not isinstance(v, str) or v not in ("even", "odd") for v in values)
            or len(values) != len(set(values))):
        raise ValueError("invalid module branch requirements")
    if manifest.get("profile", "closed-g0") != "runtime-modules" and values:
        raise ValueError("only module corpora can require mixed-module branches")
    return requirements


def specified_modules(case: dict) -> set[str]:
    if case.get("schema") != m2.MODULE_CASE_SCHEMA:
        return set()
    m2.validate_module_plan(case.get("modulePlan"))
    return {"odd" if int(m2.word(case.get("input"))) & 1 else "even"}


def constant_requirements(manifest: dict) -> list[str]:
    values = manifest.get("requiredConstantFeatures", None if manifest.get("profile") in ("runtime-comptime", "runtime-modules") else [])
    if (not isinstance(values, list) or any(not isinstance(v, str) for v in values)
            or len(values) != len(set(values))):
        raise ValueError("requiredConstantFeatures must be an array of unique strings")
    if manifest.get("profile", "closed-g0") not in ("runtime-comptime", "runtime-modules") and values:
        raise ValueError("only comptime and module corpora can require constant features")
    return values


def specified_comptime(case: dict) -> set[str]:
    if case.get("schema") != m2.COMPTIME_CASE_SCHEMA:
        return set()
    return {m2.validate_comptime_plan(case.get("comptimePlan"))["variant"]}


def constant_features(case: dict) -> set[str]:
    if case.get("schema") not in (m2.COMPTIME_CASE_SCHEMA, m2.MODULE_CASE_SCHEMA):
        return set()
    values = case.get("provenance", {}).get("constantFeatures")
    # Native provenance records ordered AST occurrences, including duplicates.
    # Replay authenticates that exact list; coverage counts distinct features.
    if not isinstance(values, list) or any(not isinstance(v, str) for v in values):
        raise ValueError("constantFeatures must be an array of strings")
    return set(values)


def recipe_requirements(manifest: dict) -> dict:
    requirements = manifest.get("generationRecipeRequirements", {"templates": [], "updates": []})
    if not isinstance(requirements, dict) or set(requirements) != {"templates", "updates"}:
        raise ValueError("generationRecipeRequirements requires templates and updates arrays")
    for key, lower, upper in (("templates", 0, 3), ("updates", 1, 4)):
        values = requirements[key]
        if not isinstance(values, list) or any(type(value) is not int or not lower <= value <= upper for value in values):
            raise ValueError(f"recipe {key} must contain integers from {lower} to {upper}")
        if len(values) != len(set(values)):
            raise ValueError(f"recipe {key} must not contain duplicates")
    profile = manifest.get("profile", "closed-g0")
    if profile not in ("runtime-mutation", "runtime-aggregates", "runtime-loops", "runtime-generics", "runtime-closures", "runtime-comptime", "runtime-modules") and any(requirements.values()):
        raise ValueError("only step-based corpora can require generation recipes")
    if profile in ("runtime-aggregates", "runtime-loops", "runtime-generics", "runtime-closures", "runtime-comptime", "runtime-modules") and requirements["updates"]:
        raise ValueError("this profile has no update-count recipe dimension")
    return requirements


def generation_recipes(case: dict) -> dict[str, set[int]]:
    """Read claimed generator metadata; native replay authenticates matched cases."""
    result = {"Templates": set(), "Updates": set()}
    schema = case.get("schema")
    if schema not in (m2.MUTATION_CASE_SCHEMA, m2.AGGREGATE_CASE_SCHEMA, m2.LOOP_CASE_SCHEMA, m2.GENERIC_CASE_SCHEMA, m2.CLOSURE_CASE_SCHEMA, m2.COMPTIME_CASE_SCHEMA, m2.MODULE_CASE_SCHEMA):
        return result
    origin_kind = {m2.MUTATION_CASE_SCHEMA: "mutation-generated",
                   m2.AGGREGATE_CASE_SCHEMA: "aggregate-generated", m2.LOOP_CASE_SCHEMA: "loop-generated",
                   m2.GENERIC_CASE_SCHEMA: "generic-generated", m2.CLOSURE_CASE_SCHEMA: "closure-generated",
                   m2.COMPTIME_CASE_SCHEMA: "comptime-generated", m2.MODULE_CASE_SCHEMA: "module-generated"}[schema]
    provenance = case.get("provenance")
    if not isinstance(provenance, dict):
        raise ValueError("recipe case provenance must be an object")
    origin = provenance.get("origin", {})
    if not isinstance(origin, dict):
        raise ValueError("recipe case origin must be an object")
    if origin.get("kind") != origin_kind:
        return result
    if schema in (m2.LOOP_CASE_SCHEMA, m2.GENERIC_CASE_SCHEMA, m2.CLOSURE_CASE_SCHEMA, m2.COMPTIME_CASE_SCHEMA, m2.MODULE_CASE_SCHEMA):
        origin = origin.get("stepOrigin")
        if not isinstance(origin, dict) or origin.get("kind") != "aggregate-generated":
            raise ValueError("generated plan recipe requires its aggregate step origin")
    helpers = origin.get("helpers")
    if not isinstance(helpers, list) or not 1 <= len(helpers) <= 3:
        raise ValueError("generated recipes require one to three helper records")
    for helper in helpers:
        if not isinstance(helper, dict):
            raise ValueError("helper recipe must be an object")
        dimensions = [("template", "Templates", 0, 3)]
        if schema == m2.MUTATION_CASE_SCHEMA:
            dimensions.append(("updates", "Updates", 1, 4))
        for field, destination, lower, upper in dimensions:
            value = helper.get(field)
            if type(value) is not int or not lower <= value <= upper:
                raise ValueError(f"recipe helper {field} must be an integer from {lower} to {upper}")
            result[destination].add(value)
    return result


def missing_coverage(summary: dict) -> bool:
    return (any(summary["coverage"][key] for key in ("missingFeatures", "missingWordLiterals", "missingInputs", "missingHelperCounts"))
        or any(summary["recipeCoverage"]["missing" + dimension] for dimension in ("Templates", "Updates"))
        or any(summary["loopCoverage"]["missing" + dimension] for dimension in ("Masks", "Iterations"))
        or bool(summary["genericCoverage"]["missingInstantiations"])
        or bool(summary["closureCoverage"]["missingVariants"])
        or bool(summary["comptimeCoverage"]["missingVariants"])
        or bool(summary["constantCoverage"]["missingFeatures"])
        or bool(summary["moduleCoverage"]["missingBranches"]))


def validate_manifest(manifest) -> dict:
    if not isinstance(manifest, dict) or manifest.get("schema") != "solcore-lean.semantic-corpus-manifest.v1" or not isinstance(manifest.get("cases"), list):
        raise ValueError("unsupported corpus manifest")
    profile = manifest.get("profile", "closed-g0")
    if profile not in PROFILES:
        raise ValueError("unsupported corpus profile")
    version_keys = ("generatorVersion", "emitterVersion", "wrapperVersion") + PROFILE_VERSION_FIELDS[profile]
    for key in version_keys:
        if not isinstance(manifest.get(key), str) or not manifest[key]:
            raise ValueError(f"missing corpus {key}")
    for key in ("requiredFeatures", "requiredWordLiterals"):
        if not isinstance(manifest.get(key), list) or any(not isinstance(value, str) for value in manifest[key]):
            raise ValueError(f"corpus {key} must be an array of strings")
    for value in manifest["requiredWordLiterals"]:
        m2.word(value)
    required_inputs = manifest.get("requiredInputs", [] if profile == "closed-g0" else None)
    if not isinstance(required_inputs, list):
        raise ValueError("runtime corpus requiredInputs must be an array")
    for value in required_inputs:
        m2.word(value, "required input")
    if profile == "closed-g0" and required_inputs:
        raise ValueError("closed G0 corpus cannot require runtime inputs")
    required_helpers = manifest.get("requiredHelperCounts", None if profile in HELPER_PROFILES else [])
    if not isinstance(required_helpers, list) or any(type(value) is not int or not 1 <= value <= 3 for value in required_helpers):
        raise ValueError("corpus requiredHelperCounts must be an array of integers from one to three")
    if len(set(required_helpers)) != len(required_helpers):
        raise ValueError("corpus requiredHelperCounts must not contain duplicates")
    if profile not in HELPER_PROFILES and required_helpers:
        raise ValueError("only function corpora can require helper counts")
    recipe_requirements(manifest)
    loop_requirements(manifest)
    generic_requirements(manifest)
    closure_requirements(manifest)
    comptime_requirements(manifest)
    constant_requirements(manifest)
    module_requirements(manifest)
    ids = set()
    for entry in manifest["cases"]:
        if not isinstance(entry, dict) or not isinstance(entry.get("id"), str) or not entry["id"] or entry["id"] in ids:
            raise ValueError("corpus entries require unique nonempty IDs")
        ids.add(entry["id"])
        if sum(key in entry for key in ("generation", "program", "loopPlan", "genericPlan", "closurePlan", "comptimePlan", "modulePlan")) != 1:
            raise ValueError("corpus entry must specify exactly one generation request, program or plan")
        plan_key = {"runtime-loops": "loopPlan", "runtime-generics": "genericPlan", "runtime-closures": "closurePlan", "runtime-comptime": "comptimePlan", "runtime-modules": "modulePlan"}.get(profile, "program")
        if "generation" not in entry and plan_key not in entry:
            raise ValueError("corpus program or plan differs from its profile")
        if profile != "closed-g0":
            m2.word(entry.get("input"), "corpus input")
            boundaries = LOOP_INPUTS if profile == "runtime-loops" else INPUT_BOUNDARIES
            if "generation" in entry and entry["input"] not in boundaries:
                raise ValueError("generated runtime inputs must be a boundary value")
        elif "input" in entry:
            raise ValueError("closed G0 corpus entries cannot specify a runtime input")
        if not isinstance(entry.get("expectedFeatures"), list) or any(not isinstance(value, str) for value in entry["expectedFeatures"]):
            raise ValueError("expectedFeatures must be an array of strings")
        if profile in ("runtime-comptime", "runtime-modules"):
            values = entry.get("expectedConstantFeatures")
            if (not isinstance(values, list) or any(not isinstance(v, str) for v in values)
                    or len(values) != len(set(values))):
                raise ValueError("expectedConstantFeatures must be an array of unique strings")
        if "generation" in entry:
            request = entry["generation"]
            if not isinstance(request, dict):
                raise ValueError("generation request must be an object")
            seed = m2.word(request.get("seed"), "generation seed")
            nodes = request.get("maxProgramNodes")
            if int(seed) >= 2**64 or type(nodes) is not int or not 3 <= nodes <= 512:
                raise ValueError("generation request exceeds seed or node limits")
        elif "loopPlan" in entry:
            m2.validate_loop_plan(entry["loopPlan"])
        elif "genericPlan" in entry:
            m2.validate_generic_plan(entry["genericPlan"])
        elif "closurePlan" in entry:
            m2.validate_closure_plan(entry["closurePlan"])
        elif "comptimePlan" in entry:
            m2.validate_comptime_plan(entry["comptimePlan"])
        elif "modulePlan" in entry:
            m2.validate_module_plan(entry["modulePlan"])
        elif not isinstance(entry["program"], dict):
            raise ValueError("corpus program must be a Core JSON object")
    return manifest


def generation_resource_exclusions(excluded: list) -> int:
    """Generation resource failures count separately from executed cases."""
    count = 0
    for entry in excluded:
        if not isinstance(entry, dict):
            raise ValueError("generation exclusions must be objects")
        if entry.get("category") == RESOURCE:
            count += 1
        else:
            detail = entry.get("detail")
            if isinstance(detail, dict) and isinstance(detail.get("excluded"), list):
                if any(not isinstance(item, dict) for item in detail["excluded"]):
                    raise ValueError("generation exclusions must be objects")
                count += sum(item.get("category") == RESOURCE for item in detail["excluded"])
    return count


def analyze(report: dict, perturb: str | None = None) -> dict:
    actual = copy.deepcopy(report.get("comparison", {"category": "adapter-error", "stage": "missing-report", "pairs": {}}))
    observed = copy.deepcopy(report.get("observations", {}))
    synthetic = False
    if perturb is not None:
        if perturb not in PATHS:
            raise ValueError("unknown test observation path")
        if actual.get("category") == "matched":
            # Require fresh completed Word observations even in the test adapter.
            if m2.compare(observed).get("category") != "matched":
                raise ValueError("matched report has inconsistent observations")
            original = int(m2.word(observed[perturb].get("word")))
            observed[perturb]["word"] = str(original ^ 1)
            synthetic = True
    result = m2.compare(observed) if synthetic else actual
    return {"schema": ANALYSIS_SCHEMA, "synthetic": synthetic,
            "testAdapter": {"name": TEST_ADAPTER, "path": perturb} if perturb else None,
            "actualComparison": actual, "comparison": result, "observations": observed}


def fingerprint(analysis: dict) -> dict:
    comparison = analysis["comparison"]
    observations = analysis.get("observations", {})
    shapes = {}
    for name in PATHS:
        row = observations.get(name, {})
        shapes[name] = {"status": row.get("status", "not-executed"),
                       "payload": "word" if "word" in row else "bytes" if "output" in row else "none"}
    return {"category": comparison.get("category"), "stage": comparison.get("stage"),
            "disagreeingPairs": sorted(pair for pair, same in comparison.get("pairs", {}).items() if same is False),
            "synthetic": analysis["synthetic"], "pathShapes": shapes}


def same_failure(expected: dict, candidate: dict) -> bool:
    return expected.get("category") in SHRINKABLE and fingerprint(candidate) == expected


def count_outcome(counts: dict, analysis: dict) -> None:
    category = analysis["comparison"]["category"]
    counts["executed"] += 1
    if category in {"matched", "semantic-mismatch"}:
        counts["completed"] += 1
    bucket = {"matched": "matched", "semantic-mismatch": "mismatched", RESOURCE: "inconclusive"}.get(category, "errors")
    counts[bucket] += 1
    if category == "source-rejected":
        counts["sourceRejected"] += 1
    elif category == "compilation-rejected":
        counts["compilationRejected"] += 1
    if analysis["synthetic"]:
        counts["syntheticMismatches"] += 1


def compact_report(report: dict) -> dict:
    """Keep receipts/observations, dropping disposable verbose process output."""
    result = copy.deepcopy(report)
    for process in result.get("processes", []):
        for stream in ("stdout", "stderr"):
            content = process.pop(stream, "")
            process[stream + "Sha256"] = m2.digest(content.encode())
    logs = result.pop("anvilLog", "")
    result["anvilLogSha256"] = m2.digest(logs.encode())
    result["archivePolicy"] = "exports removed; regenerate from saved case with --case; exact archive replay unavailable"
    return result


class Campaign:
    def __init__(self, args):
        self.args = args
        self.started = time.monotonic()
        self.deadline = self.started + args.seconds
        self.reserve = min(40 * 1024 * 1024, args.disk_bytes // 4)
        self.work = args.output / ".work"
        self.work.mkdir()
        self.counter = 0
        self.shrink_attempts = 0
        self.summary = {
            "schema": SCHEMA, "status": "running", "synthetic": args.test_perturb_path is not None,
            "testAdapter": {"name": TEST_ADAPTER, "path": args.test_perturb_path} if args.test_perturb_path else None,
            "configuration": {key: getattr(args, key) for key in ("profile", "seed", "nodes", "cases", "attempts", "seconds", "disk_bytes", "shrink_attempts", "shrink_candidates", "direct_fuel", "core_fuel", "gas", "case_timeout")},
            "tools": {"caseTool": str(args.case_tool), "coreRunner": str(args.core_runner), "anvil": str(args.anvil),
                      "campaignSha256": m2.digest(Path(__file__).read_bytes()),
                      "differentialSha256": m2.digest((ROOT / "scripts/semantic-differential.py").read_bytes())},
            "counts": {key: 0 for key in ("generated", "excluded", "generationResourceExclusions", "executed", "completed", "matched", "mismatched", "inconclusive", "errors", "sourceRejected", "compilationRejected", "syntheticMismatches")},
            "cases": [], "findings": [], "secondaryFindings": [], "shrinkAttempts": 0,
            "coverage": {"kind": "AST features, literals and declared helper counts; plan-based profiles count the step graph and exclude sc_step/ABI wrappers; not runtime call or opcode coverage",
                         "generatedFeatures": [], "generatedWordLiterals": [],
                         "matchedFeatures": [], "matchedWordLiterals": [],
                         "requiredFeatures": [], "requiredWordLiterals": [],
                         "generatedInputs": [], "matchedInputs": [], "requiredInputs": [],
                         "generatedHelperCounts": [], "matchedHelperCounts": [], "requiredHelperCounts": []},
            "recipeCoverage": {"classification": "generator recipe metadata; matched entries verified by native replay; not runtime coverage",
                "generatedTemplates": [], "matchedTemplates": [], "requiredTemplates": [],
                "generatedUpdates": [], "matchedUpdates": [], "requiredUpdates": []},
            "loopCoverage": {"classification": "loop plan masks and mathematically specified iteration counts; matched plans verified by native replay; not measured traces or opcode coverage",
                "generatedMasks": [], "matchedMasks": [], "requiredMasks": [],
                "generatedIterations": [], "matchedIterations": [], "requiredIterations": []},
            "genericCoverage": {"classification": "prescribed generic variant and input parity; matched plans verified by native replay; not measured specialization or opcode coverage",
                "generatedInstantiations": [], "matchedInstantiations": [], "requiredInstantiations": []},
            "closureCoverage": {"classification": "prescribed runtime Word capture recipes; matched plans verified by native replay; not measured closure or opcode coverage",
                "generatedVariants": [], "matchedVariants": [], "requiredVariants": []},
            "comptimeCoverage": {"classification": "prescribed staged constant composition; matched plans verified by native replay; not measured specialization or opcode coverage",
                "generatedVariants": [], "matchedVariants": [], "requiredVariants": []},
            "constantCoverage": {"classification": "original closed constant AST features; matched plans verified by native replay; not runtime opcode coverage",
                "generatedFeatures": [], "matchedFeatures": [], "requiredFeatures": []},
            "moduleCoverage": {"classification": "prescribed mixed-module selection branches; canonical bundles verified by native replay; not measured import or opcode coverage",
                "generatedBranches": [], "matchedBranches": [], "requiredBranches": []},
            "retention": "all generated cases and compact reports; complete archives for findings and final reductions; no intermediate exports"}
        self.checkpoint()

    def checkpoint(self) -> None:
        self.summary["elapsedSeconds"] = round(time.monotonic() - self.started, 3)
        self.summary["shrinkAttempts"] = self.shrink_attempts
        self.summary["counts"]["unexecuted"] = self.summary["counts"]["generated"] - self.summary["counts"]["executed"]
        self.summary["retainedBytes"] = directory_bytes(self.args.output)
        coverage = self.summary["coverage"]
        coverage["missingFeatures"] = sorted(set(coverage["requiredFeatures"]) - set(coverage["matchedFeatures"]))
        coverage["missingWordLiterals"] = sorted(set(coverage["requiredWordLiterals"]) - set(coverage["matchedWordLiterals"]), key=int)
        coverage["missingInputs"] = sorted(set(coverage["requiredInputs"]) - set(coverage["matchedInputs"]), key=int)
        coverage["missingHelperCounts"] = sorted(set(coverage["requiredHelperCounts"]) - set(coverage["matchedHelperCounts"]))
        recipe = self.summary["recipeCoverage"]
        for dimension in ("Templates", "Updates"):
            recipe["missing" + dimension] = sorted(set(recipe["required" + dimension]) - set(recipe["matched" + dimension]))
        loop = self.summary["loopCoverage"]
        for dimension in ("Masks", "Iterations"):
            loop["missing" + dimension] = sorted(set(loop["required" + dimension]) - set(loop["matched" + dimension]))
        generic = self.summary["genericCoverage"]
        generic["missingInstantiations"] = sorted(set(generic["requiredInstantiations"]) - set(generic["matchedInstantiations"]))
        closure = self.summary["closureCoverage"]
        closure["missingVariants"] = sorted(set(closure["requiredVariants"]) - set(closure["matchedVariants"]))
        comptime = self.summary["comptimeCoverage"]
        comptime["missingVariants"] = sorted(set(comptime["requiredVariants"]) - set(comptime["matchedVariants"]))
        constant = self.summary["constantCoverage"]
        constant["missingFeatures"] = sorted(set(constant["requiredFeatures"]) - set(constant["matchedFeatures"]))
        module = self.summary["moduleCoverage"]
        module["missingBranches"] = sorted(set(module["requiredBranches"]) - set(module["matchedBranches"]))
        save_json(self.args.output / "summary.json", self.summary)

    def record_recipes(self, case: dict, *, matched: bool = False) -> None:
        for dimension, values in generation_recipes(case).items():
            key = ("matched" if matched else "generated") + dimension
            self.summary["recipeCoverage"][key] = sorted(set(self.summary["recipeCoverage"][key]) | values)

    def record_loops(self, case: dict, *, matched: bool = False) -> None:
        for dimension, values in specified_loops(case).items():
            key = ("matched" if matched else "generated") + dimension
            self.summary["loopCoverage"][key] = sorted(set(self.summary["loopCoverage"][key]) | values)

    def record_generics(self, case: dict, *, matched: bool = False) -> None:
        key = ("matched" if matched else "generated") + "Instantiations"
        self.summary["genericCoverage"][key] = sorted(set(self.summary["genericCoverage"][key]) | specified_generics(case))

    def record_closures(self, case: dict, *, matched: bool = False) -> None:
        key = ("matched" if matched else "generated") + "Variants"
        self.summary["closureCoverage"][key] = sorted(set(self.summary["closureCoverage"][key]) | specified_closures(case))

    def record_comptime(self, case: dict, *, matched: bool = False) -> None:
        prefix = "matched" if matched else "generated"
        key = prefix + "Variants"
        self.summary["comptimeCoverage"][key] = sorted(set(self.summary["comptimeCoverage"][key]) | specified_comptime(case))
        key = prefix + "Features"
        self.summary["constantCoverage"][key] = sorted(set(self.summary["constantCoverage"][key]) | constant_features(case))

    def record_modules(self, case: dict, *, matched: bool = False) -> None:
        key = ("matched" if matched else "generated") + "Branches"
        self.summary["moduleCoverage"][key] = sorted(set(self.summary["moduleCoverage"][key]) | specified_modules(case))

    def guard(self) -> None:
        if time.monotonic() >= self.deadline:
            raise m2.Finding(RESOURCE, "campaign-time", "campaign time limit reached")
        if directory_bytes(self.args.output) >= self.args.disk_bytes - self.reserve:
            raise m2.Finding(RESOURCE, "campaign-disk", "campaign disk limit reached; metadata reserve retained")

    def tool(self, command: list[str], stage: str) -> dict:
        self.guard()
        process_report = {"processes": []}
        args = SimpleNamespace(total_timeout=max(0.001, self.deadline - time.monotonic()),
            timeout=self.args.case_timeout, output_limit=min(2 * 1024 * 1024, self.args.disk_bytes // 64),
            resource_guard=self.guard)
        runner = m2.Runner(args, process_report)
        result = runner.process(stage, [str(self.args.case_tool), *command])
        if result["returncode"]:
            raise m2.Finding("adapter-error", stage, result["stderr"] + result["stdout"])
        value = json.loads(result["stdout"])
        if not isinstance(value, dict):
            raise ValueError("case tool returned a non-object result")
        if "caseToolSha256" not in self.summary["tools"]:
            self.summary["tools"]["caseToolSha256"] = runner.identity(self.args.case_tool)["sha256"]
        return value

    def case_args(self, case_path: Path, run_dir: Path):
        left = max(0.001, self.deadline - time.monotonic())
        return SimpleNamespace(case=case_path, replay=None, output=run_dir,
            case_tool=self.args.case_tool, core_runner=self.args.core_runner, anvil=self.args.anvil,
            upstream=self.args.upstream, target_dir=self.args.target_dir,
            direct_fuel=self.args.direct_fuel, core_fuel=self.args.core_fuel, gas=self.args.gas,
            timeout=min(self.args.case_timeout, left), startup_timeout=min(30, left),
            total_timeout=min(self.args.case_timeout, left),
            output_limit=min(2 * 1024 * 1024, self.args.disk_bytes // 64),
            artifact_limit=min(64 * 1024 * 1024, (self.args.disk_bytes - self.reserve) // 8),
            resource_guard=self.guard)

    def execute_case(self, case: dict) -> tuple[Path, dict, dict]:
        self.guard()
        self.counter += 1
        folder = self.work / f"run-{self.counter:06d}"
        folder.mkdir()
        input_path = self.work / f"input-{self.counter:06d}.json"
        save_json(input_path, case)
        args = self.case_args(input_path, folder)
        report = {"schema": m2.REPORT_SCHEMA, "processes": [], "observations": {}, "rawObservations": {},
            "budgets": {key: getattr(args, key) for key in ("direct_fuel", "core_fuel", "gas", "timeout", "startup_timeout", "total_timeout", "output_limit", "artifact_limit")},
            "scope": "closed G0 Word/Bool, gas-independent, Sonatina O0, pure run() ABI Word"}
        try:
            m2.execute(args, report)
        except m2.Finding as error:
            report["comparison"] = {"category": error.category, "stage": error.stage, "detail": error.detail, "pairs": {}}
        except (ValueError, OSError, KeyError, TypeError, m2.RpcError) as error:
            report["comparison"] = {"category": "adapter-error", "stage": "campaign-adapter", "detail": str(error), "pairs": {}}
        except KeyboardInterrupt:
            report["comparison"] = {"category": RESOURCE, "stage": "campaign-interrupted", "detail": "interrupted", "pairs": {}}
            raise
        finally:
            report["artifacts"] = {path.name: m2.file_digest(path) for path in folder.iterdir() if path.is_file()}
            save_json(folder / "report.json", report)
            input_path.unlink(missing_ok=True)
        analysis = analyze(report, self.args.test_perturb_path)
        # analysis is deliberately outside the immutable actual M2 report.
        save_json(folder / "analysis.json", analysis)
        return folder, report, analysis

    def retain_finding(self, index: int, folder: Path, case: dict, report: dict, analysis: dict) -> dict:
        branch = "synthetic" if analysis["synthetic"] else "real"
        location = self.args.output / "findings" / branch / f"{index:04d}"
        location.mkdir(parents=True)
        original = location / "original"
        folder.rename(original)
        finding = {"caseIndex": index, "synthetic": analysis["synthetic"], "fingerprint": fingerprint(analysis),
            "originalProgramSha256": program_hash(case), "finalProgramSha256": program_hash(case),
            "originalArchive": str(original.relative_to(self.args.output)),
            "finalArchive": str(original.relative_to(self.args.output)), "history": str((location / "shrink.json").relative_to(self.args.output))}
        status = "not-shrinkable" if analysis["comparison"]["category"] not in SHRINKABLE else (
            "no-attempts" if self.args.shrink_attempts == 0 else
            "attempt-limit" if self.shrink_attempts >= self.args.shrink_attempts else "pending")
        save_json(self.args.output / finding["history"], {
            "schema": "solcore-lean.semantic-shrink.v1", "fingerprint": finding["fingerprint"],
            "originalProgramSha256": finding["originalProgramSha256"],
            "finalProgramSha256": finding["finalProgramSha256"],
            "finalArchive": finding["finalArchive"], "steps": [], "status": status})
        self.summary["findings"].append(finding)
        self.checkpoint()
        return finding

    def retain_secondary(self, folder: Path, analysis: dict, history_path: Path, step: dict) -> None:
        # Moving an already-written archive does not allocate a second copy.
        # Persist it before the next budget check; it must not disappear merely
        # because it differs from the original shrink target.
        archive = history_path.parent / "secondary" / f"{self.shrink_attempts:04d}"
        archive.parent.mkdir(parents=True, exist_ok=True)
        folder.rename(archive)
        relative = str(archive.relative_to(self.args.output))
        step["secondaryArchive"] = relative
        self.summary["secondaryFindings"].append({"archive": relative,
            "fingerprint": fingerprint(analysis), "programSha256": step["programSha256"],
            "parentHistory": str(history_path.relative_to(self.args.output)),
            "automaticReduction": False})

    def shrink(self, original: dict, finding: dict) -> None:
        location = self.args.output / finding["originalArchive"]
        history_path = self.args.output / finding["history"]
        expected = finding["fingerprint"]
        current = original
        current_path = location / "case.json"
        seen = {program_hash(current)}
        history = {"schema": "solcore-lean.semantic-shrink.v1", "fingerprint": expected,
                   "originalProgramSha256": program_hash(original), "steps": [], "status": "running"}
        save_json(history_path, history)
        try:
            while self.shrink_attempts < self.args.shrink_attempts:
                self.guard()
                limit = min(self.args.shrink_candidates, self.args.shrink_attempts - self.shrink_attempts)
                response = self.tool(["shrink", str(current_path), str(limit), str(self.args.direct_fuel)], "shrink-candidates")
                candidates = response.get("cases")
                if response.get("schema") != "solcore-lean.semantic-corpus.v1" or not isinstance(candidates, list) or len(candidates) > limit:
                    raise ValueError("invalid bounded shrink response")
                accepted = False
                for candidate in candidates:
                    self.guard()
                    candidate_hash = program_hash(candidate)
                    if candidate_hash in seen:
                        continue
                    seen.add(candidate_hash)
                    self.shrink_attempts += 1
                    folder, report, analysis = self.execute_case(candidate)
                    keep = same_failure(expected, analysis)
                    step = {"attempt": self.shrink_attempts, "programSha256": candidate_hash,
                        "sourceSha256": m2.digest(candidate["source"].encode()),
                        "actualReportSha256": m2.file_digest(folder / "report.json"),
                        "fingerprint": fingerprint(analysis), "accepted": keep,
                        "actualComparison": report.get("comparison"), "comparison": analysis["comparison"]}
                    history["steps"].append(step)
                    if keep:
                        destination = location.parent / "reduced"
                        previous = location.parent / "previous-reduced"
                        if destination.exists():
                            destination.rename(previous)
                        folder.rename(destination)
                        if previous.exists():
                            shutil.rmtree(previous)
                        current, current_path = candidate, destination / "case.json"
                        finding["finalProgramSha256"] = candidate_hash
                        finding["finalArchive"] = str(destination.relative_to(self.args.output))
                        accepted = True
                    elif not analysis["synthetic"] and analysis["comparison"]["category"] in SHRINKABLE | {"adapter-error"}:
                        self.retain_secondary(folder, analysis, history_path, step)
                    else:
                        shutil.rmtree(folder)
                    save_json(history_path, history)
                    self.checkpoint()
                    self.guard()
                    if accepted:
                        break
                if not accepted:
                    history["status"] = "no-preserving-candidate"
                    break
            else:
                history["status"] = "attempt-limit"
        except m2.Finding as error:
            history["status"] = "budget-exhausted" if error.category == RESOURCE else "error"
            history["stop"] = {"category": error.category, "stage": error.stage, "detail": error.detail}
            raise
        except KeyboardInterrupt:
            history["status"] = "interrupted"
            raise
        except (ValueError, OSError, KeyError, TypeError) as error:
            history["status"] = "error"
            history["stop"] = {"category": "adapter-error", "detail": str(error)}
            raise
        finally:
            history["finalProgramSha256"] = finding["finalProgramSha256"]
            history["finalArchive"] = finding["finalArchive"]
            save_json(history_path, history)
            self.checkpoint()

    def prepare_cases(self) -> dict:
        if self.args.case is not None:
            case = m2.read_json(self.args.case)
            m2.validate_case(case)
            self.summary["caseInput"] = {"path": str(self.args.case), "sha256": m2.file_digest(self.args.case)}
            return {"schema": "solcore-lean.semantic-corpus.v1", "requested": 1,
                "attempted": 0, "excluded": [], "cases": [case], "status": "complete"}
        if self.args.corpus is None:
            command = PROFILE_COMMANDS[self.args.profile][0]
            return self.tool([command, str(self.args.seed), str(self.args.nodes), str(self.args.cases),
                              str(self.args.attempts), str(self.args.direct_fuel)], "generation")
        manifest = validate_manifest(m2.read_json(self.args.corpus))
        profile = manifest.get("profile", "closed-g0")
        runtime_input = profile != "closed-g0"
        generate_command, emit_command, origin_kind = PROFILE_COMMANDS[profile]
        save_json(self.args.output / "corpus.json", manifest)
        self.summary["corpus"] = {"path": str(self.args.corpus), "sha256": m2.digest(m2.json_bytes(manifest))}
        coverage = self.summary["coverage"]
        coverage["requiredFeatures"] = sorted(set(manifest.get("requiredFeatures", [])))
        coverage["requiredWordLiterals"] = sorted({m2.word(value) for value in manifest.get("requiredWordLiterals", [])}, key=int)
        coverage["requiredInputs"] = sorted(set(manifest.get("requiredInputs", [])), key=int)
        coverage["requiredHelperCounts"] = sorted(manifest.get("requiredHelperCounts", []))
        requirements = recipe_requirements(manifest)
        self.summary["recipeCoverage"]["requiredTemplates"] = sorted(requirements["templates"])
        self.summary["recipeCoverage"]["requiredUpdates"] = sorted(requirements["updates"])
        loops = loop_requirements(manifest)
        self.summary["loopCoverage"]["requiredMasks"] = sorted(loops["masks"])
        self.summary["loopCoverage"]["requiredIterations"] = sorted(loops["iterations"])
        self.summary["genericCoverage"]["requiredInstantiations"] = sorted(generic_requirements(manifest)["instantiations"])
        self.summary["closureCoverage"]["requiredVariants"] = sorted(closure_requirements(manifest)["variants"])
        self.summary["comptimeCoverage"]["requiredVariants"] = sorted(comptime_requirements(manifest)["variants"])
        self.summary["constantCoverage"]["requiredFeatures"] = sorted(constant_requirements(manifest))
        self.summary["moduleCoverage"]["requiredBranches"] = sorted(module_requirements(manifest)["branches"])
        cases, excluded, ids, accepted_ids = [], [], [], []
        attempted = 0
        for entry in manifest["cases"][:self.args.cases]:
            self.guard()
            if attempted >= self.args.attempts:
                break
            attempted += 1
            if not isinstance(entry, dict) or not isinstance(entry.get("id"), str) or entry["id"] in ids:
                raise ValueError("corpus entries require unique IDs")
            ids.append(entry["id"])
            if "generation" in entry:
                request = entry["generation"]
                response = self.tool([generate_command,
                    str(request["seed"]), str(request["maxProgramNodes"]),
                    "6" if profile == "runtime-loops" else "4" if runtime_input else "1",
                    "1", str(self.args.direct_fuel)], "corpus-generation")
                generated = response.get("cases", [])
                if runtime_input:
                    generated = [case for case in generated if case.get("input") == entry["input"]]
                if len(generated) != 1:
                    excluded.append({"id": entry["id"], "stage": "generation", "detail": response})
                    self.summary["counts"]["excluded"] = len(excluded)
                    self.summary["counts"]["generationResourceExclusions"] = generation_resource_exclusions(excluded)
                    self.summary["generation"] = {"requested": self.args.cases, "attempted": attempted, "status": "running"}
                    save_json(self.args.output / "generation.json", {"excluded": excluded, **self.summary["generation"]})
                    self.checkpoint()
                    continue
                case = generated[0]
            elif any(key in entry for key in ("program", "loopPlan", "genericPlan", "closurePlan", "comptimePlan", "modulePlan")):
                program = self.work / "corpus-program.json"
                plan_key = {"runtime-loops": "loopPlan", "runtime-generics": "genericPlan", "runtime-closures": "closurePlan", "runtime-comptime": "comptimePlan", "runtime-modules": "modulePlan"}.get(profile, "program")
                save_json(program, entry[plan_key])
                try:
                    command = [emit_command, str(program)] + ([entry["input"]] if runtime_input else [])
                    case = self.tool([*command, str(self.args.direct_fuel)], "corpus-emission")
                finally:
                    program.unlink(missing_ok=True)
            else:
                raise ValueError("corpus entry has no generation request or program")
            m2.validate_case(case)
            if runtime_input and case.get("input") != entry["input"]:
                raise ValueError(f"corpus input changed for {entry['id']}")
            if "generation" in entry:
                origin = case["provenance"].get("origin", {})
                if origin.get("kind") != origin_kind or origin.get("seed") != entry["generation"]["seed"] or origin.get("maxProgramNodes") != entry["generation"]["maxProgramNodes"]:
                    raise ValueError(f"generated corpus provenance differs for {entry['id']}")
            for key in ("generatorVersion", "emitterVersion", "wrapperVersion") + PROFILE_VERSION_FIELDS[profile]:
                if manifest.get(key) != case["provenance"].get(key):
                    raise ValueError(f"corpus {key} changed")
            if set(entry.get("expectedFeatures", [])) != set(case["provenance"]["features"]):
                raise ValueError(f"corpus feature inventory changed for {entry['id']}")
            if profile in ("runtime-comptime", "runtime-modules") and set(entry["expectedConstantFeatures"]) != constant_features(case):
                raise ValueError(f"corpus constant feature inventory changed for {entry['id']}")
            cases.append(case)
            accepted_ids.append(entry["id"])
            save_json(self.args.output / "cases" / f"{len(cases)-1:04d}.json", case)
            self.summary["counts"]["generated"] = len(cases)
            coverage["generatedFeatures"] = sorted(set(coverage["generatedFeatures"]) | set(case["provenance"]["features"]))
            coverage["generatedWordLiterals"] = sorted(set(coverage["generatedWordLiterals"]) | word_literals(case["program"]), key=int)
            coverage["generatedHelperCounts"] = sorted(set(coverage["generatedHelperCounts"]) | helper_counts(case))
            self.record_recipes(case)
            self.record_loops(case)
            self.record_generics(case)
            self.record_closures(case)
            self.record_comptime(case)
            self.record_modules(case)
            if runtime_input:
                coverage["generatedInputs"] = sorted(set(coverage["generatedInputs"]) | {case["input"]}, key=int)
            self.summary["generation"] = {"requested": self.args.cases, "attempted": attempted, "status": "running"}
            self.summary["corpus"]["acceptedIds"] = accepted_ids
            self.summary["corpus"]["entryIds"] = ids
            save_json(self.args.output / "generation.json", {"excluded": excluded, **self.summary["generation"]})
            self.checkpoint()
        self.summary["corpus"]["entryIds"] = ids
        return {"schema": "solcore-lean.semantic-corpus.v1", "requested": self.args.cases,
            "attempted": attempted, "excluded": excluded, "cases": cases,
            "status": "complete" if len(cases) == self.args.cases else "generation-exhausted"}

    def run(self) -> None:
        response = self.prepare_cases()
        cases, excluded = response.get("cases"), response.get("excluded")
        if response.get("schema") != "solcore-lean.semantic-corpus.v1" or not isinstance(cases, list) or not isinstance(excluded, list) or len(cases) > self.args.cases:
            raise ValueError("invalid bounded generation response")
        self.summary["counts"]["generated"] = len(cases)
        self.summary["counts"]["excluded"] = len(excluded)
        self.summary["counts"]["generationResourceExclusions"] = generation_resource_exclusions(excluded)
        self.summary["generation"] = {key: response.get(key) for key in ("requested", "attempted", "status")}
        self.summary["generation"]["attemptUnit"] = (
            "manifest entries" if self.args.corpus else
            "function graph candidates" if self.args.profile in HELPER_PROFILES else
            "function candidates" if self.args.profile != "closed-g0" else "program candidates")
        save_json(self.args.output / "generation.json", {key: value for key, value in response.items() if key != "cases"})
        coverage = self.summary["coverage"]
        coverage["generatedFeatures"] = sorted({feature for case in cases for feature in case["provenance"]["features"]})
        coverage["generatedWordLiterals"] = sorted({value for case in cases for value in word_literals(case["program"])}, key=int)
        coverage["generatedInputs"] = sorted({case["input"] for case in cases if case["schema"] != m2.CASE_SCHEMA}, key=int)
        coverage["generatedHelperCounts"] = sorted({count for case in cases for count in helper_counts(case)})
        for case in cases:
            self.record_recipes(case)
            self.record_loops(case)
            self.record_generics(case)
            self.record_closures(case)
            self.record_comptime(case)
            self.record_modules(case)
        for index, case in enumerate(cases):
            self.guard()
            m2.validate_case(case)
            expected_schema = PROFILE_SCHEMAS[self.args.profile]
            if case["schema"] != expected_schema:
                raise ValueError("case tool returned a different generation profile")
            save_json(self.args.output / "cases" / f"{index:04d}.json", case)
        for index, case in enumerate(cases):
            self.guard()
            folder, report, analysis = self.execute_case(case)
            category = analysis["comparison"]["category"]
            counts = self.summary["counts"]
            count_outcome(counts, analysis)
            if category == "matched":
                coverage["matchedFeatures"] = sorted(set(coverage["matchedFeatures"]) | set(case["provenance"]["features"]))
                coverage["matchedWordLiterals"] = sorted(set(coverage["matchedWordLiterals"]) | word_literals(case["program"]), key=int)
                coverage["matchedHelperCounts"] = sorted(set(coverage["matchedHelperCounts"]) | helper_counts(case))
                self.record_recipes(case, matched=True)
                self.record_loops(case, matched=True)
                self.record_generics(case, matched=True)
                self.record_closures(case, matched=True)
                self.record_comptime(case, matched=True)
                self.record_modules(case, matched=True)
                if case["schema"] != m2.CASE_SCHEMA:
                    coverage["matchedInputs"] = sorted(set(coverage["matchedInputs"]) | {case["input"]}, key=int)
            save_json(self.args.output / "results" / f"{index:04d}.json", {"actualReport": compact_report(report), "analysis": analysis})
            case_id = self.summary.get("corpus", {}).get("acceptedIds", [f"generated-{i}" for i in range(len(cases))])[index]
            row = {"index": index, "id": case_id, "case": f"cases/{index:04d}.json", "result": f"results/{index:04d}.json",
                   "programSha256": program_hash(case), "category": category, "synthetic": analysis["synthetic"],
                   "fingerprint": fingerprint(analysis)}
            self.summary["cases"].append(row)
            if category in SHRINKABLE or category == "adapter-error":
                finding = self.retain_finding(index, folder, case, report, analysis)
                if category in SHRINKABLE and self.shrink_attempts < self.args.shrink_attempts:
                    self.shrink(case, finding)
            else:
                shutil.rmtree(folder)
            self.checkpoint()
            print(json.dumps({"case": index, "category": category, "synthetic": analysis["synthetic"]}), flush=True)
        self.summary["status"] = "complete" if len(cases) == self.args.cases else "generation-exhausted"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="new campaign directory")
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--profile", choices=PROFILES,
                        help="generation profile; inferred from a saved case or corpus, otherwise closed-g0")
    parser.add_argument("--nodes", type=int, help="node budget; default 384 for loops/generics/closures/comptime/modules, 256 for aggregates, 192 for local mutation, otherwise 32")
    parser.add_argument("--cases", type=int, help="case limit; default 16 or the full supplied corpus")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--corpus", type=Path, help="fixed versioned CI corpus manifest")
    selection.add_argument("--case", type=Path, help="re-execute one saved case, including a reduced finding")
    parser.add_argument("--attempts", type=int, help="generation attempt limit; default 512 for comptime/modules, otherwise 256")
    parser.add_argument("--seconds", type=float, default=300)
    parser.add_argument("--disk-bytes", type=int, default=128 * 1024 * 1024)
    parser.add_argument("--shrink-attempts", type=int, default=32, help="total candidate executions across all findings")
    parser.add_argument("--shrink-candidates", type=int, default=64)
    parser.add_argument("--case-timeout", type=float, default=90)
    parser.add_argument("--direct-fuel", type=int, default=1000000)
    parser.add_argument("--core-fuel", type=int, default=10000000)
    parser.add_argument("--gas", type=int, default=10000000)
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--core-runner", type=Path, default=ROOT / ".lake/build/bin/rust-hull-scenario")
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--test-perturb-path", choices=PATHS,
                        help="SYNTHETIC TEST ONLY: change a copied observation after real three-way agreement")
    args = parser.parse_args()
    try:
        selected_profile = None
        if args.corpus:
            selected_profile = validate_manifest(m2.read_json(args.corpus)).get("profile", "closed-g0")
        elif args.case:
            case = m2.read_json(args.case)
            m2.validate_case(case)
            selected_profile = m2.CASE_PROFILES[case["schema"]]
        if args.profile and selected_profile and args.profile != selected_profile:
            parser.error("--profile disagrees with the supplied case or corpus")
        args.profile = args.profile or selected_profile or "closed-g0"
    except (OSError, ValueError, KeyError, TypeError, m2.Finding) as error:
        parser.error(str(error))
    if args.attempts is None:
        args.attempts = 512 if args.profile in ("runtime-comptime", "runtime-modules") else 256
    if args.nodes is None:
        args.nodes = {"runtime-mutation": 192, "runtime-aggregates": 256, "runtime-loops": 384, "runtime-generics": 384, "runtime-closures": 384, "runtime-comptime": 384, "runtime-modules": 384}.get(args.profile, 32)
    if args.cases is None:
        try:
            args.cases = 1 if args.case else len(validate_manifest(m2.read_json(args.corpus))["cases"]) if args.corpus else 16
        except (OSError, ValueError, KeyError, m2.Finding) as error:
            parser.error(str(error))
    if args.case and args.cases != 1:
        parser.error("--case requires --cases 1")
    limits = {"seed": (0, 2**64 - 1), "nodes": (3, 512), "cases": (1, 1024), "attempts": (0, 10000),
              "seconds": (0.001, 86400), "disk_bytes": (16 * 1024 * 1024, 10**10),
              "shrink_attempts": (0, 10000), "shrink_candidates": (1, 4096), "case_timeout": (0.001, 3600),
              "direct_fuel": (1, 10000000), "core_fuel": (1, 1000000000), "gas": (1, 1000000000)}
    for key, (lower, upper) in limits.items():
        value = getattr(args, key)
        if not math.isfinite(value) or not lower <= value <= upper:
            parser.error(f"{key} must be between {lower} and {upper}")
    for key in ("output", "case_tool", "core_runner", "anvil", "upstream", "target_dir"):
        setattr(args, key, getattr(args, key).resolve())
    if args.corpus:
        args.corpus = args.corpus.resolve()
    if args.case:
        args.case = args.case.resolve()
    args.output.mkdir(parents=True, exist_ok=False)
    campaign = Campaign(args)
    previous_term = signal.getsignal(signal.SIGTERM)

    def interrupted(_signum, _frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupted)
    try:
        campaign.run()
    except m2.Finding as error:
        campaign.summary["status"] = "budget-exhausted" if error.category == RESOURCE else "error"
        campaign.summary["stop"] = {"category": error.category, "stage": error.stage, "detail": error.detail}
    except KeyboardInterrupt:
        campaign.summary["status"] = "interrupted"
    except (ValueError, OSError, KeyError, TypeError) as error:
        campaign.summary["status"] = "error"
        campaign.summary["stop"] = {"category": "adapter-error", "detail": str(error)}
    finally:
        try:
            shutil.rmtree(campaign.work, ignore_errors=True)
            campaign.checkpoint()
            if campaign.summary["status"] == "complete" and missing_coverage(campaign.summary):
                campaign.summary["status"] = "coverage-incomplete"
                campaign.checkpoint()
        finally:
            signal.signal(signal.SIGTERM, previous_term)
    counts = campaign.summary["counts"]
    print(json.dumps({"status": campaign.summary["status"], "synthetic": campaign.summary["synthetic"],
                      "counts": counts, "summary": str(args.output / "summary.json")}))
    return 0 if campaign.summary["status"] == "complete" and counts["matched"] == args.cases and not missing_coverage(campaign.summary) else 1


if __name__ == "__main__":
    raise SystemExit(main())
