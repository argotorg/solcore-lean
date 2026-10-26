#!/usr/bin/env python3
"""Materialize, replay and execute the fixed storage corpus with native Core.

Every sequence starts with empty persistent storage and uses the actual checked
contract runtime for each transaction. Complete histories, including every
committed prefix, must be repeatable. No Python state transition or saved result
is an execution oracle. Coverage describes checked step ASTs, declared helpers,
completed inputs and replayed generator recipes; this does not execute an EVM.
Rollback outcomes must match the fixed input-parity contract. Every reverted
transaction must preserve its previous committed snapshot. Completion patterns
are collected from actual histories, not inferred from the input sequence.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


pure = load_module("semantic_corpus", ROOT / "Tests/scripts/test-semantic-corpus.py")
protocol = load_module("storage_protocol", ROOT / "scripts/semantic-storage-differential.py")
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
MANIFEST_SCHEMA = "solcore-lean.semantic-storage-corpus-manifest.v1"
VERSIONS = pure.VERSIONS + pure.MUTATION_VERSIONS + pure.LOOP_STEP_VERSIONS
ALLOWED_FEATURES = pure.FEATURES | pure.MUTATION_FEATURES | pure.AGGREGATE_FEATURES | pure.PRIMITIVE_FEATURES | {"functionCall"}
BOUNDARIES = {0, 1, 3, 7, (1 << 256) - 1, 1 << 255}
BINDINGS = {"schema": "solcore-lean.storage-bindings.v1", "caller": "17", "address": "101"}
ZERO_STORAGE = [{"slot": "0", "value": "0"}, {"slot": "1", "value": "0"}]
ROLLBACK_PATTERNS = {"returned,reverted,returned", "reverted,reverted,returned",
                     "reverted", "reverted,returned"}


def string_set(value, label: str) -> set[str]:
    require(isinstance(value, list) and all(isinstance(item, str) for item in value)
            and len(value) == len(set(value)), f"{label} must contain unique strings")
    return set(value)


def integer_set(value, expected: set[int], label: str) -> set[int]:
    require(isinstance(value, list) and all(type(item) is int for item in value)
            and len(value) == len(set(value)) and set(value) == expected,
            f"{label} must declare exactly {sorted(expected)}")
    return set(value)


def check_manifest(manifest: dict) -> list[dict]:
    require(isinstance(manifest, dict) and manifest.get("schema") == MANIFEST_SCHEMA,
            "unexpected storage corpus manifest schema")
    require(isinstance(manifest.get("profile"), str) and manifest["profile"] in protocol.PROFILES,
            "unsupported storage corpus profile")
    selected = protocol.PROFILES[manifest["profile"]]
    require(manifest.get("coverageKind") == "step-core-ast-features", "storage coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest.get(version), str) and manifest[version], f"missing {version}")
    features = string_set(manifest.get("requiredFeatures"), "requiredFeatures")
    require(features and features <= ALLOWED_FEATURES, "unsupported step AST feature requirement")
    inputs = string_set(manifest.get("requiredInputs"), "requiredInputs")
    require({canonical_word(value) for value in inputs} == BOUNDARIES,
            "storage corpus must require all six boundary inputs")
    integer_set(manifest.get("requiredHelperCounts"), {1, 2, 3}, "requiredHelperCounts")
    integer_set(manifest.get("requiredTransactionCounts"), {1, 2, 3}, "requiredTransactionCounts")
    recipe = manifest.get("generationRecipeRequirements")
    require(isinstance(recipe, dict) and set(recipe) == {"templates"},
            "storage corpus must declare generator template requirements")
    integer_set(recipe["templates"], {0, 1, 2, 3}, "recipe templates")
    if selected["rollback"]:
        require(string_set(manifest.get("requiredOutcomes"), "requiredOutcomes") == {"returned", "reverted"},
                "rollback corpus must require returned and reverted outcomes")
        require(string_set(manifest.get("requiredCompletionPatterns"), "requiredCompletionPatterns") == ROLLBACK_PATTERNS,
                "rollback corpus must require every fixed completion pattern")
    else:
        require("requiredOutcomes" not in manifest and "requiredCompletionPatterns" not in manifest,
                "rollback coverage requirements need the rollback profile")
    entries = manifest.get("cases")
    require(isinstance(entries, list) and entries, "storage corpus must contain scenarios")
    identifiers = set()
    for entry in entries:
        require(isinstance(entry, dict), "scenario entry must be an object")
        identifier = entry.get("id")
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,64}", identifier)
                and identifier not in identifiers, "scenario IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        expected = string_set(entry.get("expectedFeatures"), f"{identifier}: expectedFeatures")
        require(expected and expected <= ALLOWED_FEATURES, f"{identifier}: unsupported step feature")
        fields = {"id", "expectedFeatures"}
        if "generation" in entry:
            require(set(entry) == fields | {"generation"},
                    f"{identifier}: choose generation or a storage plan with transactions")
            generation = entry["generation"]
            require(isinstance(generation, dict) and set(generation) == {"seed", "maxProgramNodes"},
                    f"{identifier}: invalid generation specification")
            seed = canonical_word(generation["seed"])
            require(seed < 1 << 64, f"{identifier}: seed exceeds uint64")
            nodes = generation["maxProgramNodes"]
            # Measured canonical wrapper overhead; the native checker still
            # validates the entire emitted program against the requested bound.
            minimum = 62 if selected["rollback"] else 41
            require(type(nodes) is int and minimum < nodes <= 512, f"{identifier}: invalid full-program node budget")
        else:
            require(set(entry) == fields | {"storagePlan", "transactions"},
                    f"{identifier}: imported scenarios require exactly a storage plan and transactions")
            plan = entry["storagePlan"]
            require(isinstance(plan, dict) and set(plan) == {"schema", "stepProgram"}
                    and plan["schema"] == selected["planSchema"]
                    and isinstance(plan["stepProgram"], dict), f"{identifier}: invalid storage plan")
            require(isinstance(entry["transactions"], list) and 1 <= len(entry["transactions"]) <= 3,
                    f"{identifier}: expected one to three transactions")
    return entries


def materialize(entry: dict, tool: Path, directory: Path, fuel: int,
                profile: str = "stateful-storage") -> dict:
    selected = protocol.PROFILES[profile]
    if "generation" in entry:
        generation = entry["generation"]
        corpus = run(tool, "generate", generation["seed"], str(generation["maxProgramNodes"]),
                     "1", "1", str(fuel))
        require(corpus.get("schema") == selected["corpusSchema"]
                and corpus.get("status") == "complete" and corpus.get("requested") == 1
                and corpus.get("attempted") == 1 and corpus.get("excluded") == []
                and len(corpus.get("cases", [])) == 1,
                f"{entry['id']}: fixed seed did not emit in its single allowed attempt")
        case = corpus["cases"][0]
        origin = case["provenance"]["origin"]
        require(origin.get("kind") == selected["originKind"] and origin.get("seed") == generation["seed"]
                and origin.get("maxProgramNodes") == generation["maxProgramNodes"]
                and origin.get("validationFuel") == fuel,
                f"{entry['id']}: generated provenance differs from the requested recipe")
    else:
        plan_path, tx_path = directory / "plan.json", directory / "transactions.json"
        plan_path.write_text(json.dumps(entry["storagePlan"]))
        tx_path.write_text(json.dumps(entry["transactions"]))
        case = run(tool, "emit", str(plan_path), str(tx_path), str(fuel))
        require(case.get("storagePlan") == entry["storagePlan"]
                and case.get("transactions") == entry["transactions"],
                f"{entry['id']}: emission changed the original plan or transaction sequence")
    protocol.validate_case(case)
    require(case["schema"] == selected["caseSchema"], f"{entry['id']}: native tool emitted a different profile")
    require(case.get("executionFuel") == fuel and "directCore" not in case,
            f"{entry['id']}: case must record its budget without expected execution results")
    return case


def step_parts(case: dict) -> tuple[list[dict], dict]:
    step = case["storagePlan"]["stepProgram"]
    require(step.get("schema") == "solcore-semantic-core" and step.get("dataDefinitions") == []
            and step.get("resultType") == {"tag": "function", "parameter": "word", "result": "word"},
            "storage step must be a closed Word function DAG")
    return pure.function_parts(step["body"])


def complete_history(history: dict, case: dict, fuel: int) -> dict:
    require(history.get("bindings") == BINDINGS and history.get("fuelPerTransaction") == fuel,
            "native observation did not use the current execution bindings and fuel")
    normalized = protocol.normalize_history(history, case)
    require(normalized["initialStorage"] == ZERO_STORAGE, "native storage must start empty")
    require(normalized["status"] == "complete" and normalized["unexecuted"] == []
            and normalized["unobserved"] == [] and history.get("stoppedAt") is None,
            "native storage history did not complete within its budget")
    prior = normalized["initialStorage"]
    for row, transaction in zip(normalized["transactions"], case["transactions"]):
        require(row["status"] == protocol.expected_status(case, transaction),
                "transaction outcome differs from the fixed profile's completion policy")
        require(len(protocol.common.hex_bytes(row["output"], "output")) == 32,
                "every completed transaction must return or revert with exactly one ABI Word")
        if row["status"] == "reverted":
            require(row["committedStorage"] == prior, "reverted transaction changed committed storage")
        prior = row["committedStorage"]
    return normalized


def validate(manifest: dict, tool: Path, fuel: int) -> dict:
    require(type(fuel) is int and 0 < fuel <= 10_000_000, "fuel must be positive and within the native tool limit")
    entries = check_manifest(manifest)
    profile = manifest["profile"]
    covered_features, completed_inputs, helper_counts, transaction_counts, templates = set(), set(), set(), set(), set()
    outcomes, completion_patterns = set(), set()
    plans, completed_transactions = {}, 0
    with tempfile.TemporaryDirectory(prefix="semantic-storage-corpus-") as name:
        directory = Path(name)
        bindings_path = directory / "bindings.json"
        bindings_path.write_text(json.dumps(BINDINGS))
        for entry in entries:
            case = materialize(entry, tool, directory, fuel, profile)
            require(case == materialize(entry, tool, directory, fuel, profile), f"{entry['id']}: materialization is not deterministic")
            for version in VERSIONS:
                require(case["provenance"][version] == manifest[version], f"{entry['id']}: {version} changed")
            helpers, body = step_parts(case)
            actual_features, _ = pure.ast_coverage(helpers + [body], function_calls=True,
                                                   mutable_cells=True, aggregates=True)
            require(actual_features == set(case["provenance"]["features"]) == set(entry["expectedFeatures"]),
                    f"{entry['id']}: declared features differ from the checked step AST")
            case_path = directory / "case.json"
            case_path.write_text(json.dumps(case))
            before = run(tool, "observe", str(case_path), str(bindings_path), str(fuel))
            observed = complete_history(before, case, fuel)
            # Replay reconstructs and checks the entire canonical host program,
            # source, transaction IDs, ABI data and generation recipe natively.
            replayed = run(tool, "replay", str(case_path), str(fuel))
            require(replayed == case, f"{entry['id']}: checked replay changed the scenario")
            case_path.write_text(json.dumps(replayed))
            after = run(tool, "observe", str(case_path), str(bindings_path), str(fuel))
            complete_history(after, replayed, fuel)
            require(before == after, f"{entry['id']}: repeated native history changed a committed prefix")
            key = json.dumps(case["storagePlan"], sort_keys=True, separators=(",", ":"))
            implementation = (case["source"], case["program"], case["contract"])
            require(plans.setdefault(key, implementation) == implementation,
                    f"{entry['id']}: the same plan emitted transaction-dependent source or Core")
            if "generation" in entry:
                origin = case["provenance"]["origin"]["stepOrigin"]
                metadata = origin.get("helpers")
                require(origin.get("kind") == "aggregate-generated" and isinstance(metadata, list)
                        and origin.get("helperCount") == len(helpers) == len(metadata),
                        "replayed helper metadata differs from the actual step declarations")
                for helper in metadata:
                    template = helper.get("template")
                    require(type(template) is int and template in {0, 1, 2, 3}, "unknown replayed step template")
                    templates.add(template)
            # Only a fully completed native sequence contributes coverage.
            covered_features.update(actual_features)
            completed_inputs.update(canonical_word(tx["input"]) for tx in case["transactions"])
            helper_counts.add(len(helpers))
            transaction_counts.add(len(case["transactions"]))
            completed_transactions += len(case["transactions"])
            statuses = [row["status"] for row in observed["transactions"]]
            outcomes.update(statuses)
            completion_patterns.add(",".join(statuses))
    require(covered_features == set(manifest["requiredFeatures"]), "fixed corpus lost its exact step AST feature union")
    require(BOUNDARIES <= completed_inputs, "fixed corpus lost a completed boundary input")
    require(helper_counts == {1, 2, 3}, "fixed corpus lost a completed helper declaration count")
    require(transaction_counts == {1, 2, 3}, "fixed corpus lost a completed transaction count")
    require(templates == {0, 1, 2, 3}, "fixed corpus lost a replayed generator template")
    report = {"status": "passed", "profile": profile, "scenarios": len(entries),
            "completedTransactions": completed_transactions, "planGroups": len(plans),
            "coverageKind": "step-core-ast-features", "requiredFeatures": len(covered_features),
            "completedInputs": [str(value) for value in sorted(completed_inputs)],
            "completedHelperCounts": sorted(helper_counts), "completedTransactionCounts": sorted(transaction_counts),
            "generationRecipe": {"classification": "replayed-generator-metadata", "templates": sorted(templates)},
            "bindings": BINDINGS, "nativeHistoriesReplayed": len(entries), "evmExecuted": False}
    if protocol.PROFILES[profile]["rollback"]:
        require(set(manifest["requiredOutcomes"]) <= outcomes, "fixed corpus lost a completed outcome")
        require(set(manifest["requiredCompletionPatterns"]) <= completion_patterns,
                "fixed corpus lost an executed completion pattern")
        report["rollbackCoverage"] = {"classification": "completed-native-histories",
            "requiredOutcomes": sorted(manifest["requiredOutcomes"]), "completedOutcomes": sorted(outcomes),
            "requiredCompletionPatterns": sorted(manifest["requiredCompletionPatterns"]),
            "completedPatterns": sorted(completion_patterns)}
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path,
                        default=ROOT / "scripts/semantic-storage-corpus.json")
    parser.add_argument("--case-tool", type=Path, help="defaults to the manifest profile's native tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    check_manifest(manifest)
    tool = args.case_tool or ROOT / ".lake/build/bin" / protocol.PROFILES[manifest["profile"]]["caseTool"]
    report = validate(manifest, tool.resolve(), args.fuel)
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
