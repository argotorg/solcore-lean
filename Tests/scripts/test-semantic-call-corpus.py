#!/usr/bin/env python3
"""Replay the fixed two-contract corpus through the native checked Core runtime.

Coverage comes from completed native histories and independently inspected step
ASTs. Call modes are prescribed input bits, not an executed call trace. Repeated
observations include every committed account snapshot and ordered log. No Python
storage transition, saved expected result, or EVM execution supplies an oracle.
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


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


pure = load_module("call_corpus_ast", ROOT / "Tests/scripts/test-semantic-corpus.py")
protocol = load_module("call_corpus_protocol", ROOT / "scripts/semantic-call-differential.py")
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
SCHEMA = "solcore-lean.semantic-call-corpus-manifest.v1"
VERSIONS = pure.VERSIONS + pure.MUTATION_VERSIONS + pure.LOOP_STEP_VERSIONS
FEATURES = pure.FEATURES | pure.MUTATION_FEATURES | pure.AGGREGATE_FEATURES | {"functionCall"}
INPUTS = set(range(8)) | {(1 << 256) - 1, 1 << 255}
LOG_PATTERNS = {"", "parent:1,parent:3", "parent:1,child:2,parent:3"}
BINDINGS = {"schema": "solcore-lean.call-bindings.v1", "caller": "17", "parent": "101", "child": "102"}


def strings(value, label):
    require(isinstance(value, list) and all(isinstance(item, str) for item in value)
            and len(value) == len(set(value)), f"{label} must contain unique strings")
    return set(value)


def integers(value, expected, label):
    require(isinstance(value, list) and all(type(item) is int for item in value)
            and len(value) == len(set(value)) and set(value) == expected,
            f"{label} must contain exactly {sorted(expected)}")


def transactions(rows):
    require(isinstance(rows, list) and 1 <= len(rows) <= 3, "expected one to three transactions")
    identifiers = set()
    for row in rows:
        require(isinstance(row, dict) and set(row) == {"id", "input", "value", "target", "callee"},
                "transactions require exactly symbolic roles and an input")
        identifier = row["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,64}", identifier)
                and identifier not in identifiers, "transaction IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        canonical_word(row["input"])
        require((row["value"], row["target"], row["callee"]) == ("0", "parent", "child"),
                "unexpected transaction value or contract roles")


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredInputs",
              "requiredHelperCounts", "requiredTransactionCounts", "generationRecipeRequirements",
              "requiredCallModes", "requiredOutcomes", "requiredLogPatterns", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields and manifest["schema"] == SCHEMA,
            "unexpected call corpus manifest schema or fields")
    require(manifest["profile"] == "stateful-calls", "unexpected call corpus profile")
    require(manifest["coverageKind"] == "step-core-ast-features", "call coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    features = strings(manifest["requiredFeatures"], "requiredFeatures")
    require(features and features <= FEATURES, "unsupported step feature requirement")
    require({canonical_word(value) for value in strings(manifest["requiredInputs"], "requiredInputs")} == INPUTS,
            "call corpus must require all ten fixed inputs")
    integers(manifest["requiredHelperCounts"], {1, 2, 3}, "requiredHelperCounts")
    integers(manifest["requiredTransactionCounts"], {1, 2, 3}, "requiredTransactionCounts")
    integers(manifest["requiredCallModes"], set(range(8)), "requiredCallModes")
    recipe = manifest["generationRecipeRequirements"]
    require(isinstance(recipe, dict) and set(recipe) == {"templates"}, "invalid generation recipe requirements")
    integers(recipe["templates"], {0, 1, 2, 3}, "recipe templates")
    require(strings(manifest["requiredOutcomes"], "requiredOutcomes") == {"returned", "reverted"},
            "call corpus must cover both root outcomes")
    require(strings(manifest["requiredLogPatterns"], "requiredLogPatterns") == LOG_PATTERNS,
            "call corpus must cover all three committed log patterns")
    entries = manifest["cases"]
    require(isinstance(entries, list) and entries, "call corpus must contain scenarios")
    identifiers = set()
    for entry in entries:
        require(isinstance(entry, dict), "scenario entry must be an object")
        identifier = entry.get("id")
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,64}", identifier)
                and identifier not in identifiers, "scenario IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        expected = strings(entry.get("expectedFeatures"), "expectedFeatures")
        require(expected and expected <= FEATURES, "unsupported scenario step feature")
        base = {"id", "expectedFeatures"}
        if "generation" in entry:
            require(set(entry) == base | {"generation"}, "choose generation or an imported call plan")
            generation = entry["generation"]
            require(isinstance(generation, dict) and set(generation) == {"seed", "maxProgramNodes"},
                    "invalid generation recipe")
            require(canonical_word(generation["seed"]) < 1 << 64, "seed exceeds uint64")
            nodes = generation["maxProgramNodes"]
            # Native admission remeasures both full host programs; 179 is the
            # measured fixed wrapper overhead, not the child-step budget.
            require(type(nodes) is int and 179 < nodes <= 512, "invalid combined program node budget")
        else:
            require(set(entry) == base | {"callPlan", "transactions"}, "invalid imported scenario fields")
            plan = entry["callPlan"]
            require(isinstance(plan, dict) and set(plan) == {"schema", "stepProgram"}
                    and plan["schema"] == "solcore-lean.call-plan.v1"
                    and isinstance(plan["stepProgram"], dict), "invalid checked call plan")
            transactions(entry["transactions"])
    return entries


def materialize(entry, tool, directory, fuel):
    if "generation" in entry:
        recipe = entry["generation"]
        corpus = run(tool, "generate", recipe["seed"], str(recipe["maxProgramNodes"]), "1", "1", str(fuel))
        require(corpus.get("schema") == "solcore-lean.semantic-call-corpus.v1"
                and corpus.get("status") == "complete" and corpus.get("requested") == 1
                and corpus.get("attempted") == 1 and corpus.get("excluded") == []
                and len(corpus.get("cases", [])) == 1, f"{entry['id']}: fixed generation did not complete")
        case = corpus["cases"][0]
        origin = case["provenance"]["origin"]
        require(origin.get("kind") == "call-generated" and origin.get("seed") == recipe["seed"]
                and origin.get("maxProgramNodes") == recipe["maxProgramNodes"]
                and origin.get("validationFuel") == fuel, "generated origin differs from requested recipe")
    else:
        plan, txs = directory / "plan.json", directory / "transactions.json"
        plan.write_text(json.dumps(entry["callPlan"]))
        txs.write_text(json.dumps(entry["transactions"]))
        case = run(tool, "emit", str(plan), str(txs), str(fuel))
        require(case.get("callPlan") == entry["callPlan"] and case.get("transactions") == entry["transactions"],
                "emission changed the plan or stable transaction identities")
    protocol.validate_case(case)
    require(case.get("executionFuel") == fuel and "directCore" not in case,
            "case must record its execution budget without saved execution results")
    return case


def step_parts(case):
    step = case["callPlan"]["stepProgram"]
    require(step.get("schema") == "solcore-semantic-core" and step.get("dataDefinitions") == []
            and step.get("resultType") == {"tag": "function", "parameter": "word", "result": "word"},
            "call step must be a closed Word function DAG")
    return pure.function_parts(step["body"])


def log_pattern(rows):
    roles = {BINDINGS[role]: role for role in ("parent", "child")}
    labels = []
    for row in rows:
        require(row["address"] in roles and len(row["topics"]) == 1
                and len(protocol.common.hex_bytes(row["data"], "log data")) == 32,
                "committed log must belong to a contract and contain one topic and one Word")
        labels.append(roles[row["address"]] + ":" + row["topics"][0])
    return ",".join(labels)


def complete_history(history, case, fuel):
    require(history.get("bindings") == BINDINGS and history.get("fuelPerTransaction") == fuel,
            "native observation used different bindings or fuel")
    normalized = protocol.normalize_history(history, case, BINDINGS)
    require(normalized["initialAccounts"] == protocol.initial_accounts(BINDINGS), "initial account fixture changed")
    require(normalized["status"] == "complete" and not normalized["unexecuted"]
            and not normalized["unobserved"] and history.get("stoppedAt") is None,
            "native history did not complete within its budget")
    prior = normalized["initialAccounts"]
    for row, tx in zip(normalized["transactions"], case["transactions"]):
        require(row["status"] == ("reverted" if int(tx["input"]) & 2 else "returned"),
                "root completion differs from the fixed protocol")
        require(len(protocol.common.hex_bytes(row["output"], "output")) == 32,
                "root completion must retain exactly one Word of output")
        pattern = log_pattern(row["logs"])
        if row["status"] == "reverted":
            require(row["committedAccounts"] == prior and not row["logs"],
                    "root revert changed committed accounts or retained logs")
        else:
            expected = "parent:1,parent:3" if int(tx["input"]) & 1 else "parent:1,child:2,parent:3"
            require(pattern == expected, "committed child/parent log order differs from the fixed protocol")
        require(sum(int(account["balance"]) for account in row["committedAccounts"]) == 8,
                "closed two-contract transfers changed the total contract balance")
        prior = row["committedAccounts"]
    return normalized


def policy_checks(manifest, case, history, tool, directory, fuel):
    """Reject altered transport evidence; these copies are not execution oracles."""
    count = 0

    def rejects(action, label):
        nonlocal count
        try:
            action()
        except (ValueError, protocol.Finding):
            count += 1
        else:
            raise ValueError("negative check accepted " + label)

    def change_reverted_storage(value):
        # Keep the final snapshot internally consistent so only the missing
        # rollback, rather than a malformed history envelope, rejects this.
        value["transactions"][-1]["committedAccounts"][1]["storage"][0]["value"] = "99"
        value["finalAccounts"] = copy.deepcopy(value["transactions"][-1]["committedAccounts"])

    for key, value in (("profile", "stateful-storage"), ("requiredOutcomes", ["returned"]),
                       ("requiredLogPatterns", [""]), ("requiredCallModes", list(range(7))),
                       ("requiredInputs", ["0"]), ("coverageKind", "executed-opcodes")):
        changed = copy.deepcopy(manifest)
        changed[key] = value
        rejects(lambda: check_manifest(changed), key)
    changed = copy.deepcopy(manifest)
    changed["cases"][0]["generation"] = {"seed": "1", "maxProgramNodes": 243}
    rejects(lambda: check_manifest(changed), "both imported and generated")
    for budget in (True, 179, 513):
        changed = copy.deepcopy(manifest)
        generated = next(entry for entry in changed["cases"] if "generation" in entry)
        generated["generation"]["maxProgramNodes"] = budget
        rejects(lambda: check_manifest(changed), "invalid combined budget")
    for label, mutate in (
        ("bindings", lambda value: value["bindings"].update(child="103")),
        ("root outcome", lambda value: value["transactions"][0].update(status="reverted")),
        ("missing child log", lambda value: value["transactions"][0]["logs"].pop(1)),
        ("log order", lambda value: value["transactions"][0]["logs"].reverse()),
        ("log payload length", lambda value: value["transactions"][0]["logs"][0].update(data="0x")),
        ("output length", lambda value: value["transactions"][0].update(output="0x")),
        ("transaction order", lambda value: value["transactions"][0].update(index=1)),
        ("revert account rollback", change_reverted_storage),
        ("revert log rollback", lambda value: value["transactions"][-1].update(logs=value["transactions"][0]["logs"])),
    ):
        changed = copy.deepcopy(history)
        mutate(changed)
        rejects(lambda: complete_history(changed, case, fuel), label)
    case_path, bindings_path = directory / "negative-case.json", directory / "bindings.json"
    for label, mutate in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("parent Core", lambda value: value["programs"]["parent"].update(body={"tag": "word", "value": "0x0"})),
        ("constructor funding", lambda value: value["contracts"]["parent"].update(constructorValue="0")),
        ("profile version", lambda value: value["provenance"].update(profileVersion="different-profile")),
    ):
        changed = copy.deepcopy(case)
        mutate(changed)
        case_path.write_text(json.dumps(changed))
        result = subprocess.run([str(tool), "replay", str(case_path), str(fuel)], cwd=ROOT,
                                text=True, capture_output=True, timeout=30, check=False)
        require(result.returncode != 0, "native replay accepted changed " + label)
        count += 1
    # An imported plan can be replayed at a lower budget without changing its
    # checked programs. Actual exhaustion must never contribute coverage.
    case_path.write_text(json.dumps(case))
    lower = run(tool, "replay", str(case_path), "1")
    require(lower["programs"] == case["programs"] and lower["source"] == case["source"]
            and lower["executionFuel"] == 1, "lower budget changed the checked implementation")
    case_path.write_text(json.dumps(lower))
    incomplete = run(tool, "observe", str(case_path), str(bindings_path), "1")
    normalized = protocol.normalize_history(incomplete, lower, BINDINGS)
    require(normalized["status"] == "incomplete" and len(normalized["transactions"]) == 1
            and normalized["transactions"][0]["status"] == "out-of-fuel"
            and incomplete["transactions"][0]["logs"] is None
            and normalized["finalAccounts"] == normalized["initialAccounts"]
            and incomplete["stoppedAt"] == lower["transactions"][0]["id"],
            "actual low-fuel call did not retain an incomplete committed prefix")
    rejects(lambda: complete_history(incomplete, lower, 1), "resource history as completed coverage")
    return count


def validate(manifest, tool, fuel):
    require(type(fuel) is int and 0 < fuel <= 10_000_000, "invalid native execution fuel")
    entries = check_manifest(manifest)
    covered, inputs, helpers_seen, lengths, templates = set(), set(), set(), set(), set()
    modes, outcomes, patterns, plans = set(), set(), set(), {}
    completed = 0
    with tempfile.TemporaryDirectory(prefix="semantic-call-corpus-") as name:
        directory = Path(name)
        bindings = directory / "bindings.json"
        bindings.write_text(json.dumps(BINDINGS))
        samples = []
        for entry in entries:
            case = materialize(entry, tool, directory, fuel)
            require(case == materialize(entry, tool, directory, fuel), f"{entry['id']}: nondeterministic materialization")
            for version in VERSIONS:
                require(case["provenance"][version] == manifest[version], f"{entry['id']}: {version} changed")
            helpers, body = step_parts(case)
            features, _ = pure.ast_coverage(helpers + [body], function_calls=True, mutable_cells=True, aggregates=True)
            require(features == set(case["provenance"]["features"]) == set(entry["expectedFeatures"]),
                    f"{entry['id']}: features differ from the independent step AST inspection")
            path = directory / "case.json"
            path.write_text(json.dumps(case))
            before = run(tool, "observe", str(path), str(bindings), str(fuel))
            observed = complete_history(before, case, fuel)
            replayed = run(tool, "replay", str(path), str(fuel))
            require(replayed == case, f"{entry['id']}: canonical native replay changed the case")
            path.write_text(json.dumps(replayed))
            after = run(tool, "observe", str(path), str(bindings), str(fuel))
            complete_history(after, replayed, fuel)
            require(after == before, f"{entry['id']}: replay changed a committed account or log prefix")
            key = json.dumps(case["callPlan"], sort_keys=True, separators=(",", ":"))
            implementation = (case["programs"], case["source"], case["contracts"])
            require(plans.setdefault(key, implementation) == implementation,
                    f"{entry['id']}: identical plan emitted transaction-dependent programs or source")
            if "generation" in entry:
                origin = case["provenance"]["origin"]["stepOrigin"]
                metadata = origin.get("helpers")
                require(origin.get("kind") == "aggregate-generated" and isinstance(metadata, list)
                        and origin.get("helperCount") == len(helpers) == len(metadata),
                        "replayed recipe helper count differs from declarations")
                for helper in metadata:
                    template = helper.get("template")
                    require(type(template) is int and template in {0, 1, 2, 3}, "unknown step template")
                    templates.add(template)
            elif [tx["input"] for tx in case["transactions"]] == ["0", "1", "2"]:
                samples.append((case, before))
            # Coverage is updated only after both complete actual observations.
            covered.update(features)
            inputs.update(canonical_word(tx["input"]) for tx in case["transactions"])
            modes.update(int(tx["input"]) & 7 for tx in case["transactions"])
            helpers_seen.add(len(helpers))
            lengths.add(len(case["transactions"]))
            outcomes.update(row["status"] for row in observed["transactions"])
            patterns.update(log_pattern(row["logs"]) for row in observed["transactions"])
            completed += len(case["transactions"])
        require(covered == set(manifest["requiredFeatures"]), "lost exact step AST feature union")
        require(INPUTS <= inputs and helpers_seen == {1, 2, 3} and lengths == {1, 2, 3}, "lost completed input/helper/sequence coverage")
        require(templates == {0, 1, 2, 3} and modes == set(range(8)), "lost recipe or prescribed input mode coverage")
        require(outcomes == {"returned", "reverted"} and patterns == LOG_PATTERNS, "lost actual completion or log pattern coverage")
        require(samples, "missing imported 0/1/2 policy fixture")
        checks = policy_checks(manifest, *samples[0], tool, directory, fuel)
    return {"status": "passed", "profile": "stateful-calls", "scenarios": len(entries),
            "completedTransactions": completed, "planGroups": len(plans),
            "coverageKind": "step-core-ast-features", "requiredFeatures": len(covered),
            "completedInputs": [str(value) for value in sorted(inputs)],
            "completedHelperCounts": sorted(helpers_seen), "completedTransactionCounts": sorted(lengths),
            "generationRecipe": {"classification": "replayed-generator-metadata", "templates": sorted(templates)},
            "callModes": {"classification": "prescribed-input-bits-not-trace", "values": sorted(modes)},
            "historyCoverage": {"classification": "completed-native-histories", "outcomes": sorted(outcomes),
                                "logPatterns": sorted(patterns)},
            "bindings": BINDINGS, "nativeHistoriesReplayed": len(entries), "policyChecks": checks,
            "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path, default=ROOT / "scripts/semantic-call-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-call-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
