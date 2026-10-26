#!/usr/bin/env python3
"""Bounded stateful three-way campaigns with stable-transaction reduction.

Normal execution never changes observations. The explicit test adapter changes
one copied observation only after the complete actual history matches. Original
reports stay immutable and replayable; synthetic findings have their own branch.
"""
from __future__ import annotations
import argparse
import copy
import importlib.util
import json
import math
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
from types import SimpleNamespace

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

adapter = load("storage_differential", ROOT / "scripts/semantic-storage-differential.py")
legacy = load("campaign_utilities", ROOT / "scripts/semantic-campaign.py")
common = adapter.common
save_json, directory_bytes, compact_report = legacy.save_json, legacy.directory_bytes, legacy.compact_report
PATHS = adapter.PATHS
SCHEMA = "solcore-lean.semantic-storage-campaign.v1"
MANIFEST_SCHEMA = "solcore-lean.semantic-storage-corpus-manifest.v1"
CORPUS_SCHEMA = "solcore-lean.semantic-storage-corpus.v1"
ANALYSIS_SCHEMA = "solcore-lean.semantic-storage-analysis.v1"
TEST_ADAPTER = "xor-one-history-word-after-matched-execution-v1"
RESOURCE = "inconclusive-resource"
SHRINKABLE = legacy.SHRINKABLE
VERSIONS = ("generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
            "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion")
DIMENSIONS = ("Features", "Inputs", "HelperCounts", "TransactionCounts", "Templates", "Outcomes", "CompletionPatterns")
KEYED_DIMENSIONS = DIMENSIONS + ("Keys", "Aliases")
ARRAY_DIMENSIONS = DIMENSIONS + ("Lengths",)
ARRAY_LENGTHS = (0, 1, 2, 3)
NUMERIC_DIMENSIONS = ("Inputs", "Keys")
ALIASES = ("key-counter", "successor-counter", "repeated-key", "successor-key")
TEST_FIELD = re.compile(r"output|storage:(?:0|[1-9][0-9]{0,77})")


def dimensions(profile_name):
    return {"keyed": KEYED_DIMENSIONS, "array": ARRAY_DIMENSIONS}.get(adapter.PROFILES[profile_name]["abi"], DIMENSIONS)


def inputs(case):
    """Runtime Words: the ABI input, or every element of the dynamic arrays."""
    if adapter.profile(case)["abi"] == "array":
        return {value for tx in case["transactions"] for value in tx["values"]}
    return {tx["input"] for tx in case["transactions"]}


def aliases(case):
    """Static slot aliasing among keyed transactions, independent of execution."""
    keys = [int(common.word(tx["key"], "transaction key")) for tx in case["transactions"]]
    found = set()
    if int(adapter.COUNTER_SLOT) in keys:
        found.add("key-counter")
    if (int(adapter.COUNTER_SLOT) - 1) % 2**256 in keys:
        found.add("successor-counter")
    if len(set(keys)) < len(keys):
        found.add("repeated-key")
    if any((left + 1) % 2**256 == right for i, left in enumerate(keys) for j, right in enumerate(keys) if i != j):
        found.add("successor-key")
    return found


def case_hash(case):
    # Runtime inputs and sequence removals do not change the fixed contract.
    return common.digest(common.json_bytes({key: case[key] for key in ("program", "transactions")}))


def helper_count(case):
    step = case[adapter.profile(case)["planKey"]]["stepProgram"]
    if step.get("resultType") != {"tag": "function", "parameter": "word", "result": "word"} or step.get("dataDefinitions") != []:
        raise ValueError("storage step must be a closed Word function graph")
    return legacy.bound_helper_count(step.get("body"))


def recipes(case):
    origin = case["provenance"].get("origin", {})
    if origin.get("kind") != adapter.profile(case)["originKind"]:
        return set()
    step = origin.get("stepOrigin")
    if not isinstance(step, dict) or step.get("kind") != "aggregate-generated":
        raise ValueError("generated storage case lacks its aggregate step recipe")
    helpers = step.get("helpers")
    if not isinstance(helpers, list) or not 1 <= len(helpers) <= 3:
        raise ValueError("invalid storage helper recipe count")
    result = set()
    for helper in helpers:
        value = helper.get("template") if isinstance(helper, dict) else None
        if type(value) is not int or value not in range(4):
            raise ValueError("invalid aggregate template recipe")
        result.add(value)
    return result


def validate_manifest(manifest):
    if not isinstance(manifest, dict) or manifest.get("schema") != MANIFEST_SCHEMA or manifest.get("profile") not in adapter.PROFILES:
        raise ValueError("unsupported storage corpus manifest")
    selected = adapter.PROFILES[manifest["profile"]]
    if manifest.get("coverageKind") != "step-core-ast-features":
        raise ValueError("storage corpus coverage must name the step AST")
    for key in VERSIONS:
        if not isinstance(manifest.get(key), str) or not manifest[key]:
            raise ValueError(f"missing corpus {key}")
    for key in ("requiredFeatures", "requiredInputs"):
        values = manifest.get(key)
        if not isinstance(values, list) or any(not isinstance(value, str) for value in values) or len(set(values)) != len(values):
            raise ValueError(f"{key} must contain unique strings")
    for value in manifest["requiredInputs"]:
        common.word(value)
    for key in ("requiredHelperCounts", "requiredTransactionCounts"):
        values = manifest.get(key)
        if not isinstance(values, list) or any(type(v) is not int or v not in (1, 2, 3) for v in values) or len(set(values)) != len(values):
            raise ValueError(f"invalid {key}")
    requirements = manifest.get("generationRecipeRequirements")
    if not isinstance(requirements, dict) or set(requirements) != {"templates"}:
        raise ValueError("storage recipe requirements must contain templates only")
    values = requirements["templates"]
    if not isinstance(values, list) or any(type(v) is not int or v not in range(4) for v in values) or len(set(values)) != len(values):
        raise ValueError("invalid storage template requirements")
    outcomes = manifest.get("requiredOutcomes", [])
    patterns = manifest.get("requiredCompletionPatterns", [])
    if selected["rollback"]:
        if not isinstance(outcomes, list) or any(not isinstance(v, str) for v in outcomes) or sorted(outcomes) != ["returned", "reverted"]:
            raise ValueError("rollback coverage requires returned and reverted outcomes")
        if not isinstance(patterns, list) or not patterns or any(not isinstance(v, str) or
                not 1 <= len(v.split(",")) <= 3 or any(s not in outcomes for s in v.split(",")) for v in patterns) or len(set(patterns)) != len(patterns):
            raise ValueError("invalid rollback completion pattern requirements")
    elif outcomes or patterns:
        raise ValueError("completion requirements belong to the rollback profile")
    if selected["keyed"]:
        keys, kinds = manifest.get("requiredKeys"), manifest.get("requiredAliases")
        if not isinstance(keys, list) or not keys or any(not isinstance(v, str) for v in keys) or len(set(keys)) != len(keys):
            raise ValueError("keyed coverage requires unique required keys")
        for value in keys:
            common.word(value, "required key")
        if not isinstance(kinds, list) or any(v not in ALIASES for v in kinds) or len(set(kinds)) != len(kinds):
            raise ValueError("invalid keyed alias requirements")
    elif "requiredKeys" in manifest or "requiredAliases" in manifest:
        raise ValueError("key coverage belongs to the keyed storage profile")
    if selected["abi"] == "array":
        lengths = manifest.get("requiredLengths")
        if not isinstance(lengths, list) or not lengths or any(type(v) is not int or v not in ARRAY_LENGTHS for v in lengths) or len(set(lengths)) != len(lengths):
            raise ValueError("dynamic-array coverage requires unique lengths from zero to three")
    elif "requiredLengths" in manifest:
        raise ValueError("length coverage belongs to the dynamic-array profile")
    if not isinstance(manifest.get("cases"), list):
        raise ValueError("corpus cases must be an array")
    ids = set()
    for entry in manifest["cases"]:
        if not isinstance(entry, dict) or not isinstance(entry.get("id"), str) or not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", entry["id"]) or entry["id"] in ids:
            raise ValueError("corpus IDs must be unique bounded identifiers")
        ids.add(entry["id"])
        generated = "generation" in entry
        if generated == (selected["planKey"] in entry) or ("transactions" in entry) == generated:
            raise ValueError(f"corpus entry requires generation XOR {selected['planKey']}+transactions")
        if "expectedHistory" in entry and (not selected["declared"] or not isinstance(entry["expectedHistory"], list)):
            raise ValueError("independent expected histories are declared-slot transaction lists")
        if any(key in entry for key in ("program", "loopPlan", "input")):
            raise ValueError("storage corpus uses a plan and transaction sequence")
        expected = entry.get("expectedFeatures")
        if not isinstance(expected, list) or any(not isinstance(v, str) for v in expected) or len(set(expected)) != len(expected):
            raise ValueError("expectedFeatures must contain unique strings")
        if generated:
            request = entry["generation"]
            if not isinstance(request, dict) or set(request) != {"seed", "maxProgramNodes"}:
                raise ValueError("invalid storage generation request")
            seed = common.word(request["seed"], "seed")
            nodes = request["maxProgramNodes"]
            if int(seed) >= 2**64 or type(nodes) is not int or not 1 <= nodes <= 512:
                raise ValueError("storage generation request exceeds bounds")
        else:
            if not isinstance(entry[selected["planKey"]], dict) or entry[selected["planKey"]].get("schema") != selected["planSchema"]:
                raise ValueError("invalid imported storage plan")
            # Full source/host checking and canonical ABI validation are native.
            if not isinstance(entry["transactions"], list) or not 1 <= len(entry["transactions"]) <= 3:
                raise ValueError("invalid imported transaction count")
    return manifest


def analyze(report, case, path=None, transaction_id=None, field="output"):
    actual = copy.deepcopy(report.get("comparison", {"category": "adapter-error", "stage": "missing-report", "pairs": {}}))
    histories = copy.deepcopy(report.get("histories", {}))
    synthetic = False
    selected = transaction_id or case["transactions"][0]["id"]
    if path is not None:
        if path not in PATHS or not TEST_FIELD.fullmatch(field) or (
                not adapter.profile(case)["declared"] and field not in ("output", "storage:0", "storage:1")):
            raise ValueError("unknown synthetic history adapter")
        if actual.get("category") == "matched":
            if adapter.compare(histories, case).get("category") != "matched":
                raise ValueError("matched report has inconsistent actual histories")
            rows = histories[path]["transactions"]
            row = next((row for row in rows if row["id"] == selected), None)
            # Like a removed transaction, a candidate whose keys no longer
            # declare the selected slot cannot preserve the synthetic finding.
            declared = field == "output" or field[len("storage:"):] in adapter.observed_slots(case)
            if row is not None and declared:
                if field == "output":
                    value = common.hex_bytes(row["output"], "test output")
                    if len(value) != 32:
                        raise ValueError("test adapter requires a returned Word")
                    row["output"] = "0x" + f"{int.from_bytes(value, 'big') ^ 1:064x}"
                else:
                    slot = next(index for index, entry in enumerate(row["committedStorage"]) if entry["slot"] == field[len("storage:"):])
                    value = row["committedStorage"][slot]["value"]
                    row["committedStorage"][slot]["value"] = str(int(common.word(value)) ^ 1)
                    if rows[-1]["id"] == selected:
                        histories[path]["finalStorage"] = copy.deepcopy(row["committedStorage"])
                synthetic = True
    result = adapter.compare(histories, case) if synthetic else actual
    return {"schema": ANALYSIS_SCHEMA, "backend": common.resolve_sonatina_backend(None, report), "synthetic": synthetic,
            "testAdapter": {"name": TEST_ADAPTER, "path": path, "transactionId": selected, "field": field} if path else None,
            "actualComparison": actual, "comparison": result, "histories": histories}


def fingerprint(analysis):
    comparison = analysis["comparison"]
    txid = comparison.get("transactionId")
    rows = {}
    shapes = {}
    for path in PATHS:
        history = analysis.get("histories", {}).get(path, {})
        history = history if isinstance(history, dict) else {}
        transactions = history.get("transactions", [])
        transactions = transactions if isinstance(transactions, list) else []
        row = next((r for r in transactions if isinstance(r, dict) and r.get("id") == txid), {}) if txid else {}
        rows[path] = row
        output = row.get("output")
        shape = "word" if isinstance(output, str) and re.fullmatch(r"0x[0-9a-f]{64}", output) else "bytes" if output is not None else "none"
        shapes[path] = {"status": row.get("status", "not-observed"), "payload": shape}
    snapshots = []
    for path in PATHS:
        history = analysis.get("histories", {}).get(path, {})
        snapshots.append(history.get("initialStorage", []) if comparison.get("stage") == "initial-storage" and isinstance(history, dict)
                         else rows[path].get("committedStorage", []))
    keyed = keyed_analysis(analysis)
    slots = []
    if keyed:
        named = [{row.get("slot"): row.get("value") for row in snapshot if isinstance(row, dict) and isinstance(row.get("slot"), str)}
                 if isinstance(snapshot, list) else {} for snapshot in snapshots]
        names = sorted({name for values in named for name in values if re.fullmatch(r"0|[1-9][0-9]{0,77}", name)}, key=int)
        for name in names:
            values = [values.get(name) if isinstance(values.get(name), str) else None for values in named]
            if len(set(values)) > 1:
                slots.append(name)
    for index, slot in enumerate(() if keyed else adapter.SLOTS):
        values = [snapshot[index].get("value") if isinstance(snapshot, list) and len(snapshot) > index and isinstance(snapshot[index], dict) else None for snapshot in snapshots]
        values = [value if isinstance(value, str) else None for value in values]
        if len(set(values)) > 1:
            slots.append(slot)
    result = {"backend": common.resolve_sonatina_backend(None, analysis), "category": comparison.get("category"), "stage": comparison.get("stage"), "transactionId": txid,
            "disagreeingPairs": sorted(pair for pair, same in comparison.get("pairs", {}).items() if same is False),
            "fields": sorted(comparison.get("fields", [])), "storageSlots": slots,
            "pathShapes": shapes, "synthetic": analysis["synthetic"]}
    if keyed:
        result["undeclaredPaths"] = sorted(comparison.get("undeclaredPaths", []))
    return result


def keyed_analysis(analysis):
    histories = analysis.get("histories", {})
    return isinstance(histories, dict) and any(isinstance(history, dict) and history.get("schema") in
                                               (adapter.KEYED_HISTORY_SCHEMA, adapter.ARRAY_HISTORY_SCHEMA) for history in histories.values())


def same_failure(expected, analysis):
    return expected["category"] in SHRINKABLE and fingerprint(analysis) == {**expected, "backend": common.resolve_sonatina_backend(None, expected)}


def transaction_counts(histories, case):
    """Observed on any path; completed on all paths; equal returned prefixes."""
    result = {"executed": 0, "completed": 0, "matched": 0}
    try:
        values = {path: adapter.normalize_history(histories[path], case, path) for path in PATHS if path in histories}
    except (ValueError, TypeError, KeyError):
        return result
    prefix = len(values) == 3 and all(all(row["value"] == "0" for row in value["initialStorage"]) and
                                      not value.get("initialUndeclaredStorage") for value in values.values())
    for index, tx in enumerate(case["transactions"]):
        rows = [value["transactions"][index] for value in values.values() if index < len(value["transactions"])]
        result["executed"] += bool(rows)
        complete = len(rows) == 3 and all(row["status"] in ("returned", "reverted") for row in rows)
        result["completed"] += complete
        prefix = prefix and complete and all(adapter.without_containment(row) == adapter.without_containment(rows[0]) for row in rows) and not any(
            row.get("undeclaredStorage") for row in rows) and all(
            row["status"] == adapter.expected_status(case, tx) and len(common.hex_bytes(row["output"], "output")) == 32 for row in rows)
        prefix = prefix and all(row["status"] != "reverted" or row["committedStorage"] ==
            (value["transactions"][index - 1]["committedStorage"] if index else value["initialStorage"])
            for value in values.values() for row in value["transactions"][index:index + 1])
        result["matched"] += prefix
    return result


def compact_storage_report(report):
    result = compact_report(report)
    for record in result.get("evmTransactions", []):
        trace = record.get("trace", {})
        if "structLogs" in trace:
            logs = trace.pop("structLogs")
            trace.update(structLogsSha256=common.digest(common.json_bytes(logs)), structLogsCount=len(logs))
    return result


def count_outcome(counts, analysis, case):
    """A known prefix mismatch does not imply the entire scenario completed."""
    category = analysis["comparison"]["category"]
    counts["executed"] += 1
    counts["completed"] += transaction_counts(analysis["histories"], case)["completed"] == len(case["transactions"])
    bucket = {"matched": "matched", "semantic-mismatch": "mismatched", RESOURCE: "inconclusive"}.get(category, "errors")
    counts[bucket] += 1
    if category == "source-rejected":
        counts["sourceRejected"] += 1
    elif category == "compilation-rejected":
        counts["compilationRejected"] += 1
    counts["syntheticMismatches"] += analysis["synthetic"]


class Campaign:
    def __init__(self, args):
        self.args, self.started = args, time.monotonic()
        self.backend = common.resolve_sonatina_backend(getattr(args, "backend", None))
        self.profile = getattr(args, "profile", "stateful-storage")
        self.specification = adapter.PROFILES[self.profile]
        self.deadline = self.started + args.seconds
        self.reserve = min(40 * 1024 * 1024, args.disk_bytes // 4)
        self.work = args.output / ".work"
        self.work.mkdir()
        self.counter = self.shrink_attempts = 0
        self.materialized = []
        self.summary = {"schema": SCHEMA, "backend": self.backend, "status": "running", "synthetic": args.test_perturb_path is not None,
            "configuration": {"profile": self.profile, "backend": self.backend, **{key: getattr(args, key) for key in ("seed", "nodes", "cases", "attempts", "seconds", "disk_bytes", "shrink_attempts", "shrink_candidates", "direct_fuel", "core_fuel", "gas", "case_timeout")}},
            "testAdapter": {"name": TEST_ADAPTER, "path": args.test_perturb_path, "transactionId": args.test_transaction_id, "field": args.test_field} if args.test_perturb_path else None,
            "tools": {"campaignSha256": common.file_digest(Path(__file__)), "differentialSha256": common.file_digest(ROOT / "scripts/semantic-storage-differential.py"), "caseTool": str(args.case_tool)},
            "counts": {key: 0 for key in ("generated", "excluded", "generationResourceExclusions", "executed", "completed", "matched", "mismatched", "inconclusive", "errors", "sourceRejected", "compilationRejected", "syntheticMismatches")},
            "transactionCounts": {"kind": "observed on any path; completed on all three; matched ordered prefixes; shrink executions excluded", "planned": 0, "executed": 0, "completed": 0, "matched": 0, "actualMatched": 0},
            "coverage": {"kind": "step AST features and declared helpers; native-verified generation recipes; inputs and sequence lengths of fully matched scenarios; not opcode traces",
                         **{prefix + dimension: [] for prefix in ("generated", "matched", "required", "missing") for dimension in dimensions(self.profile)}},
            "cases": [], "materializedIds": [], "findings": [], "secondaryFindings": [],
            "retention": "input cases/compact receipts; complete archives for original/final/secondary findings; matched exports removed (use --case; exact archive replay unavailable)"}
        self.checkpoint()

    def checkpoint(self):
        counts, coverage = self.summary["counts"], self.summary["coverage"]
        counts["unexecuted"] = counts["generated"] - counts["executed"]
        tx = self.summary["transactionCounts"]
        tx["unobserved"] = tx["planned"] - tx["executed"]
        for dimension in dimensions(self.profile):
            coverage["missing" + dimension] = sorted(set(coverage["required" + dimension]) - set(coverage["matched" + dimension]), key=int if dimension in NUMERIC_DIMENSIONS else None)
        self.summary.update(elapsedSeconds=round(time.monotonic() - self.started, 3), retainedBytes=directory_bytes(self.args.output), shrinkAttempts=self.shrink_attempts)
        save_json(self.args.output / "summary.json", self.summary)

    def guard(self):
        if time.monotonic() >= self.deadline:
            raise common.Finding(RESOURCE, "campaign-time", "campaign time limit reached")
        if directory_bytes(self.args.output) >= self.args.disk_bytes - self.reserve:
            raise common.Finding(RESOURCE, "campaign-disk", "campaign disk limit reached; metadata reserve retained")

    def tool(self, command, stage):
        self.guard()
        args = SimpleNamespace(total_timeout=max(.001, self.deadline - time.monotonic()), timeout=self.args.case_timeout,
                               output_limit=min(4 * 1024 * 1024, self.args.disk_bytes // 64), resource_guard=self.guard)
        runner = common.Runner(args, {"processes": []})
        result = runner.process(stage, [str(self.args.case_tool), *map(str, command)])
        if result["returncode"]:
            raise common.Finding("adapter-error", stage, result["stdout"] + result["stderr"])
        value = json.loads(result["stdout"])
        if not isinstance(value, dict):
            raise ValueError("native tool must return an object")
        if "caseToolSha256" not in self.summary["tools"]:
            self.summary["tools"]["caseToolSha256"] = runner.identity(self.args.case_tool)["sha256"]
        return value

    def record_coverage(self, case, prefix, histories=None):
        values = {"Features": set(case["provenance"]["features"]), "Inputs": inputs(case),
                  "HelperCounts": {helper_count(case)}, "TransactionCounts": {len(case["transactions"])}, "Templates": recipes(case)}
        if prefix == "matched":
            if histories is None or adapter.compare(histories, case)["category"] != "matched":
                raise ValueError("coverage requires actual matched histories")
            statuses = [row["status"] for row in histories["directCore"]["transactions"]]
        else:
            statuses = [adapter.expected_status(case, tx) for tx in case["transactions"]]
        values.update(Outcomes=set(statuses), CompletionPatterns={",".join(statuses)})
        if self.specification["abi"] == "keyed":
            values.update(Keys={tx["key"] for tx in case["transactions"]}, Aliases=aliases(case))
        elif self.specification["abi"] == "array":
            values.update(Lengths={len(tx["values"]) for tx in case["transactions"]})
        for dimension, observed in values.items():
            key = prefix + dimension
            self.summary["coverage"][key] = sorted(set(self.summary["coverage"][key]) | observed, key=int if dimension in NUMERIC_DIMENSIONS else None)

    def add_case(self, case, identifier):
        adapter.validate_case(case)
        if case["schema"] != self.specification["caseSchema"]:
            raise ValueError("case differs from the selected campaign profile")
        index = len(self.materialized)
        save_json(self.args.output / "cases" / f"{index:04d}.json", case)
        self.materialized.append(case)
        self.summary["materializedIds"].append(identifier)
        self.summary["counts"]["generated"] += 1
        self.summary["transactionCounts"]["planned"] += len(case["transactions"])
        self.record_coverage(case, "generated")
        self.checkpoint()

    def prepare_cases(self):
        if self.args.case:
            self.add_case(self.tool(["replay", self.args.case, self.args.direct_fuel], "case-replay"), "saved-case")
            return
        if not self.args.corpus:
            response = self.tool(["generate", self.args.seed, self.args.nodes, self.args.cases, self.args.attempts, self.args.direct_fuel], "generation")
            if response.get("schema") != self.specification["corpusSchema"] or not isinstance(response.get("cases"), list) or len(response["cases"]) > self.args.cases:
                raise ValueError("invalid native storage corpus")
            excluded = response.get("excluded", [])
            self.summary["counts"]["excluded"] = len(excluded)
            self.summary["counts"]["generationResourceExclusions"] = legacy.generation_resource_exclusions(excluded)
            self.summary["generation"] = {key: response.get(key) for key in ("requested", "attempted", "status")}
            save_json(self.args.output / "generation.json", {key: value for key, value in response.items() if key != "cases"})
            for index, case in enumerate(response["cases"]):
                self.add_case(case, f"generated-{index}")
            return
        manifest = validate_manifest(common.read_json(self.args.corpus))
        if manifest["profile"] != self.profile:
            raise ValueError("manifest differs from the selected campaign profile")
        save_json(self.args.output / "corpus.json", manifest)
        self.summary["corpus"] = {"path": str(self.args.corpus), "sha256": common.digest(common.json_bytes(manifest))}
        for dimension in ("Features", "Inputs", "HelperCounts", "TransactionCounts"):
            self.summary["coverage"]["required" + dimension] = manifest["required" + dimension]
        self.summary["coverage"]["requiredTemplates"] = manifest["generationRecipeRequirements"]["templates"]
        for dimension in ("Outcomes", "CompletionPatterns"):
            self.summary["coverage"]["required" + dimension] = manifest.get("required" + dimension, [])
        for dimension in {"keyed": ("Keys", "Aliases"), "array": ("Lengths",)}.get(self.specification["abi"], ()):
            self.summary["coverage"]["required" + dimension] = manifest["required" + dimension]
        self.checkpoint()
        exclusions = []
        for entry in manifest["cases"][:self.args.cases]:
            self.guard()
            if "generation" in entry:
                request = entry["generation"]
                response = self.tool(["generate", request["seed"], request["maxProgramNodes"], 1, 1, self.args.direct_fuel], "corpus-generation")
                if response.get("schema") != self.specification["corpusSchema"] or not isinstance(response.get("cases"), list) or len(response["cases"]) > 1:
                    raise ValueError("invalid bounded corpus generation")
                if not response["cases"]:
                    exclusions.append({"id": entry["id"], "detail": response})
                    self.summary["counts"]["excluded"] = len(exclusions)
                    self.summary["counts"]["generationResourceExclusions"] = legacy.generation_resource_exclusions(exclusions)
                    save_json(self.args.output / "generation.json", {"excluded": exclusions})
                    self.checkpoint()
                    continue
                case = response["cases"][0]
                origin = case["provenance"]["origin"]
                if origin.get("kind") != self.specification["originKind"] or any(origin.get(key) != request[key] for key in ("seed", "maxProgramNodes")):
                    raise ValueError("native generation differs from requested seed/budget")
            else:
                plan_path, tx_path = self.work / "plan.json", self.work / "transactions.json"
                save_json(plan_path, entry[self.specification["planKey"]])
                save_json(tx_path, entry["transactions"])
                try:
                    case = self.tool(["emit", plan_path, tx_path, self.args.direct_fuel], "corpus-emission")
                finally:
                    plan_path.unlink(missing_ok=True)
                    tx_path.unlink(missing_ok=True)
            if any(case["provenance"].get(key) != manifest[key] for key in VERSIONS) or set(case["provenance"]["features"]) != set(entry["expectedFeatures"]):
                raise ValueError("native corpus features/versions differ from manifest")
            self.add_case(case, entry["id"])
        self.summary["generation"] = {"requested": self.args.cases, "attempted": min(self.args.cases, len(manifest["cases"])), "attemptUnit": "manifest scenarios", "excluded": exclusions}
        save_json(self.args.output / "generation.json", self.summary["generation"])

    def case_args(self, case_path, folder):
        left = max(.001, self.deadline - time.monotonic())
        return SimpleNamespace(case=case_path, replay=None, backend=self.backend, output=folder, case_tool=self.args.case_tool,
            core_runner=self.args.core_runner, anvil=self.args.anvil, upstream=self.args.upstream, target_dir=self.args.target_dir,
            direct_fuel=self.args.direct_fuel, core_fuel=self.args.core_fuel, gas=self.args.gas,
            timeout=min(self.args.case_timeout, left), startup_timeout=min(30, left), total_timeout=min(self.args.case_timeout, left),
            output_limit=min(4 * 1024 * 1024, self.args.disk_bytes // 64),
            artifact_limit=min(64 * 1024 * 1024, (self.args.disk_bytes - self.reserve) // 8), resource_guard=self.guard)

    def execute_case(self, case):
        self.guard()
        self.counter += 1
        folder = self.work / f"run-{self.counter:06d}"
        folder.mkdir()
        input_path = self.work / f"input-{self.counter:06d}.json"
        save_json(input_path, case)
        args = self.case_args(input_path, folder)
        report = {"schema": adapter.REPORT_SCHEMA, "backend": self.backend, "processes": [], "histories": {},
            "budgets": {key: getattr(args, key) for key in ("direct_fuel", "core_fuel", "gas", "timeout", "startup_timeout", "total_timeout", "output_limit", "artifact_limit")},
            "scope": adapter.scope(case) if self.specification["declared"] else "initially empty committed slots0/1; ordered zero-value run(uint256); no gas/balance/nonce equivalence"}
        interrupted = False
        try:
            adapter.execute(args, report)
        except common.Finding as error:
            report["comparison"] = adapter.interrupted_comparison(args, report, {"category": error.category, "stage": error.stage, "detail": error.detail, "pairs": {}})
        except (ValueError, OSError, KeyError, TypeError, common.RpcError, subprocess.SubprocessError) as error:
            report["comparison"] = adapter.interrupted_comparison(args, report, {"category": "adapter-error", "stage": "campaign-adapter", "detail": str(error), "pairs": {}})
        except KeyboardInterrupt:
            interrupted = True
            report["comparison"] = adapter.interrupted_comparison(args, report, {"category": RESOURCE, "stage": "campaign-interrupted", "pairs": {}})
            raise
        finally:
            report["artifacts"] = {p.name: common.file_digest(p) for p in folder.iterdir() if p.is_file()}
            save_json(folder / "report.json", report)
            input_path.unlink(missing_ok=True)
            if interrupted:
                destination = self.args.output / "interruptions" / folder.name
                destination.parent.mkdir(exist_ok=True)
                folder.rename(destination)
                self.summary.setdefault("interruptions", []).append(str(destination.relative_to(self.args.output)))
        analysis = analyze(report, case, self.args.test_perturb_path, self.args.test_transaction_id, self.args.test_field)
        save_json(folder / "analysis.json", analysis)
        return folder, report, analysis

    def retain_finding(self, index, folder, case, analysis):
        location = self.args.output / "findings" / ("synthetic" if analysis["synthetic"] else "real") / f"{index:04d}"
        location.mkdir(parents=True)
        original = location / "original"
        folder.rename(original)
        finding = {"caseIndex": index, "synthetic": analysis["synthetic"], "fingerprint": fingerprint(analysis),
            "originalCaseSha256": case_hash(case), "finalCaseSha256": case_hash(case),
            "originalArchive": str(original.relative_to(self.args.output)), "finalArchive": str(original.relative_to(self.args.output)),
            "history": str((location / "shrink.json").relative_to(self.args.output))}
        status = "not-shrinkable" if analysis["comparison"]["category"] not in SHRINKABLE else (
            "no-attempts" if self.args.shrink_attempts == 0 else "attempt-limit" if self.shrink_attempts >= self.args.shrink_attempts else "pending")
        save_json(location / "shrink.json", {"schema": "solcore-lean.semantic-storage-shrink.v1", "fingerprint": finding["fingerprint"], "steps": [], "status": status, "finalArchive": finding["finalArchive"]})
        self.summary["findings"].append(finding)
        self.checkpoint()
        return finding

    def shrink(self, original, finding):
        history_path = self.args.output / finding["history"]
        history = common.read_json(history_path)
        history["status"] = "running"
        current, current_path = original, self.args.output / finding["originalArchive"] / "case.json"
        seen = {case_hash(original)}
        try:
            while self.shrink_attempts < self.args.shrink_attempts:
                self.guard()
                limit = min(self.args.shrink_candidates, self.args.shrink_attempts - self.shrink_attempts)
                response = self.tool(["shrink", current_path, limit, self.args.direct_fuel], "shrink-candidates")
                candidates = response.get("cases")
                if response.get("schema") != self.specification["corpusSchema"] or not isinstance(candidates, list) or len(candidates) > limit:
                    raise ValueError("invalid native bounded shrink response")
                accepted = False
                for candidate in candidates:
                    self.guard()
                    identity = case_hash(candidate)
                    if identity in seen:
                        continue
                    seen.add(identity)
                    self.shrink_attempts += 1
                    folder, report, analysis = self.execute_case(candidate)
                    keep = same_failure(finding["fingerprint"], analysis)
                    step = {"attempt": self.shrink_attempts, "caseSha256": identity,
                        "programSha256": common.digest(common.json_bytes(candidate["program"])),
                        "actualReportSha256": common.file_digest(folder / "report.json"), "fingerprint": fingerprint(analysis),
                        "accepted": keep, "actualComparison": report.get("comparison"), "comparison": analysis["comparison"]}
                    history["steps"].append(step)
                    if keep:
                        destination = history_path.parent / "reduced"
                        previous = history_path.parent / "previous-reduced"
                        if destination.exists():
                            destination.rename(previous)
                        folder.rename(destination)
                        if previous.exists():
                            shutil.rmtree(previous)
                        current, current_path = candidate, destination / "case.json"
                        finding.update(finalCaseSha256=identity, finalArchive=str(destination.relative_to(self.args.output)))
                        accepted = True
                    elif not analysis["synthetic"] and analysis["comparison"]["category"] not in ("matched", RESOURCE):
                        # A real discovery made while shrinking a synthetic test
                        # must survive independently of the synthetic branch.
                        destination = self.args.output / "findings" / "real" / f"secondary-{self.shrink_attempts:04d}"
                        destination.parent.mkdir(parents=True, exist_ok=True)
                        folder.rename(destination)
                        step["secondaryArchive"] = str(destination.relative_to(self.args.output))
                        self.summary["secondaryFindings"].append({"archive": step["secondaryArchive"], "fingerprint": fingerprint(analysis), "caseSha256": identity,
                            "synthetic": False, "parentHistory": str(history_path.relative_to(self.args.output)), "automaticReduction": False})
                    else:
                        shutil.rmtree(folder)
                    save_json(history_path, history)
                    self.checkpoint()
                    self.guard()
                    if accepted:
                        break
                if not accepted:
                    history["status"] = "attempt-limit" if self.shrink_attempts >= self.args.shrink_attempts else "no-preserving-candidate"
                    break
            else:
                history["status"] = "attempt-limit"
        except common.Finding as error:
            history.update(status="budget-exhausted" if error.category == RESOURCE else "error", stop={"category": error.category, "stage": error.stage, "detail": error.detail})
            raise
        except KeyboardInterrupt:
            history["status"] = "interrupted"
            raise
        except (ValueError, OSError, KeyError, TypeError, subprocess.SubprocessError) as error:
            history.update(status="error", stop={"category": "adapter-error", "detail": str(error)})
            raise
        finally:
            history.update(finalCaseSha256=finding["finalCaseSha256"], finalArchive=finding["finalArchive"])
            save_json(history_path, history)
            self.checkpoint()

    def run(self):
        self.prepare_cases()
        for index, case in enumerate(self.materialized):
            self.guard()
            if self.args.test_perturb_path and self.args.test_transaction_id and self.args.test_transaction_id not in {tx["id"] for tx in case["transactions"]}:
                raise ValueError("selected synthetic transaction ID is absent from the original scenario")
            if self.args.test_perturb_path and self.args.test_field != "output" and self.args.test_field[len("storage:"):] not in adapter.observed_slots(case):
                raise ValueError("selected synthetic slot is absent from the original scenario")
            folder, report, analysis = self.execute_case(case)
            category = analysis["comparison"]["category"]
            count_outcome(self.summary["counts"], analysis, case)
            for key, value in transaction_counts(analysis["histories"], case).items():
                self.summary["transactionCounts"][key] += value
            self.summary["transactionCounts"]["actualMatched"] += transaction_counts(report.get("histories", {}), case)["matched"]
            if category == "matched":
                self.record_coverage(case, "matched", report.get("histories"))
            save_json(self.args.output / "results" / f"{index:04d}.json", {"actualReport": compact_storage_report(report), "analysis": analysis})
            self.summary["cases"].append({"index": index, "id": self.summary["materializedIds"][index],
                "case": f"cases/{index:04d}.json", "result": f"results/{index:04d}.json", "caseSha256": case_hash(case),
                "category": category, "synthetic": analysis["synthetic"], "fingerprint": fingerprint(analysis)})
            if category not in ("matched", RESOURCE):
                finding = self.retain_finding(index, folder, case, analysis)
                if category in SHRINKABLE and self.shrink_attempts < self.args.shrink_attempts:
                    self.shrink(case, finding)
            else:
                shutil.rmtree(folder)
            self.checkpoint()
            print(json.dumps({"scenario": index, "category": category, "synthetic": analysis["synthetic"]}), flush=True)
        self.summary["status"] = "complete" if len(self.materialized) == self.args.cases else "generation-exhausted"


def missing_coverage(summary):
    return any(values for key, values in summary["coverage"].items() if key.startswith("missing"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--backend", choices=common.SONATINA_BACKENDS, default="sonatina-o0")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--corpus", type=Path)
    selection.add_argument("--case", type=Path)
    parser.add_argument("--profile", choices=tuple(adapter.PROFILES))
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--nodes", type=int, default=384)
    parser.add_argument("--cases", type=int)
    parser.add_argument("--attempts", type=int, default=256)
    parser.add_argument("--seconds", type=float, default=300)
    parser.add_argument("--disk-bytes", type=int, default=256 * 1024 * 1024)
    parser.add_argument("--shrink-attempts", type=int, default=32)
    parser.add_argument("--shrink-candidates", type=int, default=64)
    parser.add_argument("--case-timeout", type=float, default=90)
    parser.add_argument("--direct-fuel", type=int, default=1000000)
    parser.add_argument("--core-fuel", type=int, default=10000000)
    parser.add_argument("--gas", type=int, default=10000000)
    parser.add_argument("--case-tool", type=Path)
    parser.add_argument("--core-runner", type=Path, help="default: the profile's imported-Hull scenario runner")
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--test-perturb-path", choices=PATHS)
    parser.add_argument("--test-transaction-id")
    parser.add_argument("--test-field", default="output", help="output or storage:SLOT, an observed decimal slot")
    args = parser.parse_args()
    try:
        selected_profile = args.profile
        if args.corpus:
            manifest = validate_manifest(common.read_json(args.corpus))
            if selected_profile is not None and selected_profile != manifest["profile"]:
                raise ValueError("explicit profile differs from corpus")
            selected_profile = manifest["profile"]
        if args.case:
            case = common.read_json(args.case)
            adapter.validate_case(case)
            case_profile = next(name for name, specification in adapter.PROFILES.items() if case["schema"] == specification["caseSchema"])
            if selected_profile is not None and selected_profile != case_profile:
                raise ValueError("explicit profile differs from saved case")
            selected_profile = case_profile
        args.profile = selected_profile or "stateful-storage"
        if args.case_tool is None:
            args.case_tool = ROOT / ".lake/build/bin" / adapter.PROFILES[args.profile]["caseTool"]
        if args.core_runner is None:
            args.core_runner = ROOT / ".lake/build/bin" / adapter.PROFILES[args.profile]["coreRunner"]
        if args.cases is None:
            args.cases = 1 if args.case else len(common.read_json(args.corpus)["cases"]) if args.corpus else 10
    except (ValueError, OSError, KeyError, TypeError, common.Finding) as error:
        parser.error(str(error))
    if args.case and args.cases != 1:
        parser.error("--case requires --cases 1")
    if args.test_transaction_id and (not args.test_perturb_path or not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", args.test_transaction_id)):
        parser.error("test transaction ID requires the explicit adapter and a valid ID")
    if args.test_field != "output" and not args.test_perturb_path:
        parser.error("test field requires the explicit synthetic adapter")
    if not TEST_FIELD.fullmatch(args.test_field) or (not adapter.PROFILES[args.profile]["declared"] and args.test_field not in ("output", "storage:0", "storage:1")):
        parser.error("test field must be output or storage:SLOT for an observed slot")
    limits = {"seed": (0, 2**64 - 1), "nodes": (1, 512), "cases": (1, 1024), "attempts": (0, 10000),
        "seconds": (.001, 86400), "disk_bytes": (16 * 1024 * 1024, 10**10), "shrink_attempts": (0, 10000),
        "shrink_candidates": (1, 4096), "case_timeout": (.001, 3600), "direct_fuel": (1, 10000000),
        "core_fuel": (1, 1000000000), "gas": (1, 1000000000)}
    for key, (lower, upper) in limits.items():
        if not math.isfinite(getattr(args, key)) or not lower <= getattr(args, key) <= upper:
            parser.error(f"{key} must be between {lower} and {upper}")
    for key in ("output", "case_tool", "core_runner", "anvil", "upstream", "target_dir", "case", "corpus"):
        if getattr(args, key) is not None:
            setattr(args, key, getattr(args, key).resolve())
    args.output.mkdir(parents=True, exist_ok=False)
    campaign = Campaign(args)
    previous = signal.getsignal(signal.SIGTERM)
    def interrupted(_signal, _frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    try:
        campaign.run()
    except common.Finding as error:
        campaign.summary.update(status="budget-exhausted" if error.category == RESOURCE else "error", stop={"category": error.category, "stage": error.stage, "detail": error.detail})
    except KeyboardInterrupt:
        campaign.summary["status"] = "interrupted"
    except (ValueError, OSError, KeyError, TypeError, subprocess.SubprocessError) as error:
        campaign.summary.update(status="error", stop={"category": "adapter-error", "detail": str(error)})
    finally:
        try:
            shutil.rmtree(campaign.work, ignore_errors=True)
            campaign.checkpoint()
            if campaign.summary["status"] == "complete" and missing_coverage(campaign.summary):
                campaign.summary["status"] = "coverage-incomplete"
                campaign.checkpoint()
        finally:
            signal.signal(signal.SIGTERM, previous)
    print(json.dumps({"status": campaign.summary["status"], "synthetic": campaign.summary["synthetic"], "counts": campaign.summary["counts"],
                      "transactionCounts": campaign.summary["transactionCounts"], "summary": str(args.output / "summary.json")}))
    return 0 if campaign.summary["status"] == "complete" and campaign.summary["counts"]["matched"] == args.cases and not missing_coverage(campaign.summary) else 1

if __name__ == "__main__":
    raise SystemExit(main())
