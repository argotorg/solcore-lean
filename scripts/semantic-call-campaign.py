#!/usr/bin/env python3
"""Bounded parent/child campaigns with stable-transaction account/log reduction.

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

adapter = load("call_differential", ROOT / "scripts/semantic-call-differential.py")
legacy = load("campaign_utilities", ROOT / "scripts/semantic-campaign.py")
common = adapter.common
save_json, directory_bytes, compact_report = legacy.save_json, legacy.directory_bytes, legacy.compact_report
PATHS = adapter.PATHS
SCHEMA = "solcore-lean.semantic-call-campaign.v1"
MANIFEST_SCHEMA = "solcore-lean.semantic-call-corpus-manifest.v1"
CORPUS_SCHEMA = "solcore-lean.semantic-call-corpus.v1"
ANALYSIS_SCHEMA = "solcore-lean.semantic-call-analysis.v2"
TEST_ADAPTER = "xor-one-history-word-after-matched-execution-v1"
RESOURCE = "inconclusive-resource"
SHRINKABLE = legacy.SHRINKABLE
VERSIONS = ("generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
            "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion")
DIMENSIONS = ("Features", "Inputs", "HelperCounts", "TransactionCounts", "Templates", "CallModes", "Outcomes", "LogPatterns")
# Call values, forwarded amounts, the amounts a child revert keeps with the
# parent and the call values a root revert returns to the sender.
VALUE_DIMENSIONS = ("Values", "ForwardedValues", "RefundedForwards", "RevertedValues")
FORWARD_DIMENSIONS = DIMENSIONS[:-1] + VALUE_DIMENSIONS
NUMERIC_DIMENSIONS = ("Inputs",) + VALUE_DIMENSIONS
TEST_FIELDS = ("output", "parent:balance", "child:balance", "parent:storage:0", "parent:storage:1", "child:storage:0", "child:storage:1", "logs:data",
               "parent:stray", "child:stray")
# A `ROLE:stray` field XORs one into the implicit zero Word of this undeclared
# slot in one path's whole committed storage of that contract.
STRAY_SLOT = str(2**256 - 2)
LOG_PATTERNS = ("", "parent:1,parent:3", "parent:1,child:2,parent:3")
FORWARD_CORPUS_SCHEMA = "solcore-lean.semantic-forward-corpus.v1"
# Profile rules; the adapter selects schemas, programs and protocols by case schema.
PROFILES = {
    "stateful-calls": {"dimensions": DIMENSIONS, "modeMask": 7, "corpusSchema": CORPUS_SCHEMA, "originKind": "call-generated",
        "scope": "one child call; fixed parent8/child0; committed slots0/1, both contracts' whole committed storage, contract balances and ordered logs; zero root value; no gas/nonce or arbitrary-world equivalence"},
    "stateful-forwarded-value": {"dimensions": FORWARD_DIMENSIONS, "modeMask": 3, "corpusSchema": FORWARD_CORPUS_SCHEMA, "originKind": "forward-generated",
        "scope": "one value-forwarding child call; parent endowment 2^72/child0; committed slots0/1, both contracts' whole committed storage, contract balances and empty logs; payable root values; no sender-balance, gas/nonce or arbitrary-world equivalence"},
}


def case_hash(case):
    # Runtime inputs and sequence removals do not change the fixed contract.
    return common.digest(common.json_bytes({key: case[key] for key in ("programs", "transactions")}))


def helper_count(case):
    step = case[adapter.profile(case)["planKey"]]["stepProgram"]
    if step.get("resultType") != {"tag": "function", "parameter": "word", "result": "word"} or step.get("dataDefinitions") != []:
        raise ValueError("call step must be a closed Word function graph")
    return legacy.bound_helper_count(step.get("body"))


def recipes(case):
    origin = case["provenance"].get("origin", {})
    if origin.get("kind") != ("forward-generated" if adapter.forwarding(case) else "call-generated"):
        return set()
    step = origin.get("stepOrigin")
    if not isinstance(step, dict) or step.get("kind") != "aggregate-generated":
        raise ValueError("generated call case lacks its aggregate step recipe")
    helpers = step.get("helpers")
    if not isinstance(helpers, list) or not 1 <= len(helpers) <= 3:
        raise ValueError("invalid call helper recipe count")
    result = set()
    for helper in helpers:
        value = helper.get("template") if isinstance(helper, dict) else None
        if type(value) is not int or value not in range(4):
            raise ValueError("invalid aggregate template recipe")
        result.add(value)
    return result


def value_coverage(case, statuses):
    """Call values and amounts, the amounts child reverts kept with a committed
    parent, and the call values root reverts returned to the sender."""
    transactions = case["transactions"]
    return {"Values": {tx["value"] for tx in transactions}, "ForwardedValues": {tx["amount"] for tx in transactions},
            "RefundedForwards": {tx["amount"] for tx, status in zip(transactions, statuses) if status == "returned" and int(tx["input"]) & 1},
            "RevertedValues": {tx["value"] for tx, status in zip(transactions, statuses) if status == "reverted"}}


def validate_manifest(manifest):
    if not isinstance(manifest, dict) or manifest.get("schema") != MANIFEST_SCHEMA or manifest.get("profile") not in PROFILES:
        raise ValueError("unsupported call corpus manifest")
    forwards = manifest["profile"] == "stateful-forwarded-value"
    plan_key, plan_schema = ("forwardPlan", "solcore-lean.forward-plan.v1") if forwards else ("callPlan", "solcore-lean.call-plan.v1")
    if manifest.get("coverageKind") != "step-core-ast-features":
        raise ValueError("call corpus coverage must name the step AST")
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
        raise ValueError("call recipe requirements must contain templates only")
    values = requirements["templates"]
    if not isinstance(values, list) or any(type(v) is not int or v not in range(4) for v in values) or len(set(values)) != len(values):
        raise ValueError("invalid call template requirements")
    modes = manifest.get("requiredCallModes")
    if not isinstance(modes, list) or any(type(v) is not int or v not in range(PROFILES[manifest["profile"]]["modeMask"] + 1) for v in modes) or len(set(modes)) != len(modes):
        raise ValueError("requiredCallModes must name unique prescribed input-bit combinations")
    outcomes = manifest.get("requiredOutcomes")
    if not isinstance(outcomes, list) or any(not isinstance(v, str) for v in outcomes) or sorted(outcomes) != ["returned", "reverted"]:
        raise ValueError("call coverage requires returned and reverted root outcomes")
    if forwards:
        if "requiredLogPatterns" in manifest:
            raise ValueError("the forwarded-value profile commits no logs")
        for dimension in VALUE_DIMENSIONS:
            values = manifest.get("required" + dimension)
            if not isinstance(values, list) or not values or any(not isinstance(v, str) for v in values) or len(set(values)) != len(values):
                raise ValueError(f"forwarded-value coverage requires unique required{dimension}")
            for value in values:
                if int(common.word(value, "required " + dimension)) > adapter.MAX_VALUE:
                    raise ValueError(f"required{dimension} exceed 2^70")
    else:
        if any("required" + dimension in manifest for dimension in VALUE_DIMENSIONS):
            raise ValueError("value coverage belongs to the forwarded-value profile")
        patterns = manifest.get("requiredLogPatterns")
        if not isinstance(patterns, list) or any(not isinstance(v, str) or v not in LOG_PATTERNS for v in patterns) or len(set(patterns)) != len(patterns):
            raise ValueError("invalid committed log pattern requirements")
    if not isinstance(manifest.get("cases"), list):
        raise ValueError("corpus cases must be an array")
    ids = set()
    for entry in manifest["cases"]:
        if not isinstance(entry, dict) or not isinstance(entry.get("id"), str) or not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", entry["id"]) or entry["id"] in ids:
            raise ValueError("corpus IDs must be unique bounded identifiers")
        ids.add(entry["id"])
        generated = "generation" in entry
        if generated == (plan_key in entry) or ("transactions" in entry) == generated:
            raise ValueError(f"corpus entry requires generation XOR {plan_key}+transactions")
        if any(key in entry for key in ("program", "programs", "storagePlan", "loopPlan", "input",
                                        "callPlan" if forwards else "forwardPlan")):
            raise ValueError("call corpus uses a plan and transaction sequence")
        expected = entry.get("expectedFeatures")
        if not isinstance(expected, list) or any(not isinstance(v, str) for v in expected) or len(set(expected)) != len(expected):
            raise ValueError("expectedFeatures must contain unique strings")
        if generated:
            request = entry["generation"]
            if not isinstance(request, dict) or set(request) != {"seed", "maxProgramNodes"}:
                raise ValueError("invalid call generation request")
            seed = common.word(request["seed"], "seed")
            nodes = request["maxProgramNodes"]
            if int(seed) >= 2**64 or type(nodes) is not int or not 1 <= nodes <= 512:
                raise ValueError("call generation request exceeds bounds")
        else:
            if not isinstance(entry[plan_key], dict) or entry[plan_key].get("schema") != plan_schema:
                raise ValueError("invalid imported call plan")
            # Full source/host checking and canonical ABI validation are native.
            if not isinstance(entry["transactions"], list) or not 1 <= len(entry["transactions"]) <= 3:
                raise ValueError("invalid imported transaction count")
    return manifest


def analyze(report, case, path=None, transaction_id=None, field="output"):
    actual = copy.deepcopy(report.get("comparison", {"category": "adapter-error", "stage": "missing-report", "pairs": {}}))
    histories, bindings = copy.deepcopy(report.get("histories", {})), copy.deepcopy(report.get("bindings"))
    synthetic = False
    selected = transaction_id or case["transactions"][0]["id"]
    if path is not None:
        if path not in PATHS or field not in TEST_FIELDS:
            raise ValueError("unknown synthetic call adapter")
        if actual.get("category") == "matched":
            if adapter.compare(histories, case, bindings).get("category") != "matched":
                raise ValueError("matched report has inconsistent actual histories")
            rows = histories[path]["transactions"]
            row = next((row for row in rows if row["id"] == selected), None)
            if row is not None and field.endswith(":stray"):
                entries = next(account for account in row["accountStorage"] if account["role"] == field.split(":")[0])["storage"]
                # A path that already holds the slot cannot keep a synthetic stray write.
                if all(entry["slot"] != STRAY_SLOT for entry in entries):
                    entries.append({"slot": STRAY_SLOT, "value": "1"})
                    entries.sort(key=lambda entry: int(entry["slot"]))
                    if rows[-1]["id"] == selected:
                        histories[path]["finalAccountStorage"] = copy.deepcopy(row["accountStorage"])
                    synthetic = True
            elif row is not None and (field != "logs:data" or row["logs"]):
                if field == "output" or field == "logs:data":
                    container, key = (row, "output") if field == "output" else (row["logs"][0], "data")
                    value = common.hex_bytes(container[key], "test payload")
                    if len(value) != 32:
                        raise ValueError("test adapter requires a Word payload")
                    container[key] = "0x" + f"{int.from_bytes(value, 'big') ^ 1:064x}"
                else:
                    role, *parts = field.split(":")
                    account = next(account for account in row["committedAccounts"] if account["role"] == role)
                    container, key = (account, "balance") if parts == ["balance"] else (account["storage"][int(parts[1])], "value")
                    container[key] = str(int(common.word(container[key])) ^ 1)
                    if rows[-1]["id"] == selected:
                        histories[path]["finalAccounts"] = copy.deepcopy(row["committedAccounts"])
                synthetic = True
    result = adapter.compare(histories, case, bindings) if synthetic else actual
    return {"schema": ANALYSIS_SCHEMA, "backend": common.resolve_sonatina_backend(None, report), "synthetic": synthetic, "bindings": bindings,
            "testAdapter": {"name": TEST_ADAPTER, "path": path, "transactionId": selected, "field": field,
                            "applied": synthetic} if path else None,
            "actualComparison": actual, "comparison": result, "histories": histories}


def payload_shape(value):
    if isinstance(value, str) and re.fullmatch(r"0x[0-9a-f]{64}", value):
        return "word"
    return "bytes" if value is not None else "none"


def log_shape(events, bindings):
    if not isinstance(events, list):
        return None
    def role(address):
        return next((role for role in adapter.ROLES if isinstance(bindings, dict) and bindings.get(role) == address), "other")
    result = []
    for event in events:
        if not isinstance(event, dict):
            result.append({"malformed": True})
            continue
        topics = event.get("topics")
        result.append({"role": role(event.get("address")),
                       "topics": [topic if topic in ("1", "2", "3") else "other" for topic in topics] if isinstance(topics, list) else None,
                       "data": payload_shape(event.get("data"))})
    return result


def fingerprint(analysis):
    comparison, bindings = analysis["comparison"], analysis.get("bindings")
    txid = comparison.get("transactionId")
    rows, histories, shapes = {}, {}, {}
    for path in PATHS:
        history = analysis.get("histories", {}).get(path, {})
        history = history if isinstance(history, dict) else {}
        histories[path] = history
        transactions = history.get("transactions", [])
        transactions = transactions if isinstance(transactions, list) else []
        row = next((r for r in transactions if isinstance(r, dict) and r.get("id") == txid), {}) if txid else {}
        rows[path] = row
        shapes[path] = {"status": row.get("status", "not-observed"), "payload": payload_shape(row.get("output"))}
    def snapshot(path):
        return histories[path].get("initialAccounts", []) if comparison.get("stage") == "initial-accounts" else rows[path].get("committedAccounts", [])
    def account_value(snapshot, role, field):
        account = next((value for value in snapshot if isinstance(value, dict) and value.get("role") == role), {}) if isinstance(snapshot, list) else {}
        if field == "balance":
            return account.get("balance")
        storage = account.get("storage", [])
        return next((slot.get("value") for slot in storage if isinstance(slot, dict) and slot.get("slot") == field), None) if isinstance(storage, list) else None
    forwards = any(isinstance(history, dict) and history.get("schema") == adapter.FORWARD_HISTORY_SCHEMA for history in histories.values())
    differences = set()
    for role in adapter.ROLES:
        for field in ("balance", *adapter.SLOTS):
            values = [account_value(snapshot(path), role, field) for path in PATHS]
            changed = len({json.dumps(value, sort_keys=True) for value in values}) > 1
            for path in PATHS:
                if comparison.get("stage") == "initial-accounts" and isinstance(bindings, dict):
                    try:
                        adapter.validate_bindings(bindings)
                        expected = adapter.initial_accounts(bindings, forwards)
                    except ValueError:
                        continue
                elif rows[path].get("status") == "reverted":
                    transactions = histories[path].get("transactions", [])
                    transactions = transactions if isinstance(transactions, list) else []
                    position = next((i for i, row in enumerate(transactions) if isinstance(row, dict) and row.get("id") == txid), 0)
                    previous = transactions[position - 1] if position else None
                    expected = previous.get("committedAccounts", []) if isinstance(previous, dict) else histories[path].get("initialAccounts", [])
                else:
                    continue
                changed = changed or account_value(snapshot(path), role, field) != account_value(expected, role, field)
            if changed:
                differences.add(role + (":balance" if field == "balance" else ":storage:" + field))
    events = {path: rows[path].get("logs") for path in PATHS}
    log_differences = []
    lengths = [len(value) if isinstance(value, list) else None for value in events.values()]
    if len(set(lengths)) > 1:
        log_differences.append("length")
    for index in range(max((length for length in lengths if length is not None), default=0)):
        for field in ("address", "topics", "data"):
            values = [value[index].get(field) if isinstance(value, list) and index < len(value) and isinstance(value[index], dict) else None for value in events.values()]
            if len({json.dumps(value, sort_keys=True) for value in values}) > 1:
                log_differences.append(f"{index}:{field}")
    if any(rows[path].get("status") == "reverted" and events[path] for path in PATHS):
        log_differences.append("nonempty-after-root-revert")
    return {"backend": common.resolve_sonatina_backend(None, analysis), "category": comparison.get("category"), "stage": comparison.get("stage"), "transactionId": txid,
            "disagreeingPairs": sorted(pair for pair, same in comparison.get("pairs", {}).items() if same is False),
            "fields": sorted(comparison.get("fields", [])), "accountFields": sorted(differences),
            "logFields": log_differences, "logShapes": {path: log_shape(events[path], bindings) for path in PATHS},
            "accountStorageDifferences": copy.deepcopy(comparison.get("accountStorageDifferences", [])),
            "accountStorageRollbackPaths": sorted(comparison.get("accountStorageRollbackPaths", [])),
            "pathShapes": shapes, "synthetic": analysis["synthetic"]}


def same_failure(expected, analysis):
    return expected["category"] in SHRINKABLE and fingerprint(analysis) == {**expected, "backend": common.resolve_sonatina_backend(None, expected)}


def transaction_counts(histories, case, bindings):
    """Count actual observations, terminal rows and fully matching ordered prefixes."""
    result = {"executed": 0, "completed": 0, "matched": 0}
    try:
        adapter.validate_bindings(bindings)
        values = {path: adapter.normalize_history(histories[path], case, bindings) for path in PATHS if path in histories}
    except (ValueError, TypeError, KeyError):
        return result
    prefix = len(values) == 3
    for index, _tx in enumerate(case["transactions"]):
        rows = [value["transactions"][index] for value in values.values() if index < len(value["transactions"])]
        result["executed"] += bool(rows)
        complete = len(rows) == 3 and all(row["status"] in ("returned", "reverted") for row in rows)
        result["completed"] += complete
        prefix = prefix and complete
        if prefix:
            prefix_case = {**case, "transactions": case["transactions"][:index + 1]}
            prefix_histories = {path: {"schema": adapter.profile(case)["historySchema"], "initialAccounts": value["initialAccounts"],
                "transactions": value["transactions"][:index + 1], "finalAccounts": value["transactions"][index]["committedAccounts"],
                "initialAccountStorage": value["initialAccountStorage"],
                "finalAccountStorage": value["transactions"][index]["accountStorage"],
                "status": "complete", "unexecuted": []} for path, value in values.items()}
            prefix = adapter.compare(prefix_histories, prefix_case, bindings)["category"] == "matched"
        result["matched"] += prefix
    return result


def compact_call_report(report):
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
    counts["completed"] += transaction_counts(analysis["histories"], case, analysis.get("bindings"))["completed"] == len(case["transactions"])
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
        self.profile = getattr(args, "profile", "stateful-calls")
        self.specification = PROFILES[self.profile]
        self.dimensions = self.specification["dimensions"]
        self.deadline = self.started + args.seconds
        self.reserve = min(40 * 1024 * 1024, args.disk_bytes // 4)
        self.work = args.output / ".work"
        self.work.mkdir()
        self.counter = self.shrink_attempts = 0
        self.materialized = []
        self.summary = {"schema": SCHEMA, "backend": self.backend, "status": "running", "synthetic": args.test_perturb_path is not None,
            "configuration": {"profile": self.profile, "backend": self.backend, **{key: getattr(args, key) for key in ("seed", "nodes", "cases", "attempts", "seconds", "disk_bytes", "shrink_attempts", "shrink_candidates", "direct_fuel", "core_fuel", "gas", "case_timeout")}},
            "testAdapter": {"name": TEST_ADAPTER, "path": args.test_perturb_path, "transactionId": args.test_transaction_id, "field": args.test_field} if args.test_perturb_path else None,
            "tools": {"campaignSha256": common.file_digest(Path(__file__)), "differentialSha256": common.file_digest(ROOT / "scripts/semantic-call-differential.py"), "caseTool": str(args.case_tool)},
            "counts": {key: 0 for key in ("generated", "excluded", "generationResourceExclusions", "executed", "completed", "matched", "mismatched", "inconclusive", "errors", "sourceRejected", "compilationRejected", "syntheticMismatches")},
            "transactionCounts": {"kind": "observed on any path; completed on all three; matched ordered prefixes; shrink executions excluded", "planned": 0, "executed": 0, "completed": 0, "matched": 0, "actualMatched": 0},
            "coverage": {"kind": f"step AST features and declared helpers; native-verified recipes; call modes are prescribed input&{self.specification['modeMask']}, not internal traces; outcome/log-pattern coverage only from complete actual matched scenarios",
                         **{prefix + dimension: [] for prefix in ("generated", "matched", "required", "missing") for dimension in self.dimensions}},
            "cases": [], "materializedIds": [], "findings": [], "secondaryFindings": [],
            "retention": "input cases/compact receipts; complete archives for original/final/secondary findings; matched exports removed (use --case; exact archive replay unavailable)"}
        # Random generation draws steps with G0 revision two; a corpus or a saved
        # case keeps the version it records.
        self.g0_version = getattr(args, "g0_version", None)
        if self.g0_version is None and not args.corpus and not args.case:
            self.g0_version = legacy.RANDOM_G0_VERSION
        self.summary["configuration"]["g0Version"] = self.g0_version
        # Random generation requests the longest admitted sequence; a corpus or a
        # saved case keeps its own transactions.
        self.transactions = getattr(args, "transactions", None)
        if self.transactions is None and not args.corpus and not args.case:
            self.transactions = adapter.MAX_TRANSACTIONS
        self.summary["configuration"]["transactions"] = self.transactions
        self.checkpoint()

    def checkpoint(self):
        counts, coverage = self.summary["counts"], self.summary["coverage"]
        counts["unexecuted"] = counts["generated"] - counts["executed"]
        tx = self.summary["transactionCounts"]
        tx["unobserved"] = tx["planned"] - tx["executed"]
        for dimension in self.dimensions:
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

    def record_coverage(self, case, prefix, histories=None, bindings=None):
        values = {"Features": set(case["provenance"]["features"]), "Inputs": {tx["input"] for tx in case["transactions"]},
                  "HelperCounts": {helper_count(case)}, "TransactionCounts": {len(case["transactions"])}, "Templates": recipes(case),
                  "CallModes": {int(tx["input"]) & self.specification["modeMask"] for tx in case["transactions"]}, "Outcomes": set()}
        forwards = self.profile == "stateful-forwarded-value"
        if not forwards:
            values["LogPatterns"] = set()
        if prefix == "matched":
            if histories is None or adapter.compare(histories, case, bindings)["category"] != "matched":
                raise ValueError("coverage requires actual matched histories")
            for row in histories["directCore"]["transactions"]:
                values["Outcomes"].add(row["status"])
                if not forwards:
                    values["LogPatterns"].add(",".join(next(role for role in adapter.ROLES if bindings[role] == event["address"]) + ":" + event["topics"][0] for event in row["logs"]))
            statuses = [row["status"] for row in histories["directCore"]["transactions"]]
        else:
            statuses = [adapter.expected_status(tx) for tx in case["transactions"]]
        if forwards:
            values.update(value_coverage(case, statuses))
        for dimension, observed in values.items():
            key = prefix + dimension
            self.summary["coverage"][key] = sorted(set(self.summary["coverage"][key]) | observed, key=int if dimension in NUMERIC_DIMENSIONS else None)

    def add_case(self, case, identifier):
        adapter.validate_case(case)
        if case["schema"] != adapter.PROFILES[self.profile]["caseSchema"]:
            raise ValueError("case differs from the selected campaign profile")
        index = len(self.materialized)
        save_json(self.args.output / "cases" / f"{index:04d}.json", case)
        self.materialized.append(case)
        self.summary["materializedIds"].append(identifier)
        self.summary["counts"]["generated"] += 1
        self.summary["transactionCounts"]["planned"] += len(case["transactions"])
        self.record_coverage(case, "generated")
        self.checkpoint()

    def recorded_g0_version(self, versions):
        """Adopt the G0 version a corpus or saved case records; generation receives it explicitly."""
        recorded = versions.get("generatorVersion") if isinstance(versions, dict) else None
        if recorded not in legacy.G0_VERSIONS:
            raise ValueError("unsupported recorded G0 generator version")
        if self.g0_version is not None and self.g0_version != recorded:
            raise ValueError("G0 generator version disagrees with the supplied case or corpus")
        self.g0_version = recorded
        self.summary["configuration"]["g0Version"] = recorded
        return recorded

    def prepare_cases(self):
        if self.args.case:
            case = self.tool(["replay", self.args.case, self.args.direct_fuel], "case-replay")
            self.recorded_g0_version(case.get("provenance"))
            self.add_case(case, "saved-case")
            return
        if not self.args.corpus:
            response = self.tool(["generate", self.args.seed, self.args.nodes, self.args.cases, self.args.attempts, self.args.direct_fuel,
                                  self.g0_version, self.transactions], "generation")
            if response.get("schema") != self.specification["corpusSchema"] or not isinstance(response.get("cases"), list) or len(response["cases"]) > self.args.cases:
                raise ValueError("invalid native call corpus")
            excluded = response.get("excluded", [])
            self.summary["counts"]["excluded"] = len(excluded)
            self.summary["counts"]["generationResourceExclusions"] = legacy.generation_resource_exclusions(excluded)
            self.summary["generation"] = {**{key: response.get(key) for key in ("requested", "attempted", "status")},
                                          "transactions": self.transactions}
            save_json(self.args.output / "generation.json", {key: value for key, value in response.items() if key != "cases"})
            for index, case in enumerate(response["cases"]):
                self.add_case(case, f"generated-{index}")
            return
        manifest = validate_manifest(common.read_json(self.args.corpus))
        if manifest["profile"] != self.profile:
            raise ValueError("manifest differs from the selected campaign profile")
        version = self.recorded_g0_version(manifest)
        save_json(self.args.output / "corpus.json", manifest)
        self.summary["corpus"] = {"path": str(self.args.corpus), "sha256": common.digest(common.json_bytes(manifest))}
        for dimension in ("Features", "Inputs", "HelperCounts", "TransactionCounts"):
            self.summary["coverage"]["required" + dimension] = manifest["required" + dimension]
        self.summary["coverage"]["requiredTemplates"] = manifest["generationRecipeRequirements"]["templates"]
        for dimension in ("CallModes", "Outcomes") + (VALUE_DIMENSIONS if self.profile == "stateful-forwarded-value" else ("LogPatterns",)):
            self.summary["coverage"]["required" + dimension] = manifest.get("required" + dimension, [])
        self.checkpoint()
        exclusions = []
        for entry in manifest["cases"][:self.args.cases]:
            self.guard()
            if "generation" in entry:
                request = entry["generation"]
                response = self.tool(["generate", request["seed"], request["maxProgramNodes"], 1, 1, self.args.direct_fuel, version],
                                     "corpus-generation")
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
                save_json(plan_path, entry["forwardPlan" if self.profile == "stateful-forwarded-value" else "callPlan"])
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
            "scope": self.specification["scope"]}
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
        save_json(location / "shrink.json", {"schema": "solcore-lean.semantic-call-shrink.v1", "fingerprint": finding["fingerprint"], "steps": [], "status": status, "finalArchive": finding["finalArchive"]})
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
                        "programSha256": common.digest(common.json_bytes(candidate["programs"])),
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
        self.summary.setdefault("generation", {})["generatorVersions"] = sorted(
            {case["provenance"]["generatorVersion"] for case in self.materialized})
        self.checkpoint()
        for index, case in enumerate(self.materialized):
            self.guard()
            if self.args.test_perturb_path and self.args.test_transaction_id and self.args.test_transaction_id not in {tx["id"] for tx in case["transactions"]}:
                raise ValueError("selected synthetic transaction ID is absent from the original scenario")
            folder, report, analysis = self.execute_case(case)
            if self.args.test_perturb_path and report.get("comparison", {}).get("category") == "matched" and not analysis["synthetic"]:
                destination = self.args.output / "test-adapter-rejections" / folder.name
                destination.parent.mkdir(exist_ok=True)
                folder.rename(destination)
                self.summary.setdefault("testAdapterRejections", []).append({"archive": str(destination.relative_to(self.args.output)),
                    "transactionId": self.args.test_transaction_id, "field": self.args.test_field})
                raise ValueError("explicit test adapter has no selected log/payload in the original scenario")
            category = analysis["comparison"]["category"]
            count_outcome(self.summary["counts"], analysis, case)
            for key, value in transaction_counts(analysis["histories"], case, analysis.get("bindings")).items():
                self.summary["transactionCounts"][key] += value
            self.summary["transactionCounts"]["actualMatched"] += transaction_counts(report.get("histories", {}), case, report.get("bindings"))["matched"]
            if category == "matched":
                self.record_coverage(case, "matched", report.get("histories"), report.get("bindings"))
            save_json(self.args.output / "results" / f"{index:04d}.json", {"actualReport": compact_call_report(report), "analysis": analysis})
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
    parser.add_argument("--profile", choices=tuple(PROFILES), default="stateful-calls")
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--nodes", type=int, default=384)
    parser.add_argument("--cases", type=int)
    parser.add_argument("--attempts", type=int, default=256)
    parser.add_argument("--g0-version", choices=legacy.G0_VERSIONS,
                        help=f"G0 generator of the checked step in random generation; default {legacy.RANDOM_G0_VERSION}. "
                             "A corpus or saved case uses the version it records")
    parser.add_argument("--transactions", type=int,
                        help=f"transactions per random scenario, 1 to {adapter.MAX_TRANSACTIONS}; default {adapter.MAX_TRANSACTIONS}. "
                             "A corpus or saved case keeps its own sequence")
    parser.add_argument("--seconds", type=float, default=300)
    parser.add_argument("--disk-bytes", type=int, default=256 * 1024 * 1024)
    parser.add_argument("--shrink-attempts", type=int, default=32)
    parser.add_argument("--shrink-candidates", type=int, default=64)
    parser.add_argument("--case-timeout", type=float, default=90)
    parser.add_argument("--direct-fuel", type=int, default=1000000)
    parser.add_argument("--core-fuel", type=int, default=10000000)
    parser.add_argument("--gas", type=int, default=10000000)
    parser.add_argument("--case-tool", type=Path, help="default: the profile's native case tool")
    parser.add_argument("--core-runner", type=Path, help="default: the profile's imported-Hull scenario runner")
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--test-perturb-path", choices=PATHS)
    parser.add_argument("--test-transaction-id")
    parser.add_argument("--test-field", choices=TEST_FIELDS, default="output")
    args = parser.parse_args()
    selected = adapter.PROFILES[args.profile]
    args.case_tool = args.case_tool or ROOT / ".lake/build/bin" / selected["caseTool"]
    args.core_runner = args.core_runner or ROOT / ".lake/build/bin" / selected["coreRunner"]
    recorded = None
    try:
        if args.corpus:
            recorded = validate_manifest(common.read_json(args.corpus)).get("generatorVersion")
        if args.case:
            case = common.read_json(args.case)
            adapter.validate_case(case)
            recorded = case["provenance"].get("generatorVersion")
        if args.cases is None:
            args.cases = 1 if args.case else len(common.read_json(args.corpus)["cases"]) if args.corpus else 10
    except (ValueError, OSError, KeyError, TypeError, common.Finding) as error:
        parser.error(str(error))
    if args.g0_version is not None and (args.corpus or args.case) and args.g0_version != recorded:
        parser.error("--g0-version disagrees with the supplied case or corpus")
    if args.transactions is not None and (args.corpus or args.case):
        parser.error("--transactions applies only to random generation")
    if args.transactions is not None and not 1 <= args.transactions <= adapter.MAX_TRANSACTIONS:
        parser.error(f"transactions must be between 1 and {adapter.MAX_TRANSACTIONS}")
    if args.case and args.cases != 1:
        parser.error("--case requires --cases 1")
    if args.test_transaction_id and (not args.test_perturb_path or not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", args.test_transaction_id)):
        parser.error("test transaction ID requires the explicit adapter and a valid ID")
    if args.test_field != "output" and not args.test_perturb_path:
        parser.error("test field requires the explicit synthetic adapter")
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
