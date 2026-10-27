#!/usr/bin/env python3
"""Call campaign policy tests, not compiler or contract execution models.

Copied history fixtures exercise classification and retention only. Real Core,
Hull and EVM agreement is checked separately. The cancellation test owns a real
bounded subprocess so process cleanup is not simulated.
"""
from contextlib import redirect_stdout, redirect_stderr
import copy
import importlib.util
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


campaign = load("call_campaign", ROOT / "scripts/semantic-call-campaign.py")
fixtures = load("call_protocol_fixtures", ROOT / "scripts/test-semantic-call-differential.py")


def case(count=3, helpers=1):
    value = fixtures.case()
    value["transactions"] = value["transactions"][:count]
    function = lambda body: {"tag": "lambda", "parameterType": "word", "resultType": "word", "body": body}
    body = function({"tag": "var", "index": 0})
    for _ in range(helpers):
        body = {"tag": "let", "initializer": function({"tag": "var", "index": 0}), "body": body}
    value["callPlan"]["stepProgram"] = {"dataDefinitions": [], "resultType": {
        "tag": "function", "parameter": "word", "result": "word"}, "body": body}
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def report(value=None, *, path=None, transaction_id=None, field="output"):
    value = case() if value is None else value
    # These are protocol fixtures, not a simulation of reduced contracts.
    # Preserve the fixture's log shape while reindexing by stable transaction ID.
    histories = fixtures.histories()
    for history in histories.values():
        by_id = {row["id"]: row for row in history["transactions"]}
        previous = copy.deepcopy(history["initialAccounts"])
        rows = []
        for index, tx in enumerate(value["transactions"]):
            row = copy.deepcopy(by_id[tx["id"]])
            row["index"] = index
            if row["status"] == "reverted":
                row["committedAccounts"] = copy.deepcopy(previous)
            elif int(tx["input"]) & 1:
                # A child revert under a returned root keeps the child's account.
                row["committedAccounts"][1] = copy.deepcopy(previous[1])
            previous = row["committedAccounts"]
            rows.append(row)
        history.update(transactions=rows, finalAccounts=copy.deepcopy(previous))
        fixtures.with_whole(history)
    raw = {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
           "bindings": copy.deepcopy(fixtures.BINDINGS),
           "comparison": campaign.adapter.compare(histories, value, fixtures.BINDINGS)}
    if path is not None:
        changed = campaign.analyze(raw, value, path, transaction_id, field)
        raw["histories"] = changed["histories"]
        raw["comparison"] = campaign.adapter.compare(raw["histories"], value, fixtures.BINDINGS)
    return raw


def incomplete(raw, value, path="rustEvm", at=1):
    history = raw["histories"][path]
    rows = copy.deepcopy(history["transactions"][:at])
    previous = copy.deepcopy(rows[-1]["committedAccounts"] if rows else history["initialAccounts"])
    rows.append({"id": value["transactions"][at]["id"], "index": at, "status": "out-of-fuel",
                 "logs": None, "committedAccounts": previous})
    history.update(transactions=rows, finalAccounts=previous, status="incomplete",
                   unexecuted=[tx["id"] for tx in value["transactions"][at + 1:]])
    fixtures.with_whole(history)
    raw["comparison"] = campaign.adapter.compare(raw["histories"], value, fixtures.BINDINGS)
    return raw


def options(directory, **overrides):
    result = SimpleNamespace(output=Path(directory), seed=1, nodes=128, cases=1, attempts=16,
        seconds=30, disk_bytes=16 * 1024 * 1024, shrink_attempts=0, shrink_candidates=8,
        direct_fuel=1000, core_fuel=1000, gas=100000, case_timeout=10,
        case_tool=Path("/unused/case-tool"), core_runner=Path("/unused/core-runner"),
        anvil=Path("/unused/anvil"), upstream=Path("/unused/upstream"), target_dir=Path("/unused/target"),
        test_perturb_path=None, test_transaction_id=None, test_field="output", case=None, corpus=None)
    for key, value in overrides.items():
        setattr(result, key, value)
    return result


def saved_execution(instance, value, raw, analysis):
    folder = instance.work / f"policy-{len(list(instance.work.iterdir()))}"
    folder.mkdir()
    campaign.save_json(folder / "case.json", value)
    campaign.save_json(folder / "report.json", raw)
    campaign.save_json(folder / "analysis.json", analysis)
    return folder, raw, analysis


class AnalysisTests(unittest.TestCase):
    def test_normal_analysis_and_copy_only_injection_leave_raw_report_immutable(self):
        value, raw = case(), report()
        original = copy.deepcopy(raw)
        plain = campaign.analyze(raw, value)
        self.assertFalse(plain["synthetic"])
        for field in campaign.TEST_FIELDS:
            changed = campaign.analyze(raw, value, "rustEvm", "tx-1", field)
            self.assertTrue(changed["synthetic"])
            self.assertEqual(changed["actualComparison"]["category"], "matched")
            self.assertEqual(changed["comparison"]["transactionId"], "tx-1")
            self.assertEqual(changed["comparison"]["category"], "semantic-mismatch")
            self.assertEqual(raw, original)

    def test_fingerprint_keeps_stable_id_after_deletion_and_index_shift(self):
        value = case()
        first = campaign.analyze(report(value), value, "rustEvm", "tx-1", "parent:storage:1")
        reduced = copy.deepcopy(value)
        reduced["transactions"] = reduced["transactions"][1:2]
        second = campaign.analyze(report(reduced), reduced, "rustEvm", "tx-1", "parent:storage:1")
        self.assertEqual(first["comparison"]["index"], 1)
        self.assertEqual(second["comparison"]["index"], 0)
        self.assertTrue(campaign.same_failure(campaign.fingerprint(first), second))

    def test_fingerprint_rejects_field_slot_runtime_id_and_status_changes(self):
        value = case()
        expected = campaign.fingerprint(campaign.analyze(report(), value, "rustEvm", "tx-1", "parent:storage:0"))
        for path, tx, field in (("rustEvm", "tx-1", "parent:storage:1"), ("rustEvm", "tx-1", "output"),
                                ("directCore", "tx-1", "parent:storage:0"), ("rustEvm", "tx-0", "parent:storage:0")):
            with self.subTest(path=path, tx=tx, field=field):
                candidate = campaign.analyze(report(), value, path, tx, field)
                self.assertFalse(campaign.same_failure(expected, candidate))
        changed = campaign.analyze(report(), value, "rustEvm", "tx-1", "parent:storage:0")
        changed["histories"]["rustEvm"]["transactions"][1]["status"] = "reverted"
        self.assertFalse(campaign.same_failure(expected, changed))

    def test_removed_synthetic_id_does_not_create_a_fake_finding(self):
        value = case(1)
        analysis = campaign.analyze(report(value), value, "rustEvm", "tx-1")
        self.assertFalse(analysis["synthetic"])
        self.assertEqual(analysis["comparison"]["category"], "matched")

    def test_injection_requires_a_valid_complete_actual_match(self):
        value = case()
        for raw in (report(path="directCore", transaction_id="tx-0"), incomplete(report(), value)):
            analysis = campaign.analyze(raw, value, "rustEvm", "tx-1")
            self.assertFalse(analysis["synthetic"])
            self.assertEqual(analysis["comparison"], raw["comparison"])
        raw = incomplete(report(), value)
        raw["comparison"] = {"category": "matched"}
        with self.assertRaises(ValueError):
            campaign.analyze(raw, value, "rustEvm")

    def test_initial_and_intermediate_mismatch_survive_later_convergence_or_resource(self):
        value = case()
        raw = report(path="rustEvm", transaction_id="tx-0", field="parent:storage:0")
        self.assertEqual(raw["histories"]["rustEvm"]["finalAccounts"], raw["histories"]["directCore"]["finalAccounts"])
        analysis = campaign.analyze(incomplete(raw, value), value)
        self.assertEqual(analysis["comparison"]["transactionId"], "tx-0")
        self.assertEqual(campaign.fingerprint(analysis)["accountFields"], ["parent:storage:0"])
        raw = report()
        raw["histories"]["rustEvm"]["initialAccounts"] = fixtures.account_rows(8, (0, 1), 0, (0, 0))
        raw["comparison"] = campaign.adapter.compare(raw["histories"], value, fixtures.BINDINGS)
        self.assertEqual(campaign.fingerprint(campaign.analyze(raw, value))["stage"], "initial-accounts")

    def test_hash_includes_core_inputs_ids_and_sequence_order(self):
        original = case()
        for edit in (lambda x: x["programs"]["parent"].update(body="different"),
                     lambda x: x["transactions"][0].update(input="9"),
                     lambda x: x["transactions"][0].update(id="other"),
                     lambda x: x["transactions"].reverse(),
                     lambda x: x["transactions"].pop()):
            changed = copy.deepcopy(original)
            edit(changed)
            self.assertNotEqual(campaign.case_hash(original), campaign.case_hash(changed))
        changed = copy.deepcopy(original)
        changed["source"] = "metadata unrelated to original Core identity"
        self.assertEqual(campaign.case_hash(original), campaign.case_hash(changed))

    def test_account_fingerprint_preserves_role_and_field_without_values(self):
        value = case()
        expected = campaign.fingerprint(campaign.analyze(report(), value, "rustEvm", "tx-1", "parent:balance"))
        self.assertEqual(expected["accountFields"], ["parent:balance"])
        for field in ("child:balance", "parent:storage:0", "child:storage:1"):
            self.assertFalse(campaign.same_failure(expected, campaign.analyze(report(), value, "rustEvm", "tx-1", field)))
        changed = campaign.analyze(report(), value, "rustEvm", "tx-1", "parent:balance")
        changed["histories"]["rustEvm"]["transactions"][1]["committedAccounts"][0]["balance"] = "99"
        self.assertTrue(campaign.same_failure(expected, changed))

    def test_log_fingerprint_preserves_index_field_shape_and_emitter_order(self):
        value = case()
        original = campaign.analyze(report(), value, "rustEvm", "tx-0", "logs:data")
        expected = campaign.fingerprint(original)
        self.assertEqual(expected["logFields"], ["0:data"])
        self.assertEqual([event["role"] for event in expected["logShapes"]["rustEvm"]], ["parent", "child", "parent"])
        changed = copy.deepcopy(original)
        changed["histories"]["rustEvm"]["transactions"][0]["logs"][0]["data"] = fixtures.word(99)
        self.assertTrue(campaign.same_failure(expected, changed))
        for edit in (lambda events: events.reverse(), lambda events: events[1].update(data=fixtures.word(99)),
                     lambda events: events[0].update(topics=["2"]), lambda events: events[0].update(address=fixtures.BINDINGS["child"]),
                     lambda events: events[0].update(data="0x"), lambda events: events.pop()):
            changed = copy.deepcopy(original)
            edit(changed["histories"]["rustEvm"]["transactions"][0]["logs"])
            self.assertFalse(campaign.same_failure(expected, changed))

    def test_role_normalized_fingerprint_ignores_deployment_address_values(self):
        value = case()
        original = campaign.analyze(report(), value, "rustEvm", "tx-0", "logs:data")
        relocated = copy.deepcopy(original)
        relocated["bindings"].update(parent="201", child="202")
        for history in relocated["histories"].values():
            for account_list in [history["initialAccounts"], history["finalAccounts"], *[row["committedAccounts"] for row in history["transactions"]]]:
                for account in account_list:
                    account["address"] = relocated["bindings"][account["role"]]
            for row in history["transactions"]:
                for event in row["logs"]:
                    role = "parent" if event["address"] == fixtures.BINDINGS["parent"] else "child"
                    event["address"] = relocated["bindings"][role]
        self.assertTrue(campaign.same_failure(campaign.fingerprint(original), relocated))

    def test_agreed_invalid_root_rollback_has_specific_account_and_log_fields(self):
        value, raw = case(), report()
        for history in raw["histories"].values():
            history["transactions"][2]["committedAccounts"][1]["balance"] = "2"
            history["finalAccounts"] = copy.deepcopy(history["transactions"][2]["committedAccounts"])
            history["transactions"][2]["logs"] = [fixtures.event("parent", 3, 25)]
        raw["comparison"] = campaign.adapter.compare(raw["histories"], value, fixtures.BINDINGS)
        observed = campaign.fingerprint(campaign.analyze(raw, value))
        self.assertEqual(observed["category"], "semantic-mismatch")
        self.assertEqual(observed["disagreeingPairs"], [])
        self.assertEqual(observed["accountFields"], ["child:balance"])
        self.assertIn("nonempty-after-root-revert", observed["logFields"])

    def test_removed_log_or_transaction_does_not_apply_synthetic_adapter(self):
        value = case()
        for txid in ("tx-2", "missing"):
            observed = campaign.analyze(report(), value, "rustEvm", txid, "logs:data")
            self.assertFalse(observed["synthetic"])
            self.assertFalse(observed["testAdapter"]["applied"])
            self.assertEqual(observed["comparison"]["category"], "matched")

    def test_malformed_error_histories_still_have_a_serializable_fingerprint(self):
        value, raw = case(), report()
        raw["histories"]["rustEvm"]["transactions"][0]["logs"] = [None, {"topics": None}]
        raw["histories"]["importedHull"]["transactions"] = None
        raw["comparison"] = {"category": "adapter-error", "stage": "comparison", "transactionId": "tx-0", "pairs": {}}
        fingerprint = campaign.fingerprint(campaign.analyze(raw, value))
        json.dumps(fingerprint)
        self.assertEqual(fingerprint["logShapes"]["rustEvm"][0], {"malformed": True})


class CountsAndCoverageTests(unittest.TestCase):
    def test_counts_separate_observed_complete_and_matching_prefixes(self):
        value = case()
        self.assertEqual(campaign.transaction_counts(report()["histories"], value, fixtures.BINDINGS), {"executed": 3, "completed": 3, "matched": 3})
        changed = report(path="rustEvm", transaction_id="tx-1")
        self.assertEqual(campaign.transaction_counts(changed["histories"], value, fixtures.BINDINGS), {"executed": 3, "completed": 3, "matched": 1})
        partial = incomplete(report(), value)
        self.assertEqual(campaign.transaction_counts(partial["histories"], value, fixtures.BINDINGS), {"executed": 3, "completed": 1, "matched": 1})
        self.assertEqual(campaign.transaction_counts({"directCore": report()["histories"]["directCore"]}, value, fixtures.BINDINGS),
                         {"executed": 3, "completed": 0, "matched": 0})

    def test_known_mismatch_before_resource_is_not_a_completed_scenario(self):
        value = case()
        raw = incomplete(report(path="rustEvm", transaction_id="tx-0"), value)
        analysis = campaign.analyze(raw, value)
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory))
            campaign.count_outcome(instance.summary["counts"], analysis, value)
            counts = instance.summary["counts"]
            self.assertEqual((counts["executed"], counts["completed"], counts["mismatched"]), (1, 0, 1))
            self.assertEqual(campaign.transaction_counts(analysis["histories"], value, fixtures.BINDINGS)["matched"], 0)

    def test_only_wholly_matched_scenarios_satisfy_coverage(self):
        value = case()
        for kind in ("matched", "synthetic", "resource", "real-mismatch"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                instance = campaign.Campaign(options(directory))
                instance.summary["coverage"].update(requiredInputs=["4", "5", "6"], requiredHelperCounts=[1], requiredTransactionCounts=[3])
                raw = incomplete(report(), value) if kind == "resource" else report(path="directCore", transaction_id="tx-0") if kind == "real-mismatch" else report()
                analysis = campaign.analyze(raw, value, "rustEvm" if kind == "synthetic" else None, "tx-1")
                with patch.object(instance, "prepare_cases", side_effect=lambda: instance.add_case(value, "policy")), \
                     patch.object(instance, "execute_case", side_effect=lambda _: saved_execution(instance, value, raw, analysis)), redirect_stdout(io.StringIO()):
                    instance.run()
                instance.checkpoint()
                self.assertEqual(instance.summary["coverage"]["generatedInputs"], ["4", "5", "6"])
                self.assertEqual(instance.summary["coverage"]["matchedInputs"], ["4", "5", "6"] if kind == "matched" else [])
                self.assertEqual(campaign.missing_coverage(instance.summary), kind != "matched")
                if kind == "synthetic":
                    self.assertEqual(instance.summary["transactionCounts"]["actualMatched"], 3)
                    self.assertEqual(instance.summary["counts"]["matched"], 0)

    def test_partial_generation_retains_cases_exclusions_and_unexecuted_counts(self):
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, cases=2))
            response = {"schema": campaign.CORPUS_SCHEMA, "cases": [case()], "requested": 2,
                "attempted": 2, "status": "generation-exhausted", "excluded": [{"category": campaign.RESOURCE,
                "code": "validation-out-of-fuel", "reason": "storage history exhausted Core fuel"}]}
            with patch.object(instance, "tool", return_value=response):
                instance.prepare_cases()
            counts = instance.summary["counts"]
            self.assertEqual((counts["generated"], counts["excluded"], counts["generationResourceExclusions"], counts["unexecuted"]), (1, 1, 1, 1))
            self.assertEqual(instance.summary["transactionCounts"]["unobserved"], 3)
            self.assertEqual(instance.summary["coverage"]["matchedInputs"], [])
            self.assertTrue((Path(directory) / "cases/0000.json").is_file())

    def test_helper_counts_use_step_declarations_and_templates_use_nested_recipe(self):
        value = case(helpers=3)
        value["provenance"]["origin"] = {"kind": "call-generated", "helperCount": 99,
            "stepOrigin": {"kind": "aggregate-generated", "helpers": [{"template": 0}, {"template": 2}, {"template": 3}]}}
        self.assertEqual(campaign.helper_count(value), 3)
        self.assertEqual(campaign.recipes(value), {0, 2, 3})
        value["provenance"]["origin"]["stepOrigin"]["helpers"][0]["template"] = True
        with self.assertRaises(ValueError):
            campaign.recipes(value)

    def test_explicit_missing_original_synthetic_id_is_rejected_before_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, test_perturb_path="rustEvm", test_transaction_id="absent"))
            with patch.object(instance, "prepare_cases", side_effect=lambda: instance.add_case(case(), "policy")), \
                 patch.object(instance, "execute_case") as execute, self.assertRaises(ValueError):
                instance.run()
            execute.assert_not_called()

    def test_observed_outcomes_and_logs_are_separate_from_prescribed_call_modes(self):
        value, raw = case(), report()
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory))
            instance.record_coverage(value, "generated")
            coverage = instance.summary["coverage"]
            self.assertEqual(coverage["generatedCallModes"], [4, 5, 6])
            self.assertEqual(coverage["generatedOutcomes"], [])
            self.assertEqual(coverage["generatedLogPatterns"], [])
            with self.assertRaises(ValueError):
                instance.record_coverage(value, "matched")
            instance.record_coverage(value, "matched", raw["histories"], raw["bindings"])
            self.assertEqual(coverage["matchedOutcomes"], ["returned", "reverted"])
            self.assertEqual(coverage["matchedLogPatterns"], sorted(campaign.LOG_PATTERNS))
            changed = campaign.analyze(raw, value, "rustEvm", "tx-0", "logs:data")
            with self.assertRaises(ValueError):
                instance.record_coverage(value, "matched", changed["histories"], raw["bindings"])

    def test_unknown_pending_transaction_is_not_observed_or_completed(self):
        value, raw = case(), report()
        for history in raw["histories"].values():
            history.update(transactions=history["transactions"][:1], status="incomplete", finalAccounts=None,
                           finalAccountStorage=None, unobserved=["tx-1"], unexecuted=["tx-2"])
        self.assertEqual(campaign.transaction_counts(raw["histories"], value, raw["bindings"]),
                         {"executed": 1, "completed": 1, "matched": 1})

    def test_original_missing_log_rejection_retains_actual_archive(self):
        value, raw = case(), report()
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, test_perturb_path="rustEvm", test_transaction_id="tx-2", test_field="logs:data"))
            analysis = campaign.analyze(raw, value, "rustEvm", "tx-2", "logs:data")
            with patch.object(instance, "prepare_cases", side_effect=lambda: instance.add_case(value, "policy")), \
                 patch.object(instance, "execute_case", side_effect=lambda _: saved_execution(instance, value, raw, analysis)), self.assertRaises(ValueError):
                instance.run()
            archive = Path(directory) / instance.summary["testAdapterRejections"][0]["archive"]
            self.assertEqual(campaign.common.read_json(archive / "report.json")["comparison"]["category"], "matched")
            self.assertEqual(instance.summary["counts"]["matched"], 0)

    def test_rejections_are_errors_without_completed_runtime_transactions(self):
        value = case()
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory))
            for category in ("source-rejected", "compilation-rejected"):
                analysis = campaign.analyze({"comparison": {"category": category, "stage": "compiler", "pairs": {}}}, value)
                campaign.count_outcome(instance.summary["counts"], analysis, value)
            counts = instance.summary["counts"]
            self.assertEqual((counts["errors"], counts["sourceRejected"], counts["compilationRejected"], counts["completed"]), (2, 1, 1, 0))


class ManifestTests(unittest.TestCase):
    def test_fixed_manifest_and_invalid_bounds_or_ambiguous_sources(self):
        manifest = json.loads((ROOT / "scripts/semantic-call-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        changes = [lambda m: m.update(profile="runtime-loops"), lambda m: m.pop("stepFunctionVersion"),
            lambda m: m.update(requiredInputs=["00"]), lambda m: m.update(requiredTransactionCounts=[0]),
            lambda m: m.update(requiredHelperCounts=[True]),
            lambda m: m.update(generationRecipeRequirements={"templates": [4]}),
            lambda m: m["cases"].append(copy.deepcopy(m["cases"][0])),
            lambda m: m["cases"][0].update(generation={"seed": "1", "maxProgramNodes": 100}),
            lambda m: m["cases"][-1]["generation"].update(seed=str(2**64)),
            lambda m: m["cases"][-1]["generation"].update(maxProgramNodes=513),
            lambda m: m["cases"][-1]["generation"].update(maxProgramNodes=True),
            lambda m: m["cases"][0].update(transactions=[])]
        for index, change in enumerate(changes):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.subTest(index=index), self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)

    def test_cli_nondefault_field_requires_explicit_synthetic_adapter(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(sys, "argv", ["campaign", "--output", str(Path(directory) / "out"), "--test-field", "parent:storage:0"]), \
             redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as stopped:
            campaign.main()
        self.assertEqual(stopped.exception.code, 2)


class RetentionTests(unittest.TestCase):
    def retained(self, instance, value=None, synthetic=True):
        value = case() if value is None else value
        raw = report(value) if synthetic else report(value, path="rustEvm", transaction_id=value["transactions"][0]["id"])
        analysis = campaign.analyze(raw, value, "rustEvm" if synthetic else None, value["transactions"][0]["id"])
        folder, _, _ = saved_execution(instance, value, raw, analysis)
        return value, instance.retain_finding(0, folder, value, analysis)

    def test_no_attempt_and_consumed_global_budget_keep_original_and_history(self):
        for limit, used, expected in ((0, 0, "no-attempts"), (2, 2, "attempt-limit")):
            with self.subTest(expected=expected), tempfile.TemporaryDirectory() as directory:
                instance = campaign.Campaign(options(directory, shrink_attempts=limit))
                instance.shrink_attempts = used
                _, finding = self.retained(instance)
                history = campaign.common.read_json(Path(directory) / finding["history"])
                self.assertEqual(history["status"], expected)
                self.assertEqual(history["steps"], [])
                self.assertEqual(finding["originalArchive"], finding["finalArchive"])
                self.assertTrue((Path(directory) / finding["originalArchive"] / "case.json").exists())

    def test_empty_or_duplicate_candidates_terminate_without_execution(self):
        for duplicate in (False, True):
            with self.subTest(duplicate=duplicate), tempfile.TemporaryDirectory() as directory:
                instance = campaign.Campaign(options(directory, shrink_attempts=2))
                value, finding = self.retained(instance)
                with patch.object(instance, "tool", return_value={"schema": campaign.CORPUS_SCHEMA, "cases": [value] if duplicate else []}), \
                     patch.object(instance, "execute_case") as execute:
                    instance.shrink(value, finding)
                execute.assert_not_called()
                self.assertEqual(instance.shrink_attempts, 0)
                self.assertEqual(campaign.common.read_json(Path(directory) / finding["history"])["status"], "no-preserving-candidate")

    def test_shrink_resource_stop_preserves_original_and_status(self):
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, shrink_attempts=2))
            value, finding = self.retained(instance)
            with patch.object(instance, "tool", side_effect=campaign.common.Finding(campaign.RESOURCE, "campaign-time", "policy budget")), \
                 self.assertRaises(campaign.common.Finding):
                instance.shrink(value, finding)
            history = campaign.common.read_json(Path(directory) / finding["history"])
            self.assertEqual(history["status"], "budget-exhausted")
            self.assertEqual(history["finalArchive"], finding["originalArchive"])

    def test_nonpreserving_real_secondary_finding_survives_synthetic_work_cleanup(self):
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, shrink_attempts=1))
            value, finding = self.retained(instance)
            candidate = copy.deepcopy(value)
            candidate["transactions"] = candidate["transactions"][1:]
            raw = report(candidate, path="directCore", transaction_id="tx-1", field="parent:storage:1")
            analysis = campaign.analyze(raw, candidate)
            with patch.object(instance, "tool", return_value={"schema": campaign.CORPUS_SCHEMA, "cases": [candidate]}), \
                 patch.object(instance, "execute_case", side_effect=lambda _: saved_execution(instance, candidate, raw, analysis)):
                instance.shrink(value, finding)
            secondary = instance.summary["secondaryFindings"][0]
            self.assertFalse(secondary["synthetic"])
            self.assertFalse(secondary["automaticReduction"])
            self.assertEqual(secondary["parentHistory"], finding["history"])
            self.assertTrue(secondary["archive"].startswith("findings/real/"))
            campaign.shutil.rmtree(instance.work)
            self.assertTrue((Path(directory) / secondary["archive"] / "report.json").is_file())
            self.assertEqual(finding["finalArchive"], finding["originalArchive"])
            self.assertEqual(campaign.common.read_json(Path(directory) / finding["history"])["status"], "attempt-limit")


class CancellationTests(unittest.TestCase):
    def test_sigterm_stops_real_owned_child_and_saves_unexecuted_summary(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            marker, helper, output = folder / "started", folder / "case-tool", folder / "campaign"
            helper.write_text("#!" + sys.executable + "\nimport os,time\nfrom pathlib import Path\n"
                              + "Path(" + repr(str(marker)) + ").write_text(str(os.getpid()))\ntime.sleep(20)\n")
            helper.chmod(0o700)
            process = subprocess.Popen([sys.executable, "-B", str(ROOT / "scripts/semantic-call-campaign.py"),
                "--output", str(output), "--case-tool", str(helper), "--cases", "1", "--seconds", "30"],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            try:
                deadline = time.monotonic() + 5
                while not marker.exists() and process.poll() is None and time.monotonic() < deadline:
                    time.sleep(.02)
                self.assertTrue(marker.exists())
                child_pid = int(marker.read_text())
                process.send_signal(signal.SIGTERM)
                stdout, stderr = process.communicate(timeout=5)
                self.assertEqual(process.returncode, 1, stdout + stderr)
                summary = json.loads((output / "summary.json").read_text())
                self.assertEqual(summary["status"], "interrupted")
                self.assertEqual(summary["counts"]["matched"], 0)
                self.assertEqual(summary["transactionCounts"]["matched"], 0)
                self.assertFalse((output / ".work").exists())
                with self.assertRaises(ProcessLookupError):
                    os.kill(child_pid, 0)
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()



class BackendTests(unittest.TestCase):
    def test_backend_is_part_of_failure_identity_with_legacy_o0(self):
        value = case()
        legacy = campaign.analyze(report(value), value, "rustEvm", "tx-1")
        optimized = campaign.analyze({**report(value), "backend": "sonatina-o2"}, value, "rustEvm", "tx-1")
        self.assertEqual(legacy["backend"], "sonatina-o0")
        self.assertEqual(optimized["backend"], "sonatina-o2")
        expected = campaign.fingerprint(legacy)
        self.assertFalse(campaign.same_failure(expected, optimized))
        del expected["backend"]
        self.assertTrue(campaign.same_failure(expected, legacy))
        self.assertFalse(campaign.same_failure(expected, optimized))
        for invalid in (None, "yul"):
            with self.subTest(backend=invalid), self.assertRaises(ValueError):
                campaign.analyze({**report(value), "backend": invalid}, value)

    def test_each_candidate_uses_selected_backend_and_retains_it_in_report(self):
        with tempfile.TemporaryDirectory() as temporary:
            instance = campaign.Campaign(options(temporary, backend="sonatina-o2"))
            seen = []
            def execute(args, raw):
                seen.append((args.backend, raw["backend"]))
                value = json.loads(args.case.read_text())
                raw.update(report(value))
            with patch.object(campaign.adapter, "execute", side_effect=execute):
                for value in (case(3), case(1)):
                    folder, raw, analysis = instance.execute_case(value)
                    self.assertEqual(raw["backend"], "sonatina-o2")
                    self.assertEqual(analysis["backend"], "sonatina-o2")
                    self.assertEqual(campaign.common.read_json(folder / "report.json")["backend"], "sonatina-o2")
            self.assertEqual(seen, [("sonatina-o2", "sonatina-o2")] * 2)
            self.assertEqual(instance.summary["backend"], "sonatina-o2")
            self.assertEqual(instance.summary["configuration"]["backend"], "sonatina-o2")

    def test_yul_campaign_cli_is_rejected_before_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "campaign"
            arguments = ["campaign", "--output", str(output), "--backend", "yul", "--cases", "1"]
            with patch.object(sys, "argv", arguments), patch.object(campaign.Campaign, "run") as run, \
                    redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as caught:
                campaign.main()
            self.assertEqual(caught.exception.code, 2)
            run.assert_not_called()
            self.assertFalse(output.exists())

    def test_yul_programmatic_campaign_is_rejected_before_work_directory(self):
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaisesRegex(ValueError, "stateful comparisons require a Sonatina backend"):
                campaign.Campaign(options(temporary, backend="yul"))
            self.assertFalse((Path(temporary) / ".work").exists())

    def test_yul_cannot_become_a_stateful_reduction_identity(self):
        value = case()
        ordinary = campaign.analyze(report(value), value, "rustEvm", "tx-1")
        expected = campaign.fingerprint(ordinary)
        with self.assertRaisesRegex(ValueError, "stateful comparisons require a Sonatina backend"):
            campaign.fingerprint({**ordinary, "backend": "yul"})
        with self.assertRaisesRegex(ValueError, "stateful comparisons require a Sonatina backend"):
            campaign.same_failure({**expected, "backend": "yul"}, ordinary)
        with self.assertRaisesRegex(ValueError, "stateful comparisons require a Sonatina backend"):
            campaign.same_failure(expected, {**ordinary, "backend": "yul"})

    def test_campaign_cli_selects_backend(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "campaign"
            def run(instance):
                self.assertEqual(instance.backend, "sonatina-o2")
                instance.summary["status"] = "complete"
                instance.summary["counts"].update(generated=1, executed=1, completed=1, matched=1)
            arguments = ["campaign", "--output", str(output), "--backend", "sonatina-o2", "--cases", "1"]
            with patch.object(sys, "argv", arguments), patch.object(campaign.Campaign, "run", run), redirect_stdout(io.StringIO()):
                self.assertEqual(campaign.main(), 0)
            self.assertEqual(campaign.common.read_json(output / "summary.json")["backend"], "sonatina-o2")


def forward_case(rows=((0, 7, 5), (1, 0, 2**70), (2, 1, 1))):
    value = fixtures.forward_case(rows)
    value["forwardPlan"]["stepProgram"] = case()["callPlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def forward_report(value):
    histories = fixtures.forward_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories, "bindings": copy.deepcopy(fixtures.BINDINGS),
            "comparison": campaign.adapter.compare(histories, value, fixtures.BINDINGS)}


class ForwardedValueCampaignTests(unittest.TestCase):
    def test_forward_dimensions_record_values_forwards_and_refunds(self):
        value = forward_case()
        self.assertEqual(campaign.PROFILES["stateful-forwarded-value"]["dimensions"],
                         campaign.DIMENSIONS[:-1] + ("Values", "ForwardedValues", "RefundedForwards", "RevertedValues"))
        self.assertEqual(campaign.value_coverage(value, ["returned", "returned", "reverted"]),
                         {"Values": {"7", "0", "1"}, "ForwardedValues": {"5", str(2**70), "1"},
                          "RefundedForwards": {str(2**70)}, "RevertedValues": {"1"}})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-forwarded-value"))
            instance.summary["coverage"].update(requiredValues=["0", "7", str(2**64)], requiredRefundedForwards=[str(2**70)],
                                                requiredCallModes=[0, 1, 2, 3])
            instance.record_coverage(value, "generated")
            instance.record_coverage(value, "matched", forward_report(value)["histories"], fixtures.BINDINGS)
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedValues"], coverage["matchedRefundedForwards"], coverage["matchedCallModes"],
                              coverage["matchedRevertedValues"]), (["0", "1", "7"], [str(2**70)], [0, 1, 2], ["1"]))
            self.assertEqual((coverage["missingValues"], coverage["missingCallModes"]), ([str(2**64)], [3]))
            self.assertNotIn("matchedLogPatterns", coverage)
            self.assertEqual(instance.summary["configuration"]["profile"], "stateful-forwarded-value")
        with tempfile.TemporaryDirectory() as directory:
            legacy = campaign.Campaign(options(directory)).summary["coverage"]
            self.assertIn("requiredLogPatterns", legacy)
            self.assertNotIn("requiredValues", legacy)

    def test_forward_manifest_requires_value_dimensions_only_for_its_profile(self):
        manifest = json.loads((ROOT / "scripts/semantic-forward-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        changes = [lambda m: m.pop("requiredValues"), lambda m: m.update(requiredCallModes=[4]),
            lambda m: m.update(requiredLogPatterns=[""]), lambda m: m.update(requiredRefundedForwards=[]),
            lambda m: m.update(requiredValues=["07"]), lambda m: m.update(requiredRevertedValues=[str(2**70 + 1)]),
            lambda m: m["cases"][0].update(callPlan=m["cases"][0].pop("forwardPlan"))]
        for index, change in enumerate(changes):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.subTest(index=index), self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        calls = json.loads((ROOT / "scripts/semantic-call-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(calls), calls)
        calls["requiredValues"] = ["0"]
        with self.assertRaises(ValueError):
            campaign.validate_manifest(calls)

    def test_forward_fingerprints_injection_and_prefix_counts(self):
        value = forward_case()
        raw = forward_report(value)
        self.assertEqual(raw["comparison"]["category"], "matched")
        changed = campaign.analyze(raw, value, "importedHull", "tx-0", "child:balance")
        fingerprint = campaign.fingerprint(changed)
        self.assertEqual((changed["comparison"]["category"], fingerprint["accountFields"], fingerprint["transactionId"]),
                         ("semantic-mismatch", ["child:balance"], "tx-0"))
        self.assertTrue(campaign.same_failure(fingerprint, campaign.analyze(forward_report(value), value, "importedHull", "tx-0", "child:balance")))
        self.assertEqual(campaign.transaction_counts(raw["histories"], value, fixtures.BINDINGS), {"executed": 3, "completed": 3, "matched": 3})
        for history in raw["histories"].values():
            history["initialAccounts"] = campaign.adapter.initial_accounts(fixtures.BINDINGS)
        initial = campaign.analyze({**raw, "comparison": campaign.adapter.compare(raw["histories"], value, fixtures.BINDINGS)}, value)
        self.assertEqual(campaign.fingerprint(initial)["accountFields"], ["parent:balance"])
        self.assertEqual((campaign.helper_count(value), campaign.recipes(value)), (1, set()))
        generated = forward_case()
        generated["provenance"]["origin"] = {"kind": "forward-generated", "stepOrigin": {"kind": "aggregate-generated", "helpers": [{"template": 2}]}}
        self.assertEqual(campaign.recipes(generated), {2})
        self.assertNotEqual(campaign.case_hash(value), campaign.case_hash(forward_case(rows=((0, 7, 6), (1, 0, 2**70), (2, 1, 1)))))


class StrayWriteAdapterTests(unittest.TestCase):
    """`ROLE:stray` adds one undeclared nonzero slot to a contract's copied whole storage."""

    def test_stray_write_is_detected_per_contract_and_kept_by_reduction(self):
        value = case()
        for role in ("parent", "child"):
            for path in campaign.PATHS:
                analysis = campaign.analyze(report(value), value, path, "tx-0", role + ":stray")
                with self.subTest(role=role, path=path):
                    self.assertTrue(analysis["synthetic"])
                    self.assertEqual((analysis["comparison"]["category"], analysis["comparison"]["transactionId"],
                                      analysis["comparison"]["fields"]), ("semantic-mismatch", "tx-0", ["accountStorage"]))
                    observed = campaign.fingerprint(analysis)
                    self.assertEqual(observed["accountStorageDifferences"],
                                     [{"account": role, "slot": "undeclared", "zeroPaths": [other for other in campaign.PATHS if other != path]}])
                    self.assertEqual(observed["accountFields"], [])
        first = campaign.analyze(report(value), value, "importedHull", "tx-1", "child:stray")
        reduced = copy.deepcopy(value)
        reduced["transactions"] = reduced["transactions"][1:2]
        second = campaign.analyze(report(reduced), reduced, "importedHull", "tx-1", "child:stray")
        self.assertEqual(second["comparison"]["index"], 0)
        self.assertTrue(campaign.same_failure(campaign.fingerprint(first), second))
        self.assertFalse(campaign.same_failure(campaign.fingerprint(first),
                                               campaign.analyze(report(value), value, "importedHull", "tx-1", "parent:stray")))
        removed = copy.deepcopy(value)
        removed["transactions"] = removed["transactions"][:1]
        self.assertFalse(campaign.analyze(report(removed), removed, "importedHull", "tx-1", "child:stray")["synthetic"])

    def test_every_fingerprint_carries_the_whole_storage_classification(self):
        value = case()
        plain = campaign.fingerprint(campaign.analyze(report(), value))
        self.assertEqual((plain["accountStorageDifferences"], plain["accountStorageRollbackPaths"]), ([], []))


if __name__ == "__main__":
    unittest.main()
