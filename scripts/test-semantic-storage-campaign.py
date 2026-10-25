#!/usr/bin/env python3
"""Stateful campaign policy tests, not compiler or storage execution models.

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


campaign = load("storage_campaign", ROOT / "scripts/semantic-storage-campaign.py")
fixtures = load("storage_protocol_fixtures", ROOT / "scripts/test-semantic-storage-differential.py")


def case(count=3, helpers=1):
    value = fixtures.case(count)
    function = lambda body: {"tag": "lambda", "parameterType": "word", "resultType": "word", "body": body}
    body = function({"tag": "var", "index": 0})
    for _ in range(helpers):
        body = {"tag": "let", "initializer": function({"tag": "var", "index": 0}), "body": body}
    value["storagePlan"]["stepProgram"] = {"dataDefinitions": [], "resultType": {
        "tag": "function", "parameter": "word", "result": "word"}, "body": body}
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def report(value=None, *, path=None, transaction_id=None, field="output"):
    value = case() if value is None else value
    histories = fixtures.histories(value)
    for history in histories.values():
        for row, tx in zip(history["transactions"], value["transactions"]):
            row["id"] = tx["id"]
    raw = {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
           "comparison": campaign.adapter.compare(histories, value)}
    if path is not None:
        changed = campaign.analyze(raw, value, path, transaction_id, field)
        raw["histories"] = changed["histories"]
        raw["comparison"] = campaign.adapter.compare(raw["histories"], value)
    return raw


def incomplete(raw, value, path="rustEvm", at=1):
    rows = copy.deepcopy(raw["histories"][path]["transactions"][:at])
    fault = fixtures.row(at, status="out-of-fuel")
    fault["id"] = value["transactions"][at]["id"]
    rows.append(fault)
    raw["histories"][path] = fixtures.history(value, rows)
    raw["comparison"] = campaign.adapter.compare(raw["histories"], value)
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
        for field in ("output", "storage:0", "storage:1"):
            changed = campaign.analyze(raw, value, "rustEvm", "tx-1", field)
            self.assertTrue(changed["synthetic"])
            self.assertEqual(changed["actualComparison"]["category"], "matched")
            self.assertEqual(changed["comparison"]["transactionId"], "tx-1")
            self.assertEqual(changed["comparison"]["category"], "semantic-mismatch")
            self.assertEqual(raw, original)

    def test_fingerprint_keeps_stable_id_after_deletion_and_index_shift(self):
        value = case()
        first = campaign.analyze(report(value), value, "rustEvm", "tx-1", "storage:1")
        reduced = copy.deepcopy(value)
        reduced["transactions"] = reduced["transactions"][1:2]
        second = campaign.analyze(report(reduced), reduced, "rustEvm", "tx-1", "storage:1")
        self.assertEqual(first["comparison"]["index"], 1)
        self.assertEqual(second["comparison"]["index"], 0)
        self.assertTrue(campaign.same_failure(campaign.fingerprint(first), second))

    def test_fingerprint_rejects_field_slot_runtime_id_and_status_changes(self):
        value = case()
        expected = campaign.fingerprint(campaign.analyze(report(), value, "rustEvm", "tx-1", "storage:0"))
        for path, tx, field in (("rustEvm", "tx-1", "storage:1"), ("rustEvm", "tx-1", "output"),
                                ("directCore", "tx-1", "storage:0"), ("rustEvm", "tx-0", "storage:0")):
            with self.subTest(path=path, tx=tx, field=field):
                candidate = campaign.analyze(report(), value, path, tx, field)
                self.assertFalse(campaign.same_failure(expected, candidate))
        changed = campaign.analyze(report(), value, "rustEvm", "tx-1", "storage:0")
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
        raw = report(path="rustEvm", transaction_id="tx-0", field="storage:0")
        self.assertEqual(raw["histories"]["rustEvm"]["finalStorage"], raw["histories"]["directCore"]["finalStorage"])
        analysis = campaign.analyze(incomplete(raw, value), value)
        self.assertEqual(analysis["comparison"]["transactionId"], "tx-0")
        self.assertEqual(campaign.fingerprint(analysis)["storageSlots"], ["0"])
        raw = report()
        raw["histories"]["rustEvm"]["initialStorage"] = fixtures.slots(0, 1)
        raw["comparison"] = campaign.adapter.compare(raw["histories"], value)
        self.assertEqual(campaign.fingerprint(campaign.analyze(raw, value))["stage"], "initial-storage")

    def test_hash_includes_core_inputs_ids_and_sequence_order(self):
        original = case()
        for edit in (lambda x: x["program"].update(body="different"),
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


class CountsAndCoverageTests(unittest.TestCase):
    def test_counts_separate_observed_complete_and_matching_prefixes(self):
        value = case()
        self.assertEqual(campaign.transaction_counts(report()["histories"], value), {"executed": 3, "completed": 3, "matched": 3})
        changed = report(path="rustEvm", transaction_id="tx-1")
        self.assertEqual(campaign.transaction_counts(changed["histories"], value), {"executed": 3, "completed": 3, "matched": 1})
        partial = incomplete(report(), value)
        self.assertEqual(campaign.transaction_counts(partial["histories"], value), {"executed": 3, "completed": 1, "matched": 1})
        self.assertEqual(campaign.transaction_counts({"directCore": report()["histories"]["directCore"]}, value),
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
            self.assertEqual(campaign.transaction_counts(analysis["histories"], value)["matched"], 0)

    def test_only_wholly_matched_scenarios_satisfy_coverage(self):
        value = case()
        for kind in ("matched", "synthetic", "resource", "real-mismatch"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                instance = campaign.Campaign(options(directory))
                instance.summary["coverage"].update(requiredInputs=["0", "1", "2"], requiredHelperCounts=[1], requiredTransactionCounts=[3])
                raw = incomplete(report(), value) if kind == "resource" else report(path="directCore", transaction_id="tx-0") if kind == "real-mismatch" else report()
                analysis = campaign.analyze(raw, value, "rustEvm" if kind == "synthetic" else None, "tx-1")
                with patch.object(instance, "prepare_cases", side_effect=lambda: instance.add_case(value, "policy")), \
                     patch.object(instance, "execute_case", side_effect=lambda _: saved_execution(instance, value, raw, analysis)), redirect_stdout(io.StringIO()):
                    instance.run()
                instance.checkpoint()
                self.assertEqual(instance.summary["coverage"]["generatedInputs"], ["0", "1", "2"])
                self.assertEqual(instance.summary["coverage"]["matchedInputs"], ["0", "1", "2"] if kind == "matched" else [])
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
        value["provenance"]["origin"] = {"kind": "storage-generated", "helperCount": 99,
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


class ManifestTests(unittest.TestCase):
    def test_fixed_manifest_and_invalid_bounds_or_ambiguous_sources(self):
        manifest = json.loads((ROOT / "scripts/semantic-storage-corpus.json").read_text())
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
        with tempfile.TemporaryDirectory() as directory, patch.object(sys, "argv", ["campaign", "--output", str(Path(directory) / "out"), "--test-field", "storage:0"]), \
             redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as stopped:
            campaign.main()
        self.assertEqual(stopped.exception.code, 2)


class RollbackCampaignTests(unittest.TestCase):
    def setUp(self):
        self.case = case()
        self.case["schema"] = campaign.adapter.ROLLBACK_CASE_SCHEMA
        self.case["storagePlan"]["schema"] = "solcore-lean.storage-rollback-plan.v1"
        self.case["contract"].update(name="SynthesizedRollback", deployPath=["SynthesizedRollbackDeploy"],
            runtimePath=["SynthesizedRollbackDeploy", "SynthesizedRollback"])
        self.raw = report(self.case)
        for history in self.raw["histories"].values():
            history["transactions"][1]["status"] = "reverted"
        self.raw["comparison"] = campaign.adapter.compare(self.raw["histories"], self.case)

    def test_matching_revert_is_a_completed_matched_transaction(self):
        self.assertEqual(campaign.transaction_counts(self.raw["histories"], self.case),
                         {"executed": 3, "completed": 3, "matched": 3})
        for history in self.raw["histories"].values():
            history["transactions"][1]["committedStorage"] = fixtures.slots(90, 1)
        self.assertEqual(campaign.transaction_counts(self.raw["histories"], self.case),
                         {"executed": 3, "completed": 3, "matched": 1})

    def test_coverage_requires_observed_matched_outcomes_and_patterns(self):
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-storage-rollback"))
            with self.assertRaises(ValueError):
                instance.record_coverage(self.case, "matched")
            instance.record_coverage(self.case, "matched", self.raw["histories"])
            self.assertEqual(instance.summary["coverage"]["matchedOutcomes"], ["returned", "reverted"])
            self.assertEqual(instance.summary["coverage"]["matchedCompletionPatterns"], ["returned,reverted,returned"])
            instance.summary["coverage"]["requiredCompletionPatterns"] = ["reverted,reverted,returned"]
            instance.checkpoint()
            self.assertTrue(campaign.missing_coverage(instance.summary))
            self.raw["histories"]["rustEvm"]["transactions"][1]["status"] = "returned"
            with self.assertRaises(ValueError):
                instance.record_coverage(self.case, "matched", self.raw["histories"])

    def test_reverted_payload_can_be_shrunk_but_not_changed_to_a_return(self):
        changed = campaign.analyze(self.raw, self.case, "rustEvm", "tx-1", "output")
        fingerprint = campaign.fingerprint(changed)
        self.assertEqual(fingerprint["pathShapes"]["rustEvm"]["status"], "reverted")
        self.assertEqual(changed["comparison"]["category"], "semantic-mismatch")
        value = copy.deepcopy(self.case)
        value["transactions"][1].update(input="0", calldata="0xa444f5e9" + "00" * 32)
        actual = report(value)
        self.assertFalse(campaign.same_failure(fingerprint, campaign.analyze(actual, value, "rustEvm", "tx-1", "output")))

    def test_profile_and_required_completion_patterns_are_not_interchangeable(self):
        manifest = json.loads((ROOT / "scripts/semantic-storage-corpus.json").read_text())
        manifest["profile"] = "stateful-storage-rollback"
        for entry in manifest["cases"]:
            if "storagePlan" in entry:
                entry["storagePlan"]["schema"] = "solcore-lean.storage-rollback-plan.v1"
        with self.assertRaises(ValueError):
            campaign.validate_manifest(manifest)
        manifest.update(requiredOutcomes=["returned", "reverted"], requiredCompletionPatterns=["returned,reverted,returned"])
        campaign.validate_manifest(manifest)
        for pattern in ("returned,out-of-fuel", "returned,reverted,returned,reverted", ""):
            with self.subTest(pattern=pattern), self.assertRaises(ValueError):
                campaign.validate_manifest({**manifest, "requiredCompletionPatterns": [pattern]})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory))
            with self.assertRaises(ValueError):
                instance.add_case(self.case, "wrong-profile")


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
            raw = report(candidate, path="directCore", transaction_id="tx-1", field="storage:1")
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
            process = subprocess.Popen([sys.executable, "-B", str(ROOT / "scripts/semantic-storage-campaign.py"),
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


if __name__ == "__main__":
    unittest.main()
