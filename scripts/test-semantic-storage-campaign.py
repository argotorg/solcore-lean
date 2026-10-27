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


def keyed_case(pairs=((5, 2), (0, 4), (fixtures.MAX_WORD, 3))):
    value = fixtures.keyed_case(pairs)
    value["keyedStoragePlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def keyed_report(value):
    histories = fixtures.keyed_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
            "comparison": campaign.adapter.compare(histories, value)}


class KeyedCampaignTests(unittest.TestCase):
    def test_static_alias_kinds_follow_counter_successor_and_repetition(self):
        maximum = fixtures.MAX_WORD
        for pairs, expected in ((((5, 2),), set()), (((0, 2),), {"key-counter"}), (((maximum, 2),), {"successor-counter"}),
                                (((7, 0), (7, 2)), {"repeated-key"}), (((8, 0), (7, 2)), {"successor-key"}),
                                (((5, 2), (0, 4), (maximum, 3)), {"key-counter", "successor-counter", "successor-key"})):
            with self.subTest(pairs=pairs):
                self.assertEqual(campaign.aliases(keyed_case(pairs)), expected)

    def test_keyed_manifest_requires_keys_and_aliases_only_for_its_profile(self):
        manifest = json.loads((ROOT / "scripts/semantic-keyed-storage-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        self.assertEqual(manifest["requiredAliases"], list(campaign.ALIASES))
        changes = [lambda m: m.pop("requiredKeys"), lambda m: m.update(requiredKeys=["00"]),
            lambda m: m.update(requiredAliases=["key-counter", "key-counter"]),
            lambda m: m.update(requiredAliases=["unknown"]),
            lambda m: m["cases"][0].update(expectedHistory={}),
            lambda m: m["cases"][0].update(storagePlan=m["cases"][0].pop("keyedStoragePlan")),
            lambda m: m.update(requiredOutcomes=["returned"])]
        for index, change in enumerate(changes):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.subTest(index=index), self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        storage = json.loads((ROOT / "scripts/semantic-storage-corpus.json").read_text())
        for change in (lambda m: m.update(requiredKeys=["0"]), lambda m: m.update(requiredAliases=[]),
                       lambda m: m["cases"][0].update(expectedHistory=[])):
            invalid = copy.deepcopy(storage)
            change(invalid)
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)

    def test_synthetic_slot_injection_is_by_declared_slot_name(self):
        value = keyed_case()
        raw = keyed_report(value)
        self.assertEqual(raw["comparison"]["category"], "matched")
        original = copy.deepcopy(raw)
        changed = campaign.analyze(raw, value, "rustEvm", "tx-1", "storage:5")
        self.assertEqual(raw, original)
        self.assertEqual((changed["comparison"]["category"], changed["comparison"]["transactionId"]), ("semantic-mismatch", "tx-1"))
        fingerprint = campaign.fingerprint(changed)
        self.assertEqual((fingerprint["storageSlots"], fingerprint["fields"], fingerprint["undeclaredPaths"]),
                         (["5"], ["committedStorage"], []))
        self.assertFalse(campaign.same_failure(fingerprint, campaign.analyze(raw, value, "rustEvm", "tx-1", "storage:6")))
        self.assertTrue(campaign.same_failure(fingerprint, campaign.analyze(keyed_report(value), value, "rustEvm", "tx-1", "storage:5")))
        for field in ("storage:05", "slot:5"):
            with self.subTest(field=field), self.assertRaises(ValueError):
                campaign.analyze(raw, value, "rustEvm", "tx-1", field)
        with self.assertRaises(ValueError):
            campaign.analyze(report(), case(), "rustEvm", "tx-1", "storage:5")
        # A reduced key sequence that no longer declares the slot cannot keep
        # the synthetic finding; it is an ordinary actual analysis.
        reduced = keyed_case(((7, 2), (0, 4), (fixtures.MAX_WORD, 3)))
        dropped = campaign.analyze(keyed_report(reduced), reduced, "rustEvm", "tx-1", "storage:5")
        self.assertFalse(dropped["synthetic"])
        self.assertEqual(dropped["comparison"]["category"], "matched")
        self.assertFalse(campaign.same_failure(fingerprint, dropped))

    def test_original_scenario_must_declare_the_selected_synthetic_slot(self):
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-keyed-storage", test_perturb_path="rustEvm",
                                                 test_transaction_id="tx-1", test_field="storage:2"))
            with patch.object(instance, "prepare_cases", side_effect=lambda: instance.add_case(keyed_case(), "policy")), \
                 patch.object(instance, "execute_case") as execute, self.assertRaises(ValueError):
                instance.run()
            execute.assert_not_called()

    def test_undeclared_paths_join_only_the_keyed_failure_identity(self):
        value = keyed_case()
        raw = keyed_report(value)
        raw["histories"]["importedHull"]["transactions"][0]["undeclaredStorage"] = [{"slot": "9", "value": "1"}]
        raw["comparison"] = campaign.adapter.compare(raw["histories"], value)
        fingerprint = campaign.fingerprint(campaign.analyze(raw, value))
        self.assertEqual((fingerprint["category"], fingerprint["fields"], fingerprint["undeclaredPaths"], fingerprint["storageSlots"]),
                         ("semantic-mismatch", ["undeclaredStorage"], ["importedHull"], []))
        legacy = campaign.fingerprint(campaign.analyze(report(), case(), "rustEvm", "tx-1", "storage:0"))
        self.assertNotIn("undeclaredPaths", legacy)
        self.assertEqual(legacy["storageSlots"], ["0"])

    def test_keyed_prefix_counts_exclude_undeclared_storage(self):
        value = keyed_case()
        raw = keyed_report(value)
        self.assertEqual(campaign.transaction_counts(raw["histories"], value), {"executed": 3, "completed": 3, "matched": 3})
        raw["histories"]["rustEvm"]["transactions"][1]["undeclaredStorage"] = [{"slot": "9", "value": "1"}]
        self.assertEqual(campaign.transaction_counts(raw["histories"], value), {"executed": 3, "completed": 3, "matched": 1})
        raw = keyed_report(value)
        raw["histories"]["importedHull"]["initialUndeclaredStorage"] = [{"slot": "9", "value": "1"}]
        self.assertEqual(campaign.transaction_counts(raw["histories"], value)["matched"], 0)

    def test_keyed_coverage_records_keys_and_aliases_from_matched_scenarios(self):
        value = keyed_case()
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-keyed-storage"))
            self.assertIn("requiredAliases", instance.summary["coverage"])
            instance.summary["coverage"].update(requiredKeys=["0", "5", str(fixtures.MAX_WORD)], requiredAliases=list(campaign.ALIASES))
            instance.record_coverage(value, "generated")
            instance.record_coverage(value, "matched", keyed_report(value)["histories"])
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual(coverage["matchedKeys"], ["0", "5", str(fixtures.MAX_WORD)])
            self.assertEqual(coverage["matchedAliases"], ["key-counter", "successor-counter", "successor-key"])
            self.assertEqual(coverage["missingAliases"], ["repeated-key"])
        with tempfile.TemporaryDirectory() as directory:
            legacy = campaign.Campaign(options(directory))
            self.assertNotIn("requiredKeys", legacy.summary["coverage"])

    def test_keyed_cli_accepts_named_slots_but_two_slot_profiles_keep_their_fields(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "case.json"
            path.write_text(json.dumps(case()))
            for field in ("storage:5", "storage:", "slot:0"):
                with self.subTest(field=field), patch.object(sys, "argv", ["campaign", "--output", str(Path(directory) / field.replace(":", "-")),
                        "--case", str(path), "--test-perturb-path", "rustEvm", "--test-field", field]), \
                        redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as stopped:
                    campaign.main()
                self.assertEqual(stopped.exception.code, 2)
        self.assertTrue(campaign.TEST_FIELD.fullmatch("storage:" + str(fixtures.MAX_WORD)))


def array_case(rows=((0, (1, 3, 7)), (1, (fixtures.MAX_WORD,)), (2, ()))):
    value = fixtures.array_case(rows)
    value["dynamicArrayPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def array_report(value):
    histories = fixtures.array_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
            "comparison": campaign.adapter.compare(histories, value)}


class DynamicArrayCampaignTests(unittest.TestCase):
    def test_array_inputs_are_elements_and_lengths_are_their_own_dimension(self):
        value = array_case()
        self.assertEqual(campaign.inputs(value), {"1", "3", "7", str(fixtures.MAX_WORD)})
        self.assertEqual(campaign.dimensions("stateful-dynamic-array"), campaign.DIMENSIONS + ("Lengths",))
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-dynamic-array"))
            instance.summary["coverage"].update(requiredLengths=[0, 1, 2, 3], requiredInputs=["0", "1"])
            instance.record_coverage(value, "generated")
            instance.record_coverage(value, "matched", array_report(value)["histories"])
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedLengths"], coverage["missingLengths"]), ([0, 1, 3], [2]))
            self.assertEqual(coverage["missingInputs"], ["0"])
            self.assertNotIn("requiredKeys", coverage)

    def test_array_manifest_requires_lengths_only_for_its_profile(self):
        manifest = json.loads((ROOT / "scripts/semantic-dynamic-array-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        for change in (lambda m: m.pop("requiredLengths"), lambda m: m.update(requiredLengths=[4]),
                       lambda m: m.update(requiredLengths=[1, 1]), lambda m: m.update(requiredLengths=[True]),
                       lambda m: m.update(requiredKeys=["0"]),
                       lambda m: m["cases"][0].update(keyedStoragePlan=m["cases"][0].pop("dynamicArrayPlan"))):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        keyed = json.loads((ROOT / "scripts/semantic-keyed-storage-corpus.json").read_text())
        keyed["requiredLengths"] = [0]
        with self.assertRaises(ValueError):
            campaign.validate_manifest(keyed)

    def test_array_slots_are_named_in_fingerprints_and_injection(self):
        value = array_case()
        raw = array_report(value)
        changed = campaign.analyze(raw, value, "importedHull", "tx-0", "storage:3")
        fingerprint = campaign.fingerprint(changed)
        self.assertEqual((fingerprint["storageSlots"], fingerprint["undeclaredPaths"], fingerprint["transactionId"]), (["3"], [], "tx-0"))
        self.assertFalse(campaign.analyze(raw, value, "importedHull", "tx-0", "storage:5")["synthetic"])
        self.assertEqual(campaign.transaction_counts(raw["histories"], value), {"executed": 3, "completed": 3, "matched": 3})



def log_case(sites=((1, 2, 1), (3, 0, 2)), rows=((2, 5), (11, 1), (8, fixtures.HIGH_WORD))):
    value = fixtures.log_case(sites, rows)
    value["logPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.LOG_VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def log_report(value):
    histories = fixtures.log_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
            "comparison": campaign.adapter.compare(histories, value)}


class LogCampaignTests(unittest.TestCase):
    def test_log_dimensions_come_from_static_shapes_or_actual_core_logs(self):
        value = log_case()
        self.assertEqual(campaign.dimensions("stateful-logs"),
                         campaign.DIMENSIONS + ("LogCounts", "TopicArities", "DataSizes", "DiscardedLogCounts"))
        self.assertEqual(campaign.versions("stateful-logs"), campaign.VERSIONS + ("framingVersion",))
        self.assertEqual(campaign.inputs(value), {"5", "1", str(fixtures.HIGH_WORD)})
        statuses = ["returned", "reverted", "returned"]
        expected = {"LogCounts": {0, 1}, "TopicArities": {0, 2}, "DataSizes": {32, 64}, "DiscardedLogCounts": {2}}
        self.assertEqual(campaign.log_coverage(value, statuses), expected)
        raw = log_report(value)
        self.assertEqual(campaign.log_coverage(value, statuses, raw["histories"]["directCore"]["transactions"]), expected)
        # Actual coverage counts the logs original Core committed, not the plan.
        raw["histories"]["directCore"]["transactions"][0]["logs"].append(fixtures.log_entry([1, 2, 3, 4], []))
        self.assertEqual(campaign.log_coverage(value, statuses, raw["histories"]["directCore"]["transactions"])["TopicArities"], {0, 2, 4})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-logs"))
            instance.summary["coverage"].update(requiredLogCounts=[0, 1, 2], requiredTopicArities=[0, 2, 4],
                                                requiredDataSizes=[0, 32, 64], requiredDiscardedLogCounts=[2, 3])
            instance.record_coverage(value, "generated")
            instance.record_coverage(value, "matched", log_report(value)["histories"])
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedLogCounts"], coverage["matchedTopicArities"], coverage["matchedDataSizes"],
                              coverage["matchedDiscardedLogCounts"]), ([0, 1], [0, 2], [32, 64], [2]))
            self.assertEqual((coverage["missingLogCounts"], coverage["missingTopicArities"], coverage["missingDataSizes"],
                              coverage["missingDiscardedLogCounts"]), ([2], [4], [0], [3]))
            self.assertTrue(campaign.missing_coverage(instance.summary))
        with tempfile.TemporaryDirectory() as directory:
            self.assertNotIn("requiredTopicArities", campaign.Campaign(options(directory, profile="stateful-keyed-storage")).summary["coverage"])

    def test_log_manifest_requires_log_dimensions_only_for_its_profile(self):
        manifest = json.loads((ROOT / "scripts/semantic-log-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        self.assertEqual((manifest["requiredLogCounts"], manifest["requiredTopicArities"], manifest["requiredDataSizes"],
                          manifest["requiredDiscardedLogCounts"]), ([0, 1, 2, 3], [0, 1, 2, 3, 4], [0, 32, 64], [0, 1, 2, 3]))
        changes = [lambda m: m.pop("requiredTopicArities"), lambda m: m.update(requiredTopicArities=[5]),
            lambda m: m.update(requiredDataSizes=[16]), lambda m: m.update(requiredLogCounts=[4]),
            lambda m: m.update(requiredDiscardedLogCounts=[]), lambda m: m.update(requiredLogCounts=[1, 1]),
            lambda m: m.update(requiredDataSizes=[True]), lambda m: m.pop("framingVersion"),
            lambda m: m["cases"][0].update(keyedStoragePlan=m["cases"][0].pop("logPlan"))]
        for index, change in enumerate(changes):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.subTest(index=index), self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        keyed = json.loads((ROOT / "scripts/semantic-keyed-storage-corpus.json").read_text())
        for change in (lambda m: m.update(requiredTopicArities=[0]), lambda m: m.update(framingVersion="core-word-log-framing-v1")):
            invalid = copy.deepcopy(keyed)
            change(invalid)
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)

    def test_synthetic_log_injection_perturbs_one_committed_log(self):
        value = log_case()
        raw = log_report(value)
        self.assertEqual(raw["comparison"]["category"], "matched")
        original = copy.deepcopy(raw)
        changed = campaign.analyze(raw, value, "importedHull", "tx-0", "log")
        self.assertEqual(raw, original)
        self.assertTrue(changed["synthetic"])
        self.assertEqual((changed["comparison"]["category"], changed["comparison"]["transactionId"], changed["comparison"]["fields"]),
                         ("semantic-mismatch", "tx-0", ["logs"]))
        self.assertEqual(changed["histories"]["importedHull"]["transactions"][0]["logs"][0]["topics"][0],
                         str(int(raw["histories"]["importedHull"]["transactions"][0]["logs"][0]["topics"][0]) ^ 1))
        fingerprint = campaign.fingerprint(changed)
        self.assertEqual((fingerprint["fields"], fingerprint["logPaths"], fingerprint["storageSlots"]), (["logs"], [], []))
        self.assertTrue(campaign.same_failure(fingerprint, campaign.analyze(log_report(value), value, "importedHull", "tx-0", "log")))
        # A topic-free log carries the change in its last data byte.
        data = campaign.analyze(raw, value, "rustEvm", "tx-2", "log")
        before = raw["histories"]["rustEvm"]["transactions"][2]["logs"][0]["data"]
        after = data["histories"]["rustEvm"]["transactions"][2]["logs"][0]["data"]
        self.assertEqual((after[:-2], int(after[-2:], 16)), (before[:-2], int(before[-2:], 16) ^ 1))
        # A reverted transaction, or one whose only log is LOG0 without data,
        # cannot keep the synthetic finding.
        for reduced, transaction in ((value, "tx-1"), (log_case(sites=((1, 0, 0),), rows=((2, 0),)), "tx-0")):
            dropped = campaign.analyze(log_report(reduced), reduced, "rustEvm", transaction, "log")
            with self.subTest(transaction=transaction):
                self.assertFalse(dropped["synthetic"])
                self.assertEqual(dropped["comparison"]["category"], "matched")
        with self.assertRaises(ValueError):
            campaign.analyze(keyed_report(keyed_case()), keyed_case(), "rustEvm", "tx-1", "log")

    def test_log_prefix_counts_require_shapes_and_no_deployment_logs(self):
        value = log_case()
        raw = log_report(value)
        self.assertEqual(campaign.transaction_counts(raw["histories"], value), {"executed": 3, "completed": 3, "matched": 3})
        for history in raw["histories"].values():
            history["transactions"][2]["logs"] = []
        self.assertEqual(campaign.transaction_counts(raw["histories"], value)["matched"], 2)
        raw = log_report(value)
        raw["histories"]["importedHull"]["initialLogs"] = [fixtures.log_entry([], [])]
        self.assertEqual(campaign.transaction_counts(raw["histories"], value)["matched"], 0)
        raw = log_report(value)
        raw["histories"]["rustEvm"]["transactions"][0]["logs"][0]["data"] = "0x"
        self.assertEqual(campaign.transaction_counts(raw["histories"], value)["matched"], 0)
        raw = log_report(value)
        raw["histories"]["directCore"]["bindings"]["address"] = "0101"
        self.assertEqual(campaign.transaction_counts(raw["histories"], value), {"executed": 0, "completed": 0, "matched": 0})

    def test_log_failure_identity_names_log_paths_only_for_log_histories(self):
        value = log_case()
        raw = log_report(value)
        raw["histories"]["rustEvm"]["chainLogs"].pop()
        raw["comparison"] = campaign.adapter.compare(raw["histories"], value)
        fingerprint = campaign.fingerprint(campaign.analyze(raw, value))
        self.assertEqual((fingerprint["stage"], fingerprint["fields"], fingerprint["logPaths"]),
                         ("committed-log-history", ["chainLogs"], ["rustEvm"]))
        self.assertNotIn("logPaths", campaign.fingerprint(campaign.analyze(keyed_report(keyed_case()), keyed_case())))

    def test_log_cli_field_requires_the_log_profile(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "case.json"
            path.write_text(json.dumps(keyed_case()))
            with patch.object(sys, "argv", ["campaign", "--output", str(Path(directory) / "run"), "--case", str(path),
                    "--test-perturb-path", "rustEvm", "--test-field", "log"]), \
                    redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as stopped:
                campaign.main()
            self.assertEqual(stopped.exception.code, 2)
        self.assertTrue(campaign.TEST_FIELD.fullmatch("log"))
        self.assertFalse(campaign.TEST_FIELD.fullmatch("logs"))



def common_digest(value):
    return campaign.common.digest(campaign.common.json_bytes(value))


def value_case(deployment=5, rows=((0, 0, 7), (1, 1, 2**64), (0, 3, 1))):
    value = fixtures.value_case(deployment, rows)
    value["callValuePlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def value_report(value):
    histories = fixtures.value_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
            "comparison": campaign.adapter.compare(histories, value)}


class CallValueCampaignTests(unittest.TestCase):
    def test_value_dimensions_record_values_refunds_and_deployment(self):
        value = value_case()
        self.assertEqual(campaign.dimensions("stateful-call-value"),
                         campaign.DIMENSIONS + ("Values", "RevertedValues", "DeploymentValues"))
        self.assertEqual(campaign.versions("stateful-call-value"), campaign.VERSIONS)
        self.assertEqual(campaign.inputs(value), {"0", "1", "3"})
        statuses = ["returned", "reverted", "returned"]
        self.assertEqual(campaign.value_coverage(value, statuses),
                         {"Values": {"7", str(2**64), "1"}, "RevertedValues": {str(2**64)}, "DeploymentValues": {"5"}})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-call-value"))
            instance.summary["coverage"].update(requiredValues=["0", "1", "7"], requiredRevertedValues=["0", str(2**64)],
                                                requiredDeploymentValues=["0", "5"])
            instance.record_coverage(value, "generated")
            instance.record_coverage(value, "matched", value_report(value)["histories"])
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedValues"], coverage["matchedRevertedValues"], coverage["matchedDeploymentValues"]),
                             (["1", "7", str(2**64)], [str(2**64)], ["5"]))
            self.assertEqual((coverage["missingValues"], coverage["missingRevertedValues"], coverage["missingDeploymentValues"]),
                             (["0"], ["0"], ["0"]))
        with tempfile.TemporaryDirectory() as directory:
            self.assertNotIn("requiredValues", campaign.Campaign(options(directory, profile="stateful-logs")).summary["coverage"])

    def test_value_manifest_requires_value_dimensions_only_for_its_profile(self):
        manifest = json.loads((ROOT / "scripts/semantic-call-value-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        self.assertEqual(manifest["requiredDeploymentValues"], ["0", "5"])
        changes = [lambda m: m.pop("requiredValues"), lambda m: m.update(requiredValues=["07"]),
            lambda m: m.update(requiredRevertedValues=[]), lambda m: m.update(requiredDeploymentValues=["5", "5"]),
            lambda m: m.update(requiredValues=[7]),
            lambda m: m["cases"][0].update(logPlan=m["cases"][0].pop("callValuePlan"))]
        for index, change in enumerate(changes):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.subTest(index=index), self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        logs = json.loads((ROOT / "scripts/semantic-log-corpus.json").read_text())
        logs["requiredValues"] = ["0"]
        with self.assertRaises(ValueError):
            campaign.validate_manifest(logs)

    def test_synthetic_balance_injection_perturbs_one_committed_balance(self):
        value = value_case()
        raw = value_report(value)
        self.assertEqual(raw["comparison"]["category"], "matched")
        original = copy.deepcopy(raw)
        changed = campaign.analyze(raw, value, "importedHull", "tx-2", "balance")
        self.assertEqual(raw, original)
        self.assertTrue(changed["synthetic"])
        self.assertEqual((changed["comparison"]["category"], changed["comparison"]["transactionId"], changed["comparison"]["fields"]),
                         ("semantic-mismatch", "tx-2", ["committedBalance"]))
        self.assertEqual(changed["histories"]["importedHull"]["finalBalance"], str(int(raw["histories"]["importedHull"]["finalBalance"]) ^ 1))
        fingerprint = campaign.fingerprint(changed)
        self.assertEqual((fingerprint["fields"], fingerprint["storageSlots"], fingerprint["undeclaredPaths"]), (["committedBalance"], [], []))
        self.assertTrue(campaign.same_failure(fingerprint, campaign.analyze(value_report(value), value, "importedHull", "tx-2", "balance")))
        reduced = value_case(rows=((0, 0, 7),))
        dropped = campaign.analyze(value_report(reduced), reduced, "importedHull", "tx-2", "balance")
        self.assertFalse(dropped["synthetic"])
        for other, report_value in ((keyed_case(), keyed_report(keyed_case())), (log_case(), log_report(log_case()))):
            with self.subTest(schema=other["schema"]), self.assertRaises(ValueError):
                campaign.analyze(report_value, other, "rustEvm", "tx-1", "balance")

    def test_value_prefix_counts_require_funded_deployment_and_refunds(self):
        value = value_case()
        raw = value_report(value)
        self.assertEqual(campaign.transaction_counts(raw["histories"], value), {"executed": 3, "completed": 3, "matched": 3})
        for history in raw["histories"].values():
            history["transactions"][1]["committedBalance"] = str(12 + 2**64)
        self.assertEqual(campaign.transaction_counts(raw["histories"], value)["matched"], 1)
        raw = value_report(value)
        for history in raw["histories"].values():
            history["initialBalance"] = "0"
        self.assertEqual(campaign.transaction_counts(raw["histories"], value)["matched"], 0)

    def test_deployment_value_is_part_of_the_reduction_identity(self):
        value = value_case()
        lowered = copy.deepcopy(value)
        lowered["callValuePlan"]["deploymentValue"] = "0"
        self.assertNotEqual(campaign.case_hash(value), campaign.case_hash(lowered))
        legacy = log_case()
        self.assertEqual(campaign.case_hash(legacy),
                         common_digest({key: legacy[key] for key in ("program", "transactions")}))

    def test_value_cli_field_requires_the_call_value_profile(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "case.json"
            path.write_text(json.dumps(log_case()))
            with patch.object(sys, "argv", ["campaign", "--output", str(Path(directory) / "run"), "--case", str(path),
                    "--test-perturb-path", "rustEvm", "--test-field", "balance"]), \
                    redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as stopped:
                campaign.main()
            self.assertEqual(stopped.exception.code, 2)
        self.assertTrue(campaign.TEST_FIELD.fullmatch("balance"))


def bytes_case(rows=((0, bytes([1, 3, 7])), (1, b"\xff" * 33), (2, b""))):
    value = fixtures.bytes_case(rows)
    value["bytesPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def bytes_report(value):
    histories = fixtures.bytes_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
            "comparison": campaign.adapter.compare(histories, value)}


class BytesCampaignTests(unittest.TestCase):
    def test_bytes_inputs_are_chunks_and_lengths_are_their_own_dimensions(self):
        value = bytes_case()
        self.assertEqual(campaign.dimensions("stateful-bytes"), campaign.DIMENSIONS + ("PayloadLengths", "RevertedPayloadLengths"))
        self.assertEqual(campaign.versions("stateful-bytes"), campaign.VERSIONS)
        self.assertEqual(campaign.inputs(value), {str(int.from_bytes(bytes([1, 3, 7]) + bytes(29), "big")),
                                                  str(fixtures.MAX_WORD), str(0xff << 248)})
        self.assertEqual(campaign.bytes_coverage(value, ["returned", "reverted", "returned"]),
                         {"PayloadLengths": {3, 33, 0}, "RevertedPayloadLengths": {33}})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-bytes"))
            instance.summary["coverage"].update(requiredPayloadLengths=[0, 1, 3, 33], requiredRevertedPayloadLengths=[0, 33],
                                                requiredInputs=["0", str(fixtures.MAX_WORD)])
            instance.record_coverage(value, "generated")
            instance.record_coverage(value, "matched", bytes_report(value)["histories"])
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedPayloadLengths"], coverage["matchedRevertedPayloadLengths"]), ([0, 3, 33], [33]))
            self.assertEqual((coverage["missingPayloadLengths"], coverage["missingRevertedPayloadLengths"], coverage["missingInputs"]),
                             ([1], [0], ["0"]))
            self.assertNotIn("requiredLengths", coverage)
        with tempfile.TemporaryDirectory() as directory:
            self.assertNotIn("requiredPayloadLengths", campaign.Campaign(options(directory, profile="stateful-dynamic-array")).summary["coverage"])

    def test_bytes_manifest_requires_payload_lengths_only_for_its_profile(self):
        manifest = json.loads((ROOT / "scripts/semantic-bytes-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        self.assertEqual(manifest["requiredPayloadLengths"], [0, 1, 17, 31, 32, 33, 48, 63, 64])
        changes = [lambda m: m.pop("requiredPayloadLengths"), lambda m: m.update(requiredPayloadLengths=[65]),
            lambda m: m.update(requiredRevertedPayloadLengths=[]), lambda m: m.update(requiredPayloadLengths=[1, 1]),
            lambda m: m.update(requiredRevertedPayloadLengths=["0"]), lambda m: m.update(requiredLengths=[0]),
            lambda m: m["cases"][0].update(dynamicArrayPlan=m["cases"][0].pop("bytesPlan"))]
        for index, change in enumerate(changes):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.subTest(index=index), self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        array = json.loads((ROOT / "scripts/semantic-dynamic-array-corpus.json").read_text())
        array["requiredPayloadLengths"] = [0]
        with self.assertRaises(ValueError):
            campaign.validate_manifest(array)

    def test_bytes_slots_are_named_in_fingerprints_injection_and_prefix_counts(self):
        value = bytes_case()
        raw = bytes_report(value)
        self.assertEqual(raw["comparison"]["category"], "matched")
        changed = campaign.analyze(raw, value, "importedHull", "tx-2", "storage:4")
        fingerprint = campaign.fingerprint(changed)
        self.assertEqual((fingerprint["storageSlots"], fingerprint["undeclaredPaths"], fingerprint["transactionId"]), (["4"], [], "tx-2"))
        self.assertTrue(changed["synthetic"])
        self.assertFalse(campaign.analyze(raw, value, "importedHull", "tx-0", "storage:5")["synthetic"])
        self.assertEqual(campaign.transaction_counts(raw["histories"], value), {"executed": 3, "completed": 3, "matched": 3})
        for history in raw["histories"].values():
            history["transactions"][0]["committedStorage"][3]["value"] = "4"
        self.assertEqual(campaign.transaction_counts(raw["histories"], value)["matched"], 0)
        with self.assertRaises(ValueError):
            campaign.analyze(bytes_report(value), value, "rustEvm", "tx-1", "balance")


def mapping_case(rows=((0, 5, 7), (1, 6, 3), (2, fixtures.MAX_WORD, 1))):
    value = fixtures.mapping_case(rows)
    value["mappingPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def mapping_report(value):
    histories = fixtures.mapping_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
            "comparison": campaign.adapter.compare(histories, value)}


class MappingCampaignTests(unittest.TestCase):
    def test_mapping_aliases_follow_repetition_succession_and_wrapping(self):
        self.assertEqual(campaign.dimensions("stateful-mapping"), campaign.KEYED_DIMENSIONS)
        self.assertEqual(campaign.versions("stateful-mapping"), campaign.VERSIONS)
        maximum = fixtures.MAX_WORD
        # Entry slots never meet the counter, so key zero is no alias here.
        for rows, expected in ((((0, 5, 7),), set()), (((0, 0, 1),), set()), (((0, maximum, 1),), {"wrapped-successor"}),
                               (((0, 5, 0), (2, 5, 1)), {"repeated-key"}), (((0, 6, 0), (0, 5, 1)), {"successor-key"}),
                               (((0, maximum, 1), (0, 0, 1)), {"successor-key", "wrapped-successor"}),
                               (((0, 5, 7), (1, 6, 3), (2, maximum, 1)), {"successor-key", "wrapped-successor"})):
            with self.subTest(rows=rows):
                self.assertEqual(campaign.aliases(mapping_case(rows)), expected)

    def test_mapping_manifest_requires_keys_and_mapping_aliases(self):
        manifest = json.loads((ROOT / "scripts/semantic-mapping-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        self.assertEqual(manifest["requiredAliases"], list(campaign.MAPPING_ALIASES))
        changes = [lambda m: m.pop("requiredKeys"), lambda m: m.pop("requiredAliases"), lambda m: m.update(requiredKeys=["00"]),
            lambda m: m.update(requiredAliases=["key-counter"]), lambda m: m.update(requiredAliases=["repeated-key", "repeated-key"]),
            lambda m: m.update(requiredLengths=[0]), lambda m: m.update(requiredOutcomes=["returned"]),
            lambda m: m["cases"][0].update(keyedStoragePlan=m["cases"][0].pop("mappingPlan")),
            lambda m: m["cases"][0].update(expectedHistory={})]
        for index, change in enumerate(changes):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.subTest(index=index), self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        keyed = json.loads((ROOT / "scripts/semantic-keyed-storage-corpus.json").read_text())
        keyed["requiredAliases"] = ["wrapped-successor"]
        with self.assertRaises(ValueError):
            campaign.validate_manifest(keyed)

    def test_mapping_coverage_records_keys_and_aliases_from_matched_scenarios(self):
        value = mapping_case()
        maximum = str(fixtures.MAX_WORD)
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-mapping"))
            self.assertIn("requiredAliases", instance.summary["coverage"])
            instance.summary["coverage"].update(requiredKeys=["0", "5", "6", maximum], requiredAliases=list(campaign.MAPPING_ALIASES))
            instance.record_coverage(value, "generated")
            instance.record_coverage(value, "matched", mapping_report(value)["histories"])
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedKeys"], coverage["matchedAliases"]), (["5", "6", maximum], ["successor-key", "wrapped-successor"]))
            self.assertEqual((coverage["missingKeys"], coverage["missingAliases"]), (["0"], ["repeated-key"]))

    def test_mapping_entry_slots_are_named_in_fingerprints_injection_and_prefix_counts(self):
        value = mapping_case()
        raw = mapping_report(value)
        self.assertEqual(raw["comparison"]["category"], "matched")
        slot = str(fixtures.CAST_ENTRY_SLOTS[5])
        changed = campaign.analyze(raw, value, "rustEvm", "tx-0", "storage:" + slot)
        self.assertTrue(changed["synthetic"])
        fingerprint = campaign.fingerprint(changed)
        self.assertEqual((fingerprint["storageSlots"], fingerprint["fields"], fingerprint["undeclaredPaths"], fingerprint["transactionId"]),
                         ([slot], ["committedStorage"], [], "tx-0"))
        self.assertTrue(campaign.same_failure(fingerprint, campaign.analyze(mapping_report(value), value, "rustEvm", "tx-0", "storage:" + slot)))
        # Solidity's slot of key five is undeclared and cannot carry a synthetic difference.
        self.assertFalse(campaign.analyze(raw, value, "rustEvm", "tx-0", "storage:" + str(fixtures.CAST_SOLIDITY_SLOT_5))["synthetic"])
        # A reduced key that no longer declares the entry slot cannot keep the finding.
        reduced = mapping_case(((0, 0, 7), (1, 6, 3), (2, fixtures.MAX_WORD, 1)))
        dropped = campaign.analyze(mapping_report(reduced), reduced, "rustEvm", "tx-0", "storage:" + slot)
        self.assertFalse(dropped["synthetic"])
        self.assertFalse(campaign.same_failure(fingerprint, dropped))
        self.assertEqual(campaign.transaction_counts(raw["histories"], value), {"executed": 3, "completed": 3, "matched": 3})
        raw["histories"]["importedHull"]["transactions"][1]["undeclaredStorage"] = [{"slot": str(fixtures.CAST_SOLIDITY_SLOT_5), "value": "1"}]
        self.assertEqual(campaign.transaction_counts(raw["histories"], value)["matched"], 1)

    def test_mapping_shrink_requests_at_most_its_native_batch(self):
        slot = "storage:" + str(fixtures.CAST_ENTRY_SLOTS[5])
        for profile, value, candidates, expected in (("stateful-mapping", mapping_case(), 64, 16), ("stateful-mapping", mapping_case(), 8, 8),
                                                     ("stateful-keyed-storage", keyed_case(), 64, 40)):
            with self.subTest(profile=profile, candidates=candidates), tempfile.TemporaryDirectory() as directory:
                instance = campaign.Campaign(options(directory, profile=profile, shrink_attempts=40, shrink_candidates=candidates))
                raw = mapping_report(value) if profile == "stateful-mapping" else keyed_report(value)
                analysis = campaign.analyze(raw, value, "rustEvm", "tx-0", slot if profile == "stateful-mapping" else "storage:5")
                folder, _, _ = saved_execution(instance, value, raw, analysis)
                finding = instance.retain_finding(0, folder, value, analysis)
                with patch.object(instance, "tool", return_value={"schema": instance.specification["corpusSchema"], "cases": []}) as tool:
                    instance.shrink(value, finding)
                self.assertEqual(tool.call_args.args[0][2], expected)
                self.assertEqual(campaign.common.read_json(Path(directory) / finding["history"])["status"], "no-preserving-candidate")


def ledger_case(rows=None):
    value = fixtures.ledger_case() if rows is None else fixtures.ledger_case(rows)
    value["ledgerPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def ledger_report(value):
    histories = fixtures.ledger_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
            "comparison": campaign.adapter.compare(histories, value)}


class LedgerCampaignTests(unittest.TestCase):
    def test_ledger_dimensions_and_static_aliases(self):
        self.assertEqual(campaign.dimensions("stateful-ledger"), campaign.DIMENSIONS + (
            "Senders", "Recipients", "Amounts", "SenderCounts", "RevertCauses", "Aliases"))
        self.assertEqual(campaign.versions("stateful-ledger"), campaign.VERSIONS)
        s0, s1, s2 = fixtures.LEDGER_SENDERS
        maximum = fixtures.MAX_WORD
        for rows, expected in ((((0, 0, 0, 1, 1),), set()), (((0, 0, s0, 1, 1),), {"self-transfer"}),
                               (((0, 0, s1, 1, 1), (1, 0, 0, 1, 1)), {"received-then-sent"}),
                               (((1, 0, 0, 1, 1), (0, 0, s1, 1, 1)), set()),
                               (((2, 0, maximum, 1, 1), (2, 0, 2**160 - 1, 1, 1)), {"repeated-sender"}),
                               (((0, 0, s1, 1, 7), (1, 0, s1, 2**64, 3), (2, 1, maximum, 7, 7)),
                                {"received-then-sent", "self-transfer"})):
            with self.subTest(rows=rows):
                self.assertEqual(campaign.aliases(ledger_case(rows)), expected)
        value = ledger_case()
        statuses = [row["status"] for row in fixtures.ledger_history(value, "directCore")["transactions"]]
        self.assertEqual(statuses, ["returned", "reverted", "reverted"])
        self.assertEqual(campaign.ledger_coverage(value, statuses), {
            "Senders": {str(s0), str(s1), str(s2)}, "Recipients": {str(s1), str(maximum)}, "Amounts": {"1", str(2**64), "7"},
            "SenderCounts": {3}, "RevertCauses": {"insufficient-balance", "odd-flags"}})

    def test_ledger_manifest_requires_its_dimensions_only_for_its_profile(self):
        manifest = json.loads((ROOT / "scripts/semantic-ledger-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        self.assertEqual(manifest["requiredAliases"], list(campaign.LEDGER_ALIASES))
        self.assertEqual(manifest["requiredSenders"], list(campaign.adapter.LEDGER_SENDERS))
        changes = [lambda m: m.pop("requiredSenders"), lambda m: m.update(requiredSenders=["1"]),
            lambda m: m.update(requiredRecipients=["00"]), lambda m: m.update(requiredAmounts=[]),
            lambda m: m.update(requiredSenderCounts=[4]), lambda m: m.update(requiredRevertCauses=["unknown"]),
            lambda m: m.update(requiredRevertCauses=[]), lambda m: m.update(requiredAliases=["repeated-key"]),
            lambda m: m.update(requiredKeys=["0"]), lambda m: m.update(requiredLengths=[0]),
            lambda m: m.update(requiredOutcomes=["returned"]),
            lambda m: m["cases"][0].update(mappingPlan=m["cases"][0].pop("ledgerPlan")),
            lambda m: m["cases"][0].update(expectedHistory={})]
        for index, change in enumerate(changes):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.subTest(index=index), self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        mapping = json.loads((ROOT / "scripts/semantic-mapping-corpus.json").read_text())
        for key, value in (("requiredSenders", list(campaign.adapter.LEDGER_SENDERS)), ("requiredRevertCauses", ["odd-flags"])):
            invalid = copy.deepcopy(mapping)
            invalid[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)

    def test_ledger_coverage_counts_insufficient_balances_only_from_matched_histories(self):
        value = ledger_case()
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-ledger"))
            self.assertIn("requiredRevertCauses", instance.summary["coverage"])
            instance.summary["coverage"].update(requiredRevertCauses=list(campaign.LEDGER_CAUSES), requiredSenderCounts=[1, 2, 3],
                                                requiredAliases=list(campaign.LEDGER_ALIASES))
            instance.record_coverage(value, "generated")
            self.assertEqual(instance.summary["coverage"]["generatedRevertCauses"], ["odd-flags"])
            instance.record_coverage(value, "matched", ledger_report(value)["histories"])
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual(coverage["matchedRevertCauses"], ["insufficient-balance", "odd-flags"])
            self.assertEqual((coverage["missingRevertCauses"], coverage["missingSenderCounts"], coverage["missingAliases"]),
                             ([], [1, 2], ["repeated-sender"]))
            self.assertEqual(coverage["matchedSenders"], sorted(campaign.adapter.LEDGER_SENDERS, key=int))
        with tempfile.TemporaryDirectory() as directory:
            self.assertNotIn("requiredSenders", campaign.Campaign(options(directory, profile="stateful-mapping")).summary["coverage"])

    def test_ledger_entry_slots_are_named_in_fingerprints_and_injection(self):
        value = ledger_case()
        raw = ledger_report(value)
        self.assertEqual(raw["comparison"]["category"], "matched")
        slot = str(fixtures.CAST_LEDGER_SLOTS[fixtures.LEDGER_SENDERS[1]])
        changed = campaign.analyze(raw, value, "importedHull", "tx-0", "storage:" + slot)
        self.assertTrue(changed["synthetic"])
        fingerprint = campaign.fingerprint(changed)
        # The perturbed entry also breaks the returned sum, which the ledger protocol reports.
        self.assertEqual((fingerprint["storageSlots"], fingerprint["fields"], fingerprint["transactionId"]),
                         ([slot], ["committedStorage", "output"], "tx-0"))
        self.assertFalse(campaign.analyze(raw, value, "importedHull", "tx-0", "storage:" + str(fixtures.CAST_SOLIDITY_SENDER_SLOT))["synthetic"])
        # A reduced recipient that no longer declares the slot cannot keep the finding.
        reduced = ledger_case(((0, 0, 0, 1, 7), (1, 0, 0, 2**64, 3), (2, 1, fixtures.MAX_WORD, 7, 7)))
        dropped = campaign.analyze(ledger_report(reduced), reduced, "importedHull", "tx-0", "storage:" + slot)
        self.assertFalse(dropped["synthetic"] and campaign.same_failure(fingerprint, dropped))
        self.assertEqual(campaign.transaction_counts(raw["histories"], value), {"executed": 3, "completed": 3, "matched": 3})

    def test_ledger_shrink_requests_at_most_its_native_batch(self):
        value = ledger_case()
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-ledger", shrink_attempts=40, shrink_candidates=64))
            raw = ledger_report(value)
            analysis = campaign.analyze(raw, value, "rustEvm", "tx-0", "storage:0")
            folder, _, _ = saved_execution(instance, value, raw, analysis)
            finding = instance.retain_finding(0, folder, value, analysis)
            with patch.object(instance, "tool", return_value={"schema": instance.specification["corpusSchema"], "cases": []}) as tool:
                instance.shrink(value, finding)
            self.assertEqual(tool.call_args.args[0][2], 16)


def long_bytes_case(rows=None):
    value = fixtures.long_bytes_case() if rows is None else fixtures.long_bytes_case(rows)
    value["longBytesPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def long_bytes_report(value):
    histories = fixtures.long_bytes_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
            "comparison": campaign.adapter.compare(histories, value)}


class LongBytesCampaignTests(unittest.TestCase):
    def test_long_bytes_shares_the_bytes_dimensions_up_to_its_own_bound(self):
        self.assertEqual(campaign.dimensions("stateful-long-bytes"), campaign.BYTES_DIMENSIONS)
        self.assertEqual(campaign.versions("stateful-long-bytes"), campaign.VERSIONS)
        value = long_bytes_case()
        self.assertEqual(campaign.bytes_coverage(value, ["returned", "reverted", "returned"]),
                         {"PayloadLengths": {97, 256, 0}, "RevertedPayloadLengths": {256}})
        self.assertEqual(len(campaign.inputs(value)), 5)
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-long-bytes"))
            instance.summary["coverage"].update(requiredPayloadLengths=[0, 97, 255, 256], requiredRevertedPayloadLengths=[0, 256])
            instance.record_coverage(value, "matched", long_bytes_report(value)["histories"])
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedPayloadLengths"], coverage["missingPayloadLengths"]), ([0, 97, 256], [255]))
            self.assertEqual((coverage["matchedRevertedPayloadLengths"], coverage["missingRevertedPayloadLengths"]), ([256], [0]))

    def test_long_bytes_manifest_bounds_lengths_by_its_profile(self):
        manifest = json.loads((ROOT / "scripts/semantic-long-bytes-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        self.assertEqual(manifest["requiredPayloadLengths"], [0, 1, 64, 65, 96, 97, 128, 129, 192, 223, 255, 256])
        for change in (lambda m: m.update(requiredPayloadLengths=[0, 257]), lambda m: m.update(requiredRevertedPayloadLengths=[300]),
                       lambda m: m.pop("requiredRevertedPayloadLengths"), lambda m: m.update(requiredLengths=[0]),
                       lambda m: m["cases"][0].update(bytesPlan=m["cases"][0].pop("longBytesPlan"))):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        short = json.loads((ROOT / "scripts/semantic-bytes-corpus.json").read_text())
        short["requiredPayloadLengths"] = short["requiredPayloadLengths"] + [65]
        with self.assertRaises(ValueError):
            campaign.validate_manifest(short)

    def test_long_bytes_slots_are_named_and_shrinking_requests_at_most_32_candidates(self):
        value = long_bytes_case()
        raw = long_bytes_report(value)
        self.assertEqual(raw["comparison"]["category"], "matched")
        changed = campaign.analyze(raw, value, "importedHull", "tx-2", "storage:9")
        fingerprint = campaign.fingerprint(changed)
        self.assertEqual((fingerprint["storageSlots"], fingerprint["transactionId"]), (["9"], "tx-2"))
        self.assertFalse(campaign.analyze(raw, value, "importedHull", "tx-2", "storage:11")["synthetic"])
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-long-bytes", shrink_attempts=40, shrink_candidates=64))
            folder, _, _ = saved_execution(instance, value, raw, changed)
            finding = instance.retain_finding(0, folder, value, changed)
            with patch.object(instance, "tool", return_value={"schema": instance.specification["corpusSchema"], "cases": []}) as tool:
                instance.shrink(value, finding)
            self.assertEqual(tool.call_args.args[0][2], 32)


if __name__ == "__main__":
    unittest.main()
