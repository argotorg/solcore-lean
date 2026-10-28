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
        test_perturb_path=None, test_transaction_id=None, test_field="output", case=None, corpus=None, g0_version=None,
        transactions=None)
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
        for invalid in (None, "solc-yul"):
            with self.subTest(backend=invalid), self.assertRaises(ValueError):
                campaign.analyze({**report(value), "backend": invalid}, value)

    def test_each_candidate_uses_selected_backend_and_retains_it_in_report(self):
        for backend in ("sonatina-o2", "yul"):
            with self.subTest(backend=backend), tempfile.TemporaryDirectory() as temporary:
                instance = campaign.Campaign(options(temporary, backend=backend, solc=Path(temporary) / "solc"))
                seen = []
                def execute(args, raw):
                    seen.append((args.backend, raw["backend"], args.solc))
                    value = json.loads(args.case.read_text())
                    raw.update(report(value))
                with patch.object(campaign.adapter, "execute", side_effect=execute):
                    for value in (case(3), case(1)):
                        folder, raw, analysis = instance.execute_case(value)
                        self.assertEqual(raw["backend"], backend)
                        self.assertEqual(analysis["backend"], backend)
                        self.assertEqual(campaign.common.read_json(folder / "report.json")["backend"], backend)
                # Every candidate receives the same compiler; only Yul uses it.
                self.assertEqual(seen, [(backend, backend, (Path(temporary) / "solc").resolve())] * 2)
                self.assertEqual(instance.summary["backend"], backend)
                self.assertEqual(instance.summary["configuration"]["backend"], backend)
                self.assertEqual(instance.summary["tools"].get("solc"), str((Path(temporary) / "solc").resolve()) if backend == "yul" else None)

    def test_yul_campaign_cli_forwards_its_compiler(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "campaign"
            def run(instance):
                self.assertEqual((instance.backend, instance.args.solc, instance.solc), ("yul", (Path(temporary) / "solc").resolve(),
                                                                                         (Path(temporary) / "solc").resolve()))
                instance.summary["status"] = "complete"
                instance.summary["counts"].update(generated=1, executed=1, completed=1, matched=1)
            arguments = ["campaign", "--output", str(output), "--backend", "yul", "--solc", str(Path(temporary) / "solc"), "--cases", "1"]
            with patch.object(sys, "argv", arguments), patch.object(campaign.Campaign, "run", run), redirect_stdout(io.StringIO()):
                self.assertEqual(campaign.main(), 0)
            summary = campaign.common.read_json(output / "summary.json")
            self.assertEqual((summary["backend"], summary["configuration"]["backend"]), ("yul", "yul"))
            self.assertEqual(summary["tools"]["solc"], str((Path(temporary) / "solc").resolve()))

    def test_unknown_backend_campaign_is_rejected_before_output_or_work_directory(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "campaign"
            arguments = ["campaign", "--output", str(output), "--backend", "solc-yul", "--cases", "1"]
            with patch.object(sys, "argv", arguments), patch.object(campaign.Campaign, "run") as run, \
                    redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as caught:
                campaign.main()
            self.assertEqual(caught.exception.code, 2)
            run.assert_not_called()
            self.assertFalse(output.exists())
            with self.assertRaisesRegex(ValueError, "unsupported backend"):
                campaign.Campaign(options(temporary, backend="solc-yul"))
            self.assertFalse((Path(temporary) / ".work").exists())

    def test_yul_is_part_of_a_stateful_reduction_identity(self):
        value = case()
        ordinary = campaign.analyze(report(value), value, "rustEvm", "tx-1")
        yul = campaign.analyze({**report(value), "backend": "yul"}, value, "rustEvm", "tx-1")
        self.assertEqual(campaign.fingerprint(yul)["backend"], "yul")
        expected = campaign.fingerprint(yul)
        self.assertTrue(campaign.same_failure(expected, yul))
        # A Yul finding is not reproduced by the same difference on Sonatina, nor the reverse.
        self.assertFalse(campaign.same_failure(expected, ordinary))
        self.assertFalse(campaign.same_failure(campaign.fingerprint(ordinary), yul))
        with self.assertRaisesRegex(ValueError, "unsupported saved backend"):
            campaign.fingerprint({**ordinary, "backend": "solc-yul"})

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



def malformed_case(rows=None):
    value = fixtures.malformed_case() if rows is None else fixtures.malformed_case(rows)
    value["malformedCalldataPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def malformed_report(value):
    histories = fixtures.malformed_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
            "comparison": campaign.adapter.compare(histories, value)}


class MalformedCalldataCampaignTests(unittest.TestCase):
    def test_coverage_names_lengths_malformations_and_std_outcomes(self):
        value = malformed_case()
        self.assertEqual(campaign.inputs(value), {"1", "3", "5", "7"})
        self.assertEqual(campaign.dimensions("stateful-malformed-calldata"),
                         campaign.DIMENSIONS + ("Lengths", "Malformations", "Rejections"))
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-malformed-calldata"))
            instance.summary["coverage"].update(requiredMalformations=["none", "selector", "offset"],
                                                requiredRejections=["0x4924aef0", "0x08638556", "accepted"])
            instance.record_coverage(value, "matched", malformed_report(value)["histories"])
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual(coverage["matchedMalformations"], ["none", "selector", "trailing"])
            self.assertEqual((coverage["missingMalformations"], coverage["missingRejections"]), (["offset"], ["0x08638556"]))

    def test_a_std_rejection_counts_as_a_matched_prefix_and_its_analysis_names_the_selector(self):
        value = malformed_case()
        raw = malformed_report(value)
        self.assertEqual(campaign.transaction_counts(raw["histories"], value), {"executed": 3, "completed": 3, "matched": 3})
        analysis = campaign.analyze(raw, value)
        self.assertEqual(analysis["selectorRows"], [{"id": "tx-1", "index": 1, "selector": "0x4924aef0"}])
        changed = copy.deepcopy(raw)
        changed["histories"]["rustEvm"]["transactions"][1]["output"] = fixtures.selector_word("0x4924aef0")
        self.assertEqual(campaign.transaction_counts(changed["histories"], value)["matched"], 1)
        self.assertNotIn("selectorRows", campaign.analyze(array_report(array_case()), array_case()))

    def test_the_manifest_requires_malformations_only_for_its_profile(self):
        manifest = json.loads((ROOT / "scripts/semantic-malformed-calldata-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        for change in (lambda m: m.pop("requiredMalformations"), lambda m: m.update(requiredMalformations=["reorder"]),
                       lambda m: m.update(requiredRejections=["0x7f52b2bf"]), lambda m: m.update(requiredRejections=[]),
                       lambda m: m.pop("requiredLengths")):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        array = json.loads((ROOT / "scripts/semantic-dynamic-array-corpus.json").read_text())
        array["requiredMalformations"] = ["none"]
        with self.assertRaises(ValueError):
            campaign.validate_manifest(array)


def malformed_nested_case(rows=None):
    value = fixtures.malformed_nested_case() if rows is None else fixtures.malformed_nested_case(rows)
    value["malformedNestedArrayPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def malformed_nested_report(value):
    histories = fixtures.malformed_nested_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
            "comparison": campaign.adapter.compare(histories, value)}


class MalformedNestedArrayCampaignTests(unittest.TestCase):
    def test_coverage_names_rows_malformed_rows_malformations_and_std_outcomes(self):
        value = malformed_nested_case()
        self.assertEqual(campaign.inputs(value), {"0", "1", "3", "4", "7", "9"})
        self.assertEqual(campaign.dimensions("stateful-malformed-nested-array"),
                         campaign.DIMENSIONS + ("RowCounts", "RowLengths", "MalformedRows", "Malformations", "Rejections"))
        self.assertEqual(campaign.malformed_coverage(value),
                         {"RowCounts": {3, 4}, "RowLengths": {0, 1, 2, 3}, "MalformedRows": {0, 1, 3},
                          "Malformations": {"none", "row-length", "row-offset", "offset"}, "Rejections": {"accepted", "0x08638556"}})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-malformed-nested-array"))
            instance.summary["coverage"].update(requiredMalformedRows=[0, 1, 2, 3],
                                                requiredRejections=["0x4924aef0", "0x08638556", "accepted"])
            instance.record_coverage(value, "matched", malformed_nested_report(value)["histories"])
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual(coverage["matchedMalformedRows"], [0, 1, 3])
            self.assertEqual((coverage["missingMalformedRows"], coverage["missingRejections"]), ([2], ["0x4924aef0"]))

    def test_a_nested_rejection_counts_as_a_matched_prefix_and_its_analysis_names_the_selector(self):
        value = malformed_nested_case()
        raw = malformed_nested_report(value)
        self.assertEqual(campaign.transaction_counts(raw["histories"], value), {"executed": 5, "completed": 5, "matched": 5})
        self.assertEqual(campaign.analyze(raw, value)["selectorRows"], [{"id": "tx-2", "index": 2, "selector": "0x08638556"}])
        changed = copy.deepcopy(raw)
        changed["histories"]["importedHull"]["transactions"][2]["output"] = fixtures.selector_word("0x08638556")
        self.assertEqual(campaign.transaction_counts(changed["histories"], value)["matched"], 2)

    def test_the_manifest_requires_row_coverage_and_row_malformations_only_for_its_profile(self):
        manifest = json.loads((ROOT / "scripts/semantic-malformed-nested-array-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        for change in (lambda m: m.pop("requiredMalformedRows"), lambda m: m.update(requiredMalformedRows=[4]),
                       lambda m: m.update(requiredRowCounts=[5]), lambda m: m.update(requiredLengths=[0]),
                       lambda m: m.update(requiredMalformations=["reorder"]), lambda m: m.update(requiredRejections=["0x7f52b2bf"])):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        nested = json.loads((ROOT / "scripts/semantic-nested-array-corpus.json").read_text())
        nested["requiredMalformedRows"] = [0]
        array = json.loads((ROOT / "scripts/semantic-malformed-calldata-corpus.json").read_text())
        array["requiredMalformations"] = ["none", "row-offset"]
        for invalid in (nested, array):
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)


def malformed_bytes_case(rows=None):
    value = fixtures.malformed_bytes_case() if rows is None else fixtures.malformed_bytes_case(rows)
    value["malformedBytesPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def malformed_bytes_report(value):
    histories = fixtures.malformed_bytes_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
            "comparison": campaign.adapter.compare(histories, value)}


class MalformedBytesCampaignTests(unittest.TestCase):
    def test_coverage_names_payload_lengths_malformations_and_std_outcomes(self):
        value = malformed_bytes_case()
        self.assertEqual(campaign.dimensions("stateful-malformed-bytes"),
                         campaign.DIMENSIONS + ("PayloadLengths", "Malformations", "Rejections"))
        self.assertEqual(campaign.malformed_coverage(value),
                         {"PayloadLengths": {65}, "Malformations": {"none", "truncate", "padding", "length"},
                          "Rejections": {"accepted", "0x08638556"}})
        self.assertEqual(len(campaign.inputs(value)), 3)
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-malformed-bytes"))
            instance.summary["coverage"].update(requiredPayloadLengths=[0, 65], requiredMalformations=["padding", "offset"])
            instance.record_coverage(value, "matched", malformed_bytes_report(value)["histories"])
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["missingPayloadLengths"], coverage["missingMalformations"]), ([0], ["offset"]))

    def test_a_bytes_rejection_counts_as_a_matched_prefix_and_its_analysis_names_the_selector(self):
        value = malformed_bytes_case()
        raw = malformed_bytes_report(value)
        self.assertEqual(campaign.transaction_counts(raw["histories"], value), {"executed": 5, "completed": 5, "matched": 5})
        self.assertEqual(campaign.analyze(raw, value)["selectorRows"], [{"id": "tx-2", "index": 2, "selector": "0x08638556"}])

    def test_the_manifest_requires_payload_lengths_and_padding_only_for_its_profile(self):
        manifest = json.loads((ROOT / "scripts/semantic-malformed-bytes-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        for change in (lambda m: m.pop("requiredPayloadLengths"), lambda m: m.update(requiredPayloadLengths=[257]),
                       lambda m: m.update(requiredRevertedPayloadLengths=[0]), lambda m: m.update(requiredLengths=[0]),
                       lambda m: m.update(requiredMalformations=["row-offset"]), lambda m: m.update(requiredMalformedRows=[0])):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        array = json.loads((ROOT / "scripts/semantic-malformed-calldata-corpus.json").read_text())
        array["requiredMalformations"] = ["none", "padding"]
        with self.assertRaises(ValueError):
            campaign.validate_manifest(array)


def methods_case(rows=None):
    value = fixtures.methods_case() if rows is None else fixtures.methods_case(rows=rows)
    for method in value["methodsPlan"]["methods"]:
        method["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def methods_report(value):
    histories = fixtures.methods_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
            "comparison": campaign.adapter.compare(histories, value)}


class MethodsCampaignTests(unittest.TestCase):
    def test_coverage_names_method_counts_called_positions_selector_orders_arities_and_std_outcomes(self):
        value = methods_case()
        self.assertEqual(campaign.dimensions("stateful-methods"),
                         campaign.DIMENSIONS + ("MethodCounts", "MethodPositions", "SelectorOrders", "Arities", "Rejections"))
        self.assertEqual(campaign.methods_coverage(value),
                         {"MethodCounts": {3}, "MethodPositions": {0, 1, 2}, "SelectorOrders": {"mixed"},
                          "Arities": {0, 1, 2}, "Rejections": {"0x4924aef0", "accepted"}})
        self.assertEqual(campaign.inputs(value), {"1", "2", "3", "4", "6"})
        uncalled = methods_case(rows=(("m_00000002", ()), (None, (1,))))
        self.assertEqual(campaign.methods_coverage(uncalled)["MethodPositions"], {1})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-methods"))
            instance.summary["coverage"].update(requiredMethodCounts=[2, 3, 4], requiredMethodPositions=[0, 1, 2, 3],
                                                requiredSelectorOrders=["ascending", "mixed"])
            instance.record_coverage(value, "matched", methods_report(value)["histories"])
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedMethodPositions"], coverage["matchedSelectorOrders"]), ([0, 1, 2], ["mixed"]))
            self.assertEqual((coverage["missingMethodCounts"], coverage["missingMethodPositions"], coverage["missingSelectorOrders"]),
                             ([2, 4], [3], ["ascending"]))

    def test_helper_counts_and_templates_cover_every_method_step(self):
        value = methods_case()
        value["methodsPlan"]["methods"][1]["stepProgram"] = case(helpers=3)["storagePlan"]["stepProgram"]
        self.assertEqual(campaign.helper_counts(value), {1, 3})
        value["provenance"]["origin"] = {"kind": "methods-generated", "stepOrigins": [
            {"kind": "aggregate-generated", "helpers": [{"template": 0}]},
            {"kind": "aggregate-generated", "helpers": [{"template": 2}, {"template": 3}]},
            {"kind": "aggregate-generated", "helpers": [{"template": 2}]}]}
        self.assertEqual(campaign.recipes(value), {0, 2, 3})
        for change in (lambda origin: origin.pop("stepOrigins"), lambda origin: origin.update(stepOrigins=[]),
                       lambda origin: origin["stepOrigins"][1].update(kind="storage-generated"),
                       lambda origin: origin["stepOrigins"][2]["helpers"][0].update(template=4)):
            invalid = copy.deepcopy(value)
            change(invalid["provenance"]["origin"])
            with self.assertRaises(ValueError):
                campaign.recipes(invalid)

    def test_a_missing_selector_counts_as_a_matched_prefix_and_its_analysis_names_the_selector(self):
        value = methods_case()
        raw = methods_report(value)
        self.assertEqual(campaign.transaction_counts(raw["histories"], value), {"executed": 5, "completed": 5, "matched": 5})
        self.assertEqual(campaign.analyze(raw, value)["selectorRows"], [{"id": "tx-2", "index": 2, "selector": "0x4924aef0"}])
        changed = copy.deepcopy(raw)
        changed["histories"]["importedHull"]["transactions"][2]["output"] = fixtures.selector_word("0x4924aef0")
        self.assertEqual(campaign.transaction_counts(changed["histories"], value)["matched"], 2)

    def test_the_manifest_requires_method_coverage_only_for_its_profile(self):
        manifest = json.loads((ROOT / "scripts/semantic-methods-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        for change in (lambda m: m.pop("requiredMethodCounts"), lambda m: m.update(requiredMethodCounts=[5]),
                       lambda m: m.update(requiredMethodPositions=[4]), lambda m: m.update(requiredSelectorOrders=["random"]),
                       lambda m: m.update(requiredArities=[True]), lambda m: m.update(requiredArities=[3]),
                       lambda m: m.update(requiredRejections=["0x08638556"]), lambda m: m.update(requiredRejections=[]),
                       lambda m: m.update(requiredMalformations=["none"])):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        storage = json.loads((ROOT / "scripts/semantic-storage-corpus.json").read_text())
        storage["requiredMethodCounts"] = [2]
        nested = json.loads((ROOT / "scripts/semantic-malformed-nested-array-corpus.json").read_text())
        nested["requiredSelectorOrders"] = ["mixed"]
        for invalid in (storage, nested):
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)


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
            self.assertEqual(tool.call_args.args[0][2], 16)


def nested_case(rows=None):
    value = fixtures.nested_case() if rows is None else fixtures.nested_case(rows)
    value["nestedArrayPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


def nested_report(value):
    histories = fixtures.nested_histories(value)
    return {"schema": campaign.adapter.REPORT_SCHEMA, "histories": histories,
            "comparison": campaign.adapter.compare(histories, value)}


class NestedArrayCampaignTests(unittest.TestCase):
    def test_nested_coverage_counts_outer_and_row_lengths(self):
        self.assertEqual(campaign.dimensions("stateful-nested-array"), campaign.NESTED_DIMENSIONS)
        self.assertEqual(campaign.versions("stateful-nested-array"), campaign.VERSIONS)
        value = nested_case()
        self.assertEqual(campaign.nested_coverage(value), {"RowCounts": {3, 2, 0}, "RowLengths": {2, 0, 1}})
        self.assertEqual(campaign.inputs(value), {"1", "3", "7", str(2**256 - 1), str(2**255), "0"})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-nested-array"))
            instance.summary["coverage"].update(requiredRowCounts=[0, 1, 2, 3], requiredRowLengths=[0, 1, 2])
            instance.record_coverage(value, "matched", nested_report(value)["histories"])
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedRowCounts"], coverage["missingRowCounts"]), ([0, 2, 3], [1]))
            self.assertEqual((coverage["matchedRowLengths"], coverage["missingRowLengths"]), ([0, 1, 2], []))

    def test_nested_manifest_requires_bounded_row_coverage(self):
        manifest = json.loads((ROOT / "scripts/semantic-nested-array-corpus.json").read_text())
        self.assertIs(campaign.validate_manifest(manifest), manifest)
        self.assertEqual((manifest["requiredRowCounts"], manifest["requiredRowLengths"]), ([0, 1, 2, 3], [0, 1, 2]))
        for change in (lambda m: m.update(requiredRowCounts=[0, 4]), lambda m: m.update(requiredRowLengths=[3]),
                       lambda m: m.update(requiredRowLengths=[0, 0]), lambda m: m.pop("requiredRowCounts"),
                       lambda m: m.update(requiredLengths=[0]),
                       lambda m: m["cases"][0].update(dynamicArrayPlan=m["cases"][0].pop("nestedArrayPlan"))):
            invalid = copy.deepcopy(manifest)
            change(invalid)
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        flat = json.loads((ROOT / "scripts/semantic-dynamic-array-corpus.json").read_text())
        flat["requiredRowCounts"] = [0]
        with self.assertRaises(ValueError):
            campaign.validate_manifest(flat)

    def test_nested_slots_are_named_and_shrinking_requests_at_most_32_candidates(self):
        value = nested_case()
        raw = nested_report(value)
        self.assertEqual(raw["comparison"]["category"], "matched")
        changed = campaign.analyze(raw, value, "importedHull", "tx-2", "storage:8")
        fingerprint = campaign.fingerprint(changed)
        self.assertEqual((fingerprint["storageSlots"], fingerprint["transactionId"]), (["8"], "tx-2"))
        self.assertFalse(campaign.analyze(raw, value, "importedHull", "tx-2", "storage:9")["synthetic"])
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-nested-array", shrink_attempts=40, shrink_candidates=64))
            folder, _, _ = saved_execution(instance, value, raw, changed)
            finding = instance.retain_finding(0, folder, value, changed)
            with patch.object(instance, "tool", return_value={"schema": instance.specification["corpusSchema"], "cases": []}) as tool:
                instance.shrink(value, finding)
            self.assertEqual(tool.call_args.args[0][2], 16)


class StrayWriteAdapterTests(unittest.TestCase):
    """The `stray` adapter adds one undeclared nonzero slot to a copied whole
    storage after actual agreement; the comparison must classify it as such."""

    def test_stray_write_is_detected_and_fingerprinted_by_account_and_absent_paths(self):
        value, raw = case(), report()
        original = copy.deepcopy(raw)
        for path in campaign.PATHS:
            analysis = campaign.analyze(raw, value, path, "tx-1", "stray")
            others = [other for other in campaign.PATHS if other != path]
            with self.subTest(path=path):
                self.assertTrue(analysis["synthetic"])
                self.assertEqual(analysis["actualComparison"]["category"], "matched")
                self.assertEqual((analysis["comparison"]["category"], analysis["comparison"]["transactionId"],
                                  analysis["comparison"]["fields"]), ("semantic-mismatch", "tx-1", ["accountStorage"]))
                observed = campaign.fingerprint(analysis)
                self.assertEqual(observed["accountStorageDifferences"],
                                 [{"account": "contract", "slot": "undeclared", "zeroPaths": others}])
                self.assertEqual(observed["accountStorageRollbackPaths"], [])
                self.assertEqual(observed["fields"], ["accountStorage"])
                self.assertEqual(observed["storageSlots"], [])
                stored = analysis["histories"][path]["transactions"][1]["accountStorage"][0]["storage"]
                self.assertIn({"slot": campaign.STRAY_SLOT, "value": "1"}, stored)
        self.assertEqual(raw, original)

    def test_reduction_keeps_the_stray_fingerprint_and_removal_cannot_fake_it(self):
        value = case()
        first = campaign.analyze(report(value), value, "importedHull", "tx-1", "stray")
        reduced = copy.deepcopy(value)
        reduced["transactions"] = reduced["transactions"][1:2]
        second = campaign.analyze(report(reduced), reduced, "importedHull", "tx-1", "stray")
        self.assertEqual(second["comparison"]["index"], 0)
        self.assertTrue(campaign.same_failure(campaign.fingerprint(first), second))
        self.assertEqual(second["histories"]["importedHull"]["finalAccountStorage"],
                         second["histories"]["importedHull"]["transactions"][0]["accountStorage"])
        removed = copy.deepcopy(value)
        removed["transactions"] = removed["transactions"][:1]
        self.assertFalse(campaign.analyze(report(removed), removed, "importedHull", "tx-1", "stray")["synthetic"])
        for other in ("output", "storage:0"):
            self.assertFalse(campaign.same_failure(campaign.fingerprint(first),
                                                   campaign.analyze(report(value), value, "importedHull", "tx-1", other)))
        self.assertFalse(campaign.same_failure(campaign.fingerprint(first),
                                               campaign.analyze(report(value), value, "rustEvm", "tx-1", "stray")))

    def test_a_declared_or_already_held_slot_cannot_carry_a_stray_write(self):
        declared = fixtures.keyed_case(((2**256 - 3, 2), (0, 4)))
        self.assertIn(campaign.STRAY_SLOT, declared["observedSlots"])
        raw = {"schema": campaign.adapter.REPORT_SCHEMA, "histories": fixtures.keyed_histories(declared)}
        raw["comparison"] = campaign.adapter.compare(raw["histories"], declared)
        self.assertEqual(raw["comparison"]["category"], "matched")
        self.assertFalse(campaign.analyze(raw, declared, "rustEvm", "tx-0", "stray")["synthetic"])
        value, held = case(), report()
        for history in held["histories"].values():
            for row in history["transactions"]:
                row["accountStorage"][0]["storage"].append({"slot": campaign.STRAY_SLOT, "value": "5"})
            history["finalAccountStorage"] = copy.deepcopy(history["transactions"][-1]["accountStorage"])
        held["comparison"] = campaign.adapter.compare(held["histories"], value)
        self.assertEqual(held["comparison"]["category"], "matched")
        self.assertFalse(campaign.analyze(held, value, "rustEvm", "tx-1", "stray")["synthetic"])

    def test_every_fingerprint_carries_the_whole_storage_classification(self):
        value = case()
        plain = campaign.fingerprint(campaign.analyze(report(), value))
        self.assertEqual((plain["accountStorageDifferences"], plain["accountStorageRollbackPaths"]), ([], []))
        output = campaign.fingerprint(campaign.analyze(report(), value, "rustEvm", "tx-1", "output"))
        self.assertEqual((output["accountStorageDifferences"], output["accountStorageRollbackPaths"]), ([], []))

    def test_a_declared_stray_slot_is_rejected_before_execution(self):
        declared, template = fixtures.keyed_case(((2**256 - 3, 2), (0, 4))), case()
        declared["keyedStoragePlan"]["stepProgram"] = template["storagePlan"]["stepProgram"]
        declared["provenance"] = template["provenance"]
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-keyed-storage", test_perturb_path="rustEvm",
                                                 test_transaction_id="tx-0", test_field="stray"))
            with patch.object(instance, "prepare_cases", side_effect=lambda: instance.add_case(declared, "policy")), \
                 patch.object(instance, "execute_case") as execute, self.assertRaisesRegex(ValueError, "stray slot is declared"):
                instance.run()
            execute.assert_not_called()

    def test_cli_admits_the_stray_field_on_every_profile(self):
        # A zero time limit stops after field validation, so the error names the limit, not the field.
        for profile, field, message in (("stateful-storage", "stray", "seconds must be between"),
                                        ("stateful-keyed-storage", "stray", "seconds must be between"),
                                        ("stateful-storage", "stray:1", "test field must be")):
            with tempfile.TemporaryDirectory() as directory, patch.object(sys, "argv", [
                    "campaign", "--output", str(Path(directory) / "out"), "--profile", profile, "--seconds", "0",
                    "--test-perturb-path", "importedHull", "--test-field", field]), \
                    redirect_stderr(io.StringIO()) as errors, self.assertRaises(SystemExit):
                campaign.main()
            with self.subTest(profile=profile, field=field):
                self.assertIn(message, errors.getvalue())


class G0VersionTests(unittest.TestCase):
    """Random generation draws checked steps with G0 revision two; a corpus or a
    saved case keeps the version it records, and the summary names it."""

    @staticmethod
    def fresh(directory, name):
        path = Path(directory) / name
        path.mkdir()
        return path

    @staticmethod
    def generated(version):
        value = case()
        value["provenance"]["generatorVersion"] = version
        return value

    def test_random_generation_requests_and_records_revision_three(self):
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory))
            self.assertEqual(instance.summary["configuration"]["g0Version"], "core-g0-v3/lcg64-v1")
            response = {"schema": campaign.CORPUS_SCHEMA, "cases": [self.generated("core-g0-v3/lcg64-v1")], "requested": 1,
                        "attempted": 1, "status": "complete", "excluded": []}
            with patch.object(instance, "tool", return_value=response) as tool:
                instance.prepare_cases()
            self.assertEqual(tool.call_args.args[0][-2:], ["core-g0-v3/lcg64-v1", 8])
            for version in ("core-g0-v1/lcg64-v1", "core-g0-v2/lcg64-v1"):
                explicit = campaign.Campaign(options(self.fresh(directory, version.split("/")[0]), g0_version=version))
                with patch.object(explicit, "tool", return_value=response) as tool:
                    explicit.prepare_cases()
                self.assertEqual(tool.call_args.args[0][-2:], [version, 8])

    def test_a_corpus_generates_with_its_recorded_version(self):
        manifest = json.loads((ROOT / "scripts/semantic-storage-corpus.json").read_text())
        entry = next(item for item in manifest["cases"] if "generation" in item)
        manifest["cases"] = [entry]
        generated = self.generated(manifest["generatorVersion"])
        generated["provenance"].update({key: manifest[key] for key in campaign.versions("stateful-storage")},
                                       features=entry["expectedFeatures"],
                                       origin={"kind": "storage-generated", **entry["generation"],
                                               "stepOrigin": {"kind": "aggregate-generated", "helpers": [{"template": 0}]}})
        response = {"schema": campaign.CORPUS_SCHEMA, "cases": [generated]}
        with tempfile.TemporaryDirectory() as directory:
            corpus = Path(directory) / "corpus.json"
            corpus.write_text(json.dumps(manifest))
            instance = campaign.Campaign(options(self.fresh(directory, "run"), corpus=corpus))
            self.assertIsNone(instance.summary["configuration"]["g0Version"])
            with patch.object(instance, "tool", return_value=response) as tool:
                instance.prepare_cases()
            self.assertEqual(tool.call_args.args[0], ["generate", entry["generation"]["seed"], entry["generation"]["maxProgramNodes"],
                                                      1, 1, 1000, "core-g0-v1/lcg64-v1"])
            self.assertEqual(instance.summary["configuration"]["g0Version"], "core-g0-v1/lcg64-v1")
            disagreeing = campaign.Campaign(options(self.fresh(directory, "other"), corpus=corpus, g0_version="core-g0-v2/lcg64-v1"))
            with patch.object(disagreeing, "tool", return_value=response), self.assertRaisesRegex(ValueError, "disagrees"):
                disagreeing.prepare_cases()

    def test_a_saved_case_keeps_its_version_and_run_records_every_version(self):
        with tempfile.TemporaryDirectory() as directory:
            saved = Path(directory) / "case.json"
            saved.write_text(json.dumps(self.generated("core-g0-v2/lcg64-v1")))
            instance = campaign.Campaign(options(self.fresh(directory, "run"), case=saved))
            with patch.object(instance, "tool", return_value=self.generated("core-g0-v2/lcg64-v1")):
                instance.prepare_cases()
            self.assertEqual(instance.summary["configuration"]["g0Version"], "core-g0-v2/lcg64-v1")
            masked = campaign.Campaign(options(self.fresh(directory, "masked"), case=saved))
            with patch.object(masked, "tool", return_value=self.generated("core-g0-v3/lcg64-v1")):
                masked.prepare_cases()
            self.assertEqual(masked.summary["configuration"]["g0Version"], "core-g0-v3/lcg64-v1")
            unknown = campaign.Campaign(options(self.fresh(directory, "unknown"), case=saved))
            with patch.object(unknown, "tool", return_value=self.generated("core-g0-v9/lcg64-v1")), \
                    self.assertRaisesRegex(ValueError, "unsupported recorded"):
                unknown.prepare_cases()
            value = self.generated("core-g0-v2/lcg64-v1")
            raw = report(value)
            analysis = campaign.analyze(raw, value)
            recorder = campaign.Campaign(options(self.fresh(directory, "recorded")))
            with patch.object(recorder, "prepare_cases", side_effect=lambda: recorder.add_case(value, "policy")), \
                 patch.object(recorder, "execute_case", side_effect=lambda _: saved_execution(recorder, value, raw, analysis)), \
                 redirect_stdout(io.StringIO()):
                recorder.run()
            self.assertEqual(recorder.summary["generation"]["generatorVersions"], ["core-g0-v2/lcg64-v1"])

    def test_cli_refuses_a_version_that_disagrees_with_a_corpus(self):
        for version, message in (("core-g0-v2/lcg64-v1", "disagrees with the supplied"), ("core-g0-v9/lcg64-v1", "invalid choice"),
                                 ("core-g0-v3/lcg64-v1", "disagrees with the supplied")):
            with tempfile.TemporaryDirectory() as directory, patch.object(sys, "argv", [
                    "campaign", "--output", str(Path(directory) / "out"), "--corpus", str(ROOT / "scripts/semantic-storage-corpus.json"),
                    "--g0-version", version]), redirect_stderr(io.StringIO()) as errors, self.assertRaises(SystemExit):
                campaign.main()
            with self.subTest(version=version):
                self.assertIn(message, errors.getvalue())


class TransactionCountTests(unittest.TestCase):
    """Random generation requests the longest admitted sequence or an explicit
    length; a corpus or a saved case keeps its own transactions."""

    def test_random_generation_requests_and_records_the_length(self):
        response = {"schema": campaign.CORPUS_SCHEMA, "cases": [], "requested": 1, "attempted": 1,
                    "status": "generation-exhausted", "excluded": []}
        with tempfile.TemporaryDirectory() as directory:
            for name, requested, expected in (("default", None, campaign.adapter.MAX_TRANSACTIONS), ("explicit", 4, 4)):
                path = Path(directory) / name
                path.mkdir()
                instance = campaign.Campaign(options(path, transactions=requested))
                self.assertEqual(instance.summary["configuration"]["transactions"], expected)
                with patch.object(instance, "tool", return_value=response) as tool:
                    instance.prepare_cases()
                self.assertEqual(tool.call_args.args[0][-1], expected)
                self.assertEqual(instance.summary["generation"]["transactions"], expected)
            saved = Path(directory) / "case.json"
            saved.write_text(json.dumps(case()))
            path = Path(directory) / "saved"
            path.mkdir()
            self.assertIsNone(campaign.Campaign(options(path, case=saved)).summary["configuration"]["transactions"])

    def test_cli_limits_the_length_to_random_generation(self):
        for extra, message in ((["--transactions", "0"], "between 1 and"),
                               (["--transactions", str(campaign.adapter.MAX_TRANSACTIONS + 1)], "between 1 and"),
                               (["--corpus", str(ROOT / "scripts/semantic-storage-corpus.json"), "--transactions", "3"],
                                "only to random generation")):
            with tempfile.TemporaryDirectory() as directory, \
                    patch.object(sys, "argv", ["campaign", "--output", str(Path(directory) / "out"), *extra]), \
                    redirect_stderr(io.StringIO()) as errors, self.assertRaises(SystemExit):
                campaign.main()
            self.assertIn(message, errors.getvalue())


def loop_case(mask=7, rows=((0, 7), (1, 6), (0, 3), (0, 0))):
    value = fixtures.loop_case(mask, rows)
    value["storageLoopPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


class LoopCampaignTests(unittest.TestCase):
    def test_coverage_names_masks_iteration_counts_carries_and_carried_slots(self):
        value = loop_case()
        self.assertEqual(campaign.dimensions("stateful-storage-loops"),
                         campaign.DIMENSIONS + ("Masks", "IterationCounts", "IterationCarries", "CarriedSlots"))
        statuses = ["returned", "reverted", "returned", "returned"]
        # The reverted six iterations and the later three read what the first
        # committed seven wrote; the revert discards its own writes.
        self.assertEqual(campaign.loops_coverage(value, statuses),
                         {"Masks": {7}, "IterationCounts": {0, 3, 6, 7}, "IterationCarries": {"iteration", "rollback"},
                          "CarriedSlots": {2, 3, 4, 5, 6, 7}})
        self.assertEqual(campaign.inputs(value), {"0", "3", "6", "7"})
        # Nothing is carried from a reverted transaction, and one iteration carries nothing within its transaction.
        first_reverted = loop_case(rows=((1, 7), (0, 1)))
        self.assertEqual(campaign.loops_coverage(first_reverted, ["reverted", "returned"]),
                         {"Masks": {7}, "IterationCounts": {7, 1}, "IterationCarries": {"iteration", "rollback"},
                          "CarriedSlots": set()})
        self.assertEqual(campaign.loops_coverage(loop_case(1, rows=((0, 1), (0, 3))), ["returned", "returned"]),
                         {"Masks": {1}, "IterationCounts": {1}, "IterationCarries": set(), "CarriedSlots": {2}})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-storage-loops"))
            instance.summary["coverage"].update(requiredMasks=[0, 7], requiredIterationCounts=list(range(8)),
                                                requiredCarriedSlots=list(range(2, 9)))
            histories = fixtures.loop_histories(value)
            instance.record_coverage(value, "matched", histories)
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedMasks"], coverage["matchedIterationCounts"], coverage["matchedCarriedSlots"]),
                             ([7], [0, 3, 6, 7], [2, 3, 4, 5, 6, 7]))
            self.assertEqual((coverage["missingMasks"], coverage["missingIterationCounts"], coverage["missingCarriedSlots"]),
                             ([0], [1, 2, 4, 5], [8]))

    def test_the_fixed_corpus_validates_and_its_loop_requirements_are_checked(self):
        manifest = json.loads((ROOT / "scripts/semantic-storage-loop-corpus.json").read_text())
        self.assertEqual(campaign.validate_manifest(manifest)["profile"], "stateful-storage-loops")
        self.assertEqual((manifest["requiredMasks"], manifest["requiredIterationCounts"], manifest["requiredCarriedSlots"]),
                         ([0, 1, 3, 7], list(range(8)), list(range(2, 9))))
        for key, changed in (("requiredMasks", [2]), ("requiredMasks", []), ("requiredMasks", [True]),
                             ("requiredIterationCounts", [8]), ("requiredIterationCarries", ["other"]),
                             ("requiredCarriedSlots", [1]), ("requiredCarriedSlots", [2, 2])):
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                campaign.validate_manifest({**manifest, key: changed})
        with self.assertRaises(ValueError):
            campaign.validate_manifest({key: value for key, value in manifest.items() if key != "requiredCarriedSlots"})
        other = json.loads((ROOT / "scripts/semantic-methods-corpus.json").read_text())
        with self.assertRaisesRegex(ValueError, "loop coverage belongs to the storage-loop profile"):
            campaign.validate_manifest({**other, "requiredMasks": [0, 1, 3, 7]})



def keccak_loop_case(mask=7, key_mask=1, rows=((0, 7), (1, 3), (2, 2))):
    value = fixtures.keccak_loop_case(mask, key_mask, rows)
    value["keccakLoopPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.LOG_VERSIONS})
    value["provenance"].update(features=["local"], origin={"kind": "imported"})
    return value


class KeccakLoopCampaignTests(unittest.TestCase):
    def test_coverage_names_masks_key_masks_iteration_counts_and_carries(self):
        value = keccak_loop_case()
        self.assertEqual(campaign.dimensions("stateful-keccak-loops"),
                         campaign.DIMENSIONS + ("Masks", "KeyMasks", "IterationCounts", "IterationCarries"))
        self.assertEqual(campaign.versions("stateful-keccak-loops"), campaign.LOG_VERSIONS)
        statuses = ["returned", "reverted", "returned"]
        # Seven iterations alternate two entries; the revert discards three
        # logged iterations; the last transaction rereads both committed entries.
        self.assertEqual(campaign.keccak_loops_coverage(value, statuses),
                         {"Masks": {7}, "KeyMasks": {1}, "IterationCounts": {7, 3, 2},
                          "IterationCarries": {"iteration", "entry", "rollback", "transaction"}})
        self.assertEqual(campaign.inputs(value), {"7", "3", "2"})
        # Nothing is carried from a reverted transaction; key mask 7 gives every
        # iteration its own entry; one iteration carries nothing within its transaction.
        first_reverted = keccak_loop_case(key_mask=7, rows=((1, 1), (0, 1)))
        self.assertEqual(campaign.keccak_loops_coverage(first_reverted, ["reverted", "returned"]),
                         {"Masks": {7}, "KeyMasks": {7}, "IterationCounts": {1}, "IterationCarries": {"rollback"}})
        self.assertEqual(campaign.keccak_loops_coverage(keccak_loop_case(7, 0, rows=((0, 1), (0, 0))), ["returned", "returned"]),
                         {"Masks": {7}, "KeyMasks": {0}, "IterationCounts": {1, 0}, "IterationCarries": set()})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-keccak-loops"))
            instance.summary["coverage"].update(requiredMasks=[0, 7], requiredKeyMasks=[1, 3], requiredIterationCounts=list(range(8)),
                                                requiredIterationCarries=["entry", "iteration", "rollback", "transaction"])
            instance.record_coverage(value, "matched", fixtures.keccak_loop_histories(value))
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedMasks"], coverage["matchedKeyMasks"], coverage["matchedIterationCounts"],
                              coverage["matchedIterationCarries"]), ([7], [1], [2, 3, 7], ["entry", "iteration", "rollback", "transaction"]))
            self.assertEqual((coverage["missingMasks"], coverage["missingKeyMasks"], coverage["missingIterationCounts"],
                              coverage["missingIterationCarries"]), ([0], [3], [0, 1, 4, 5, 6], []))

    def test_the_fixed_corpus_validates_and_its_keccak_loop_requirements_are_checked(self):
        manifest = json.loads((ROOT / "scripts/semantic-keccak-loop-corpus.json").read_text())
        self.assertEqual(campaign.validate_manifest(manifest)["profile"], "stateful-keccak-loops")
        self.assertEqual((manifest["requiredMasks"], manifest["requiredKeyMasks"], manifest["requiredIterationCounts"],
                          manifest["requiredIterationCarries"]),
                         ([0, 1, 3, 7], [0, 1, 3, 7], list(range(8)), ["entry", "iteration", "rollback", "transaction"]))
        for key, changed in (("requiredKeyMasks", [2]), ("requiredKeyMasks", []), ("requiredMasks", [True]),
                             ("requiredIterationCounts", [8]), ("requiredIterationCarries", ["other"]),
                             ("requiredIterationCarries", ["entry", "entry"]), ("requiredCarriedSlots", [2]),
                             ("requiredLogCounts", [0]), ("framingVersion", 1)):
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                campaign.validate_manifest({**manifest, key: changed})
        for key in ("requiredKeyMasks", "requiredIterationCarries", "framingVersion"):
            with self.subTest(key=key), self.assertRaises(ValueError):
                campaign.validate_manifest({name: value for name, value in manifest.items() if name != key})
        # Key masks belong to this profile alone, and loop coverage to the loop profiles.
        loops = json.loads((ROOT / "scripts/semantic-storage-loop-corpus.json").read_text())
        other = json.loads((ROOT / "scripts/semantic-mapping-corpus.json").read_text())
        for value in (loops, other):
            with self.assertRaisesRegex(ValueError, "key-mask coverage belongs to the Keccak-loop profile"):
                campaign.validate_manifest({**value, "requiredKeyMasks": [0, 1, 3, 7]})
        with self.assertRaisesRegex(ValueError, "loop coverage belongs to the storage-loop profile"):
            campaign.validate_manifest({**other, "requiredIterationCounts": list(range(8))})
        with self.assertRaisesRegex(ValueError, "log coverage belongs to the log profile"):
            campaign.validate_manifest({**other, "framingVersion": manifest["framingVersion"]})


class AssemblyLoopCampaignTests(unittest.TestCase):
    def test_coverage_adds_the_form_and_its_iteration_counts_and_carries(self):
        self.assertEqual(campaign.dimensions("stateful-assembly-storage-loops"),
                         campaign.dimensions("stateful-storage-loops") + ("Forms", "FormIterations", "FormCarries"))
        self.assertEqual(campaign.dimensions("stateful-assembly-keccak-loops"),
                         campaign.dimensions("stateful-keccak-loops") + ("Forms", "FormIterations", "FormCarries"))
        self.assertEqual(campaign.versions("stateful-assembly-keccak-loops"), campaign.LOG_VERSIONS)
        self.assertEqual(campaign.versions("stateful-assembly-storage-loops"), campaign.VERSIONS)
        value = fixtures.assembly_case(keccak_loop_case(), "pipelined")
        statuses = ["returned", "reverted", "returned"]
        self.assertEqual(campaign.forms_coverage(value, campaign.keccak_loops_coverage(value, statuses)),
                         {"Forms": {"pipelined"}, "FormIterations": {"pipelined:7", "pipelined:3", "pipelined:2"},
                          "FormCarries": {"pipelined:iteration", "pipelined:entry", "pipelined:rollback",
                                          "pipelined:transaction"}})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-assembly-keccak-loops"))
            instance.summary["coverage"].update(requiredForms=["split", "pipelined"],
                                                requiredFormIterations=["pipelined:0", "pipelined:7"],
                                                requiredFormCarries=["pipelined:entry", "split:entry"])
            instance.record_coverage(value, "matched", fixtures.keccak_loop_histories(value))
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedForms"], coverage["matchedFormIterations"], coverage["matchedMasks"]),
                             (["pipelined"], ["pipelined:2", "pipelined:3", "pipelined:7"], [7]))
            self.assertEqual((coverage["missingForms"], coverage["missingFormIterations"], coverage["missingFormCarries"]),
                             (["split"], ["pipelined:0"], ["split:entry"]))
        # A storage-loop case pairs its form with the storage-loop carries.
        value = fixtures.assembly_case(loop_case(), "split")
        self.assertEqual(campaign.forms_coverage(value, campaign.loops_coverage(value, ["returned", "reverted", "returned", "returned"])),
                         {"Forms": {"split"}, "FormIterations": {"split:7", "split:6", "split:3", "split:0"},
                          "FormCarries": {"split:iteration", "split:rollback"}})

    def test_the_fixed_corpora_validate_and_their_form_requirements_are_checked(self):
        for name, parent in (("assembly-storage-loop", "storage-loop"), ("assembly-keccak-loop", "keccak-loop")):
            manifest = json.loads((ROOT / f"scripts/semantic-{name}-corpus.json").read_text())
            original = json.loads((ROOT / f"scripts/semantic-{parent}-corpus.json").read_text())
            self.assertEqual(campaign.validate_manifest(manifest)["profile"], "stateful-" + name + "s")
            carries = original["requiredIterationCarries"]
            self.assertEqual((manifest["requiredForms"], manifest["requiredFormIterations"], manifest["requiredFormCarries"]),
                             (["split", "carried", "pipelined"],
                              [f"{form}:{count}" for form in ("split", "carried", "pipelined") for count in (0, 1, 7)],
                              [f"{form}:{carry}" for form in ("split", "carried", "pipelined") for carry in carries]))
            for key, changed in (("requiredForms", ["blocks"]), ("requiredForms", []), ("requiredForms", ["split", "split"]),
                                 ("requiredFormIterations", ["split:8"]), ("requiredFormIterations", ["blocks:0"]),
                                 ("requiredFormCarries", ["split:other"]), ("requiredFormCarries", "split:iteration")):
                with self.subTest(name=name, key=key, changed=changed), self.assertRaises(ValueError):
                    campaign.validate_manifest({**manifest, key: changed})
            for key in ("requiredForms", "requiredFormIterations", "requiredFormCarries"):
                with self.subTest(name=name, key=key), self.assertRaises(ValueError):
                    campaign.validate_manifest({name: value for name, value in manifest.items() if name != key})
            # Form coverage belongs to the inline Yul loop profiles alone.
            with self.assertRaisesRegex(ValueError, "form coverage belongs to the inline Yul loop profiles"):
                campaign.validate_manifest({**original, "requiredForms": ["split", "carried", "pipelined"]})
        keccak = json.loads((ROOT / "scripts/semantic-assembly-keccak-loop-corpus.json").read_text())
        with self.assertRaises(ValueError):
            campaign.validate_manifest({**keccak, "requiredFormCarries": ["split:entry", "split:carried"]})
        storage = json.loads((ROOT / "scripts/semantic-assembly-storage-loop-corpus.json").read_text())
        with self.assertRaises(ValueError):
            campaign.validate_manifest({**storage, "requiredFormCarries": ["split:entry"]})


def tuple_case(arity=4, rows=((0, 5), (1, 9), (2, 7)), origin=None):
    value = fixtures.tuple_case(arity, rows)
    value["tupleReturnPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin=origin or {"kind": "imported"})
    return value


class AdtStorageCampaignTests(unittest.TestCase):
    def test_coverage_records_shape_classes_overwrites_updates_stale_reads_keys_and_reverts(self):
        self.assertEqual(campaign.dimensions("stateful-adt-storage"), campaign.DIMENSIONS + tuple(campaign.ADT_EXTRA))
        self.assertEqual(campaign.versions("stateful-adt-storage"), campaign.VERSIONS)
        value = fixtures.adt_case()
        shape = {"AdtVariantCounts": {2}, "AdtPayloads": {"words2", "words0"}, "AdtClearPositions": {"last"},
                 "AdtChoicePositions": {0}, "AdtWordTypes": {"word"},
                 "AdtMethods": {"putChoice", "clearChoice", "getChoice", "putRecordAt", "setRecordAt", "getRecordAt"}}
        # The clear overwrites `V0` with `V1`; key 0's Word field is updated, so
        # both keys of `records` are written across the wrap; the reverted read
        # records nothing, and the record read decodes the variant it wrote.
        statuses = ["returned", "returned", "reverted", "returned", "returned", "returned"]
        self.assertEqual(campaign.adt_coverage(value, statuses), {**shape, "AdtOverwrites": {"2:0>1"},
            "AdtFieldUpdates": {"entry:word"}, "AdtStaleReads": set(), "AdtNeighbourKeys": {"records", "wrap"},
            "AdtRevertedWrites": set()})
        # Returned, the read after the clear decodes `V1` over the stale pair.
        returned = campaign.adt_coverage(value, ["returned"] * 6)
        self.assertEqual(returned["AdtStaleReads"], {"getChoice"})
        # A reverted write commits no variant, so the clear overwrites nothing,
        # and without the update only one key of `records` is written.
        reverted = campaign.adt_coverage(value, ["reverted", "returned", "returned", "returned", "reverted", "returned"])
        self.assertEqual((reverted["AdtOverwrites"], reverted["AdtRevertedWrites"], reverted["AdtNeighbourKeys"],
                          reverted["AdtFieldUpdates"]), (set(), {"putChoice", "setRecordAt"}, set(), set()))
        self.assertEqual(campaign.inputs(value), {"2", "1", "0", "3"})
        value["adtStoragePlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
        value["provenance"].update(features=["local"], origin={"kind": "imported"})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-adt-storage"))
            instance.summary["coverage"].update(requiredAdtOverwrites=["2:0>1", "2:1>0"], requiredAdtStaleReads=["getRecord"])
            instance.record_coverage(value, "matched", fixtures.adt_histories(value))
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedAdtOverwrites"], coverage["matchedAdtNeighbourKeys"]),
                             (["2:0>1"], ["records", "wrap"]))
            self.assertEqual((coverage["missingAdtOverwrites"], coverage["missingAdtStaleReads"]), (["2:1>0"], ["getRecord"]))

    def test_the_fixed_corpus_validates_and_its_requirements_are_checked(self):
        manifest = json.loads((ROOT / "scripts/semantic-adt-storage-corpus.json").read_text())
        self.assertEqual(campaign.validate_manifest(manifest)["profile"], "stateful-adt-storage")
        for dimension, allowed in campaign.ADT_EXTRA.items():
            self.assertEqual(sorted(manifest["required" + dimension], key=str), sorted(allowed, key=str))
        self.assertEqual(len(manifest["requiredAdtOverwrites"]), 20)
        for key, changed in (("requiredAdtOverwrites", ["2:0>2"]), ("requiredAdtOverwrites", []),
                             ("requiredAdtOverwrites", ["2:0>1", "2:0>1"]), ("requiredAdtVariantCounts", [5]),
                             ("requiredAdtVariantCounts", [True]), ("requiredAdtPayloads", ["words4"]),
                             ("requiredAdtStaleReads", ["putChoice"]), ("requiredAdtNeighbourKeys", "wrap"),
                             ("requiredAdtRevertedWrites", ["getChoice"])):
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                campaign.validate_manifest({**manifest, key: changed})
        for dimension in campaign.ADT_EXTRA:
            with self.subTest(dimension=dimension), self.assertRaises(ValueError):
                campaign.validate_manifest({name: value for name, value in manifest.items() if name != "required" + dimension})
        # Imported entries keep one to three transactions, as every fixed corpus does.
        entry = next(entry for entry in manifest["cases"] if "transactions" in entry)
        longer = {**entry, "transactions": entry["transactions"] * 2}
        with self.assertRaises(ValueError):
            campaign.validate_manifest({**manifest, "cases": [longer]})
        # The enum and struct dimensions belong to this profile alone.
        tuple_manifest = json.loads((ROOT / "scripts/semantic-tuple-return-corpus.json").read_text())
        with self.assertRaisesRegex(ValueError, "enum and struct coverage belongs to the enum and struct storage profile"):
            campaign.validate_manifest({**tuple_manifest, "requiredAdtOverwrites": ["2:0>1"]})


class TupleCampaignTests(unittest.TestCase):
    def test_coverage_names_arities_their_outcomes_carries_and_node_budgets(self):
        value = tuple_case()
        self.assertEqual(campaign.dimensions("stateful-tuple-returns"),
                         campaign.DIMENSIONS + ("TupleArities", "ArityOutcomes", "TupleCarries", "NodeBudgets"))
        # tx-2 returns after the committed tx-0 and past the revert of tx-1; an
        # imported case has no node budget.
        self.assertEqual(campaign.tuples_coverage(value, ["returned", "reverted", "returned"]),
                         {"TupleArities": {4}, "ArityOutcomes": {"4:returned", "4:reverted"},
                          "TupleCarries": {"committed", "rollback"}, "NodeBudgets": set()})
        self.assertEqual(campaign.inputs(value), {"5", "7", "9"})
        # A first revert carries nothing committed, and a returned first row carries nothing.
        self.assertEqual(campaign.tuples_coverage(tuple_case(2, rows=((1, 1), (0, 2))), ["reverted", "returned"]),
                         {"TupleArities": {2}, "ArityOutcomes": {"2:reverted", "2:returned"},
                          "TupleCarries": {"rollback"}, "NodeBudgets": set()})
        generated = tuple_case(3, rows=((0, 1),), origin={"kind": "tuple-return-generated", "maxProgramNodes": 512})
        self.assertEqual(campaign.tuples_coverage(generated, ["returned"]),
                         {"TupleArities": {3}, "ArityOutcomes": {"3:returned"}, "TupleCarries": set(), "NodeBudgets": {512}})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-tuple-returns"))
            instance.summary["coverage"].update(requiredTupleArities=[2, 3, 4], requiredNodeBudgets=[384, 512],
                                                requiredArityOutcomes=list(campaign.TUPLE_EXTRA["ArityOutcomes"]))
            histories = fixtures.tuple_histories(value)
            instance.record_coverage(value, "matched", histories)
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedTupleArities"], coverage["matchedArityOutcomes"], coverage["matchedTupleCarries"]),
                             ([4], ["4:returned", "4:reverted"], ["committed", "rollback"]))
            self.assertEqual((coverage["missingTupleArities"], coverage["missingNodeBudgets"], coverage["missingArityOutcomes"]),
                             ([2, 3], [384, 512], ["2:returned", "2:reverted", "3:returned", "3:reverted"]))

    def test_the_fixed_corpus_validates_and_its_tuple_requirements_are_checked(self):
        manifest = json.loads((ROOT / "scripts/semantic-tuple-return-corpus.json").read_text())
        self.assertEqual(campaign.validate_manifest(manifest)["profile"], "stateful-tuple-returns")
        self.assertEqual((manifest["requiredTupleArities"], manifest["requiredNodeBudgets"], manifest["requiredTupleCarries"]),
                         ([2, 3, 4], [384, 512], ["committed", "rollback"]))
        self.assertEqual(manifest["requiredArityOutcomes"], list(campaign.TUPLE_EXTRA["ArityOutcomes"]))
        for key, changed in (("requiredTupleArities", [1]), ("requiredTupleArities", []), ("requiredTupleArities", [True]),
                             ("requiredArityOutcomes", ["5:returned"]), ("requiredTupleCarries", ["other"]),
                             ("requiredNodeBudgets", [448]), ("requiredNodeBudgets", [384, 384])):
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                campaign.validate_manifest({**manifest, key: changed})
        with self.assertRaises(ValueError):
            campaign.validate_manifest({key: value for key, value in manifest.items() if key != "requiredNodeBudgets"})
        other = json.loads((ROOT / "scripts/semantic-storage-loop-corpus.json").read_text())
        with self.assertRaisesRegex(ValueError, "tuple coverage belongs to the tuple-return profile"):
            campaign.validate_manifest({**other, "requiredTupleArities": [2, 3, 4]})


def bytes_return_case(rows=((0, 5, 0), (1, 9, 31), (2, 7, 33)), origin=None):
    value = fixtures.bytes_return_case(rows)
    value["bytesReturnPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin=origin or {"kind": "imported"})
    return value


class BytesReturnCampaignTests(unittest.TestCase):
    def test_coverage_names_returned_lengths_length_outcomes_carries_and_node_budgets(self):
        value = bytes_return_case()
        self.assertEqual(campaign.dimensions("stateful-bytes-returns"),
                         campaign.DIMENSIONS + ("ReturnedLengths", "LengthOutcomes", "ReturnCarries", "ReturnNodeBudgets"))
        # tx-2 returns 33 bytes after the committed tx-0 and past the revert of
        # tx-1; an imported case has no node budget.
        self.assertEqual(campaign.bytes_returns_coverage(value, ["returned", "reverted", "returned"]),
                         {"ReturnedLengths": {0, 33}, "LengthOutcomes": {"empty:returned", "partial:reverted", "partial:returned"},
                          "ReturnCarries": {"committed", "rollback"}, "ReturnNodeBudgets": set()})
        self.assertEqual(campaign.inputs(value), {"5", "7", "9"})
        # A first revert carries nothing committed; a whole-Word length is its own class.
        self.assertEqual(campaign.bytes_returns_coverage(bytes_return_case(rows=((1, 1, 64), (0, 2, 32))), ["reverted", "returned"]),
                         {"ReturnedLengths": {32}, "LengthOutcomes": {"whole:reverted", "whole:returned"},
                          "ReturnCarries": {"rollback"}, "ReturnNodeBudgets": set()})
        generated = bytes_return_case(rows=((0, 1, 1),), origin={"kind": "bytes-return-generated", "maxProgramNodes": 512})
        self.assertEqual(campaign.bytes_returns_coverage(generated, ["returned"]),
                         {"ReturnedLengths": {1}, "LengthOutcomes": {"partial:returned"}, "ReturnCarries": set(),
                          "ReturnNodeBudgets": {512}})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-bytes-returns"))
            instance.summary["coverage"].update(requiredReturnedLengths=[0, 1, 31, 32, 33, 63, 64],
                                                requiredReturnNodeBudgets=[384, 512],
                                                requiredLengthOutcomes=list(campaign.BYTES_RETURN_EXTRA["LengthOutcomes"]))
            histories = fixtures.bytes_return_histories(value)
            instance.record_coverage(value, "matched", histories)
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedReturnedLengths"], coverage["matchedLengthOutcomes"], coverage["matchedReturnCarries"]),
                             ([0, 33], ["empty:returned", "partial:returned", "partial:reverted"], ["committed", "rollback"]))
            self.assertEqual((coverage["missingReturnedLengths"], coverage["missingReturnNodeBudgets"], coverage["missingLengthOutcomes"]),
                             ([1, 31, 32, 63, 64], [384, 512], ["empty:reverted", "whole:returned", "whole:reverted"]))

    def test_the_fixed_corpus_validates_and_its_bytes_return_requirements_are_checked(self):
        manifest = json.loads((ROOT / "scripts/semantic-bytes-return-corpus.json").read_text())
        self.assertEqual(campaign.validate_manifest(manifest)["profile"], "stateful-bytes-returns")
        self.assertEqual((manifest["requiredReturnedLengths"], manifest["requiredReturnNodeBudgets"], manifest["requiredReturnCarries"]),
                         ([0, 1, 31, 32, 33, 63, 64], [384, 512], ["committed", "rollback"]))
        self.assertEqual(manifest["requiredLengthOutcomes"], list(campaign.BYTES_RETURN_EXTRA["LengthOutcomes"]))
        for key, changed in (("requiredReturnedLengths", [65]), ("requiredReturnedLengths", []), ("requiredReturnedLengths", [True]),
                             ("requiredLengthOutcomes", ["full:returned"]), ("requiredReturnCarries", ["other"]),
                             ("requiredReturnNodeBudgets", [448]), ("requiredReturnNodeBudgets", [384, 384])):
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                campaign.validate_manifest({**manifest, key: changed})
        with self.assertRaises(ValueError):
            campaign.validate_manifest({key: value for key, value in manifest.items() if key != "requiredReturnNodeBudgets"})
        other = json.loads((ROOT / "scripts/semantic-tuple-return-corpus.json").read_text())
        with self.assertRaisesRegex(ValueError, "bytes-return coverage belongs to the bytes-return profile"):
            campaign.validate_manifest({**other, "requiredReturnedLengths": [0]})


def enum_return_case(rows=((0, 5, 0, 0), (1, 9, 2, 31), (2, 7, 2, 33)), origin=None, shape=fixtures.ENUM_SHAPE):
    value = fixtures.enum_return_case(rows, shape)
    value["enumReturnPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin=origin or {"kind": "imported"})
    return value


class EnumReturnCampaignTests(unittest.TestCase):
    def test_coverage_names_positions_fields_padding_lengths_bytes_constructors_carries_and_budgets(self):
        value = enum_return_case()
        self.assertEqual(campaign.dimensions("stateful-enum-returns"),
                         campaign.DIMENSIONS + ("EnumPositions", "EnumFields", "EnumPadding", "EnumBytesLengths",
                                                "EnumBytesConstructors", "EnumCarries", "EnumNodeBudgets"))
        # tx-0 returns Pair, as wide as the widest constructor; tx-2 returns Blob
        # with 33 bytes after the committed tx-0 and past the revert of tx-1,
        # narrower than Pair; an imported case has no node budget.
        self.assertEqual(campaign.enum_returns_coverage(value, ["returned", "reverted", "returned"]),
                         {"EnumPositions": {"4:0", "4:2"}, "EnumFields": {"dynamic:two", "dynamic:bytes"},
                          "EnumPadding": {"dynamic:full", "dynamic:padded"}, "EnumBytesLengths": {33},
                          "EnumBytesConstructors": {1}, "EnumCarries": {"committed", "rollback"},
                          "EnumNodeBudgets": set()})
        self.assertEqual(campaign.inputs(value), {"5", "7", "9"})
        # A static enum's widest constructor returns full width; a first revert
        # carries nothing committed.
        static = enum_return_case(rows=((1, 1, 0, 0), (0, 2, 1, 0)), shape=(("Idle", ""), ("Q", "uint256")),
                                  origin={"kind": "enum-return-generated", "maxProgramNodes": 512})
        self.assertEqual(campaign.enum_returns_coverage(static, ["reverted", "returned"]),
                         {"EnumPositions": {"2:1"}, "EnumFields": {"static:one"}, "EnumPadding": {"static:full"},
                          "EnumBytesLengths": set(), "EnumBytesConstructors": {0}, "EnumCarries": {"rollback"},
                          "EnumNodeBudgets": {512}})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-enum-returns"))
            instance.summary["coverage"].update(requiredEnumBytesLengths=[0, 1, 31, 32, 33, 63, 64],
                                                requiredEnumNodeBudgets=[384, 512],
                                                requiredEnumPadding=list(campaign.ENUM_RETURN_EXTRA["EnumPadding"]))
            histories = fixtures.enum_return_histories(value)
            instance.record_coverage(value, "matched", histories)
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedEnumPositions"], coverage["matchedEnumBytesLengths"], coverage["matchedEnumCarries"]),
                             (["4:0", "4:2"], [33], ["committed", "rollback"]))
            self.assertEqual((coverage["missingEnumBytesLengths"], coverage["missingEnumNodeBudgets"], coverage["missingEnumPadding"]),
                             ([0, 1, 31, 32, 63, 64], [384, 512], ["static:full", "static:padded"]))

    def test_the_fixed_corpus_validates_and_its_enum_return_requirements_are_checked(self):
        manifest = json.loads((ROOT / "scripts/semantic-enum-return-corpus.json").read_text())
        self.assertEqual(campaign.validate_manifest(manifest)["profile"], "stateful-enum-returns")
        self.assertEqual((manifest["requiredEnumBytesLengths"], manifest["requiredEnumNodeBudgets"], manifest["requiredEnumCarries"]),
                         ([0, 1, 31, 32, 33, 63, 64], [384, 512], ["committed", "rollback"]))
        for dimension in ("EnumPositions", "EnumFields", "EnumPadding", "EnumBytesConstructors"):
            self.assertEqual(manifest["required" + dimension], list(campaign.ENUM_RETURN_EXTRA[dimension]))
        for key, changed in (("requiredEnumPositions", ["5:0"]), ("requiredEnumFields", ["static:bytes"]),
                             ("requiredEnumPadding", []), ("requiredEnumBytesLengths", [65]),
                             ("requiredEnumBytesLengths", [True]), ("requiredEnumBytesConstructors", [3]),
                             ("requiredEnumCarries", ["other"]), ("requiredEnumNodeBudgets", [448]),
                             ("requiredEnumNodeBudgets", [384, 384])):
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                campaign.validate_manifest({**manifest, key: changed})
        with self.assertRaises(ValueError):
            campaign.validate_manifest({key: value for key, value in manifest.items() if key != "requiredEnumNodeBudgets"})
        other = json.loads((ROOT / "scripts/semantic-bytes-return-corpus.json").read_text())
        with self.assertRaisesRegex(ValueError, "enum-return coverage belongs to the enum-return profile"):
            campaign.validate_manifest({**other, "requiredEnumPositions": ["2:0"]})

    def test_the_synthetic_output_adapter_flips_the_last_word_of_a_multi_word_output(self):
        value = enum_return_case()
        histories = fixtures.enum_return_histories(value)
        report = {"comparison": campaign.adapter.compare(histories, value), "histories": histories}
        analysis = campaign.analyze(report, value, "rustEvm", "tx-2", "output")
        self.assertTrue(analysis["synthetic"])
        self.assertEqual(analysis["comparison"]["category"], "semantic-mismatch")
        self.assertEqual(analysis["comparison"]["transactionId"], "tx-2")
        original = bytes.fromhex(histories["rustEvm"]["transactions"][2]["output"][2:])
        flipped = bytes.fromhex(analysis["histories"]["rustEvm"]["transactions"][2]["output"][2:])
        self.assertEqual((len(flipped), flipped[:-1], flipped[-1]), (len(original), original[:-1], original[-1] ^ 1))
        # A reverted transaction's one Word changes as it always did.
        reverted = campaign.analyze(report, value, "rustEvm", "tx-1", "output")
        self.assertEqual(reverted["histories"]["rustEvm"]["transactions"][1]["output"],
                         "0x" + f"{int(histories['rustEvm']['transactions'][1]['output'], 16) ^ 1:064x}")


def enum_argument_case(rows=((0, 0, 1, 2, 33, None), (1, 1, 7, 0, 0, None), (0, 2, 3, 5, 0, {"kind": "tag", "value": "0"}),
                             (0, 1, 9, 0, 0, None)), origin=None, shape=fixtures.ARGUMENT_SHAPE):
    value = fixtures.enum_argument_case(rows=rows, shape=shape)
    value["enumArgumentPlan"]["stepProgram"] = case()["storagePlan"]["stepProgram"]
    value["provenance"].update({key: "policy-test" for key in campaign.VERSIONS})
    value["provenance"].update(features=["local"], origin=origin or {"kind": "imported"})
    return value


class EnumArgumentCampaignTests(unittest.TestCase):
    def test_coverage_names_decisions_positions_fields_lengths_accepted_kinds_carries_and_budgets(self):
        value = enum_argument_case()
        self.assertEqual(campaign.dimensions("stateful-enum-arguments"),
                         campaign.DIMENSIONS + ("ArgumentPositions", "ArgumentFields", "ArgumentBytesLengths",
                                                "ArgumentBytesConstructors", "ArgumentMalformations", "ArgumentRejections",
                                                "ArgumentAccepted", "ArgumentCarries", "ArgumentNodeBudgets"))
        # tx-0 decodes Blob of 33 bytes and commits; tx-1 decodes Ready and
        # reverts in the body; tx-2's unknown tag is rejected; tx-3 decodes
        # Ready after all three. An imported case has no node budget.
        self.assertEqual(campaign.enum_arguments_coverage(value),
                         {"ArgumentPositions": {"4:0", "4:1"}, "ArgumentFields": {"dynamic:bytes", "dynamic:one"},
                          "ArgumentBytesLengths": {33}, "ArgumentBytesConstructors": {1},
                          "ArgumentMalformations": {"none", "tag"}, "ArgumentRejections": {"accepted", "0x"},
                          "ArgumentAccepted": set(), "ArgumentCarries": {"committed", "rollback", "rejection"},
                          "ArgumentNodeBudgets": set()})
        # The inputs are the Word fields of Word constructors.
        self.assertEqual(campaign.inputs(value), {"3", "5", "7", "9"})
        # A struct in a static enum, an accepted retag and a generated budget.
        static = enum_argument_case(rows=((0, 0, 1, 2, 0, None), (0, 0, 3, 4, 0, {"kind": "retag", "constructor": 1})),
                                    shape=(("Ready", "ScPair"), ("Idle", "")),
                                    origin={"kind": "enum-argument-generated", "maxProgramNodes": 512})
        self.assertEqual(campaign.enum_arguments_coverage(static),
                         {"ArgumentPositions": {"2:0", "2:1"}, "ArgumentFields": {"static:pair", "static:none"},
                          "ArgumentBytesLengths": set(), "ArgumentBytesConstructors": {0},
                          "ArgumentMalformations": {"none", "retag"}, "ArgumentRejections": {"accepted"},
                          "ArgumentAccepted": {"retag"}, "ArgumentCarries": {"committed"}, "ArgumentNodeBudgets": {512}})
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory, profile="stateful-enum-arguments"))
            instance.summary["coverage"].update(requiredArgumentBytesLengths=[0, 1, 31, 32, 33, 63, 64],
                                                requiredArgumentNodeBudgets=[384, 512],
                                                requiredArgumentRejections=["0x4924aef0", "0x08638556", "0x"])
            histories = fixtures.enum_argument_histories(value)
            instance.record_coverage(value, "matched", histories)
            instance.checkpoint()
            coverage = instance.summary["coverage"]
            self.assertEqual((coverage["matchedArgumentPositions"], coverage["matchedArgumentRejections"],
                              coverage["matchedArgumentCarries"]),
                             (["4:0", "4:1"], ["0x", "accepted"], ["committed", "rejection", "rollback"]))
            self.assertEqual((coverage["missingArgumentBytesLengths"], coverage["missingArgumentNodeBudgets"],
                              coverage["missingArgumentRejections"]),
                             ([0, 1, 31, 32, 63, 64], [384, 512], ["0x08638556", "0x4924aef0"]))
            # The selector and empty-revert rows are recorded in the analysis.
            report = {"comparison": campaign.adapter.compare(histories, value), "histories": histories}
            self.assertEqual(report["comparison"]["selectorRows"], [{"id": "tx-2", "index": 2, "selector": "0x"}])

    def test_the_fixed_corpus_validates_and_its_enum_argument_requirements_are_checked(self):
        manifest = json.loads((ROOT / "scripts/semantic-enum-argument-corpus.json").read_text())
        self.assertEqual(campaign.validate_manifest(manifest)["profile"], "stateful-enum-arguments")
        self.assertEqual((manifest["requiredArgumentBytesLengths"], manifest["requiredArgumentNodeBudgets"],
                          manifest["requiredArgumentCarries"]),
                         ([0, 1, 31, 32, 33, 63, 64], [384, 512], ["committed", "rollback", "rejection"]))
        for dimension in ("ArgumentPositions", "ArgumentFields", "ArgumentBytesConstructors", "ArgumentMalformations"):
            self.assertEqual(manifest["required" + dimension], list(campaign.ENUM_ARGUMENT_EXTRA[dimension]))
        self.assertEqual(manifest["requiredArgumentRejections"], ["0x4924aef0", "0x08638556", "0x"])
        for key, changed in (("requiredArgumentPositions", ["5:0"]), ("requiredArgumentFields", ["static:bytes"]),
                             ("requiredArgumentBytesLengths", [1025]), ("requiredArgumentBytesLengths", [True]),
                             ("requiredArgumentBytesConstructors", [3]), ("requiredArgumentMalformations", ["other"]),
                             ("requiredArgumentRejections", ["0x7f52b2bf"]), ("requiredArgumentAccepted", ["none"]),
                             ("requiredArgumentCarries", ["other"]), ("requiredArgumentNodeBudgets", [448]),
                             ("requiredArgumentNodeBudgets", [384, 384])):
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                campaign.validate_manifest({**manifest, key: changed})
        with self.assertRaises(ValueError):
            campaign.validate_manifest({key: value for key, value in manifest.items() if key != "requiredArgumentCarries"})
        other = json.loads((ROOT / "scripts/semantic-enum-return-corpus.json").read_text())
        with self.assertRaisesRegex(ValueError, "enum-argument coverage belongs to the enum-argument profile"):
            campaign.validate_manifest({**other, "requiredArgumentPositions": ["2:0"]})

if __name__ == "__main__":
    unittest.main()
