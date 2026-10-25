#!/usr/bin/env python3
"""Finding-validator policy fixtures; these tests do not simulate a compiler/EVM.

The separate check-semantic-findings.py command executes the real toolchain.
"""
import contextlib
import copy
import importlib.util
import io
import json
from pathlib import Path
import signal
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("findings_policy", ROOT / "scripts/check-semantic-findings.py")
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


def policy_report():
    raw = {"directCore": {"stage": "execution", "status": "returned", "word": "7"},
           "importedHull": {"stage": "execution", "status": "returned", "output": "0x" + f"{7:064x}"},
           "rustEvm": {"stage": "execution", "status": "returned", "output": "0x" + f"{7:064x}"}}
    observed = {key: check.m2.normalize_observation(value, direct=key == "directCore") for key, value in raw.items()}
    return {"schema": check.m2.REPORT_SCHEMA, "rawObservations": raw, "observations": observed,
            "comparison": check.m2.compare(observed), "policyFixture": "not an execution report"}


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value))


class FindingsPolicyTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="findings-policy-")
        self.root = Path(self.temporary.name).resolve()

    def tearDown(self):
        self.temporary.cleanup()

    def fixture(self, accepted=True):
        folder = self.root / "policy-campaign"
        report = policy_report()
        analysis = check.campaign.analyze(report, "rustEvm")
        fingerprint = check.campaign.fingerprint(analysis)
        original, final = "findings/synthetic/0000/original", "findings/synthetic/0000/reduced"
        for archive in (original, final):
            save(folder / archive / "report.json", report)
            save(folder / archive / "analysis.json", analysis)
        steps = [{"attempt": 1, "accepted": True, "fingerprint": fingerprint,
                  "comparison": analysis["comparison"], "actualComparison": report["comparison"]}] if accepted else []
        finding = {"synthetic": True, "fingerprint": fingerprint, "originalArchive": original,
                   "finalArchive": final, "history": "findings/synthetic/0000/shrink.json",
                   "originalProgramSha256": "policy-original", "finalProgramSha256": "policy-reduced" if accepted else "policy-original"}
        history = {"fingerprint": fingerprint, "finalArchive": final,
                   "finalProgramSha256": finding["finalProgramSha256"], "status": "attempt-limit" if accepted else "no-attempts",
                   "steps": steps}
        counts = {key: 1 for key in ("generated", "executed", "completed", "mismatched", "syntheticMismatches")}
        counts.update({key: 0 for key in ("matched", "unexecuted", "inconclusive", "errors", "sourceRejected", "compilationRejected")})
        summary = {"schema": check.campaign.SCHEMA, "status": "complete", "synthetic": True,
                   "testAdapter": {"name": check.campaign.TEST_ADAPTER, "path": "rustEvm"},
                   "counts": counts, "secondaryFindings": [], "findings": [finding], "shrinkAttempts": len(steps)}
        save(folder / "summary.json", summary)
        save(folder / finding["history"], history)
        return folder, summary, history

    def test_raw_match_and_synthetic_copy_are_separate(self):
        report = policy_report()
        before = copy.deepcopy(report)
        check.actual_match(report)
        analysis = check.campaign.analyze(report, "rustEvm")
        self.assertEqual(report, before)
        self.assertEqual(analysis["actualComparison"]["category"], "matched")
        self.assertEqual(analysis["comparison"]["category"], "semantic-mismatch")

    def test_saved_match_cannot_hide_changed_raw_observation(self):
        report = policy_report()
        report["rawObservations"]["rustEvm"]["output"] = "0x" + f"{8:064x}"
        with self.assertRaises(check.CheckFailure):
            check.actual_match(report)

    def test_real_mismatch_is_not_a_passing_controlled_test(self):
        report = policy_report()
        report["rawObservations"]["directCore"]["word"] = "8"
        report["observations"]["directCore"]["word"] = "8"
        report["comparison"] = check.m2.compare(report["observations"])
        with self.assertRaises(check.CheckFailure):
            check.actual_match(report)

    def test_synthetic_policy_accepts_bounded_reduction_and_same_fingerprint(self):
        folder, _, _ = self.fixture()
        result = check.verify_synthetic(folder, 1, True)
        self.assertEqual((result["attempts"], result["acceptedReductions"]), (1, 1))

    def test_irreducible_case_is_not_shrink_coverage(self):
        folder, _, _ = self.fixture(False)
        with self.assertRaisesRegex(check.CheckFailure, "no accepted smaller"):
            check.verify_synthetic(folder, 1, True)
        self.assertEqual(check.verify_synthetic(folder, 1, False)["attempts"], 0)

    def test_nonzero_and_complete_counts_are_both_required(self):
        folder, summary, _ = self.fixture()
        for code in (0, -15, 2):
            with self.assertRaises(check.CheckFailure):
                check.verify_synthetic(folder, code, True)
        summary["counts"]["inconclusive"] = 1
        save(folder / "summary.json", summary)
        with self.assertRaises(check.CheckFailure):
            check.verify_synthetic(folder, 1, True)

    def test_secondary_genuine_finding_cannot_be_suppressed(self):
        folder, summary, _ = self.fixture()
        summary["secondaryFindings"] = [{"fingerprint": {"category": "semantic-mismatch", "synthetic": False}}]
        save(folder / "summary.json", summary)
        with self.assertRaisesRegex(check.CheckFailure, "secondary"):
            check.verify_synthetic(folder, 1, True)

    def test_corrupt_copy_and_failed_candidate_rejected(self):
        folder, summary, history = self.fixture()
        archive = folder / summary["findings"][0]["finalArchive"]
        analysis = json.loads((archive / "analysis.json").read_text())
        analysis["observations"]["directCore"]["word"] = "8"
        save(archive / "analysis.json", analysis)
        with self.assertRaisesRegex(check.CheckFailure, "analysis"):
            check.verify_synthetic(folder, 1, True)
        save(archive / "analysis.json", check.campaign.analyze(policy_report(), "rustEvm"))
        history["steps"][0]["actualComparison"]["category"] = "inconclusive-resource"
        save(folder / summary["findings"][0]["history"], history)
        with self.assertRaisesRegex(check.CheckFailure, "actual execution"):
            check.verify_synthetic(folder, 1, True)

    def test_missing_escape_and_symlink_archives_rejected(self):
        (self.root / "file").write_text("policy")
        (self.root / "link").symlink_to(self.root / "file")
        for relative in ("missing", "../escape", str(self.root / "file"), "link"):
            with self.assertRaises(check.CheckFailure):
                check.safe_member(self.root, relative)

    def test_only_actual_direct_fuel_exhaustion_passes_resource_gate(self):
        report = {"schema": check.m2.REPORT_SCHEMA, "comparison": {"category": "inconclusive-resource"},
                  "budgets": {"direct_fuel": 1}, "rawObservations": {"directCore": {"status": "out-of-fuel"}},
                  "observations": {"directCore": {"status": "out-of-fuel"}}}
        check.verify_resource(report, 1)
        with self.assertRaises(check.CheckFailure):
            check.verify_resource(report, 0)
        report["rawObservations"]["directCore"]["status"] = "returned"
        with self.assertRaises(check.CheckFailure):
            check.verify_resource(report, 1)

    def test_command_forwards_tools_and_uses_real_campaign_test_adapter(self):
        case = self.root / "case.json"
        case.write_text("policy")
        args = check.parse_args(["--case", str(case), "--output", str(self.root / "output"),
                                 "--anvil", "/policy/anvil", "--case-tool", "/policy/case-tool"])
        args.output.mkdir()
        verification = check.Verification(args)
        command = verification.campaign_command(case, args.output / "synthetic", 4)
        self.assertEqual(Path(command[1]).name, "semantic-campaign.py")
        self.assertEqual(command[command.index("--test-perturb-path") + 1], "rustEvm")
        self.assertEqual(command[command.index("--shrink-attempts") + 1], "4")
        self.assertIn("/policy/anvil", command)
        self.assertIn("/policy/case-tool", command)
        verification.deadline = time.monotonic() - 1
        with patch.object(check.suite, "run_process") as launch, self.assertRaises(check.CheckFailure) as failure:
            verification.process(check.PHASES[0], command)
        self.assertEqual(failure.exception.category, "inconclusive-resource")
        launch.assert_not_called()

    def test_main_restores_handler_and_records_unexecuted_checks(self):
        case = self.root / "case.json"
        case.write_text("policy fixture")
        output = self.root / "output"
        before = signal.getsignal(signal.SIGTERM)
        with patch.object(check.m2, "read_json", return_value={}), patch.object(check.m2, "validate_case"), \
                patch.object(check.Verification, "run", side_effect=KeyboardInterrupt), contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(check.main(["--case", str(case), "--output", str(output)]), 1)
        self.assertEqual(signal.getsignal(signal.SIGTERM), before)
        report = json.loads((output / "verification.json").read_text())
        self.assertEqual(report["status"], "inconclusive-resource")
        self.assertEqual(report["unexecuted"], list(check.PHASES))

    def test_invalid_limits_and_existing_output_fail(self):
        for key, value in (("seconds", "nan"), ("seconds", "0"), ("disk-bytes", "1")):
            with self.assertRaises(check.CheckFailure):
                check.parse_args(["--case", "policy", "--output", "policy", "--" + key, value])
        with patch.object(check.m2, "read_json", return_value={}), patch.object(check.m2, "validate_case"), self.assertRaises(FileExistsError):
            check.main(["--case", "policy", "--output", str(self.root)])


if __name__ == "__main__":
    unittest.main()
