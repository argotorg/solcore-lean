#!/usr/bin/env python3
"""Regression checks for raw directive extraction and scenario result accounting."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("scenario_parity", ROOT / "scripts/rust-scenario-parity.py")
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)


def lines(*rows):
    return "\n".join(json.dumps(row) for row in rows)


DEPLOYED = {"stage": "deployment", "status": "returned", "output": "0x6000"}
CALL = {"stage": "execution", "status": "returned", "output": "0x", "index": 0}


class ResultTests(unittest.TestCase):
    def test_manifests_partition_the_pinned_fixture_catalog(self):
        upstream = ROOT / ".upstream/solcore-rs-20261023/tests/e2e"
        if not upstream.exists():
            self.skipTest("pinned reference checkout is absent")
        raw = json.loads((ROOT / "scripts/rust-scenario-parity.json").read_text())["fixtures"]
        methods = json.loads((ROOT / "scripts/rust-method-parity.json").read_text())["fixtures"]
        raw_ids, method_ids = {item["id"] for item in raw}, {item["id"] for item in methods}
        self.assertTrue(raw_ids.isdisjoint(method_ids))
        self.assertEqual(raw_ids | method_ids, {path.parent.name for path in upstream.glob("*/main.sol")})
        self.assertEqual(sum(item["expectedCallCount"] for item in raw), 626)
        self.assertEqual(sum(item["expectedCallCount"] for item in methods), 618)

    def test_runtime_prepare_failure_keeps_deployment(self):
        failed = {"stage": "preparation", "status": "rejected", "detail": "external call"}
        self.assertEqual(parity.results(lines(DEPLOYED, failed), "", 1, 3), [DEPLOYED, failed, failed])

    def test_malformed_completion_is_not_a_pass(self):
        for output in (None, "0x0", "garbage"):
            self.assertEqual(parity.results(lines({**DEPLOYED, "output": output}), "", 0, 1)[0]["status"], "error")

    def test_constructor_revert_blocks_calls(self):
        reverted = {"stage": "deployment", "status": "reverted", "output": "0x12"}
        actual = parity.results(lines(reverted), "", 0, 2)
        self.assertEqual(actual[0], reverted)
        self.assertEqual(actual[1]["status"], "not-executed")

    def test_invalid_order_and_unexplained_exit_fail(self):
        for text, code in [(lines(DEPLOYED, {**CALL, "index": 1}), 0), (lines(DEPLOYED, CALL), 1)]:
            self.assertTrue(all(row["status"] == "error" for row in parity.results(text, "", code, 2)))

    def test_timeout_retains_completed_prefix(self):
        result = parity.results(lines(DEPLOYED, CALL), "timeout", None, 3)
        self.assertEqual(result[:2], [DEPLOYED, CALL])
        self.assertEqual(result[2]["status"], "timeout")

    def test_fault_does_not_taint_other_results(self):
        fault = {"stage": "execution", "status": "core-fault", "index": 0}
        later = {**CALL, "index": 1}
        self.assertEqual(parity.results(lines(DEPLOYED, fault, later), "", 1, 3), [DEPLOYED, fault, later])

    def test_exact_and_wildcard_reverts(self):
        actual = {"stage": "execution", "status": "reverted", "output": "0x12"}
        for output, expected in [(None, "succeeded"), ("0x12", "succeeded"), ("0x", "mismatch")]:
            row = {"expectedStage": "execution", "expected": {"status": "reverted", "output": output}}
            parity.compare(row, actual)
            self.assertEqual(row["status"], expected)

    def test_gas_is_absent_by_default(self):
        call = {"calldata": "0x", "value": "0x2a"}
        self.assertNotIn("availableGas", parity.context(call, None))
        self.assertEqual(parity.context(call, "30000000")["availableGas"], "30000000")
        self.assertEqual(parity.context(call, None)["value"], "42")


class ExtractorTests(unittest.TestCase):
    binary = ROOT / ".upstream/rust-parity-target/debug/solcore-directive-export"
    upstream = ROOT / ".upstream/solcore-rs-20261023"

    @classmethod
    def setUpClass(cls):
        if not cls.binary.exists():
            raise unittest.SkipTest("build export-rust-directives.py --build to check the pinned extractor")

    def fixture(self, name):
        return json.loads(subprocess.check_output([str(self.binary), str(self.upstream / f"tests/e2e/{name}/main.sol")], text=True))

    def test_raw_stateful_sequence_and_constructor_revert(self):
        raw = self.fixture("raw-vector")
        self.assertEqual(raw["mode"], "raw")
        self.assertEqual(len(raw["scenario"]["calls"]), 4)
        self.assertEqual(int(raw["scenario"]["calls"][-1]["expected"]["output"], 16), 41)
        rejected = self.fixture("nonpayable-ctor")["scenario"]
        self.assertFalse(rejected["constructor"]["expectedSuccess"])
        self.assertEqual(rejected["constructor"]["expectedOutput"], "0xb5988ea3")
        self.assertEqual(int(rejected["constructor"]["value"], 16), 42)

    def test_method_directives_stay_separate(self):
        document = self.fixture("00answer")
        self.assertEqual(document["mode"], "methods")
        self.assertIsNone(document["scenario"])
        self.assertEqual(document["methods"][0]["directives"][0]["directive"]["action"]["expected"]["values"][0]["value"], "0x" + f"{42:064x}")

    def test_malformed_or_mixed_directives_rejected(self):
        sources = [
            '// #[scenario("bad")]\n// #[raw(0x0) -> success(0x)]\ncontract C {}',
            '// #[scenario("mixed")]\n// #[raw(0x) -> success(0x)]\ncontract C {\n// #[() -> 1]\nfunction f() public returns (Word) { return 1; }\n}',
            '// #[() -> 1]\nfunction outside() returns (Word) { return 1; }',
        ]
        with tempfile.TemporaryDirectory(prefix="solcore-directive-test-") as directory:
            file = Path(directory) / "main.sol"
            for source in sources:
                file.write_text(source)
                result = subprocess.run([str(self.binary), str(file)], text=True, capture_output=True)
                self.assertNotEqual(result.returncode, 0, result.stdout)


if __name__ == "__main__":
    unittest.main()
