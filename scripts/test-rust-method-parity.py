#!/usr/bin/env python3
"""Check upstream ABI resolution, send persistence, and caller selection."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("method_parity", ROOT / "scripts/rust-method-parity.py")
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)


class MethodTests(unittest.TestCase):
    binary = ROOT / ".upstream/rust-parity-target/debug/solcore-directive-resolve"

    def resolve(self, comments, inputs=None, outputs=None):
        if not self.binary.exists():
            self.skipTest("build-rust-directive-resolver.py is required")
        target = {"contract": "C", "method": "f", "signature": "f()", "selector": "0x12345678",
            "inputs": inputs or [], "outputs": outputs or [], "comments": comments}
        with tempfile.TemporaryDirectory(prefix="solcore-resolver-test-") as directory:
            file = Path(directory) / "input.json"
            file.write_text(json.dumps({"schema": "solcore-rs.method-resolution-input.v1", "targets": [target]}))
            return subprocess.run([str(self.binary), str(file)], text=True, capture_output=True)

    def test_call_and_send_have_different_state_and_caller(self):
        result = self.resolve(["#[() -> ()]", "#[send()]", "#[() -> revert(0x12)]", "#[() -> revert]"])
        self.assertEqual(result.returncode, 0, result.stderr)
        calls = json.loads(result.stdout)["calls"]
        self.assertEqual([call["persist"] for call in calls], [False, True, False, False])
        self.assertEqual([call["expected"]["output"] for call in calls], ["0x", None, "0x12", None])
        self.assertEqual(parity.call_context("0x", False, None)["caller"], "0")
        self.assertEqual(parity.call_context("0x", True, None)["caller"], str(int(parity.METHOD_SENDER, 16)))

    def test_nested_tuple_unit_and_bool_use_upstream_encoding(self):
        shape = {"type": "tuple", "components": [{"type": "uint256"}, {"type": "bool"}, {"type": "tuple", "components": []}]}
        result = self.resolve(["#[((42, true, ())) -> ((42, true, ())) ]"], [shape], [shape])
        self.assertEqual(result.returncode, 0, result.stderr)
        call = json.loads(result.stdout)["calls"][0]
        expected = f"{42:064x}{1:064x}"
        self.assertEqual(call["calldata"], "0x12345678" + expected)
        self.assertEqual(call["expected"]["output"], "0x" + expected)

    def test_invalid_shapes_and_values_rejected(self):
        for comment, shape in [("#[(1) -> ()]", {"type": "bool"}), ("#[(1) -> ()]", {"type": "uint256[]"})]:
            result = self.resolve([comment], [shape])
            self.assertNotEqual(result.returncode, 0)

    def test_empty_output_and_multiple_scalar_outputs(self):
        result = self.resolve(["#[() -> (1, false)]"], outputs=[{"type": "uint256"}, {"type": "bool"}])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["calls"][0]["expected"]["output"], "0x" + f"{1:064x}{0:064x}")


if __name__ == "__main__":
    unittest.main()
