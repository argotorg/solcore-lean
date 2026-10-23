#!/usr/bin/env python3
"""Keep missing, skipped and rejected EVM tests distinct from executed passes."""
import importlib.util
from pathlib import Path
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("reference", Path(__file__).with_name("rust-evm-reference.py"))
reference = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reference)


class Classification(unittest.TestCase):
    def result(self, text, exit_code=0):
        return reference.outcome(subprocess.CompletedProcess([], exit_code, text, ""))

    def test_executed_pass(self):
        self.assertEqual(self.result("test result: ok. 1 passed; 0 failed; 0 ignored;"), ("passed", "evm"))

    def test_empty_or_multiple_selection_is_not_pass(self):
        for count in [0, 2]:
            self.assertEqual(self.result(f"test result: ok. {count} passed; 0 failed; 0 ignored;"),
                             ("failed", "harness"))

    def test_skip_is_not_pass(self):
        self.assertEqual(self.result("test result: ok. 0 passed; 0 failed; 1 ignored;"), ("skipped", "tooling"))
        self.assertEqual(self.result("skipping E2E: missing anvil\ntest result: ok. 1 passed; 0 failed; 0 ignored;"),
                         ("skipped", "tooling"))

    def test_yul_skip_is_not_pass(self):
        self.assertEqual(self.result("skipping Yul E2E execution: missing solc\ntest result: ok. 1 passed; 0 failed; 0 ignored;"),
                         ("skipped", "tooling"))

    def test_failure_stage_and_nonzero_exit(self):
        self.assertEqual(self.result("fixture failed: Tooling: denied\ntest result: FAILED. 0 passed; 1 failed; 0 ignored;", 101),
                         ("failed", "tooling"))
        self.assertEqual(self.result("fixture failed: Mismatch: bytes\ntest result: FAILED. 0 passed; 1 failed; 0 ignored;", 101),
                         ("failed", "mismatch"))
        self.assertEqual(self.result("test result: ok. 1 passed; 0 failed; 0 ignored;", 1), ("failed", "harness"))


if __name__ == "__main__":
    unittest.main()
