#!/usr/bin/env python3
"""Check the fixed shift corpus using fresh native Core executions.

The corpus takes, from seed 1 upwards at the default budget, every generated
plan that covers a missing shape value, each at the eight primitive boundary
inputs; every value is required. This test runs the checked arithmetic corpus
checker's walk with the shift profile: its admission of the value and amount
types, inputs and shifts, its interpreter, which shifts Python integers by the
amount and wraps a left shift to the width, its shapes, shrink measure and
exact re-emission, and native replay, observation and shrinking. It neither
compiles Rust nor executes an EVM.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("shift_corpus_integers", ROOT / "Tests/scripts/test-semantic-checked-arithmetic-corpus.py")
integers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(integers)


if __name__ == "__main__":
    integers.main(integers.SHIFTS)
