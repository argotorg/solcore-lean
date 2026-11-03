#!/usr/bin/env python3
"""Check the fixed array ABI corpus with the memory array corpus's walk: its own
admission, interpreter, shapes, shrink measure and emission, the calldata of
the T[] and calldata<T[]> parameters encoded from the ABI specification with
selectors from keccak256, and native replay, observation and shrinking. It
neither compiles Rust nor executes an EVM."""
from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("array_corpus", ROOT / "Tests/scripts/test-semantic-memory-array-corpus.py")
arrays = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(arrays)


if __name__ == "__main__":
    arrays.main(arrays.ABI)
