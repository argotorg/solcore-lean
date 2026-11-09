#!/usr/bin/env python3
"""Check the fixed closure factory corpus with the closure capture corpus's walk:
its own admission, interpreter, shapes, shrink measure and emission, and native
replay, observation and shrinking. It neither compiles Rust nor executes an
EVM."""
from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("closure_corpus", ROOT / "Tests/scripts/test-semantic-closure-captures-corpus.py")
closures = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(closures)


if __name__ == "__main__":
    closures.main(closures.FACTORIES)
