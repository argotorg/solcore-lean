#!/usr/bin/env python3
"""Run all twenty newly supported std.opcodes wrappers through checked Rust Hull.

Requires the retained pinned exporter and existing Lean artifacts; no compiler
binaries are rebuilt. Five source contracts exercise all twelve ambient reads,
three external-code reads, CALLCODE, DELEGATECALL, CREATE, CREATE2, and
SELFDESTRUCT. The Core runner checks outputs, account changes, missing context,
and static restrictions. Exports and provenance sidecars are temporary.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "Tests/Fixtures/RustHullOpcodes/main.sol"
WRAPPERS = {
    "origin", "gasprice", "coinbase", "timestamp", "number", "prevrandao",
    "gaslimit", "chainid", "basefee", "blobbasefee", "blockhash", "blobhash",
    "extcodesize", "extcodecopy", "extcodehash", "callcode", "delegatecall",
    "create", "create2", "selfdestruct",
}


def verify_call_sites(envelope: dict) -> None:
    source_calls, assembly_calls = set(), set()
    pending = [envelope]
    while pending:
        item = pending.pop()
        if isinstance(item, dict):
            if item.get("tag") == "call":
                file = (item.get("span") or {}).get("file", "")
                callee = item.get("callee", "")
                if file == SOURCE.as_uri():
                    for name in WRAPPERS:
                        if callee.startswith(f"opcodes_{name}_d"):
                            source_calls.add(name)
                name = item.get("name", {})
                if file.endswith("/std/opcodes.sol") and isinstance(name, dict):
                    assembly_calls.add(name.get("name"))
            pending.extend(item.values())
        elif isinstance(item, list):
            pending.extend(item)
    if WRAPPERS - source_calls:
        raise ValueError(f"checked export lost source wrapper calls: {sorted(WRAPPERS - source_calls)}")
    if WRAPPERS - assembly_calls:
        raise ValueError(f"checked export lost std assembly bodies: {sorted(WRAPPERS - assembly_calls)}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--timeout", type=float, default=120)
    args = parser.parse_args()

    def run(command: list[str]) -> subprocess.CompletedProcess:
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=args.timeout)
        if result.returncode:
            raise ValueError(f"command failed: {' '.join(command)}\n{result.stdout}{result.stderr}")
        return result

    with tempfile.TemporaryDirectory(prefix="opcode-wrappers-", dir=ROOT / ".upstream") as directory:
        output = Path(directory) / "hull.json"
        run([sys.executable, str(ROOT / "scripts/export-rust-hull.py"), str(SOURCE),
             "--upstream", str(args.upstream), "--target-dir", str(args.target_dir),
             "--output", str(output)])
        verify_call_sites(json.loads(output.read_text()))
        result = run(["lake", "env", "lean", "--run", "Tests/RustHullOpcodeWrappersRun.lean", str(output)])
        print(result.stdout, end="")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"opcode-wrappers: {error}", file=sys.stderr)
        raise SystemExit(1)
