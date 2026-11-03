#!/usr/bin/env python3
"""Check the pinned compiler's refusal of recursive runtime layouts through the actual exporter.

Requires the retained checked-Hull driver; does not build or modify Rust.
Since solcore-rs #130 the checked compiler reports SC0420 before backend
emission for every concrete recursive layout that would need boxing: the
three local fixtures, which construct, relay and match a recursive enum at
runtime, and upstream's recursive layout fixtures. The checked export and
both driver backends refuse each with that diagnostic alone. Lean's recursive
Hull representation stays covered by its Lean tests. Exports are temporary.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
FIXTURES = ROOT / "tests/Fixtures/RustHullRecursive"
REFUSAL = "recursive runtime values are not supported"
# Upstream's layout fixtures that its tests mark `unsupported-recursive`; at
# 2a745e12 these two were finite layouts that the checked export accepted.
UPSTREAM_LAYOUTS = ("finite_regular", "finite_wrapped_regular")


def refused(result: subprocess.CompletedProcess) -> bool:
    codes = set(re.findall(r"error\[(SC\d+)\]", result.stderr))
    return result.returncode != 0 and codes == {"SC0420"} and REFUSAL in result.stderr


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261102")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--evm-reference", action="store_true",
                        help="also require both driver backends, Sonatina and Yul, to refuse the local fixtures")
    args = parser.parse_args()

    def run(command: list[str]) -> subprocess.CompletedProcess:
        return subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=args.timeout)

    driver = args.target_dir / "debug/solcore-driver"
    sources = [(name, FIXTURES / f"{name}.sol") for name in ("base", "nested", "unfold")]
    sources += [(name, args.upstream / "crates/hull/tests/fixtures/layouts" / name / "main.sol") for name in UPSTREAM_LAYOUTS]
    with tempfile.TemporaryDirectory(prefix="recursive-layouts-", dir=ROOT / ".upstream") as directory:
        for name, source in sources:
            output = Path(directory) / f"{name}.json"
            exported = run([sys.executable, str(ROOT / "scripts/export-rust-hull.py"), str(source),
                            "--upstream", str(args.upstream), "--target-dir", str(args.target_dir),
                            "--output", str(output)])
            if not refused(exported) or output.exists():
                raise ValueError(f"expected the checked export to refuse {name} with SC0420 alone: "
                                 f"{exported.stdout}{exported.stderr}")
            print(f"{name}: the checked compiler refuses its recursive runtime layout (SC0420)")
        if args.evm_reference:
            for name, source in sources[:3]:
                for emit in ("--emit-sonatina", "--emit-yul"):
                    emitted = run([str(driver), str(source), "--std-root", str(args.upstream / "std"), emit])
                    if not refused(emitted):
                        raise ValueError(f"expected {emit} to refuse {name} with SC0420 alone: {emitted.stderr}")
                print(f"{name}: Sonatina and Yul emission refuse it as well")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"recursive-layouts: {error}", file=sys.stderr)
        raise SystemExit(1)
