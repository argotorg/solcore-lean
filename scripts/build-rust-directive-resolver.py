#!/usr/bin/env python3
"""Build the pinned upstream method-directive resolver without the Rust workspace."""
from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.dont_write_bytecode = True
_spec = importlib.util.spec_from_file_location("directive_export", ROOT / "scripts/export-rust-directives.py")
assert _spec and _spec.loader
export = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(export)
SOURCE = ROOT / "scripts/rust-directive-resolve.rs"
TOOL = ROOT / ".upstream/rust-directive-resolve-tool"


def manifest(upstream: Path) -> str:
    dependency = json.dumps(str(upstream / "crates/test-directives"))
    return f'''[package]
name = "solcore-directive-resolve"
version = "0.1.0"
edition = "2024"
rust-version = "1.97.0"
[workspace]
[dependencies]
serde_json = "=1.0.151"
solcore-test-directives = {{ path = {dependency} }}
'''


def identity(upstream: Path, target: Path) -> dict:
    if export.pins(TOOL / "Cargo.lock") - export.pins(upstream / "Cargo.lock"):
        raise ValueError("resolver dependencies differ from pinned upstream")
    return {"upstreamCommit": export.hull.COMMIT,
        "sourceSha256": export.hull.digest(SOURCE.read_bytes()),
        "manifestSha256": export.hull.digest(manifest(upstream).encode()),
        "lockSha256": export.hull.digest((TOOL / "Cargo.lock").read_bytes()),
        "binarySha256": export.hull.digest((target / "debug/solcore-directive-resolve").read_bytes())}


def checked_identity(upstream: Path, target: Path) -> dict:
    current = identity(upstream, target)
    if json.loads((target / "directive-resolve-build.json").read_text()) != current:
        raise ValueError("method resolver receipt is stale; run build-rust-directive-resolver.py")
    return current


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    args = parser.parse_args()
    upstream, target = args.upstream.resolve(), args.target_dir.resolve()
    if not target.is_relative_to((ROOT / ".upstream").resolve()):
        raise ValueError("disposable Cargo target must stay inside .upstream")
    export.hull.prepare(upstream)
    (TOOL / "src").mkdir(parents=True, exist_ok=True)
    (TOOL / "Cargo.toml").write_text(manifest(upstream))
    (TOOL / "src/main.rs").write_bytes(SOURCE.read_bytes())
    if not (TOOL / "Cargo.lock").exists():
        (TOOL / "Cargo.lock").write_bytes((upstream / "Cargo.lock").read_bytes())
    subprocess.run(["cargo", "build", "--offline", "--manifest-path", str(TOOL / "Cargo.toml"),
        "--target-dir", str(target)], check=True, cwd=ROOT)
    (target / "directive-resolve-build.json").write_text(json.dumps(identity(upstream, target), indent=2) + "\n")
    print("Built pinned method directive resolver")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"build-rust-directive-resolver: {error}", file=sys.stderr)
        raise SystemExit(2)
