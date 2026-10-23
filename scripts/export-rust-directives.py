#!/usr/bin/env python3
"""Extract attached E2E directives with the pinned Rust parser and test-directives grammar.

The standalone tool uses upstream HIR comment ownership and test-directives
grammar, including raw scenarios. It does not compile or execute contracts.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parent.parent
sys.dont_write_bytecode = True
_spec = importlib.util.spec_from_file_location("hull_export", ROOT / "scripts/export-rust-hull.py")
assert _spec and _spec.loader
hull = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(hull)
SOURCE = ROOT / "scripts/rust-directive-export.rs"
TOOL = ROOT / ".upstream/rust-directive-tool"
SCHEMA = "solcore-rs.test-directives.v1"


def manifest(upstream: Path) -> str:
    def dependency(name: str, directory: str) -> str:
        return f'{{ package = "{name}", path = {json.dumps(str(upstream / "crates" / directory))} }}'
    return f'''[package]
name = "solcore-directive-export"
version = "0.1.0"
edition = "2024"
rust-version = "1.97.0"

[workspace]

[dependencies]
serde_json = "=1.0.151"
salsa = "=0.27.2"
url = "=2.5.8"
hir = {dependency("solcore-hir", "hir")}
parser = {dependency("solcore-parser", "parser")}
solcore-test-directives = {dependency("solcore-test-directives", "test-directives")}
solcore-test-utils = {dependency("solcore-test-utils", "test-utils")}
'''


def pins(path: Path) -> set[tuple]:
    return {(package["name"], package["version"], package["source"], package.get("checksum"))
        for package in tomllib.loads(path.read_text())["package"] if "source" in package}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?", type=Path)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--allow-network", action="store_true")
    args = parser.parse_args()
    upstream, target = args.upstream.resolve(), args.target_dir.resolve()
    if not target.is_relative_to((ROOT / ".upstream").resolve()):
        raise ValueError("the disposable Cargo target must stay inside .upstream")
    hull.prepare(upstream)  # Verify the pinned checkout and all permitted tracked patches.
    binary = target / "debug/solcore-directive-export"
    receipt = target / "directive-export-build.json"
    package = manifest(upstream)
    if args.build:
        (TOOL / "src").mkdir(parents=True, exist_ok=True)
        (TOOL / "Cargo.toml").write_text(package)
        (TOOL / "src/main.rs").write_bytes(SOURCE.read_bytes())
        if not (TOOL / "Cargo.lock").exists():
            (TOOL / "Cargo.lock").write_bytes((upstream / "Cargo.lock").read_bytes())
        command = ["cargo", "build", "--manifest-path", str(TOOL / "Cargo.toml"), "--target-dir", str(target)]
        if not args.allow_network:
            command.append("--offline")
        subprocess.run(command, cwd=ROOT, check=True)
    if pins(TOOL / "Cargo.lock") - pins(upstream / "Cargo.lock"):
        raise ValueError("directive tool dependencies differ from pinned upstream")
    identity = {"upstreamCommit": hull.COMMIT, "sourceSha256": hull.digest(SOURCE.read_bytes()),
        "manifestSha256": hull.digest(package.encode()), "lockSha256": hull.digest((TOOL / "Cargo.lock").read_bytes()),
        "binarySha256": hull.digest(binary.read_bytes())}
    if args.build:
        receipt.write_text(json.dumps(identity, indent=2) + "\n")
    if not args.source:
        if args.build:
            print(f"Built pinned directive extractor: {binary}")
            return 0
        parser.error("source is required unless --build is selected")
    if not args.output:
        parser.error("--output is required when extracting a source")
    if not receipt.exists() or json.loads(receipt.read_text()) != identity:
        raise ValueError("directive extractor receipt is stale; run with --build")
    source, output = args.source.resolve(), args.output.resolve()
    original = source.read_bytes()
    result = subprocess.run([str(binary), str(source)], capture_output=True, text=True, timeout=60)
    if result.returncode:
        raise ValueError(result.stderr + result.stdout)
    if source.read_bytes() != original:
        raise ValueError("source changed during directive extraction")
    document = json.loads(result.stdout)
    if document.get("schema") != SCHEMA or document.get("upstreamCommit") != hull.COMMIT:
        raise ValueError("unexpected directive schema or revision")
    output.parent.mkdir(parents=True, exist_ok=True)
    contents = (json.dumps(document, separators=(",", ":")) + "\n").encode()
    output.write_bytes(contents)
    output.with_suffix(output.suffix + ".provenance.json").write_text(json.dumps({
        "schema": SCHEMA, "toolBuild": identity, "source": source.as_uri(),
        "sourceSha256": hull.digest(original), "outputSha256": hull.digest(contents)}, indent=2) + "\n")
    print(f"Extracted pinned directives: {output}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"export-rust-directives: {error}", file=sys.stderr)
        raise SystemExit(2)
