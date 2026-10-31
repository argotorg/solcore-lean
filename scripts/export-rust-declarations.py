#!/usr/bin/env python3
"""Extract a source's declarations with the pinned Rust parser.

The standalone tool prints the pinned HIR of one source file: its data types
with their constructors' field types, its type aliases, and every function and
contract method with its parameter and return types, as written and before name
resolution. It does not compile or execute contracts. It is built offline from
the directive extractor's pinned lock, beside the directive tools.
"""
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
hull = export.hull
SOURCE = ROOT / "scripts/rust-declaration-export.rs"
TOOL = ROOT / ".upstream/rust-declaration-tool"
PACKAGE = "solcore-declaration-export"
RECEIPT = "declaration-export-build.json"
SCHEMA = "solcore-rs.declarations.v1"


def manifest(upstream: Path) -> str:
    def dependency(name: str, directory: str) -> str:
        return f'{{ package = "{name}", path = {json.dumps(str(upstream / "crates" / directory))} }}'
    return f'''[package]
name = "{PACKAGE}"
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
'''


def identity(upstream: Path, target: Path) -> dict:
    if export.pins(TOOL / "Cargo.lock") - export.pins(upstream / "Cargo.lock"):
        raise ValueError("declaration extractor dependencies differ from pinned upstream")
    return {"upstreamCommit": hull.COMMIT, "sourceSha256": hull.digest(SOURCE.read_bytes()),
        "manifestSha256": hull.digest(manifest(upstream).encode()), "lockSha256": hull.digest((TOOL / "Cargo.lock").read_bytes()),
        "binarySha256": hull.digest((target / "debug" / PACKAGE).read_bytes())}


def checked_identity(upstream: Path, target: Path) -> dict:
    current = identity(upstream, target)
    if json.loads((target / RECEIPT).read_text()) != current:
        raise ValueError("declaration extractor receipt is stale; run export-rust-declarations.py --build")
    return current


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?", type=Path)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--build", action="store_true")
    args = parser.parse_args()
    upstream, target = args.upstream.resolve(), args.target_dir.resolve()
    if not target.is_relative_to((ROOT / ".upstream").resolve()):
        raise ValueError("the disposable Cargo target must stay inside .upstream")
    hull.prepare(upstream)  # Verify the pinned checkout and all permitted tracked patches.
    if args.build:
        (TOOL / "src").mkdir(parents=True, exist_ok=True)
        (TOOL / "Cargo.toml").write_text(manifest(upstream))
        (TOOL / "src/main.rs").write_bytes(SOURCE.read_bytes())
        if not (TOOL / "Cargo.lock").exists():
            (TOOL / "Cargo.lock").write_bytes((upstream / "Cargo.lock").read_bytes())
        # Offline: the upstream lock that the directive tools build from holds every dependency.
        subprocess.run(["cargo", "build", "--offline", "--manifest-path", str(TOOL / "Cargo.toml"),
                        "--target-dir", str(target)], cwd=ROOT, check=True)
        (target / RECEIPT).write_text(json.dumps(identity(upstream, target), indent=2) + "\n")
        if not args.source:
            print(f"Built pinned declaration extractor: {target / 'debug' / PACKAGE}")
            return 0
    if not args.source:
        parser.error("source is required unless --build is selected")
    if not args.output:
        parser.error("--output is required when extracting a source")
    build = checked_identity(upstream, target)
    source, output = args.source.resolve(), args.output.resolve()
    original = source.read_bytes()
    result = subprocess.run([str(target / "debug" / PACKAGE), str(source)], capture_output=True, text=True, timeout=60)
    if result.returncode:
        raise ValueError(result.stderr + result.stdout)
    if source.read_bytes() != original:
        raise ValueError("source changed during declaration extraction")
    document = json.loads(result.stdout)
    if document.get("schema") != SCHEMA or document.get("upstreamCommit") != hull.COMMIT:
        raise ValueError("unexpected declaration schema or revision")
    output.parent.mkdir(parents=True, exist_ok=True)
    contents = (json.dumps(document, separators=(",", ":")) + "\n").encode()
    output.write_bytes(contents)
    output.with_suffix(output.suffix + ".provenance.json").write_text(json.dumps({
        "schema": SCHEMA, "toolBuild": build, "source": source.as_uri(),
        "sourceSha256": hull.digest(original), "outputSha256": hull.digest(contents)}, indent=2) + "\n")
    print(f"Extracted pinned declarations: {output}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"export-rust-declarations: {error}", file=sys.stderr)
        raise SystemExit(2)
