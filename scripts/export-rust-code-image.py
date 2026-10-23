#!/usr/bin/env python3
"""Export actual pinned Sonatina object bytes for execution by Lean Core.

The existing checked Hull exporter and driver remain unchanged. A separate
compiler tool parses the driver's Sonatina IR and emits exact linked sections
and symbol extents. Compilation supplies code observables; no EVM is executed.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parent.parent
sys.dont_write_bytecode = True
_spec = importlib.util.spec_from_file_location("hull_export", ROOT / "scripts/export-rust-hull.py")
assert _spec and _spec.loader
hull = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(hull)
BACKEND = "8ee24814ea9b32c762df8ef80c796e7d48797c0f"
SCHEMA = "solcore-rs.code-images.v1"
SOURCE = ROOT / "scripts/rust-code-image-export.rs"
TOOL = ROOT / ".upstream/rust-code-image-tool"
MANIFEST = f'''[package]
name = "solcore-code-image-export"
version = "0.1.0"
edition = "2024"
rust-version = "1.97.0"

[workspace]

[dependencies]
serde_json = {{ version = "=1.0.151", features = ["unbounded_depth"] }}
sonatina-codegen = {{ git = "https://github.com/fe-lang/sonatina", rev = "{BACKEND}" }}
sonatina-parser = {{ git = "https://github.com/fe-lang/sonatina", rev = "{BACKEND}" }}
'''


def package_pins(lock: Path) -> set[tuple]:
    return {(p["name"], p["version"], p["source"], p.get("checksum"))
            for p in tomllib.loads(lock.read_text())["package"] if "source" in p}


def check_pins(upstream: Path) -> None:
    extra = package_pins(TOOL / "Cargo.lock") - package_pins(upstream / "Cargo.lock")
    if extra:
        raise ValueError(f"code image tool dependencies differ from the pinned compiler: {sorted(extra)}")


def tool_hashes() -> dict:
    return {"sourceSha256": hull.digest(SOURCE.read_bytes()),
            "manifestSha256": hull.digest(MANIFEST.encode()),
            "lockSha256": hull.digest((TOOL / "Cargo.lock").read_bytes())}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, nargs="?")
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--hull-output", type=Path, help="matching checked Hull; default OUTPUT.hull.json")
    parser.add_argument("--root", type=Path)
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--allow-network", action="store_true")
    parser.add_argument("--timeout", type=float, default=300, help="per-export process timeout")
    args = parser.parse_args()
    upstream, target = args.upstream.resolve(), args.target_dir.resolve()
    if not target.is_relative_to((ROOT / ".upstream").resolve()):
        raise ValueError("the Cargo target must stay inside .upstream")
    patches = hull.prepare(upstream)
    driver = target / "debug/solcore-driver"
    driver_receipt = target / "lean-export-build.json"
    if not driver_receipt.exists():
        raise ValueError("build the checked Hull driver with export-rust-hull.py --build first")
    driver_build = json.loads(driver_receipt.read_text())
    if (driver_build.get("upstreamCommit") != hull.COMMIT or driver_build.get("patches") != patches
            or driver_build.get("binarySha256") != hull.digest(driver.read_bytes())):
        raise ValueError("checked Hull exporter receipt is stale; rebuild export-rust-hull.py first")
    binary, receipt = target / "debug/solcore-code-image-export", target / "code-image-export-build.json"
    if args.build:
        (TOOL / "src").mkdir(parents=True, exist_ok=True)
        (TOOL / "Cargo.toml").write_text(MANIFEST)
        (TOOL / "src/main.rs").write_bytes(SOURCE.read_bytes())
        if not (TOOL / "Cargo.lock").exists():
            (TOOL / "Cargo.lock").write_bytes((upstream / "Cargo.lock").read_bytes())
        command = ["cargo", "build", "--manifest-path", str(TOOL / "Cargo.toml"), "--target-dir", str(target)]
        if not args.allow_network:
            command.append("--offline")
        subprocess.run(command, cwd=ROOT, check=True)
        check_pins(upstream)
        receipt.write_text(json.dumps({"upstreamCommit": hull.COMMIT, "backendRevision": BACKEND,
            **tool_hashes(), "binarySha256": hull.digest(binary.read_bytes())}, indent=2) + "\n")
    if not args.source:
        if args.build:
            print(f"Built code image exporter: {binary}")
            return 0
        parser.error("source is required unless --build is selected")
    if not args.output:
        parser.error("--output is required when exporting a source")
    if not receipt.exists():
        raise ValueError("no code image exporter receipt; run with --build first")
    build = json.loads(receipt.read_text())
    check_pins(upstream)
    if (build.get("upstreamCommit") != hull.COMMIT or build.get("backendRevision") != BACKEND
            or any(build.get(key) != value for key, value in tool_hashes().items())
            or build.get("binarySha256") != hull.digest(binary.read_bytes())):
        raise ValueError("code image exporter changed; rebuild with --build")
    source, output = args.source.resolve(), args.output.resolve()
    hull_output = args.hull_output.resolve() if args.hull_output else output.with_suffix(".hull.json")
    if hull_output == output:
        raise ValueError("Hull and code image outputs must differ")
    command = [sys.executable, str(ROOT / "scripts/export-rust-hull.py"), str(source),
        "--upstream", str(upstream), "--target-dir", str(target), "--output", str(hull_output)]
    if args.root:
        command += ["--root", str(args.root.resolve())]
    subprocess.run(command, cwd=ROOT, check=True, timeout=args.timeout)
    hull_record = json.loads(hull_output.with_suffix(hull_output.suffix + ".provenance.json").read_text())
    hull_document = json.loads(hull_output.read_text())
    with tempfile.TemporaryDirectory(prefix="solcore-code-image-") as temporary:
        ir = Path(temporary) / "checked.ir"
        ir_command = [str(driver), str(source), "--std-root", str(upstream / "std"), "--emit-sonatina"]
        if args.root:
            ir_command += ["--root", str(args.root.resolve())]
        compiled = subprocess.run(ir_command, cwd=upstream, capture_output=True, text=True, timeout=args.timeout)
        if compiled.stderr:
            sys.stderr.write(compiled.stderr)
        if compiled.returncode:
            raise ValueError(f"Sonatina translation failed with status {compiled.returncode}")
        ir.write_text(compiled.stdout)
        code = subprocess.run([str(binary), str(hull_output), str(ir)], cwd=ROOT,
            capture_output=True, text=True, timeout=args.timeout)
        if code.stderr:
            sys.stderr.write(code.stderr)
        if code.returncode:
            raise ValueError(f"code image compilation failed with status {code.returncode}")
        document = json.loads(code.stdout)
        if document.get("schema") != SCHEMA or document.get("upstreamCommit") != hull.COMMIT:
            raise ValueError("unexpected code image schema or revision")
        sources = hull.source_hashes(hull_document)
        sources[source.as_uri()] = hull.digest(source.read_bytes())
        if sources != hull_record["sources"]:
            raise ValueError("source files changed between checked Hull and code generation")
        contents = (json.dumps(document, separators=(",", ":")) + "\n").encode()
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(contents)
        record = {"schema": SCHEMA, "upstreamCommit": hull.COMMIT, "backendRevision": BACKEND,
            "optimization": "O0", "toolBuild": build, "hullProvenance": hull_record,
            "hullOutput": str(hull_output), "sonatinaSha256": hull.digest(ir.read_bytes()),
            "outputSha256": hull.digest(contents), "sources": sources, "command": ir_command}
        output.with_suffix(output.suffix + ".provenance.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"Exported actual linked code images: {output}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"export-rust-code-image: {error}", file=sys.stderr)
        raise SystemExit(2)
