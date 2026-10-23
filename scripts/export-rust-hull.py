#!/usr/bin/env python3
"""Export checked Hull JSON from the pinned solcore-rs compiler.

Only the isolated checkout under .upstream is patched. The patch replaces the
Hull pretty printer with a typed serializer after the normal checked compiler
pipeline; parsing, type checking, specialization, emission and Hull validation
are unchanged. A sidecar records compiler and source hashes for every export.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from urllib.parse import unquote, urlparse


ROOT = Path(__file__).resolve().parent.parent
COMMIT = "2a745e12974c373c3799fec81b48a53c7dce2ab4"
SCHEMA = "solcore-rs.hull.v1"


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def git(upstream: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(upstream), *args], text=True)


def prepare(upstream: Path) -> dict[str, str]:
    if not upstream.resolve().is_relative_to((ROOT / ".upstream").resolve()):
        raise ValueError("the exporter may only patch a checkout inside this repository's .upstream directory")
    if git(upstream, "rev-parse", "HEAD").strip() != COMMIT:
        raise ValueError(f"the exporter requires upstream commit {COMMIT}")
    allowed = {"crates/driver/src/main.rs", "crates/driver/src/emit.rs"}
    changed = set(git(upstream, "diff", "--name-only", "HEAD").splitlines())
    if changed - allowed:
        raise ValueError(f"upstream compiler has unrelated tracked changes: {sorted(changed - allowed)}")
    replacements = {
        "crates/driver/src/main.rs": ("mod emit;", "mod emit;\nmod lean_export;"),
        "crates/driver/src/emit.rs": (
            "&hull::pretty_program(db, &program)", "&crate::lean_export::export(db, &program)"
        ),
    }
    hashes = {}
    for path, (old, new) in replacements.items():
        original = git(upstream, "show", f"{COMMIT}:{path}")
        if original.count(old) != 1:
            raise ValueError(f"expected one checked export injection point in {path}")
        patched = original.replace(old, new)
        target = upstream / path
        if target.read_text() not in (original, patched):
            raise ValueError(f"refusing to overwrite an unexpected upstream change: {path}")
        if target.read_text() != patched:
            target.write_text(patched)
        hashes[path] = digest(patched.encode())
    serializer = (ROOT / "scripts/rust-hull-export.rs").read_bytes()
    target = upstream / "crates/driver/src/lean_export.rs"
    if not target.exists() or target.read_bytes() != serializer:
        target.write_bytes(serializer)
    hashes["crates/driver/src/lean_export.rs"] = digest(serializer)
    return hashes


def source_hashes(value: object) -> dict[str, str]:
    urls = set()
    pending = [value]
    while pending:
        current = pending.pop()
        if isinstance(current, dict):
            if {"file", "start", "end"}.issubset(current):
                urls.add(current["file"])
            pending.extend(current.values())
        elif isinstance(current, list):
            pending.extend(current)
    result = {}
    for url in sorted(urls):
        parsed = urlparse(url)
        if parsed.scheme != "file":
            raise ValueError(f"cannot hash a non-file source in this filesystem export: {url}")
        result[url] = digest(Path(unquote(parsed.path)).read_bytes())
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, nargs="?")
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--build", action="store_true", help="build only the pinned compiler driver")
    parser.add_argument("--allow-network", action="store_true", help="allow Cargo to fetch missing pinned dependencies")
    parser.add_argument("--prepare-only", action="store_true", help="install the serializer without building or exporting")
    parser.add_argument("--root", type=Path, help="source module root passed to the upstream driver")
    args = parser.parse_args()
    upstream = args.upstream.resolve()
    target = args.target_dir.resolve()
    if not target.is_relative_to((ROOT / ".upstream").resolve()):
        raise ValueError("the disposable Cargo target must be inside .upstream")
    patches = prepare(upstream)
    if args.prepare_only:
        print(f"Prepared checked Hull export at {COMMIT}")
        return 0
    binary = target / "debug/solcore-driver"
    receipt = target / "lean-export-build.json"
    if args.build:
        command = ["cargo", "build", "-p", "solcore-driver", "--locked", "--target-dir", str(target)]
        if not args.allow_network:
            command.append("--offline")
        subprocess.run(command, cwd=upstream, check=True)
        receipt.write_text(json.dumps({"upstreamCommit": COMMIT, "patches": patches,
            "binarySha256": digest(binary.read_bytes())}, indent=2) + "\n")
    if not args.source:
        if args.build:
            print(f"Built checked Hull exporter: {binary}")
            return 0
        parser.error("source is required unless --build or --prepare-only is selected")
    if not args.output:
        parser.error("--output is required when exporting a source")
    if not receipt.exists():
        raise ValueError("no pinned exporter build receipt; run with --build first")
    build = json.loads(receipt.read_text())
    if build.get("upstreamCommit") != COMMIT or build.get("patches") != patches:
        raise ValueError("exporter changed since its recorded build; rebuild with --build")
    if digest(binary.read_bytes()) != build["binarySha256"]:
        raise ValueError("exporter binary changed since its recorded build; rebuild with --build")
    source = args.source.resolve()
    command = [str(binary), str(source), "--std-root", str(upstream / "std"), "--emit-hull"]
    if args.root:
        command += ["--root", str(args.root.resolve())]
    compiled = subprocess.run(command, cwd=upstream, capture_output=True, text=True)
    if compiled.stderr:
        sys.stderr.write(compiled.stderr)
    if compiled.returncode:
        return compiled.returncode
    envelope = json.loads(compiled.stdout)
    if envelope.get("schema") != SCHEMA or envelope.get("upstreamCommit") != COMMIT:
        raise ValueError("compiler returned an unexpected Hull schema or revision")
    sources = source_hashes(envelope)
    sources[source.as_uri()] = digest(source.read_bytes())
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    contents = (json.dumps(envelope, separators=(",", ":")) + "\n").encode()
    output.write_bytes(contents)
    provenance = {"schema": SCHEMA, "upstreamCommit": COMMIT, "patches": patches,
        "binarySha256": build["binarySha256"], "outputSha256": digest(contents),
        "command": command, "sources": sources}
    output.with_suffix(output.suffix + ".provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    print(f"Exported checked Hull: {output}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"export-rust-hull: {error}", file=sys.stderr)
        raise SystemExit(2)
