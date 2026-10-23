#!/usr/bin/env python3
"""Execute the pinned scalar fixture inventory through Rust Hull and Lean Core.

This complements rust-parity.py, which exercises Lean's native source frontend.
Expected scalar values are checked after actual Core execution. Upstream
compile failures, unsupported lowering and exhausted execution remain failures.
"""

from __future__ import annotations

import argparse
from collections import Counter
import fnmatch
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote, urlparse

ROOT = Path(__file__).resolve().parent.parent


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def recorded_sources_match(sources: dict[str, str]) -> bool:
    for url, expected in sources.items():
        parsed = urlparse(url)
        if parsed.scheme != "file":
            return False
        path = Path(unquote(parsed.path))
        if not path.exists() or digest(path.read_bytes()) != expected:
            return False
    return True


def normalized_scalar(value: dict, expected: dict) -> dict:
    if expected["kind"] == "bool" and value.get("kind") in ("inl", "inr"):
        if value.get("value") == {"kind": "unit"}:
            return {"kind": "bool", "value": str(value["kind"] == "inr").lower()}
    scalar = value.get("value", "")
    if isinstance(scalar, bool):
        scalar = str(scalar).lower()
    return {"kind": value.get("kind"), "value": str(scalar)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--manifest", type=Path, default=ROOT / "scripts/rust-parity.json")
    parser.add_argument("--cache", type=Path, default=ROOT / ".upstream/hull-fixtures/scalars")
    parser.add_argument("--case", action="append", default=[], help="case ID glob; repeatable")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--timeout", type=float, default=120, help="per-process timeout in seconds")
    parser.add_argument("--reuse-exports", action="store_true", help="reuse exports whose recorded sources and JSON hashes still match")
    parser.add_argument("--report-only", action="store_true", help="inventory remaining failures without passing a compatibility gate")
    args = parser.parse_args()
    upstream = args.upstream.resolve()
    manifest = json.loads(args.manifest.read_text())
    head = subprocess.check_output(["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True).strip()
    if head != manifest["upstream_commit"]:
        raise ValueError("upstream revision does not match the pinned manifest")
    cases = [case for case in manifest["cases"] if not args.case or any(
        fnmatch.fnmatchcase(case["id"], pattern) for pattern in args.case)]
    if not cases:
        raise ValueError("no fixtures matched the requested patterns")
    args.cache.mkdir(parents=True, exist_ok=True)
    observations = []
    exported = set()
    for case in cases:
        source_spec = next(source for source in case["sources"]
            if source["workspace_path"] == case.get("entry", "main.sol"))
        source = (upstream / source_spec["upstream_path"]).resolve()
        for specification in case["sources"]:
            path = (upstream / specification["upstream_path"]).resolve()
            if not path.is_relative_to(upstream):
                raise ValueError("fixture path escapes the upstream checkout")
            if digest(path.read_bytes()) != specification["sha256"]:
                raise ValueError(f"fixture changed: {path}")
        exported_file = args.cache / f"{source_spec['sha256']}.json"
        provenance_file = exported_file.with_suffix(".json.provenance.json")
        reuse = False
        if args.reuse_exports and exported_file.exists() and provenance_file.exists():
            provenance = json.loads(provenance_file.read_text())
            reuse = (provenance.get("upstreamCommit") == manifest["upstream_commit"]
                and provenance.get("outputSha256") == digest(exported_file.read_bytes())
                and provenance.get("sources", {}).get(source.as_uri()) == source_spec["sha256"]
                and recorded_sources_match(provenance.get("sources", {}))
                and provenance.get("patches", {}).get("crates/driver/src/lean_export.rs")
                    == digest((ROOT / "scripts/rust-hull-export.rs").read_bytes()))
        if exported_file not in exported and not reuse:
            result = subprocess.run([sys.executable, str(ROOT / "scripts/export-rust-hull.py"),
                str(source), "--upstream", str(upstream), "--output", str(exported_file)],
                cwd=ROOT, capture_output=True, text=True, timeout=args.timeout)
            if result.returncode:
                observations.append({"id": case["id"], "stage": "rust-compilation", "status": "rejected",
                    "detail": result.stderr + result.stdout})
                print(f"{case['id']}: rust-compilation/rejected", flush=True)
                continue
        exported.add(exported_file)
        envelope = json.loads(exported_file.read_text())
        entries = envelope["program"]["entryPoints"]
        name = case.get("function", "main")
        selected = [entry for entry in entries if re.search(r"(?:^|_)" + re.escape(name) + r"_d[0-9a-f]+$", entry)]
        if len(entries) == 1:
            selected = entries
        if len(selected) != 1:
            observation = {"id": case["id"], "stage": "entry", "status": "rejected",
                "detail": f"cannot select {name!r} uniquely from {entries!r}"}
        else:
            command = ["lake", "env", "lean", "--run", "Tests/RustHullRun.lean",
                str(exported_file), selected[0], *[arg["value"] for arg in case.get("arguments", [])]]
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=args.timeout)
            try:
                observation = json.loads(result.stdout)
            except json.JSONDecodeError:
                observation = {"stage": "harness", "status": "error", "detail": result.stdout + result.stderr}
            observation["id"] = case["id"]
            observation["entry"] = selected[0]
            observation["export"] = str(exported_file)
            if observation.get("status") == "succeeded":
                expected = case.get("expected")
                if expected is not None and normalized_scalar(observation["value"], expected) != expected:
                    observation["status"] = "mismatch"
                    observation["expected"] = expected
        observations.append(observation)
        print(f"{case['id']}: {observation['stage']}/{observation['status']}", flush=True)
    summary = Counter(f"{row['stage']}:{row['status']}" for row in observations)
    succeeded = sum(row["status"] == "succeeded" for row in observations)
    report = {"upstream_commit": head, "mode": "inventory" if args.report_only else "compatibility-check",
        "passed": succeeded == len(cases), "total": len(cases), "succeeded": succeeded,
        "stages": dict(sorted(summary.items())), "observations": observations}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{succeeded}/{len(cases)} executed with the expected result")
    for stage, count in sorted(summary.items()):
        print(f"  {stage}: {count}")
    if args.report_only and not report["passed"]:
        print("Inventory only: compatibility remains incomplete.")
    return 0 if args.report_only or report["passed"] else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"rust-hull-parity: {error}", file=sys.stderr)
        raise SystemExit(2)
