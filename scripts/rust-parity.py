#!/usr/bin/env python3
"""Run pinned solcore-rs source fixtures through Lean's public Core compiler.

The upstream files are read unchanged. Fixture hashes and the upstream commit
prevent a moving checkout from silently changing the compatibility target.
Every result records the first failing stage; report-only runs are inventories,
not successful compatibility checks.
"""

from __future__ import annotations

import argparse
from collections import Counter
import fnmatch
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent


def load_cases(manifest: dict, upstream: Path, patterns: list[str]) -> list[dict]:
    head = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True
    ).strip()
    if head != manifest["upstream_commit"]:
        raise ValueError(f"expected upstream {manifest['upstream_commit']}, found {head}")
    requests = []
    for case in manifest["cases"]:
        if patterns and not any(fnmatch.fnmatchcase(case["id"], pattern) for pattern in patterns):
            continue
        sources = []
        for source in case["sources"]:
            path = (upstream / source["upstream_path"]).resolve()
            if not path.is_relative_to(upstream.resolve()):
                raise ValueError(f"source escapes upstream checkout: {path}")
            contents = path.read_bytes()
            digest = hashlib.sha256(contents).hexdigest()
            if digest != source["sha256"]:
                raise ValueError(f"upstream fixture content changed: {source['upstream_path']}")
            sources.append({"path": source["workspace_path"], "content": contents.decode("utf-8")})
        requests.append({
            "id": case["id"],
            "entry": case.get("entry", "main.sol"),
            "sources": sources,
            "function": case.get("function", "main"),
            "arguments": case.get("arguments", []),
            "expected": case.get("expected"),
            "checkingFuel": 4096,
            "compilationFuel": 4096,
            "specializationBudget": 1024,
            "executionFuel": 1000000,
            **case.get("budgets", {}),
        })
    if not requests:
        raise ValueError("no fixtures matched the requested patterns")
    return requests


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--manifest", type=Path, default=ROOT / "scripts/rust-parity.json")
    parser.add_argument("--case", action="append", default=[], help="case ID glob; repeatable")
    parser.add_argument("--output", type=Path, help="write the complete JSON result report")
    parser.add_argument("--timeout", type=float, default=300, help="whole batch timeout in seconds")
    parser.add_argument("--report-only", action="store_true", help="inventory failures without passing a compatibility gate")
    parser.add_argument("--list", action="store_true", help="list matching cases without running Lean")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    requests = load_cases(manifest, args.upstream, args.case)
    if args.list:
        for request in requests:
            print(request["id"])
        return 0
    with tempfile.TemporaryDirectory(prefix="solcore-rust-parity-") as temporary:
        request_file = Path(temporary) / "requests.json"
        request_file.write_text(json.dumps(requests))
        completed = subprocess.run(
            ["lake", "env", "lean", "--run", "Tests/RustParity.lean", str(request_file)],
            cwd=ROOT, capture_output=True, text=True, timeout=args.timeout,
        )
    if completed.returncode:
        sys.stderr.write(completed.stdout)
        sys.stderr.write(completed.stderr)
        return completed.returncode
    observations = [json.loads(line) for line in completed.stdout.splitlines() if line.strip()]
    if [row["id"] for row in observations] != [row["id"] for row in requests]:
        raise ValueError("runner omitted, reordered, or duplicated fixture results")
    failures = [row for row in observations if row["status"] != "succeeded"]
    summary = Counter(f"{row['stage']}:{row['status']}" for row in observations)
    report = {
        "upstream_commit": manifest["upstream_commit"],
        "mode": "inventory" if args.report_only else "compatibility-check",
        "passed": not failures,
        "total": len(observations),
        "succeeded": len(observations) - len(failures),
        "stages": dict(sorted(summary.items())),
        "observations": observations,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    for row in observations:
        detail = f" = {row['value']['kind']}({row['value']['value']})" if row.get("value") else ""
        print(f"{row['id']}: {row['stage']}/{row['status']}{detail}")
    print(f"{report['succeeded']}/{report['total']} executed with the expected result")
    for stage, count in sorted(summary.items()):
        print(f"  {stage}: {count}")
    if args.report_only and failures:
        print("Inventory only: compatibility remains incomplete.")
    return 0 if args.report_only or not failures else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"rust-parity: {error}", file=sys.stderr)
        raise SystemExit(2)
