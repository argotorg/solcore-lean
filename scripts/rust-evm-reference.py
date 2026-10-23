#!/usr/bin/env python3
"""Run the pinned Rust E2E harness on Anvil, separately from Core parity.

Sonatina tests execute both O0 and O2; Yul tests execute solc-produced bytecode.
The upstream harness owns deployment, calldata, expectations and state changes.
E2E_REQUIRED prevents unavailable tools from silently skipping execution.
"""
from __future__ import annotations

import argparse
from collections import Counter
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
COMMIT = "2a745e12974c373c3799fec81b48a53c7dce2ab4"
PREFIX = {"sonatina": "sonatina_evm_e2e__", "yul": "yul_evm_e2e_fixture__"}
BUILD = ["cargo", "test", "--profile", "e2e", "-p", "solcore-yul", "-p",
         "solcore-sonatina", "--test", "e2e", "--locked", "--offline", "--no-run",
         "--message-format=json"]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str], cwd: Path, **kwargs) -> subprocess.CompletedProcess:
    return subprocess.run(command, cwd=cwd, text=True, capture_output=True, **kwargs)


def sources(upstream: Path) -> dict:
    head = run(["git", "rev-parse", "HEAD"], upstream)
    if head.returncode or head.stdout.strip() != COMMIT:
        raise ValueError(f"expected upstream {COMMIT}")
    changed = run(["git", "diff", "--name-only", "HEAD"], upstream)
    allowed = {"crates/driver/src/main.rs", "crates/driver/src/emit.rs"}
    if changed.returncode or set(changed.stdout.splitlines()) - allowed:
        raise ValueError("upstream E2E sources have tracked modifications")
    # Driver-only exporter patches are not dependencies of these test binaries.
    files = ["Cargo.lock", "rust-toolchain.toml", "crates/yul/tests/e2e.rs",
             "crates/sonatina/tests/e2e.rs", "crates/test-utils/src/e2e.rs",
             "crates/test-utils/src/e2e/process.rs"]
    return {"upstreamCommit": COMMIT, "files": {p: digest(upstream / p) for p in files},
            "excludedDriverPatches": changed.stdout.splitlines()}


def build(upstream: Path, target: Path, identity: dict) -> dict:
    target.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "CARGO_INCREMENTAL": "0", "CARGO_TARGET_DIR": str(target)}
    result = run(BUILD, upstream, env=env)
    if result.returncode:
        raise ValueError(f"E2E build failed:\n{result.stderr}")
    binaries = {}
    for line in result.stdout.splitlines():
        item = json.loads(line)
        if (item.get("reason") != "compiler-artifact" or not item.get("executable")
                or item["target"]["name"] != "e2e"):
            continue
        for backend in PREFIX:
            if f"#solcore-{backend}@" in item["package_id"]:
                binary = target / "bin" / f"{backend}-e2e"
                binary.parent.mkdir(exist_ok=True)
                shutil.copy2(item["executable"], binary)
                binaries[backend] = {"path": str(binary), "sha256": digest(binary)}
    if set(binaries) != set(PREFIX):
        raise ValueError("Cargo did not produce both E2E test binaries")
    receipt = {**identity, "command": BUILD, "incremental": False,
               "rustc": run(["rustc", "--version"], upstream).stdout.strip(),
               "binaries": binaries}
    (target / "build.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def outcome(result: subprocess.CompletedProcess) -> tuple[str, str]:
    text = result.stdout + result.stderr
    # Missing/ignored selection must never count as an executed fixture.
    summary = re.search(r"test result: \w+\. (\d+) passed; (\d+) failed; (\d+) ignored", text)
    if not summary or sum(map(int, summary.groups())) != 1:
        return "failed", "harness"
    if int(summary[3]) or re.search(r"skipping (?:Yul )?E2E(?: execution)?:", text):
        return "skipped", "tooling"
    if result.returncode == 0 and int(summary[1]) == 1:
        return "passed", "evm"
    failure = re.search(r"failed: (Directive|Pipeline|Tooling|Solc|Codegen|Deploy|Transaction|Call|Decode|Mismatch):", text)
    return "failed", failure[1].lower() if failure else "harness"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/evm-reference-target")
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--build-only", action="store_true")
    parser.add_argument("--backend", choices=list(PREFIX), action="append")
    parser.add_argument("--fixture", action="append", help="fixture id glob; omitted selects all 168")
    parser.add_argument("--output", type=Path, default=ROOT / ".upstream/evm-reference.json")
    parser.add_argument("--report-only", action="store_true")
    args = parser.parse_args()
    upstream, target = args.upstream.resolve(), args.target_dir.resolve()
    if (not target.is_relative_to(ROOT / ".upstream")
            or target == ROOT / ".upstream/rust-parity-target"):
        raise ValueError("use a separate disposable EVM Cargo target inside .upstream")
    identity = sources(upstream)
    receipt = build(upstream, target, identity) if args.build else json.loads((target / "build.json").read_text())
    if any(receipt.get(k) != v for k, v in identity.items()):
        raise ValueError("EVM test build receipt is stale")
    if args.build_only:
        return 0
    tools = {}
    for name in ["anvil", "cast", "solc"]:
        path = shutil.which(name)
        if not path:
            raise ValueError(f"required tool missing: {name}")
        version = run([path, "--version"], upstream)
        tools[name] = {"path": path, "version": version.stdout.strip(), "sha256": digest(Path(path))}
    fixtures = {p.parent.name: p for p in sorted((upstream / "tests/e2e").glob("*/main.sol"))}
    selected = {key: value for key, value in fixtures.items()
                if not args.fixture or any(fnmatch.fnmatchcase(key, pattern) for pattern in args.fixture)}
    if not selected:
        raise ValueError("no matching fixture")
    env = {**os.environ, "E2E": "1", "E2E_REQUIRED": "1", "ANVIL_HARDFORK": "osaka",
           "ANVIL": tools["anvil"]["path"], "CAST": tools["cast"]["path"], "SOLC": tools["solc"]["path"]}
    env.pop("E2E_PIPELINE_ONLY", None)
    report = {"schema": "solcore-lean.evm-reference.v1", "build": receipt, "tools": tools,
              "environment": {key: env[key] for key in ["E2E", "E2E_REQUIRED", "ANVIL_HARDFORK"]},
              "evmReferenceRequested": True, "evmReferenceExecuted": False, "coreExecuted": False,
              "runnerSha256": digest(Path(__file__)),
              "scope": "upstreamDeploymentAndCalls", "fixtureCount": len(selected),
              "optimization": {"sonatina": ["O0", "O2"], "yul": "upstream solc configuration"},
              "results": []}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for backend in args.backend or list(PREFIX):
        record = receipt["binaries"][backend]
        binary = Path(record["path"])
        if digest(binary) != record["sha256"]:
            raise ValueError("EVM binary hash differs from build receipt")
        listing = run([str(binary), "--list"], upstream)
        names = {line.removesuffix(": test") for line in listing.stdout.splitlines() if line.endswith(": test")}
        for fixture, source in selected.items():
            name = PREFIX[backend] + re.sub(r"[^A-Za-z0-9_]", "_", fixture) + "_main"
            if name not in names:
                raise ValueError(f"compiled fixture absent: {name}")
            command = [str(binary), "--exact", name, "--nocapture", "--test-threads=1"]
            started = time.monotonic()
            # Upstream bounds every external process and owns their cleanup.
            result = run(command, upstream, env=env)
            status, stage = outcome(result)
            row = {"backend": backend, "fixture": fixture, "source": str(source.relative_to(upstream)),
                   "sourceSha256": digest(source), "test": name, "command": command,
                   "status": status, "stage": stage, "exitCode": result.returncode,
                   "seconds": round(time.monotonic() - started, 3),
                   "stdout": result.stdout, "stderr": result.stderr}
            report["results"].append(row)
            report["evmReferenceExecuted"] = any(r["stage"] in
                {"evm", "deploy", "transaction", "call", "decode", "mismatch"} for r in report["results"])
            report["counts"] = dict(Counter(r["status"] for r in report["results"]))
            report["completed"] = len(report["results"]) == len(selected) * len(args.backend or PREFIX)
            report["passed"] = report["completed"] and all(r["status"] == "passed" for r in report["results"])
            args.output.write_text(json.dumps(report, indent=2) + "\n")
            print(f"{backend}/{fixture}: {status} ({stage}, {row['seconds']}s)", flush=True)
    return 0 if report["passed"] or args.report_only else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(2)
