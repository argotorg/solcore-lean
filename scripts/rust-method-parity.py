#!/usr/bin/env python3
"""Run pinned method directives after deployment, using Rust's ABI resolver.

Ordinary directives discard writes as upstream eth_call does; send directives
persist writes and require success without asserting returned bytes. Constructor
and sends use the fixture's standard Anvil account; eth_call omits from and uses
address zero. No EVM is run and available gas is not metered.
"""
from __future__ import annotations

import argparse
from collections import Counter
import fnmatch
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
sys.dont_write_bytecode = True
import importlib.util
_spec = importlib.util.spec_from_file_location("scenario_parity", ROOT / "scripts/rust-scenario-parity.py")
assert _spec and _spec.loader
scenario = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(scenario)
resolver = scenario.module("directive_resolve", "build-rust-directive-resolver.py")
static = scenario.module("static_parity", "rust-contract-parity.py")
hull = scenario.hull
METHOD_SENDER = "0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266"
METHOD_ADDRESS = "0x5fbdb2315678afecb367f032d93f642f64180aa3"
METHOD_ACCOUNTS = [{"address": str(int(METHOD_SENDER, 16)),
    "balance": str(10000 * 10**18), "empty": True}]


def resolve(extracted: dict, abis: dict, binary: Path, cast: str, timeout: float) -> dict:
    targets = []
    for method in extracted["methods"]:
        entries = [item for item in abis[method["contract"]] if item["type"] == "function" and item["name"] == method["method"]]
        if len(entries) != 1:
            raise ValueError("method does not have a unique ABI")
        abi = entries[0]
        signature = method["method"] + "(" + ",".join(static.canonical_type(item) for item in abi["inputs"]) + ")"
        selector = subprocess.check_output([cast, "sig", signature], text=True, timeout=timeout).strip()
        targets.append({"contract": method["contract"], "method": method["method"], "signature": signature,
            "selector": selector, "inputs": abi["inputs"], "outputs": abi["outputs"],
            "comments": [item["comment"] for item in method["directives"]]})
    with tempfile.TemporaryDirectory(prefix="solcore-method-resolve-") as directory:
        input_file = Path(directory) / "input.json"
        input_file.write_text(json.dumps({"schema": "solcore-rs.method-resolution-input.v1", "targets": targets}))
        result = subprocess.run([str(binary), str(input_file)], text=True, capture_output=True, timeout=timeout)
        if result.returncode:
            raise ValueError(result.stderr + result.stdout)
        document = json.loads(result.stdout)
    if document.get("schema") != "solcore-rs.resolved-methods.v1" or document.get("upstreamCommit") != hull.COMMIT:
        raise ValueError("unexpected method resolver schema or revision")
    return document


def call_context(calldata: str, persist: bool, gas: str | None) -> dict:
    result = {"calldata": calldata, "value": "0", "caller": str(int(METHOD_SENDER, 16)) if persist else "0",
        "address": str(int(METHOD_ADDRESS, 16)), "persist": persist}
    if gas is not None:
        result["availableGas"] = gas
    return result


def expected_rows(fixture: str, extracted: dict) -> list[dict]:
    rows = [{"id": fixture + "/deploy", "expectedStage": "deployment", "expected": {"status": "returned", "output": None}}]
    for method in extracted["methods"]:
        for vector, directive in enumerate(method["directives"], 1):
            rows.append({"id": f"{fixture}/{method['method']}/{vector}", "expectedStage": "execution",
                "method": method["method"], "vector": vector, "comment": directive["comment"]})
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--manifest", type=Path, default=ROOT / "scripts/rust-method-parity.json")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--cache", type=Path, default=ROOT / ".upstream/hull-fixtures/methods")
    parser.add_argument("--fixture", action="append", default=[])
    parser.add_argument("--call-prefix", type=int)
    parser.add_argument("--timeout", type=float, default=180)
    parser.add_argument("--reuse-exports", action="store_true")
    parser.add_argument("--report-only", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.call_prefix is not None and args.call_prefix < 0:
        raise ValueError("--call-prefix must be nonnegative")
    upstream, target = args.upstream.resolve(), args.target_dir.resolve()
    driver_build, image_build, directive_build = scenario.identities(upstream, target)
    resolver_build = resolver.checked_identity(upstream, target)
    manifest = json.loads(args.manifest.read_text())
    if manifest["upstreamCommit"] != hull.COMMIT:
        raise ValueError("unexpected method manifest revision")
    fixtures = [item for item in manifest["fixtures"] if not args.fixture or
        any(fnmatch.fnmatchcase(item["id"], pattern) for pattern in args.fixture)]
    if not fixtures:
        raise ValueError("no method fixtures matched")
    cast = shutil.which("cast")
    if not cast:
        raise ValueError("cast is required for Ethereum function selectors")
    observations, inventories = [], []
    for fixture in fixtures:
        source = (upstream / fixture["source"]).resolve()
        if not source.is_relative_to(upstream) or hull.digest(source.read_bytes()) != fixture["sha256"]:
            raise ValueError(f"fixture differs from pinned manifest: {fixture['id']}")
        directory = (args.cache / fixture["id"]).resolve()
        directory.mkdir(parents=True, exist_ok=True)
        extracted = scenario.extract(source, directory / "directives.json", upstream, target,
            directive_build, args.reuse_exports, args.timeout)
        rows = expected_rows(fixture["id"], extracted)
        if extracted["mode"] != "methods" or len(rows) - 1 != fixture["expectedCallCount"]:
            raise ValueError(f"method inventory changed: {fixture['id']}")
        if args.call_prefix is not None:
            rows = rows[:args.call_prefix + 1]
        gas = fixture.get("availableGas")
        inventory = {"id": fixture["id"], "source": str(source), "sha256": fixture["sha256"],
            "contract": fixture["contract"], "declaredCalls": fixture["expectedCallCount"],
            "selectedCalls": len(rows) - 1, "availableGas": gas, "coreFuel": fixture.get("coreFuel", 10000000)}
        inventories.append(inventory)
        stage = "rust-code-image-export"
        try:
            exported, image = directory / "hull.json", directory / "images.json"
            document = scenario.export_images(source, exported, image, upstream, target,
                driver_build, image_build, args.reuse_exports, args.timeout)
            stage = "rust-abi-resolution"
            abis = static.compile_abis(target / "debug/solcore-driver", upstream, source, args.timeout)
            resolved = resolve(extracted, abis, target / "debug/solcore-directive-resolve", cast, args.timeout)
            calls = resolved["calls"][:len(rows) - 1]
            if len(calls) != len(rows) - 1 or any(call["contract"] != fixture["contract"] for call in calls):
                raise ValueError("resolved directive count or contract changed")
            for row, call in zip(rows[1:], calls):
                if row["method"] != call["method"] or row["vector"] != call["vector"]:
                    raise ValueError("resolved method ordering changed")
                row.update(expected=call["expected"], calldata=call["calldata"], persist=call["persist"], signature=call["signature"])
            output = directory / "resolved.json"
            output.write_text(json.dumps(resolved, indent=2) + "\n")
            abi = directory / "abi.json"
            abi.write_text(json.dumps(abis, indent=2) + "\n")
            scenario.sidecar(output).write_text(json.dumps({"schema": "solcore-rs.resolved-methods.v1",
                "toolBuild": resolver_build, "driverBuild": driver_build,
                "directivesProvenance": json.loads(scenario.sidecar(directory / "directives.json").read_text()),
                "sources": json.loads(scenario.sidecar(exported).read_text())["sources"],
                "abiSha256": hull.digest(abi.read_bytes()), "outputSha256": hull.digest(output.read_bytes())}, indent=2) + "\n")
            stage = "object-inventory"
            selected = [path for path in scenario.paths(document["program"]["objects"]) if path[-1] == fixture["contract"]]
            if len(selected) != 1 or len(selected[0]) < 2:
                raise ValueError(f"runtime lacks a unique deploy parent: {selected}")
            config = {"schema": "solcore-lean.contract-scenario.v1", "hull": str(exported), "images": str(image),
                "deployPath": list(selected[0][:-1]), "runtimePath": list(selected[0]),
                "accounts": METHOD_ACCOUNTS, "constructor": call_context("0x", True, gas),
                "calls": [call_context(call["calldata"], call["persist"], gas) for call in calls]}
            if "coreFuel" in fixture:
                config["fuel"] = fixture["coreFuel"]
            inventory.update(deployPath=config["deployPath"], runtimePath=config["runtimePath"],
                imageSha256=hull.digest(image.read_bytes()), hullSha256=hull.digest(exported.read_bytes()))
            stage = "harness"
            with tempfile.TemporaryDirectory(prefix="solcore-core-methods-") as temporary:
                inputs = Path(temporary) / "scenario.json"
                inputs.write_text(json.dumps(config))
                command = ["lake", "env", "lean", "--run", "Tests/RustHullScenarioRun.lean", str(inputs)]
                try:
                    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=args.timeout)
                    actuals = scenario.results(result.stdout, result.stderr, result.returncode, len(rows))
                except subprocess.TimeoutExpired as error:
                    stdout = error.stdout or b""
                    actuals = scenario.results(stdout.decode() if isinstance(stdout, bytes) else stdout,
                        str(error), None, len(rows))
        except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
            actuals = [{"stage": stage, "status": "rejected", "detail": str(error)}] * len(rows)
        for row, actual in zip(rows, actuals):
            if "expected" in row:
                scenario.compare(row, actual)
            else:
                row.update(actual=actual, stage=actual["stage"], status=actual["status"])
            observations.append(row)
            print(f"{row['id']}: {row['stage']}/{row['status']}", flush=True)
    succeeded = sum(row["status"] == "succeeded" for row in observations)
    summary = Counter(f"{row['stage']}:{row['status']}" for row in observations)
    report = {"upstreamCommit": hull.COMMIT, "scope": "deploymentAndMethodDirectives",
        "expectationSource": "upstream-rust-parser-and-abi-resolver", "evmReferenceExecuted": False,
        "backendRevision": scenario.images.BACKEND, "backendOptimization": "O0", "evmGasMetering": False,
        "constructorAndSendCaller": METHOD_SENDER, "readOnlyCallCaller": "0x" + "0" * 40,
        "address": METHOD_ADDRESS, "deploymentNonce": 0, "accounts": METHOD_ACCOUNTS,
        "selection": {"fixtures": args.fixture, "callPrefix": args.call_prefix},
        "mode": "inventory" if args.report_only else "compatibility-check",
        "passed": succeeded == len(observations), "total": len(observations), "succeeded": succeeded,
        "stages": dict(sorted(summary.items())), "fixtures": inventories, "observations": observations}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{succeeded}/{len(observations)} constructor/method expectations matched")
    return 0 if args.report_only or report["passed"] else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(f"rust-method-parity: {error}", file=sys.stderr)
        raise SystemExit(2)
