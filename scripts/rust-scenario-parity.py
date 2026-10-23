#!/usr/bin/env python3
"""Execute pinned raw E2E scenarios through constructor and Core runtime calls.

Rust's own parser supplies ordered calldata, value and exact expectations.
Sonatina supplies linked code observables; no EVM or source evaluator executes.
Successful transactions retain storage, reverted transactions roll it back.
"""
from __future__ import annotations

import argparse
from collections import Counter
import fnmatch
import importlib.util
import json
import re
from pathlib import Path
import subprocess
import sys
import tempfile
from urllib.parse import unquote, urlparse

ROOT = Path(__file__).resolve().parent.parent
sys.dont_write_bytecode = True


def module(name: str, file: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / file)
    assert spec and spec.loader
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


images = module("code_images", "export-rust-code-image.py")
directives = module("directives", "export-rust-directives.py")
hull = images.hull
RAW_SENDER = "0x1212121212121212121212121212120000000012"
# CREATE(sender, nonce=0), matching the pinned raw scenario runner. No preceding
# transaction is sent when upstream funds and impersonates this account.
RAW_ADDRESS = "0x822d76f4c4ac0d26e89071fb06f116e7f3fc7a56"
RAW_ACCOUNTS = [{"address": str(int(RAW_SENDER, 16)),
    "balance": str(int("10000000000000000000000000", 16)), "empty": True}]


def sidecar(path: Path) -> Path:
    return path.with_suffix(path.suffix + ".provenance.json")


def valid_sources(sources: dict, source: Path) -> bool:
    if sources.get(source.as_uri()) != hull.digest(source.read_bytes()):
        return False
    for uri, expected in sources.items():
        parsed = urlparse(uri)
        path = Path(unquote(parsed.path))
        if parsed.scheme != "file" or not path.is_file() or hull.digest(path.read_bytes()) != expected:
            return False
    return True


def identities(upstream: Path, target: Path) -> tuple[dict, dict, dict]:
    patches = hull.prepare(upstream)
    driver = json.loads((target / "lean-export-build.json").read_text())
    if (driver.get("upstreamCommit") != hull.COMMIT or driver.get("patches") != patches
            or driver.get("binarySha256") != hull.digest((target / "debug/solcore-driver").read_bytes())):
        raise ValueError("checked Hull driver receipt is stale; rebuild export-rust-hull.py")
    image = json.loads((target / "code-image-export-build.json").read_text())
    images.check_pins(upstream)
    if (image.get("upstreamCommit") != hull.COMMIT or image.get("backendRevision") != images.BACKEND
            or any(image.get(key) != value for key, value in images.tool_hashes().items())
            or image.get("binarySha256") != hull.digest((target / "debug/solcore-code-image-export").read_bytes())):
        raise ValueError("code image tool receipt is stale; rebuild export-rust-code-image.py")
    directive = json.loads((target / "directive-export-build.json").read_text())
    expected = {"upstreamCommit": hull.COMMIT, "sourceSha256": hull.digest(directives.SOURCE.read_bytes()),
        "manifestSha256": hull.digest(directives.manifest(upstream).encode()),
        "lockSha256": hull.digest((directives.TOOL / "Cargo.lock").read_bytes()),
        "binarySha256": hull.digest((target / "debug/solcore-directive-export").read_bytes())}
    if directive != expected or directives.pins(directives.TOOL / "Cargo.lock") - directives.pins(upstream / "Cargo.lock"):
        raise ValueError("directive tool receipt is stale; rebuild export-rust-directives.py")
    return driver, image, directive


def run_export(command: list[str], timeout: float) -> None:
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=timeout)
    if result.returncode:
        raise ValueError(result.stderr + result.stdout)


def extract(source: Path, output: Path, upstream: Path, target: Path,
            identity: dict, reuse: bool, timeout: float) -> dict:
    if reuse and output.exists() and sidecar(output).exists():
        record = json.loads(sidecar(output).read_text())
        if (record.get("schema") == directives.SCHEMA and record.get("toolBuild") == identity
                and record.get("source") == source.as_uri()
                and record.get("sourceSha256") == hull.digest(source.read_bytes())
                and record.get("outputSha256") == hull.digest(output.read_bytes())):
            return json.loads(output.read_text())
    run_export([sys.executable, str(ROOT / "scripts/export-rust-directives.py"), str(source),
        "--output", str(output), "--upstream", str(upstream), "--target-dir", str(target)], timeout)
    return json.loads(output.read_text())


def export_images(source: Path, exported: Path, image: Path, upstream: Path, target: Path,
                  driver_build: dict, image_build: dict, reuse: bool, timeout: float) -> dict:
    if reuse and all(path.exists() for path in (exported, sidecar(exported), image, sidecar(image))):
        record = json.loads(sidecar(image).read_text())
        source_record = json.loads(sidecar(exported).read_text())
        if (record.get("schema") == images.SCHEMA and record.get("upstreamCommit") == hull.COMMIT
                and record.get("backendRevision") == images.BACKEND and record.get("optimization") == "O0"
                and record.get("toolBuild") == image_build
                and record.get("hullProvenance") == source_record
                and record.get("hullOutput") == str(exported)
                and source_record.get("upstreamCommit") == hull.COMMIT
                and source_record.get("binarySha256") == driver_build["binarySha256"]
                and source_record.get("patches") == driver_build["patches"]
                and source_record.get("outputSha256") == hull.digest(exported.read_bytes())
                and record.get("outputSha256") == hull.digest(image.read_bytes())
                and record.get("sources") == source_record.get("sources")
                and valid_sources(record.get("sources", {}), source)):
            return json.loads(exported.read_text())
    run_export([sys.executable, str(ROOT / "scripts/export-rust-code-image.py"), str(source),
        "--output", str(image), "--hull-output", str(exported), "--upstream", str(upstream),
        "--target-dir", str(target), "--timeout", str(timeout)], timeout * 3)
    return json.loads(exported.read_text())


def paths(objects: list[dict], parent: tuple = ()) -> list[tuple]:
    return [path for item in objects for path in
        [(*parent, item["name"]), *paths(item["inners"], (*parent, item["name"]))]]


def context(call: dict, gas: str | None) -> dict:
    result = {"calldata": call["calldata"], "value": str(int(call["value"], 16)),
        "caller": str(int(RAW_SENDER, 16)), "address": str(int(RAW_ADDRESS, 16))}
    if gas is not None:
        result["availableGas"] = gas
    return result


def expected_rows(fixture: str, scenario: dict, calls: list[dict]) -> list[dict]:
    constructor = scenario["constructor"]
    return [{"id": fixture + "/deploy", "expectedStage": "deployment", "expected": {
        "status": "returned" if constructor["expectedSuccess"] else "reverted",
        "output": constructor["expectedOutput"]}}] + [
        {"id": f"{fixture}/call/{index}", "index": index, "label": call["label"],
         "calldata": call["calldata"], "value": call["value"], "persist": True,
         "expectedStage": "execution", "expected": call["expected"]}
        for index, call in enumerate(calls)]


def results(stdout: str, stderr: str, exit_code: int | None, count: int) -> list[dict]:
    """Keep completed rows even when later preparation/execution fails."""
    error = {"stage": "harness", "status": "error", "detail": stdout + stderr}
    try:
        rows = [json.loads(line) for line in stdout.splitlines() if line.strip()]
        if any(not isinstance(row, dict) or "stage" not in row or "status" not in row for row in rows):
            raise ValueError("invalid result row")
        if any(row["status"] in ("returned", "reverted") and
                (not isinstance(row.get("output"), str) or not re.fullmatch(r"0x(?:[0-9a-f]{2})*", row["output"]))
                for row in rows):
            raise ValueError("completed result has no canonical byte output")
    except (ValueError, json.JSONDecodeError):
        return [error] * count
    if exit_code not in (None, 0, 1):
        return [{**error, "detail": f"unexpected process exit {exit_code}\n" + stdout + stderr}] * count
    normal, failure = [], None
    for row_index, row in enumerate(rows):
        if row["stage"] == "preparation" and row["status"] == "rejected":
            if row_index != len(rows) - 1:
                return [{**error, "detail": "result after terminal preparation failure\n" + stdout + stderr}] * count
            failure = row
            break
        position = len(normal)
        if (row["stage"] != ("deployment" if position == 0 else "execution")
                or (position > 0 and row.get("index") != position - 1)):
            return [{**error, "detail": "unexpected result order\n" + stdout + stderr}] * count
        normal.append(row)
    if len(normal) > count:
        return [{**error, "detail": "extra result rows\n" + stdout + stderr}] * count
    if exit_code is None:
        failure = {"stage": "harness", "status": "timeout", "detail": stderr}
    elif exit_code == 1 and not failure and all(row["status"] in ("returned", "reverted", "invalid") for row in normal):
        return [{**error, "detail": "unexplained nonzero process exit\n" + stdout + stderr}] * count
    blocked = failure or {"stage": "execution", "status": "not-executed", "detail": "deployment did not produce an executable runtime"}
    return normal + [blocked] * (count - len(normal))


def compare(observation: dict, actual: dict) -> None:
    expected = observation["expected"]
    matched = (actual["stage"] == observation["expectedStage"] and actual["status"] == expected["status"]
        and (expected["output"] is None or actual.get("output") == expected["output"]))
    observation.update(actual=actual, stage=actual["stage"], status="succeeded" if matched else
        "mismatch" if actual["status"] in ("returned", "reverted", "invalid") else actual["status"])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--manifest", type=Path, default=ROOT / "scripts/rust-scenario-parity.json")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--cache", type=Path, default=ROOT / ".upstream/hull-fixtures/scenarios")
    parser.add_argument("--fixture", action="append", default=[], help="fixture glob; repeatable")
    parser.add_argument("--call-prefix", type=int, help="execute first N calls in order, preserving state")
    parser.add_argument("--timeout", type=float, default=180)
    parser.add_argument("--reuse-exports", action="store_true")
    parser.add_argument("--report-only", action="store_true")
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.call_prefix is not None and args.call_prefix < 0:
        raise ValueError("--call-prefix must be nonnegative")
    upstream, target = args.upstream.resolve(), args.target_dir.resolve()
    manifest = json.loads(args.manifest.read_text())
    if manifest["upstreamCommit"] != hull.COMMIT:
        raise ValueError("scenario manifest has an unexpected upstream revision")
    driver_build, image_build, directive_build = identities(upstream, target)
    fixtures = [item for item in manifest["fixtures"] if not args.fixture or
        any(fnmatch.fnmatchcase(item["id"], pattern) for pattern in args.fixture)]
    if not fixtures:
        raise ValueError("no scenarios matched")
    observations, inventories = [], []
    for fixture in fixtures:
        source = (upstream / fixture["source"]).resolve()
        if not source.is_relative_to(upstream) or hull.digest(source.read_bytes()) != fixture["sha256"]:
            raise ValueError(f"fixture differs from pinned manifest: {fixture['id']}")
        directory = (args.cache / fixture["id"]).resolve()
        directory.mkdir(parents=True, exist_ok=True)
        extracted = extract(source, directory / "directives.json", upstream, target,
            directive_build, args.reuse_exports, args.timeout)
        if extracted["mode"] != "raw":
            raise ValueError(f"expected raw scenario: {fixture['id']}")
        scenario = extracted["scenario"]
        if scenario["contract"] != fixture["contract"] or len(scenario["calls"]) != fixture["expectedCallCount"]:
            raise ValueError(f"scenario inventory changed: {fixture['id']}")
        calls = scenario["calls"] if args.call_prefix is None else scenario["calls"][:args.call_prefix]
        rows = expected_rows(fixture["id"], scenario, calls)
        if args.list:
            for row in rows:
                print(row["id"], row.get("label", ""), row["expected"])
            continue
        gas = fixture.get("availableGas")
        inventory = {"id": fixture["id"], "source": str(source), "sha256": fixture["sha256"],
            "contract": scenario["contract"], "declaredCalls": len(scenario["calls"]), "selectedCalls": len(calls),
            "availableGas": gas, "coreFuel": fixture.get("coreFuel", 10000000),
            "evmVersionMetadata": scenario["evmVersionMetadata"],
            "effectiveEvmVersion": scenario["effectiveEvmVersion"], "capabilityNotes": fixture.get("capabilityNotes", [])}
        inventories.append(inventory)
        stage = "rust-code-image-export"
        try:
            exported, image = directory / "hull.json", directory / "images.json"
            document = export_images(source, exported, image, upstream, target,
                driver_build, image_build, args.reuse_exports, args.timeout)
            stage = "object-inventory"
            selected = [path for path in paths(document["program"]["objects"]) if path[-1] == scenario["contract"]]
            if len(selected) != 1 or len(selected[0]) < 2:
                raise ValueError(f"runtime object does not have a unique deploy parent: {selected}")
            config = {"schema": "solcore-lean.contract-scenario.v1", "hull": str(exported), "images": str(image),
                "deployPath": list(selected[0][:-1]), "runtimePath": list(selected[0]),
                "accounts": RAW_ACCOUNTS, "constructor": context(scenario["constructor"], gas),
                "calls": [{**context(call, gas), "persist": True} for call in calls]}
            if "coreFuel" in fixture:
                config["fuel"] = fixture["coreFuel"]
            inventory.update(deployPath=config["deployPath"], runtimePath=config["runtimePath"],
                imageSha256=hull.digest(image.read_bytes()), hullSha256=hull.digest(exported.read_bytes()))
            stage = "harness"
            with tempfile.TemporaryDirectory(prefix="solcore-core-scenario-") as temporary:
                inputs = Path(temporary) / "scenario.json"
                inputs.write_text(json.dumps(config))
                command = ["lake", "env", "lean", "--run", "Tests/RustHullScenarioRun.lean", str(inputs)]
                try:
                    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=args.timeout)
                    actuals = results(result.stdout, result.stderr, result.returncode, len(rows))
                except subprocess.TimeoutExpired as error:
                    stdout = error.stdout or b""
                    actuals = results(stdout.decode() if isinstance(stdout, bytes) else stdout,
                        str(error), None, len(rows))
        except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
            actuals = [{"stage": stage, "status": "rejected", "detail": str(error)}] * len(rows)
        for row, actual in zip(rows, actuals):
            compare(row, actual)
            observations.append(row)
            print(f"{row['id']}: {row['stage']}/{row['status']}", flush=True)
    if args.list:
        return 0
    succeeded = sum(row["status"] == "succeeded" for row in observations)
    summary = Counter(f"{row['stage']}:{row['status']}" for row in observations)
    report = {"upstreamCommit": hull.COMMIT, "scope": "deploymentAndPersistentCalls",
        "expectationSource": "upstream-rust-parser-and-test-directives", "evmReferenceExecuted": False,
        "backendRevision": images.BACKEND, "backendOptimization": "O0", "evmGasMetering": False,
        "caller": RAW_SENDER, "address": RAW_ADDRESS, "deploymentNonce": 0, "accounts": RAW_ACCOUNTS,
        "selection": {"fixtures": args.fixture, "callPrefix": args.call_prefix},
        "mode": "inventory" if args.report_only else "compatibility-check",
        "passed": succeeded == len(observations), "total": len(observations), "succeeded": succeeded,
        "stages": dict(sorted(summary.items())), "fixtures": inventories, "observations": observations}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{succeeded}/{len(observations)} constructor/call expectations matched")
    return 0 if args.report_only or report["passed"] else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(f"rust-scenario-parity: {error}", file=sys.stderr)
        raise SystemExit(2)
