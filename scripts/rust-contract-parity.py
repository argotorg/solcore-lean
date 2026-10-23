#!/usr/bin/env python3
"""Check pinned contract call expectations on Lean's Core runtime objects.

This is a runtime-only gate: each call starts with empty storage and default
context. Constructors, deployment, send directives, and raw EVM scenarios are
not executed. Expected values come from the unmodified upstream directives;
the upstream driver's ABI determines selectors and static encoding shapes.
"""

from __future__ import annotations

import argparse
from collections import Counter
import fnmatch
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from urllib.parse import unquote, urlparse

ROOT = Path(__file__).resolve().parent.parent
sys.dont_write_bytecode = True
_spec = importlib.util.spec_from_file_location("hull_export", ROOT / "scripts/export-rust-hull.py")
assert _spec and _spec.loader
exporter = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(exporter)


class Unsupported(ValueError):
    """An expectation cannot be represented by this runtime-only harness."""


class DirectiveParser:
    """The call subset of crates/test-directives/src/lib.rs, with strict EOF."""

    def __init__(self, text: str):
        self.text, self.position = text, 0

    def consume(self, token: str) -> bool:
        self.position += len(self.text[self.position:]) - len(self.text[self.position:].lstrip())
        if not self.text.startswith(token, self.position):
            return False
        self.position += len(token)
        return True

    def expect(self, token: str) -> None:
        if not self.consume(token):
            raise ValueError(f"expected {token!r} at directive offset {self.position}")

    def values(self) -> list:
        self.expect("(")
        values = []
        if self.consume(")"):
            return values
        while True:
            values.append(self.value())
            if self.consume(")"):
                return values
            self.expect(",")

    def value(self):
        remaining = self.text[self.position:].lstrip()
        if remaining.startswith("("):
            return self.values()
        for token, value in [("true", True), ("false", False)]:
            if re.match(token + r"\b", remaining):
                self.expect(token)
                return value
        match = re.match(r"(?:0[xX][0-9a-fA-F]+|[0-9]+)", remaining)
        if not match:
            raise ValueError(f"expected uint256, boolean, or tuple at offset {self.position}")
        token = match.group()
        self.expect(token)
        value = int(token, 16 if token.lower().startswith("0x") else 10)
        if value >= 2**256:
            raise ValueError("directive word exceeds 256 bits")
        return value

    def parse(self) -> dict:
        self.expect("#[")
        if self.text[self.position:].lstrip().startswith("send"):
            raise Unsupported("send requires persistent call sequencing")
        arguments = self.values()
        self.expect("->")
        if re.match(r"revert\b", self.text[self.position:].lstrip()):
            self.expect("revert")
            output = None
            if self.consume("("):
                match = re.match(r"\s*(0x(?:[0-9a-fA-F]{2})*)", self.text[self.position:])
                if not match:
                    raise ValueError("expected a whole-byte revert payload")
                self.position += len(match.group())
                output = "0x" + match.group(1)[2:].lower()
                self.expect(")")
            expected = {"status": "reverted", "output": output}
        else:
            values = self.values() if self.text[self.position:].lstrip().startswith("(") else [self.value()]
            expected = {"status": "returned", "values": values}
        self.expect("]")
        if self.text[self.position:].strip():
            raise ValueError("unexpected trailing directive text")
        return {"arguments": arguments, "expected": expected}


def source_directives(source: str) -> list[dict]:
    """Require directives to directly precede named functions in one contract.

    This bounded inventory deliberately rejects raw scenario/block directives
    and multiple contracts instead of silently associating them with a method.
    """
    contracts = re.findall(r"^\s*contract\s+(\w+)\b", source, re.MULTILINE)
    if len(contracts) != 1:
        raise Unsupported("fixture must contain exactly one contract")
    pending, cases = [], []
    for line_number, line in enumerate(source.splitlines(), 1):
        stripped = line.strip()
        if "#[" in stripped:
            match = re.fullmatch(r"//\s*(#\[.*)", stripped)
            if not match:
                raise Unsupported(f"unsupported directive at line {line_number}")
            pending.append({"line": line_number, "directive": match.group(1),
                **DirectiveParser(match.group(1)).parse()})
            continue
        if pending and stripped and not stripped.startswith("//"):
            match = re.match(r"function\s+(\w+)\s*(?:<|\()", stripped)
            if not match:
                raise Unsupported(f"directive does not precede a function at line {line_number}")
            for index, case in enumerate(pending, 1):
                cases.append({"contract": contracts[0], "method": match.group(1),
                    "vector": index, **case})
            pending = []
    if pending:
        raise ValueError("unattached directives at end of source")
    if not cases:
        raise Unsupported("fixture has no supported call directives")
    return cases


def canonical_type(shape: dict) -> str:
    if shape["type"] == "tuple":
        return "(" + ",".join(canonical_type(item) for item in shape["components"]) + ")"
    return shape["type"]


def encode_value(shape: dict, value) -> bytes:
    kind = shape["type"]
    if kind == "tuple":
        if not isinstance(value, list):
            raise ValueError("ABI tuple requires a tuple directive value")
        return encode_values(shape["components"], value)
    if kind == "bool":
        if type(value) is not bool:
            raise ValueError("ABI bool requires a boolean directive value")
        return int(value).to_bytes(32, "big")
    if kind not in ("uint256", "bytes32", "address"):
        raise Unsupported(f"unsupported ABI shape: {kind}")
    if type(value) is not int or not 0 <= value < 2 ** (160 if kind == "address" else 256):
        raise ValueError(f"invalid value for ABI {kind}")
    return value.to_bytes(32, "big")


def encode_values(shapes: list[dict], values: list) -> bytes:
    if len(shapes) != len(values):
        raise ValueError(f"ABI arity {len(shapes)} differs from directive arity {len(values)}")
    return b"".join(encode_value(shape, value) for shape, value in zip(shapes, values))


def object_paths(objects: list[dict], parent: tuple = ()) -> list[tuple]:
    result = []
    for item in objects:
        path = (*parent, item["name"])
        result.append(path)
        result.extend(object_paths(item["inners"], path))
    return result


def checked_export(upstream: Path, binary: Path, build: dict, source: Path,
                   output: Path, timeout: float, reuse: bool) -> dict:
    sidecar = output.with_suffix(".json.provenance.json")
    if reuse and output.exists() and sidecar.exists():
        record = json.loads(sidecar.read_text())
        urls = record.get("sources", {})
        valid_sources = bool(urls) and urls.get(source.as_uri()) == exporter.digest(source.read_bytes())
        for url, expected in urls.items():
            parsed = urlparse(url)
            path = Path(unquote(parsed.path))
            valid_sources &= parsed.scheme == "file" and path.exists() and exporter.digest(path.read_bytes()) == expected
        if (valid_sources and record.get("upstreamCommit") == build["upstreamCommit"]
                and record.get("binarySha256") == build["binarySha256"]
                and record.get("patches") == build["patches"]
                and record.get("outputSha256") == exporter.digest(output.read_bytes())):
            return json.loads(output.read_text())
    result = subprocess.run([sys.executable, str(ROOT / "scripts/export-rust-hull.py"),
        str(source), "--upstream", str(upstream), "--target-dir", str(binary.parent.parent),
        "--output", str(output)], cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    if result.returncode:
        raise RuntimeError(result.stderr + result.stdout)
    return json.loads(output.read_text())


def compile_abis(binary: Path, upstream: Path, source: Path, timeout: float) -> dict:
    with tempfile.TemporaryDirectory(prefix="solcore-runtime-abi-") as temporary:
        result = subprocess.run([str(binary), str(source), "--std-root", str(upstream / "std"),
            "--abi", "--output-dir", temporary], cwd=upstream,
            capture_output=True, text=True, timeout=timeout)
        if result.returncode:
            raise RuntimeError(result.stderr + result.stdout)
        return {path.stem: json.loads(path.read_text()) for path in Path(temporary).glob("*.abi")}


def batch_results(stdout: str, stderr: str, exit_code: int, count: int) -> list[dict]:
    error = {"stage": "harness", "status": "error", "detail": stdout + stderr}
    try:
        rows = [json.loads(line) for line in stdout.splitlines() if line.strip()]
        if any(not isinstance(row, dict) or "stage" not in row or "status" not in row for row in rows):
            raise ValueError("invalid result row")
    except (ValueError, json.JSONDecodeError):
        return [error] * count
    if len(rows) == 1 and exit_code != 0 and rows[0]["stage"] in ("input", "transport", "lowering"):
        return rows * count
    if len(rows) != count or exit_code not in (0, 1):
        return [{**error, "detail": f"unexpected batch result count/exit code: {len(rows)}/{exit_code}\n" + stdout + stderr}] * count
    # Exit 1 summarizes per-call failures. It must not invalidate successful
    # rows, but an unexplained nonzero exit cannot count as a passing batch.
    if exit_code == 1 and all(row["status"] in ("returned", "reverted", "invalid") for row in rows):
        return [{**error, "detail": "unexplained nonzero batch exit\n" + stdout + stderr}] * count
    return rows


def record_result(observation: dict, actual: dict, exit_code: int, count: int) -> None:
    expected = observation["expected"]
    observation.update(actual=actual, batchExitCode=exit_code, batchSize=count)
    matched = (actual.get("stage") == "execution" and actual.get("status") == expected["status"]
        and (expected["output"] is None or actual.get("output") == expected["output"]))
    observation.update(stage=actual.get("stage", "harness"),
        status="succeeded" if matched else "mismatch" if actual.get("status")
        in ("returned", "reverted", "invalid") else actual.get("status", "error"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--manifest", type=Path, default=ROOT / "scripts/rust-contract-parity.json")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--cache", type=Path, default=ROOT / ".upstream/hull-fixtures/contracts")
    parser.add_argument("--fixture", action="append", default=[], help="fixture ID glob; repeatable")
    parser.add_argument("--case", action="append", default=[], help="fixture/method/vector glob; repeatable")
    parser.add_argument("--limit-per-fixture", type=int, help="execute only the first N selected calls per fixture")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--timeout", type=float, default=120, help="per-process timeout seconds")
    parser.add_argument("--reuse-exports", action="store_true")
    parser.add_argument("--report-only", action="store_true", help="collect failures without passing a gate")
    parser.add_argument("--list", action="store_true", help="list directives without exporting or executing")
    args = parser.parse_args()
    upstream = args.upstream.resolve()
    manifest = json.loads(args.manifest.read_text())
    head = exporter.git(upstream, "rev-parse", "HEAD").strip()
    if head != manifest["upstream_commit"]:
        raise ValueError("upstream revision differs from pinned contract manifest")
    if args.limit_per_fixture is not None and args.limit_per_fixture < 1:
        raise ValueError("--limit-per-fixture must be positive")
    fixtures, discovered_calls = [], 0
    for fixture in manifest["fixtures"]:
        if args.fixture and not any(fnmatch.fnmatchcase(fixture["id"], pattern) for pattern in args.fixture):
            continue
        source = (upstream / fixture["source"]).resolve()
        if not source.is_relative_to(upstream) or exporter.digest(source.read_bytes()) != fixture["sha256"]:
            raise ValueError(f"fixture source differs from pinned manifest: {fixture['id']}")
        cases = []
        declared = source_directives(source.read_text())
        if len(declared) != fixture["expectedCallCount"]:
            raise ValueError(f"directive inventory changed for {fixture['id']}")
        discovered_calls += len(declared)
        for case in declared:
            case["id"] = f"{fixture['id']}/{case['method']}/{case['vector']}"
            if not args.case or any(fnmatch.fnmatchcase(case["id"], pattern) for pattern in args.case):
                cases.append(case)
        if args.limit_per_fixture:
            cases = cases[:args.limit_per_fixture]
        if args.list:
            for case in cases:
                print(f"{case['id']}: {case['directive']}")
        if cases:
            fixtures.append((fixture, source, cases))
    if not fixtures:
        raise ValueError("no contract calls matched")
    if args.list:
        return 0
    cast = shutil.which("cast")
    if cast is None:
        raise ValueError("cast is required to compute Ethereum Keccak function selectors")
    patches = exporter.prepare(upstream)
    target = args.target_dir.resolve()
    binary = target / "debug/solcore-driver"
    build = json.loads((target / "lean-export-build.json").read_text())
    if (build.get("upstreamCommit") != head or build.get("patches") != patches
            or exporter.digest(binary.read_bytes()) != build.get("binarySha256")):
        raise ValueError("exporter build receipt does not match; rebuild with export-rust-hull.py --build")
    observations, selectors = [], {}
    for fixture, source, cases in fixtures:
        directory = args.cache / fixture["id"]
        directory.mkdir(parents=True, exist_ok=True)
        exported = directory / "hull.json"
        preparation_stage = "rust-hull-export"
        try:
            envelope = checked_export(upstream, binary, build, source, exported, args.timeout, args.reuse_exports)
            preparation_stage = "rust-abi"
            abis = compile_abis(binary, upstream, source, args.timeout)
            # Persist the exact ABI used, together with the same compiler/source identity.
            abi_path = directory / "abi.json"
            abi_path.write_text(json.dumps(abis, indent=2) + "\n")
            abi_path.with_suffix(".json.provenance.json").write_text(json.dumps({
                "upstreamCommit": head, "binarySha256": build["binarySha256"],
                "patches": patches, "outputSha256": exporter.digest(abi_path.read_bytes()),
                "source": source.as_uri(), "sourceSha256": fixture["sha256"]}, indent=2) + "\n")
            preparation_stage = "object-inventory"
            paths = object_paths(envelope["program"]["objects"])
            preparation_error = None
        except (ValueError, KeyError, OSError, RuntimeError, subprocess.SubprocessError) as error:
            preparation_error = str(error)
        fixture_observations = []
        for case in cases:
            observation = {**case, "scope": "runtimeOnly", "deploymentTested": False,
                "constructorTested": False, "export": str(exported)}
            try:
                if preparation_error:
                    observation.update(stage=preparation_stage, status="rejected", detail=preparation_error)
                else:
                    selected = [path for path in paths if path[-1] == case["contract"]]
                    if len(selected) != 1:
                        raise ValueError(f"runtime object not unique: {selected}")
                    abi = [entry for entry in abis[case["contract"]]
                        if entry["type"] == "function" and entry["name"] == case["method"]]
                    if len(abi) != 1:
                        raise Unsupported("overloaded or absent method ABI")
                    method = abi[0]
                    signature = case["method"] + "(" + ",".join(canonical_type(item) for item in method["inputs"]) + ")"
                    if signature not in selectors:
                        selectors[signature] = subprocess.check_output([cast, "sig", signature],
                            text=True, timeout=args.timeout).strip()
                    selector = selectors[signature]
                    if not re.fullmatch(r"0x[0-9a-fA-F]{8}", selector):
                        raise ValueError("cast returned an invalid selector")
                    calldata = selector + encode_values(method["inputs"], case["arguments"]).hex()
                    expected = dict(case["expected"])
                    if expected["status"] == "returned":
                        expected["output"] = "0x" + encode_values(method["outputs"], expected["values"]).hex()
                    observation.update(object="/".join(selected[0]), signature=signature,
                        calldata=calldata, expected=expected)
            except Unsupported as error:
                observation.update(stage="expectation", status="unsupported", detail=str(error))
            except subprocess.TimeoutExpired as error:
                observation.update(stage="harness", status="timeout", detail=str(error))
            except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
                observation.update(stage="harness", status="error", detail=str(error))
            fixture_observations.append(observation)
        pending = [row for row in fixture_observations if "status" not in row]
        if pending:
            try:
                if len({row["object"] for row in pending}) != 1:
                    raise ValueError("batch cases refer to different runtime objects")
                with tempfile.TemporaryDirectory(prefix="solcore-runtime-calls-") as temporary:
                    inputs = Path(temporary) / "inputs.json"
                    inputs.write_text(json.dumps([row["calldata"] for row in pending]))
                    command = ["lake", "env", "lean", "--run", "Tests/RustHullContractRun.lean",
                        str(exported), pending[0]["object"], "--batch", str(inputs)]
                    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=args.timeout)
                for row, actual in zip(pending, batch_results(result.stdout, result.stderr, result.returncode, len(pending))):
                    record_result(row, actual, result.returncode, len(pending))
            except subprocess.TimeoutExpired as error:
                for row in pending:
                    row.update(stage="harness", status="timeout", detail=str(error))
            except (ValueError, OSError, subprocess.SubprocessError) as error:
                for row in pending:
                    row.update(stage="harness", status="error", detail=str(error))
        observations.extend(fixture_observations)
        for row in fixture_observations:
            print(f"{row['id']}: {row['stage']}/{row['status']}", flush=True)
    summary = Counter(f"{row['stage']}:{row['status']}" for row in observations)
    succeeded = sum(row["status"] == "succeeded" for row in observations)
    report = {"upstream_commit": head, "scope": "runtimeOnly", "deploymentTested": False,
        "constructorTested": False, "freshContextPerCall": True,
        "expectationSource": "upstream-call-directives", "evmReferenceExecuted": False,
        "selection": {"fixtures": args.fixture, "cases": args.case,
            "limitPerFixture": args.limit_per_fixture},
        "discoveredCallsInSelectedFixtures": discovered_calls,
        "mode": "inventory" if args.report_only else "compatibility-check",
        "passed": succeeded == len(observations), "total": len(observations), "succeeded": succeeded,
        "stages": dict(sorted(summary.items())), "observations": observations}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{succeeded}/{len(observations)} runtime-only calls matched upstream expectations")
    for stage, count in sorted(summary.items()):
        print(f"  {stage}: {count}")
    if args.report_only and not report["passed"]:
        print("Inventory only: runtime compatibility remains incomplete.")
    return 0 if args.report_only or report["passed"] else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"rust-contract-parity: {error}", file=sys.stderr)
        raise SystemExit(2)
