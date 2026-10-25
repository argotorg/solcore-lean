#!/usr/bin/env python3
"""Replay one checked pure case through direct Core, imported Hull and local EVM.

This is a single-case runner, not a campaign or shrinker. It starts its own
loopback-only Anvil and never connects to an existing chain. Passing means all
three fresh executions completed and returned the same ABI Word. The source
emitter remains part of the test setup, not a proved compiler pass.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CASE_SCHEMA = "solcore-lean.semantic-case.v1"
INPUT_CASE_SCHEMA = "solcore-lean.semantic-input-case.v1"
FUNCTION_CASE_SCHEMA = "solcore-lean.semantic-function-case.v1"
MUTATION_CASE_SCHEMA = "solcore-lean.semantic-mutation-case.v1"
AGGREGATE_CASE_SCHEMA = "solcore-lean.semantic-aggregate-case.v1"
CASE_PROFILES = {CASE_SCHEMA: "closed-g0", INPUT_CASE_SCHEMA: "runtime-word",
                 FUNCTION_CASE_SCHEMA: "runtime-functions", MUTATION_CASE_SCHEMA: "runtime-mutation",
                 AGGREGATE_CASE_SCHEMA: "runtime-aggregates"}
CASE_CONTRACTS = {CASE_SCHEMA: "SynthesizedG0", INPUT_CASE_SCHEMA: "SynthesizedInput",
                  FUNCTION_CASE_SCHEMA: "SynthesizedFunctions", MUTATION_CASE_SCHEMA: "SynthesizedMutation",
                  AGGREGATE_CASE_SCHEMA: "SynthesizedAggregates"}
REPORT_SCHEMA = "solcore-lean.semantic-differential.v1"
UPSTREAM_COMMIT = "2a745e12974c373c3799fec81b48a53c7dce2ab4"
BACKEND_COMMIT = "8ee24814ea9b32c762df8ef80c796e7d48797c0f"
MAX_CASE_BYTES = 4 * 1024 * 1024
GAS_RESOURCE = re.compile(r"out[ _-]?of[ _-]?gas|intrinsic gas.{0,40}(too low|exceed)|"
                          r"gas (required|limit).{0,40}(allowance|exceed)|gas too low", re.I)
RESOURCE = re.compile(GAS_RESOURCE.pattern + r"|out.of.fuel|fuel.{0,40}(exhaust|limit|budget)|"
                      r"(specialization|recursion|export|depth).{0,40}(limit|exhaust)|"
                      r"stack overflow|memory limit", re.I)
COMPLETED = {"returned", "reverted"}


class Finding(Exception):
    def __init__(self, category: str, stage: str, detail: str):
        self.category, self.stage, self.detail = category, stage, detail
        super().__init__(detail)


class RpcError(Exception):
    def __init__(self, error):
        self.error = error
        super().__init__(str(error))


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_digest(path: Path) -> str:
    """Hash artifacts without loading a rejected oversized file into memory."""
    result = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(65536), b""):
            result.update(chunk)
    return result.hexdigest()


def verify_archive(directory: Path, report: dict) -> None:
    if not isinstance(report, dict) or report.get("schema") != REPORT_SCHEMA:
        raise ValueError("unsupported saved report schema")
    artifacts = report.get("artifacts")
    if not isinstance(artifacts, dict) or "case.json" not in artifacts:
        raise ValueError("saved artifact inventory is missing its case")
    for name, expected in artifacts.items():
        if (not isinstance(name, str) or not name or name in {".", "..", "report.json"}
                or "/" in name or "\\" in name or Path(name).name != name):
            raise ValueError("saved artifact name must be a plain file name")
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError(f"invalid saved artifact hash: {name}")
        path = directory / name
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"saved artifact is missing or is not a regular file: {name}")
        if file_digest(path) != expected:
            raise ValueError(f"saved artifact hash changed: {name}")
    if artifacts["case.json"] != report.get("caseSha256"):
        raise ValueError("saved case hash differs from the artifact inventory")


def json_bytes(value) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2) + "\n").encode()


def read_json(path: Path, limit: int = MAX_CASE_BYTES):
    if path.stat().st_size > limit:
        raise Finding("inconclusive-resource", "input", f"file exceeds {limit} bytes: {path}")
    return json.loads(path.read_text())


def hex_bytes(value, label: str) -> bytes:
    if not isinstance(value, str) or not re.fullmatch(r"0x(?:[0-9a-fA-F]{2})*", value):
        raise ValueError(f"{label} is not a hexadecimal byte string")
    return bytes.fromhex(value[2:])


def word(value, label="word") -> str:
    if not isinstance(value, str) or not re.fullmatch(r"0|[1-9][0-9]*", value):
        raise ValueError(f"{label} must be a canonical decimal string")
    if len(value) > 78 or int(value) >= 2**256:
        raise ValueError(f"{label} exceeds 256 bits")
    return value


def validate_case(case: dict) -> None:
    if not isinstance(case, dict) or case.get("schema") not in CASE_PROFILES:
        raise ValueError("unsupported semantic case schema")
    if not isinstance(case.get("program"), dict) or not isinstance(case.get("source"), str):
        raise ValueError("case requires its original Core program and emitted source")
    provenance = case.get("provenance")
    if not isinstance(provenance, dict):
        raise ValueError("case provenance is missing")
    for key in ("generatorVersion", "emitterVersion", "wrapperVersion"):
        if not isinstance(provenance.get(key), str) or not provenance[key]:
            raise ValueError(f"missing provenance {key}")
    contract = case.get("contract", {})
    if not isinstance(contract, dict):
        raise ValueError("case contract metadata is missing")
    name = CASE_CONTRACTS[case["schema"]]
    if case["schema"] != CASE_SCHEMA:
        signature = "run(uint256)"
        calldata = bytes.fromhex("a444f5e9") + int(word(case.get("input"), "input")).to_bytes(32, "big")
    else:
        signature = "run()"
        calldata = bytes.fromhex("c0406226")
    if (contract.get("name"), contract.get("method"), contract.get("signature")) != (name, "run", signature):
        raise Finding("unsupported-scope", "input", "contract wrapper differs from its case profile")
    if contract.get("deployPath") != [name + "Deploy"] or contract.get("runtimePath") != [name + "Deploy", name]:
        raise ValueError("unexpected generated object paths")
    if hex_bytes(contract.get("calldata"), "calldata") != calldata:
        raise ValueError("calldata differs from the profile selector and original Core input")
    if hex_bytes(contract.get("constructorCalldata"), "constructorCalldata"):
        raise Finding("unsupported-scope", "input", "constructor arguments are outside the initial profile")


def normalize_observation(row: dict, *, direct: bool = False) -> dict:
    if not isinstance(row, dict) or row.get("stage") != "execution":
        raise ValueError("missing execution observation")
    status = row.get("status")
    if status == "returned":
        if direct:
            result = word(row.get("word"))
        else:
            data = hex_bytes(row.get("output"), "return data")
            if len(data) != 32:
                return {"status": status, "output": "0x" + data.hex()}
            result = str(int.from_bytes(data, "big"))
        return {"status": status, "word": result}
    if status == "reverted":
        return {"status": status, "output": "0x" + hex_bytes(row.get("output"), "revert data").hex()}
    if not isinstance(status, str):
        raise ValueError("missing execution status")
    return {"status": status, "detail": row.get("detail", "")}


def compare(observations: dict) -> dict:
    """Classify only actual completed observations, never missing paths as equal."""
    names = ("directCore", "importedHull", "rustEvm")
    if set(observations) != set(names):
        return {"category": "adapter-error", "detail": "three observations are required", "pairs": {}}
    rows = [observations[name] for name in names]
    completed = []
    try:
        for row in rows:
            if row.get("status") == "returned":
                if ("word" in row) == ("output" in row):
                    raise ValueError("a returned observation requires exactly one payload")
                data = (int(word(row["word"])).to_bytes(32, "big") if "word" in row
                        else hex_bytes(row["output"], "return data"))
                completed.append(("returned", data))
            elif row.get("status") == "reverted":
                completed.append(("reverted", hex_bytes(row.get("output"), "revert data")))
            else:
                completed.append(None)
    except (AttributeError, ValueError):
        return {"category": "adapter-error", "detail": "malformed completed observation", "pairs": {}}
    statuses = [row.get("status") for row in rows]
    if any(status in {"out-of-fuel", "out-of-gas", "timeout", "output-limit", "resource-limit"} for status in statuses):
        return {"category": "inconclusive-resource", "pairs": {}}
    if any(status not in COMPLETED for status in statuses):
        return {"category": "execution-error", "pairs": {}}
    pairs = {f"{names[left]}/{names[right]}": completed[left] == completed[right]
             for left, right in ((0, 2), (0, 1), (1, 2))}
    return {"category": "matched" if all(pairs.values()) and all(status == "returned" for status in statuses) else "semantic-mismatch", "pairs": pairs}


def core_rows(stdout: str, exit_code: int) -> list[dict]:
    rows = [json.loads(line) for line in stdout.splitlines() if line.strip()]
    if exit_code not in (0, 1) or not rows or any(not isinstance(row, dict) for row in rows):
        raise ValueError("invalid Core scenario process result")
    if rows[-1].get("stage") == "preparation" and rows[-1].get("status") == "rejected":
        detail = rows[-1].get("detail", "Core preparation rejected")
        raise Finding("inconclusive-resource" if RESOURCE.search(str(detail)) else "compilation-rejected", "core-preparation", detail)
    if rows[0].get("stage") != "deployment":
        raise ValueError("missing Core deployment result")
    if rows[0].get("status") != "returned":
        status = rows[0].get("status")
        category = "inconclusive-resource" if status == "out-of-fuel" else "execution-error"
        raise Finding(category, "core-deployment", json.dumps(rows[0]))
    if len(rows) != 2 or rows[1].get("stage") != "execution" or rows[1].get("index") != 0:
        raise ValueError("expected exactly one ordered Core call after deployment")
    if exit_code != 0 and rows[1].get("status") in {"returned", "reverted", "invalid"}:
        raise ValueError("unexplained Core process failure after completed result")
    return rows


def stop_process(process: subprocess.Popen) -> None:
    # Each process owns a new session. Also stop descendants if its leader has
    # already exited; never signal a shared shell or unrelated Lean process.
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait(timeout=2)


class Runner:
    def __init__(self, args, report):
        self.args, self.report = args, report
        self.deadline = time.monotonic() + args.total_timeout

    def guard(self) -> None:
        guard = getattr(self.args, "resource_guard", None)
        if guard is not None:
            guard()

    def remaining(self, timeout: float) -> float:
        self.guard()
        left = min(timeout, self.deadline - time.monotonic())
        if left <= 0:
            raise Finding("inconclusive-resource", "runner", "total time budget exhausted")
        return left

    def process(self, stage: str, command: list[str], timeout: float | None = None) -> dict:
        started = time.monotonic()
        budget = self.remaining(timeout or self.args.timeout)
        with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
            process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.DEVNULL,
                                       stdout=stdout, stderr=stderr, start_new_session=True)
            reason = None
            try:
                while process.poll() is None:
                    self.guard()
                    if time.monotonic() - started >= budget:
                        reason = "timeout"
                        break
                    if stdout.tell() + stderr.tell() > self.args.output_limit:
                        reason = "output-limit"
                        break
                    time.sleep(0.05)
            finally:
                stop_process(process)
            if stdout.tell() + stderr.tell() > self.args.output_limit:
                reason = "output-limit"
            stdout.seek(0)
            stderr.seek(0)
            result = {"stage": stage, "command": command, "returncode": process.returncode,
                      "elapsedSeconds": round(time.monotonic() - started, 3),
                      "stdout": stdout.read(self.args.output_limit).decode(errors="replace"),
                      "stderr": stderr.read(self.args.output_limit).decode(errors="replace")}
        if reason:
            result["resourceFailure"] = reason
        self.report["processes"].append(result)
        self.guard()
        if reason:
            raise Finding("inconclusive-resource", stage, reason)
        return result

    def identity(self, path: Path, version=False) -> dict:
        path = path.resolve(strict=True)
        self.guard()
        result = {"path": str(path), "sha256": file_digest(path)}
        self.guard()
        if version:
            outcome = self.process("tool-version", [str(path), "--version"], 10)
            if outcome["returncode"]:
                raise Finding("adapter-error", "tool-version", str(path))
            result["version"] = outcome["stdout"].strip()
        return result


class Rpc:
    def __init__(self, url: str, runner: Runner):
        self.url, self.runner, self.counter = url, runner, 0
        # A local chain must not be routed through HTTP_PROXY/HTTPS_PROXY.
        self.opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))

    def call(self, method: str, params):
        self.runner.guard()
        self.counter += 1
        payload = {"jsonrpc": "2.0", "id": self.counter, "method": method, "params": params}
        request = urllib.request.Request(self.url, json_bytes(payload), {"Content-Type": "application/json"})
        with self.opener.open(request, timeout=self.runner.remaining(10)) as response:
            content = response.read(self.runner.args.output_limit + 1)
        self.runner.guard()
        if len(content) > self.runner.args.output_limit:
            raise Finding("inconclusive-resource", "evm-rpc", "RPC output limit")
        result = json.loads(content)
        if result.get("id") != self.counter or result.get("jsonrpc") != "2.0":
            raise ValueError("invalid JSON-RPC response")
        if "error" in result:
            raise RpcError(result["error"])
        if "result" not in result:
            raise ValueError("missing JSON-RPC result")
        return result["result"]


@contextmanager
def anvil(runner: Runner, binary: Path):
    command = [str(binary), "--host", "127.0.0.1", "--port", "0", "--hardfork", "osaka",
               "--chain-id", "31337", "--timestamp", "1700000000", "--gas-limit", str(max(30000000, runner.args.gas))]
    budget = runner.remaining(runner.args.startup_timeout)
    with tempfile.TemporaryFile() as log:
        process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.DEVNULL, stdout=log,
                                   stderr=log, start_new_session=True)
        start = time.monotonic()
        try:
            while True:
                runner.guard()
                contents = os.pread(log.fileno(), runner.args.output_limit + 1, 0)
                if len(contents) > runner.args.output_limit:
                    raise Finding("inconclusive-resource", "anvil-startup", "output limit")
                matched = re.search(rb"Listening on (127\.0\.0\.1:\d+)", contents)
                if matched:
                    rpc = Rpc("http://" + matched[1].decode(), runner)
                    runner.report["evmConfiguration"] = {
                        "command": command, "url": rpc.url, "hardfork": "osaka", "chainId": "31337",
                        "timestamp": 1700000000, "gas": runner.args.gas,
                        "clientVersion": rpc.call("web3_clientVersion", [])}
                    yield rpc
                    break
                if process.poll() is not None:
                    raise Finding("adapter-error", "anvil-startup", contents.decode(errors="replace"))
                if time.monotonic() - start >= budget:
                    raise Finding("inconclusive-resource", "anvil-startup", "startup timeout")
                time.sleep(0.05)
        finally:
            stop_process(process)
            runner.report["anvilLog"] = os.pread(log.fileno(), runner.args.output_limit, 0).decode(errors="replace")


def evm_failure(error: RpcError) -> dict:
    message = str(error.error.get("message", "")) if isinstance(error.error, dict) else str(error.error)
    if GAS_RESOURCE.search(message):
        return {"stage": "execution", "status": "out-of-gas", "detail": message}
    if RESOURCE.search(message):
        return {"stage": "execution", "status": "resource-limit", "detail": message}
    data = error.error.get("data") if isinstance(error.error, dict) else None
    if "revert" in message.lower() and isinstance(data, str):
        return {"stage": "execution", "status": "reverted", "output": "0x" + hex_bytes(data, "RPC revert data").hex()}
    return {"stage": "execution", "status": "evm-exceptional", "detail": message, "rpcError": error.error}


def deployment_failure(error: RpcError) -> Finding:
    failure = evm_failure(error)
    if failure["status"] in {"out-of-gas", "resource-limit"}:
        category = "inconclusive-resource"
    elif isinstance(error.error, dict) and error.error.get("code") in {-32700, -32600, -32601, -32602}:
        category = "adapter-error"
    else:
        category = "execution-error"
    return Finding(category, "evm-deployment", str(error))


def image_bytes(images: dict, path: list[str]) -> bytes:
    if images.get("schema") != "solcore-rs.code-images.v1" or images.get("upstreamCommit") != UPSTREAM_COMMIT:
        raise ValueError("code image schema/revision differs from pinned reference")
    found = [item for item in images.get("images", []) if item.get("path") == path]
    if len(found) != 1:
        raise ValueError(f"expected one exact code image: {path}")
    return hex_bytes(found[0].get("bytes"), "code image")


def validate_export(hull_path: Path, image_path: Path, source: Path, limit: int) -> dict:
    hull = read_json(hull_path, limit)
    images = read_json(image_path, limit)
    hp = read_json(hull_path.with_suffix(".json.provenance.json"), limit)
    ip = read_json(image_path.with_suffix(".json.provenance.json"), limit)
    if hull.get("schema") != "solcore-rs.hull.v1" or hull.get("upstreamCommit") != UPSTREAM_COMMIT:
        raise ValueError("Hull schema/revision differs from pinned reference")
    if hp.get("outputSha256") != file_digest(hull_path) or ip.get("outputSha256") != file_digest(image_path):
        raise ValueError("export artifact hash mismatch")
    if ip.get("hullProvenance") != hp or ip.get("sources") != hp.get("sources"):
        raise ValueError("Hull/image provenance differs")
    if ip.get("backendRevision") != BACKEND_COMMIT or ip.get("optimization") != "O0":
        raise ValueError("backend revision/optimization differs")
    if hp.get("sources", {}).get(source.as_uri()) != file_digest(source):
        raise ValueError("source hash differs from exported artifact")
    return {"hull": hp, "images": ip}


def checked_process(runner: Runner, stage: str, command: list[str], timeout=None) -> dict:
    result = runner.process(stage, command, timeout)
    if result["returncode"]:
        detail = result["stderr"] + result["stdout"]
        if RESOURCE.search(detail):
            category = "inconclusive-resource"
        elif result["returncode"] < 0 or re.search(r"panicked at|internal compiler error|backtrace:", detail, re.I):
            category = "compiler-crash" if stage.startswith("rust-") else "adapter-error"
        elif stage == "direct-core-replay":
            category = "unsupported-scope" if "unsupported" in detail.lower() else "adapter-error"
        elif (stage == "rust-checked-source" and detail.startswith("export-rust-hull:")) or any(
                text in detail for text in ("receipt is stale", "receipt;", "rebuild with", "unexpected code image schema", "source files changed")):
            category = "adapter-error"
        else:
            category = "source-rejected" if stage == "rust-checked-source" else "compilation-rejected"
        raise Finding(category, stage, detail)
    return result


def execute(args, report: dict) -> None:
    runner = Runner(args, report)
    original = args.case
    if args.replay:
        previous = read_json(args.replay / "report.json", args.artifact_limit)
        verify_archive(args.replay, previous)
        original = args.replay / "case.json"
    case = read_json(original)
    validate_case(case)
    report["scope"] = {
        CASE_SCHEMA: "closed G0 Word/Bool, gas-independent, Sonatina O0, pure run() ABI Word",
        INPUT_CASE_SCHEMA: "runtime Word input, pure scalar function, Sonatina O0, run(uint256) ABI Word",
        FUNCTION_CASE_SCHEMA: "runtime Word input, acyclic named Word functions, Sonatina O0, run(uint256) ABI Word",
        MUTATION_CASE_SCHEMA: "runtime Word input, local Word mutation and acyclic named functions, Sonatina O0, run(uint256) ABI Word",
        AGGREGATE_CASE_SCHEMA: "runtime Word input, internal Word pairs/sums, matches, private cells and acyclic named functions, Sonatina O0, run(uint256) ABI Word"
    }[case["schema"]]
    case_path, source = args.output / "case.json", args.output / "case.sol"
    case_path.write_bytes(json_bytes(case))
    source.write_text(case["source"])
    report.update(caseSha256=file_digest(case_path), sourceSha256=file_digest(source),
                  programSha256=digest(json_bytes(case["program"])), provenance=case["provenance"],
                  replayOf=str(args.replay.resolve()) if args.replay else None)
    report["tools"] = {
        "caseTool": runner.identity(args.case_tool), "coreRunner": runner.identity(args.core_runner),
        "anvil": runner.identity(args.anvil, version=True),
        "python": {"path": sys.executable, "version": sys.version},
        "runnerSha256": file_digest(Path(__file__)),
        "leanToolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "exporters": {name: file_digest(ROOT / "scripts" / name) for name in
                      ("export-rust-hull.py", "export-rust-code-image.py", "rust-hull-export.rs", "rust-code-image-export.rs")}}
    revision = runner.process("repository-revision", ["git", "rev-parse", "HEAD"], 10)
    dirty = runner.process("repository-diff", ["git", "diff", "--binary", "HEAD"], 10)
    if revision["returncode"] or dirty["returncode"]:
        raise ValueError("cannot identify repository revision")
    report["repository"] = {"revision": revision["stdout"].strip(), "trackedDiffSha256": digest(dirty["stdout"].encode())}
    if args.replay:
        # Tool drift is an explicit finding, never silently a reproducible replay.
        for key in ("runnerSha256", "exporters", "leanToolchain"):
            if report["tools"][key] != previous.get("tools", {}).get(key):
                raise Finding("adapter-error", "replay", f"{key} changed since saved run")
        for key in ("caseTool", "coreRunner", "anvil"):
            if report["tools"][key]["sha256"] != previous.get("tools", {}).get(key, {}).get("sha256"):
                raise Finding("adapter-error", "replay", f"{key} binary changed since saved run")
    refreshed = checked_process(runner, "direct-core-replay",
        [str(args.case_tool), "replay", str(case_path), str(args.direct_fuel)])
    fresh = json.loads(refreshed["stdout"])
    validate_case(fresh)
    for key in ("program", "source", "provenance", "contract", "input"):
        if fresh.get(key) != case.get(key):
            raise ValueError(f"case replay changed {key}")
    (args.output / "replayed-case.json").write_bytes(json_bytes(fresh))
    report["rawObservations"]["directCore"] = fresh.get("directCore")
    report["observations"]["directCore"] = normalize_observation(fresh.get("directCore"), direct=True)
    if report["observations"]["directCore"]["status"] not in COMPLETED:
        report["comparison"] = {"category": "inconclusive-resource" if report["observations"]["directCore"]["status"] == "out-of-fuel" else "execution-error", "pairs": {}}
        return
    hull_path, image_path = args.output / "hull.json", args.output / "images.json"
    common = [str(source), "--root", str(args.output), "--upstream", str(args.upstream), "--target-dir", str(args.target_dir)]
    checked_process(runner, "rust-checked-source", [sys.executable, str(ROOT / "scripts/export-rust-hull.py"), *common, "--output", str(hull_path)])
    checked_process(runner, "rust-code-images", [sys.executable, str(ROOT / "scripts/export-rust-code-image.py"), *common,
        "--output", str(image_path), "--hull-output", str(hull_path), "--timeout", str(args.timeout)], args.timeout * 3)
    report["exportProvenance"] = validate_export(hull_path, image_path, source, args.artifact_limit)
    if args.replay and "exportProvenance" in previous:
        old = previous["exportProvenance"]
        new = report["exportProvenance"]
        if old["images"].get("toolBuild") != new["images"].get("toolBuild") or old["hull"].get("patches") != new["hull"].get("patches") or old["hull"].get("binarySha256") != new["hull"].get("binarySha256"):
            raise Finding("adapter-error", "replay", "Rust compiler/exporter build changed")
        # The saved .sol path changes in a copied run; the pinned library hashes
        # must still agree. The emitted source is independently rechecked above.
        old_sources = {key: value for key, value in old["hull"].get("sources", {}).items() if not key.endswith("/case.sol")}
        new_sources = {key: value for key, value in new["hull"].get("sources", {}).items() if not key.endswith("/case.sol")}
        if old_sources != new_sources:
            raise Finding("adapter-error", "replay", "imported source/library hashes changed")
    images = read_json(image_path, args.artifact_limit)
    init = image_bytes(images, case["contract"]["deployPath"])
    runtime = image_bytes(images, case["contract"]["runtimePath"])
    with anvil(runner, args.anvil) as rpc:
        accounts = rpc.call("eth_accounts", [])
        if not accounts or not re.fullmatch(r"0x[0-9a-fA-F]{40}", accounts[0]):
            raise ValueError("Anvil supplied no valid local sender")
        sender = accounts[0]
        gas = hex(args.gas)
        transaction = {"from": sender, "data": "0x" + init.hex(), "value": "0x0", "gas": gas}
        try:
            tx_hash = rpc.call("eth_sendTransaction", [transaction])
        except RpcError as error:
            report["evmDeployment"] = {"rpcError": error.error}
            raise deployment_failure(error) from error
        deadline = time.monotonic() + runner.remaining(args.startup_timeout)
        while True:
            deployed = rpc.call("eth_getTransactionReceipt", [tx_hash])
            if deployed is not None:
                break
            if time.monotonic() >= deadline:
                raise Finding("inconclusive-resource", "evm-deployment", "receipt timeout")
            time.sleep(0.05)
        report["evmDeployment"] = deployed
        if deployed.get("status") != "0x1":
            trace = rpc.call("debug_traceTransaction", [tx_hash, {"disableStorage": True, "disableStack": True, "enableMemory": False}])
            reason = str(trace.get("error", "deployment failed"))
            raise Finding("inconclusive-resource" if RESOURCE.search(reason) else "execution-error", "evm-deployment", reason)
        address = deployed.get("contractAddress")
        if not isinstance(address, str) or not re.fullmatch(r"0x[0-9a-fA-F]{40}", address):
            raise ValueError("invalid deployed contract address")
        installed = hex_bytes(rpc.call("eth_getCode", [address, "latest"]), "installed runtime")
        if installed != runtime:
            raise Finding("adapter-error", "evm-deployment", "deployed bytes differ from exported runtime image")
        call = {"from": sender, "to": address, "data": case["contract"]["calldata"], "value": "0x0", "gas": gas}
        try:
            returned = rpc.call("eth_call", [call, "latest"])
            evm = {"stage": "execution", "status": "returned", "output": returned}
        except RpcError as error:
            evm = evm_failure(error)
        report["rawObservations"]["rustEvm"] = evm
        report["observations"]["rustEvm"] = normalize_observation(evm)
        report["executionContext"] = {"sender": sender, "address": address, "calldata": case["contract"]["calldata"], "value": "0", "persist": False, "gas": args.gas}
        base = {"caller": str(int(sender, 16)), "address": str(int(address, 16)), "value": "0", "availableGas": str(args.gas)}
        scenario = {"schema": "solcore-lean.contract-scenario.v1", "hull": str(hull_path), "images": str(image_path),
            "deployPath": case["contract"]["deployPath"], "runtimePath": case["contract"]["runtimePath"],
            "fuel": args.core_fuel, "constructor": {**base, "calldata": "0x"},
            "calls": [{**base, "calldata": case["contract"]["calldata"], "persist": False}]}
        scenario_path = args.output / "scenario.json"
        scenario_path.write_bytes(json_bytes(scenario))
        result = runner.process("imported-hull", [str(args.core_runner), str(scenario_path)])
        rows = core_rows(result["stdout"], result["returncode"])
        report["coreDeployment"] = rows[0]
        report["rawObservations"]["importedHull"] = rows[1]
        report["observations"]["importedHull"] = normalize_observation(rows[1])
    report["comparison"] = compare(report["observations"])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--case", type=Path)
    selection.add_argument("--replay", type=Path, help="saved run directory; recompile and execute its immutable case")
    parser.add_argument("--output", type=Path, required=True, help="new run directory; never overwritten")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--core-runner", type=Path, default=ROOT / ".lake/build/bin/rust-hull-scenario")
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    defaults = {"direct_fuel": 1000000, "core_fuel": 10000000, "gas": 10000000,
                "timeout": 300, "startup_timeout": 30, "total_timeout": 900,
                "output_limit": 2 * 1024 * 1024, "artifact_limit": 64 * 1024 * 1024}
    for key in defaults:
        parser.add_argument("--" + key.replace("_", "-"), type=float if "timeout" in key else int)
    args = parser.parse_args()
    saved_budgets = {}
    if args.replay:
        saved_budgets = read_json(args.replay / "report.json", defaults["artifact_limit"]).get("budgets", {})
    for key, default in defaults.items():
        explicit = getattr(args, key)
        value = saved_budgets.get(key, default) if explicit is None else explicit
        if isinstance(value, bool) or not isinstance(value, (int, float)) or ("timeout" not in key and not isinstance(value, int)) or not math.isfinite(value) or value <= 0 or value > 10**9:
            parser.error(f"{key} must be finite, positive and at most 1000000000")
        if args.replay and explicit is not None and value != saved_budgets.get(key):
            parser.error(f"replay must retain the saved {key}; use --case for changed budgets")
        setattr(args, key, value)
    for key in ("case", "replay", "output", "case_tool", "core_runner", "anvil", "upstream", "target_dir"):
        if getattr(args, key) is not None:
            setattr(args, key, getattr(args, key).resolve())
    args.output.mkdir(parents=True, exist_ok=False)
    report = {"schema": REPORT_SCHEMA, "processes": [], "observations": {}, "rawObservations": {},
              "budgets": {key: getattr(args, key) for key in ("direct_fuel", "core_fuel", "gas", "timeout", "startup_timeout", "total_timeout", "output_limit", "artifact_limit")},
              "scope": "closed G0 Word/Bool, gas-independent, Sonatina O0, pure run() ABI Word"}
    previous_term = signal.getsignal(signal.SIGTERM)

    def interrupted(_signal, _frame):
        # A second termination request must not interrupt owned-process cleanup.
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupted)
    try:
        execute(args, report)
    except KeyboardInterrupt:
        report["comparison"] = {"category": "inconclusive-resource", "stage": "runner", "detail": "interrupted", "pairs": {}}
    except Finding as error:
        report["comparison"] = {"category": error.category, "stage": error.stage, "detail": error.detail, "pairs": {}}
    except (ValueError, OSError, KeyError, TypeError, RpcError, subprocess.SubprocessError) as error:
        report["comparison"] = {"category": "adapter-error", "stage": "runner", "detail": str(error), "pairs": {}}
    finally:
        try:
            report["artifacts"] = {path.name: file_digest(path) for path in args.output.iterdir() if path.is_file()}
            (args.output / "report.json").write_bytes(json_bytes(report))
        finally:
            signal.signal(signal.SIGTERM, previous_term)
    category = report["comparison"]["category"]
    print(json.dumps({"category": category, "report": str(args.output / "report.json")}))
    return 0 if category == "matched" else 1


if __name__ == "__main__":
    raise SystemExit(main())
