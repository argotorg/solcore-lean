#!/usr/bin/env python3
"""Check the pinned recursive Hull representation through the actual exporter.

Requires the retained checked-Hull driver; does not build or modify Rust. The
successful case constructs, relays and matches a recursive enum at runtime.
Two checker/backend disagreements remain explicit lowering rejections.
All exports, provenance sidecars and auxiliary runners are temporary.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
import urllib.request


ROOT = Path(__file__).resolve().parent.parent
FIXTURES = ROOT / "tests/Fixtures/RustHullRecursive"
ZERO_RUNNER = r'''import Solcore.Frontend.RustHull.Decode
import Solcore.Frontend.RustHull.Lowering
open Solcore Solcore.Frontend.RustHull
def main (args : List String) : IO Unit := do
  let [file] := args | throw (IO.userError "expected one export")
  let envelope ← match decodeText (← IO.FS.readFile file) with
    | .ok envelope => pure envelope
    | .error error => throw (IO.userError (reprStr error))
  let [entry] := envelope.program.entryPoints | throw (IO.userError "expected one entry")
  let compiled ← match compile envelope.program entry with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError (reprStr error))
  let arguments ← match compiled.parameters.mapM zeroValue with
    | .ok arguments => pure arguments
    | .error error => throw (IO.userError (reprStr error))
  match Core.runStateful 1000000 (.initial (.apply compiled.expression (bundle arguments))) with
  | .done (.inRight _ (.word value)) _ =>
      unless value.val == 0 do throw (IO.userError "unexpected nonzero result")
      IO.println "zero-input recursive layout executed"
  | other => throw (IO.userError (reprStr other))
'''


def has_tag(value: object, tag: str) -> bool:
    pending = [value]
    while pending:
        current = pending.pop()
        if isinstance(current, dict):
            if current.get("tag") == tag:
                return True
            pending.extend(current.values())
        elif isinstance(current, list):
            pending.extend(current)
    return False


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--evm-reference", action="store_true",
                        help="also deploy Sonatina and solc/Yul images on local Anvil (Osaka)")
    args = parser.parse_args()

    def run(command: list[str], *, checked: bool = True) -> subprocess.CompletedProcess:
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=args.timeout)
        if checked and result.returncode:
            raise ValueError(f"command failed: {' '.join(command)}\n{result.stdout}{result.stderr}")
        return result

    def export(source: Path, output: Path) -> dict:
        run([sys.executable, str(ROOT / "scripts/export-rust-hull.py"), str(source),
             "--upstream", str(args.upstream), "--target-dir", str(args.target_dir),
             "--output", str(output)])
        envelope = json.loads(output.read_text())
        if not has_tag(envelope, "namedRef"):
            raise ValueError(f"recursive layout was removed before export: {source}")
        return envelope

    with tempfile.TemporaryDirectory(prefix="recursive-layouts-", dir=ROOT / ".upstream") as directory:
        scratch = Path(directory)
        inputs = [0, 42, 2**256 - 1]
        input_path = scratch / "inputs.json"
        input_path.write_text(json.dumps([f"0x{value:064x}" for value in inputs]))
        driver = args.target_dir / "debug/solcore-driver"
        for name in ["base", "nested", "unfold"]:
            source = FIXTURES / f"{name}.sol"
            output = scratch / f"{name}.json"
            envelope = export(source, output)
            if not has_tag(envelope, "match") or not has_tag(envelope, "inl"):
                raise ValueError(f"constructor/match was removed before export: {name}")
            sonatina = run([str(driver), str(source), "--std-root", str(args.upstream / "std"),
                            "--emit-sonatina"], checked=False)
            core = run(["lake", "env", "lean", "--run", "Tests/RustHullContractRun.lean",
                        str(output), "RecursiveDeploy/Recursive", "--batch", str(input_path)], checked=False)
            rows = [json.loads(line) for line in core.stdout.splitlines() if line.strip()]
            if name == "base":
                if sonatina.returncode:
                    raise ValueError(f"base recursive layout no longer emits: {sonatina.stderr}")
                expected = [{"stage": "execution", "status": "returned", "storage": [],
                             "output": f"0x{value:064x}"} for value in inputs]
                if core.returncode or rows != expected:
                    raise ValueError(f"runtime recursive construction/match failed: {core.stdout}{core.stderr}")
                print("base: checked recursive constructor, relay and match execute for all three inputs")
            else:
                if not sonatina.returncode or "cannot coerce Sonatina value" not in sonatina.stderr:
                    raise ValueError(f"expected pinned backend mismatch for {name}: {sonatina.stdout}{sonatina.stderr}")
                if (not core.returncode or len(rows) != 1 or rows[0].get("stage") != "lowering"
                        or rows[0].get("status") != "rejected"
                        or "type mismatch" not in rows[0].get("detail", "")):
                    raise ValueError(f"missing explicit recursive-layout rejection: {core.stdout}{core.stderr}")
                print(f"{name}: checked Hull/backend mismatch remains an explicit Core lowering rejection")

        runner = scratch / "ZeroInput.lean"
        runner.write_text(ZERO_RUNNER)
        for name in ["finite_regular", "finite_wrapped_regular"]:
            source = args.upstream / "crates/hull/tests/fixtures/layouts" / name / "main.sol"
            output = scratch / f"{name}.json"
            export(source, output)
            run(["lake", "env", "lean", "--run", str(runner), str(output)])
            print(f"{name}: actual checked export executes with its zero-initialized recursive layout")
        if args.evm_reference:
            image_path = scratch / "images.json"
            run([sys.executable, str(ROOT / "scripts/export-rust-code-image.py"), str(FIXTURES / "base.sol"),
                 "--upstream", str(args.upstream), "--target-dir", str(args.target_dir),
                 "--output", str(image_path)])
            images = json.loads(image_path.read_text())["images"]
            init = next(image["bytes"] for image in images if image["path"] == ["RecursiveDeploy"])
            runtime = next(image["bytes"] for image in images if image["path"] == ["RecursiveDeploy", "Recursive"])
            yul = run([str(driver), str(FIXTURES / "base.sol"), "--std-root", str(args.upstream / "std"),
                       "--emit-yul"]).stdout
            yul_path = scratch / "base.yul"
            yul_path.write_text(yul)
            compiled = run(["solc", "--strict-assembly", "--optimize", "--evm-version", "osaka",
                            "--bin", str(yul_path)])
            binary = re.search(r"Binary representation:\s*([0-9a-f]+)", compiled.stdout)
            if not binary:
                raise ValueError(f"missing Yul bytecode: {compiled.stdout}")
            with tempfile.TemporaryFile(mode="w+") as logs:
                child = subprocess.Popen(["anvil", "--host", "127.0.0.1", "--port", "0", "--hardfork", "osaka"],
                                         stdout=logs, stderr=logs)
                try:
                    url = None
                    for _ in range(150):
                        logs.seek(0)
                        text = logs.read()
                        listen = re.search(r"Listening on (127\.0\.0\.1:\d+)", text)
                        if listen:
                            url = "http://" + listen[1]
                            break
                        if child.poll() is not None:
                            raise ValueError(f"Anvil failed: {text}")
                        time.sleep(0.1)
                    if url is None:
                        raise ValueError("Anvil did not become ready")

                    def rpc(method: str, params: list) -> object:
                        request = urllib.request.Request(url, json.dumps({"jsonrpc": "2.0", "id": 1,
                            "method": method, "params": params}).encode(), {"Content-Type": "application/json"})
                        with urllib.request.urlopen(request, timeout=args.timeout) as response:
                            result = json.load(response)
                        if "error" in result:
                            raise ValueError(f"{method}: {result['error']}")
                        return result["result"]

                    sender = rpc("eth_accounts", [])[0]
                    for backend, creation in [("Sonatina", init), ("Yul", "0x" + binary[1])]:
                        tx = rpc("eth_sendTransaction", [{"from": sender, "data": creation, "gas": "0x1c9c380"}])
                        receipt = None
                        for _ in range(100):
                            receipt = rpc("eth_getTransactionReceipt", [tx])
                            if receipt is not None:
                                break
                            time.sleep(0.05)
                        if receipt is None or receipt["status"] != "0x1":
                            raise ValueError(f"{backend} deployment failed: {receipt}")
                        address = receipt["contractAddress"]
                        if backend == "Sonatina" and rpc("eth_getCode", [address, "latest"]) != runtime:
                            raise ValueError("Sonatina deployment did not return its exact linked runtime image")
                        for value in inputs:
                            data = f"0x{value:064x}"
                            actual = rpc("eth_call", [{"to": address, "data": data, "gas": "0x1c9c380"}, "latest"])
                            if actual != data:
                                raise ValueError(f"{backend} returned {actual}, expected {data}")
                        print(f"{backend}: deployment and all three recursive-layout calls agree with Core")
                finally:
                    child.terminate()
                    try:
                        child.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        child.kill()
                        child.wait()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"recursive-layouts: {error}", file=sys.stderr)
        raise SystemExit(1)
