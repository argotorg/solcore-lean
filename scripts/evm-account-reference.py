#!/usr/bin/env python3
"""Measure Osaka account lifecycle on Anvil using independent small Yul probes.

This does not modify or execute the pinned Rust fixture corpus. The resulting
bytes and account snapshots are runtime test vectors, not semantic proofs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
FIXTURES = ROOT / "Tests/Fixtures/EvmAccounts"
GAS = hex(10_000_000)


def word(value: int | str) -> bytes:
    return (int(value, 16) if isinstance(value, str) else value).to_bytes(32, "big")


def words(data: bytes) -> list[int]:
    assert len(data) % 32 == 0
    return [int.from_bytes(data[i:i + 32], "big") for i in range(0, len(data), 32)]


def address(value: int | str) -> str:
    return f"0x{(int(value, 16) if isinstance(value, str) else value):040x}"


def keccak(data: bytes) -> bytes:
    result = subprocess.run(["cast", "keccak", "0x" + data.hex()], check=True, capture_output=True, text=True)
    return bytes.fromhex(result.stdout.strip().removeprefix("0x"))


def create_address(sender: str, nonce: int) -> str:
    encoded = bytes() if nonce == 0 else nonce.to_bytes((nonce.bit_length() + 7) // 8, "big")
    nonce_rlp = encoded if len(encoded) == 1 and encoded[0] < 128 else bytes([128 + len(encoded)]) + encoded
    payload = b"\x94" + bytes.fromhex(sender[2:]) + nonce_rlp
    return address(int.from_bytes(keccak(bytes([192 + len(payload)]) + payload)[12:], "big"))


def create2_address(sender: str, salt: int, init: bytes) -> str:
    return address(int.from_bytes(keccak(b"\xff" + bytes.fromhex(sender[2:]) + word(salt) + keccak(init))[12:], "big"))


class RpcError(Exception):
    def __init__(self, error):
        self.error = error
        super().__init__(str(error))


class Reference:
    def __init__(self, url: str, output: Path, tools: dict, compiled: dict):
        self.url, self.output, self.compiled = url, output, compiled
        self.checks = []
        self.report = {"schema": "solcore-lean.evm-account-reference.v1", "hardfork": "osaka",
            "tools": tools, "fixtures": {name: {"sourceSha256": hashlib.sha256((FIXTURES / (name + '.yul')).read_bytes()).hexdigest(),
                "init": data.hex()} for name, data in compiled.items()}, "checks": self.checks}
        self.sender, self.beneficiary = self.rpc("eth_accounts", [])[:2]
        self.probe = self.deploy(compiled["Probe"], 1000)
        self.target = self.deploy(compiled["Target"], 1111)
        self.runtime = self.code(self.target)
        self.empty_hash = int.from_bytes(keccak(b""), "big")
        self.target_hash = int.from_bytes(keccak(self.runtime), "big")
        self.base = self.rpc("evm_snapshot", [])
        self.report["initial"] = {"sender": self.sender, "beneficiary": self.beneficiary,
            "probe": self.probe, "target": self.target, "targetRuntime": self.runtime.hex()}

    def rpc(self, method, params):
        request = urllib.request.Request(self.url, json.dumps({"jsonrpc": "2.0", "id": 1,
            "method": method, "params": params}).encode(), {"Content-Type": "application/json"})
        with urllib.request.urlopen(request, timeout=30) as response:
            result = json.load(response)
        if "error" in result:
            raise RpcError(result["error"])
        return result["result"]

    def check(self, name, actual, expected):
        def serial(value):
            if isinstance(value, bytes):
                return "0x" + value.hex()
            return value
        row = {"name": name, "actual": serial(actual), "expected": serial(expected), "passed": actual == expected}
        self.checks.append(row)
        self.report["passed"] = all(r["passed"] for r in self.checks)
        self.output.write_text(json.dumps(self.report, indent=2) + "\n")
        print(f"{'PASS' if row['passed'] else 'FAIL'} {name}", flush=True)

    def reset(self):
        assert self.rpc("evm_revert", [self.base])
        self.base = self.rpc("evm_snapshot", [])

    def tx(self, data, to=None, value=0):
        tx = {"from": self.sender, "data": "0x" + data.hex(), "value": hex(value), "gas": GAS}
        if to is not None:
            tx["to"] = to
        return tx

    def send(self, tx):
        tx_hash = self.rpc("eth_sendTransaction", [tx])
        for _ in range(100):
            receipt = self.rpc("eth_getTransactionReceipt", [tx_hash])
            if receipt is not None:
                return receipt
            time.sleep(0.05)
        raise RuntimeError(f"transaction receipt timed out: {tx_hash}")

    def deploy(self, init, value=0):
        result = self.send(self.tx(init, value=value))
        assert result["status"] == "0x1", result
        return result["contractAddress"]

    def call(self, data, to=None, value=0):
        return bytes.fromhex(self.rpc("eth_call", [self.tx(data, to or self.probe, value), "latest"])[2:])

    def invoke(self, data, to=None, value=0):
        output = self.call(data, to, value)
        receipt = self.send(self.tx(data, to or self.probe, value))
        assert receipt["status"] == "0x1", receipt
        return output

    def code(self, addr):
        return bytes.fromhex(self.rpc("eth_getCode", [addr, "latest"])[2:])

    def balance(self, addr):
        return int(self.rpc("eth_getBalance", [addr, "latest"]), 16)

    def nonce(self, addr):
        return int(self.rpc("eth_getTransactionCount", [addr, "latest"]), 16)

    def storage(self, addr, slot):
        return int(self.rpc("eth_getStorageAt", [addr, hex(slot), "latest"]), 16)

    def wrapped(self, mode, target, value=0, payload=b""):
        return word(mode) + word(target) + word(value) + payload

    def creation(self, mode=6, value=0, salt=0, init=None):
        return word(mode) + word(value) + word(salt) + (init if init is not None else self.compiled["Target"])

    def run(self):
        target, probe = self.target, self.probe
        self.check("constructor.self.extcodesize", self.storage(target, 8), 0)
        self.check("constructor.self.extcodehash", self.storage(target, 9), self.empty_hash)

        self.reset()
        data = self.wrapped(1, target, payload=word(1) + word(77))
        result = words(self.invoke(data, value=13))
        self.check("delegate.context.bytes", result, [1, 192, int(probe, 16), int(self.sender, 16), 13, 77, 1013, len(self.runtime), 77, 1013])
        self.check("delegate.storage.owner", [self.storage(probe, 7), self.storage(target, 7)], [77, 99])
        self.check("delegate.balance.owner", [self.balance(probe), self.balance(target)], [1013, 1111])

        self.reset()
        result = words(self.invoke(self.wrapped(2, target, 17, word(1) + word(88)), value=5))
        self.check("callcode.context.bytes", result, [1, 192, int(probe, 16), int(probe, 16), 17, 88, 1005, len(self.runtime), 88, 1005])
        self.check("callcode.no.transfer", [self.balance(probe), self.balance(target)], [1005, 1111])
        self.check("callcode.storage.owner", [self.storage(probe, 7), self.storage(target, 7)], [88, 99])
        result = words(self.invoke(self.wrapped(2, target, 1006, word(1) + word(55))))
        self.check("callcode.insufficient.balance", result, [0, 0, 88, 1005])

        self.reset()
        result = self.invoke(self.wrapped(1, target, payload=word(2) + word(123)))
        self.check("delegate.revert.bytes.and.rollback", result, word(0) + word(4) + bytes.fromhex("deadbeef") + word(10) + word(1000))
        self.check("delegate.revert.storage", self.storage(probe, 7), 10)
        nested = self.wrapped(2, target, 17, word(0))
        outer = words(self.invoke(self.wrapped(4, probe, payload=nested)))
        self.check("static.callcode.nonzero.value.allowed", outer[:7], [1, 320, 1, 192, int(probe, 16), int(probe, 16), 17])
        self.check("static.state.write.rejected", words(self.invoke(self.wrapped(4, target, payload=word(1) + word(42))))[:2], [0, 0])

        self.reset()
        absent, funded, nonce_only, empty = map(address, [0x123456, 0x234567, 0x345678, 0x456789])
        self.rpc("anvil_setBalance", [funded, "0x1"])
        self.rpc("anvil_setNonce", [nonce_only, "0x1"])
        self.rpc("anvil_setBalance", [empty, "0x0"])
        for name, account, size, hash_value, balance in [
            ("nonexistent", absent, 0, 0, 0), ("funded.no.code", funded, 0, self.empty_hash, 1),
            ("nonce.no.code", nonce_only, 0, self.empty_hash, 0), ("empty", empty, 0, 0, 0),
            ("contract", target, len(self.runtime), self.target_hash, 1111)]:
            out = self.call(word(5) + word(account) + word(0))
            self.check("inspect." + name, out, word(size) + word(hash_value) + (self.runtime[:64] if size else bytes(64)) + word(balance))
        self.check("inspect.address.low160", self.call(word(5) + word(int(target, 16) + 2**160) + word(0)),
                   self.call(word(5) + word(target) + word(0)))
        self.check("extcodecopy.right.zero.padding", self.call(word(5) + word(target) + word(len(self.runtime) - 2))[64:128], self.runtime[-2:] + bytes(62))
        self.check("extcodecopy.huge.offset.zero", self.call(word(5) + word(target) + word(2**256 - 1))[64:128], bytes(64))

        self.reset()
        child = create_address(probe, 1)
        result = words(self.invoke(self.creation(value=17)))
        self.check("create.address.return.data", result, [int(child, 16), 0, len(self.runtime), self.target_hash])
        self.check("create.installed.runtime", self.code(child), self.runtime)
        self.check("create.account.state", [self.nonce(probe), self.nonce(child), self.balance(probe), self.balance(child), self.storage(child, 7)], [2, 1, 983, 17, 99])
        child2 = create_address(probe, 2)
        self.check("create.next.nonce.address", words(self.invoke(self.creation()))[0], int(child2, 16))

        self.reset()
        prefunded = create_address(probe, 1)
        self.rpc("anvil_setBalance", [prefunded, "0x9"])
        self.check("create.prefunded.permitted", words(self.invoke(self.creation(value=17)))[0], int(prefunded, 16))
        self.check("create.prefunded.balance", self.balance(prefunded), 26)

        for name, init, returned in [("revert", bytes.fromhex("63deadbeef5f526004601cfd"), bytes.fromhex("deadbeef")), ("invalid", b"\xfe", b"")]:
            self.reset()
            result = self.invoke(self.creation(value=17, init=init))
            self.check("create." + name + ".returndata", result, word(0) + word(len(returned)) + word(0) + word(0) + returned)
            self.check("create." + name + ".rollback", [self.nonce(probe), self.nonce(child), self.balance(probe), self.balance(child)], [2, 0, 1000, 0])
        self.reset()
        self.check("create.insufficient.balance.result", words(self.invoke(self.creation(value=1001))), [0, 0, 0, 0])
        self.check("create.insufficient.balance.nonce", self.nonce(probe), 1)

        self.reset()
        salt = 12345
        c2 = create2_address(probe, salt, self.compiled["Target"])
        self.check("create2.address.hash", words(self.invoke(self.creation(7, 17, salt)))[0], int(c2, 16))
        self.check("create2.collision.result", words(self.invoke(self.creation(7, 0, salt))), [0, 0, 0, 0])
        self.check("create2.collision.creator.nonce", self.nonce(probe), 3)
        self.check("create2.collision.original.unchanged", [self.nonce(c2), self.balance(c2), self.storage(c2, 7)], [1, 17, 99])
        self.reset()
        self.rpc("anvil_setNonce", [c2, "0x1"])
        self.check("create2.nonce.only.collision", words(self.invoke(self.creation(7, 0, salt))), [0, 0, 0, 0])
        self.reset()
        self.rpc("anvil_setCode", [c2, "0x00"])
        self.check("create2.code.only.collision", words(self.invoke(self.creation(7, 0, salt))), [0, 0, 0, 0])

        self.reset()
        reverted = self.send(self.tx(self.creation(8, 17), probe))
        self.check("parent.revert.receipt", reverted["status"], "0x0")
        self.check("parent.revert.creation.state", [self.nonce(probe), self.nonce(child), self.balance(probe), self.balance(child)], [1, 0, 1000, 0])
        self.check("parent.revert.creation.code", self.code(child), b"")
        for mode in [6, 7]:
            self.check(f"static.create{mode}.rejected", words(self.invoke(self.wrapped(4, probe, payload=self.creation(mode))))[:2], [0, 0])
        self.check("static.create.creator.nonce", self.nonce(probe), 1)

        for self_beneficiary in [False, True]:
            self.reset()
            recipient = target if self_beneficiary else self.beneficiary
            before = self.balance(recipient)
            self.invoke(word(3) + word(recipient), to=target)
            prefix = "selfdestruct.existing.self" if self_beneficiary else "selfdestruct.existing.other"
            self.check(prefix + ".balance", self.balance(target), 1111 if self_beneficiary else 0)
            self.check(prefix + ".recipient", self.balance(recipient), before if self_beneficiary else before + 1111)
            self.check(prefix + ".code", self.code(target), self.runtime)
            self.check(prefix + ".storage.nonce", [self.storage(target, 7), self.nonce(target)], [99, 1])

        self.reset()
        self.check("static.selfdestruct.rejected", words(self.invoke(self.wrapped(4, target, payload=word(3) + word(self.beneficiary))))[:2], [0, 0])
        self.check("static.selfdestruct.balance", self.balance(target), 1111)
        before = self.balance(self.beneficiary)
        receipt = self.send(self.tx(self.wrapped(12, target, payload=word(3) + word(self.beneficiary)), probe))
        self.check("parent.revert.selfdestruct.receipt", receipt["status"], "0x0")
        self.check("parent.revert.selfdestruct.balances", [self.balance(target), self.balance(self.beneficiary)], [1111, before])

        for self_beneficiary in [False, True]:
            self.reset()
            recipient = 0 if self_beneficiary else self.beneficiary
            before = self.balance(self.beneficiary)
            data = word(9) + word(17) + word(salt) + word(recipient) + self.compiled["Target"]
            out = words(self.invoke(data))
            prefix = "selfdestruct.created.self" if self_beneficiary else "selfdestruct.created.other"
            self.check(prefix + ".same.tx.visibility.and.collision", out, [int(c2, 16), 1, len(self.runtime), self.target_hash, 0, 0])
            self.check(prefix + ".final.code", self.code(c2), b"")
            self.check(prefix + ".final.state", [self.nonce(c2), self.storage(c2, 7), self.balance(c2)], [0, 0, 0])
            self.check(prefix + ".recipient.balance", self.balance(self.beneficiary), before + (0 if self_beneficiary else 17))
            self.check(prefix + ".parent.balance", self.balance(probe), 983)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / ".upstream/evm-account-reference.json")
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    tools = {}
    for name in ["anvil", "cast", "solc"]:
        path = shutil.which(name)
        if not path:
            raise RuntimeError(f"missing {name}")
        tools[name] = {"path": path, "version": subprocess.check_output([path, "--version"], text=True).strip()}
    compiled = {}
    for name in ["Probe", "Target"]:
        result = subprocess.run([tools["solc"]["path"], "--strict-assembly", "--optimize", "--evm-version", "osaka", "--bin", str(FIXTURES / (name + ".yul"))], text=True, capture_output=True, check=True)
        match = re.search(r"Binary representation:\s*([0-9a-f]+)", result.stdout)
        assert match, result.stdout
        compiled[name] = bytes.fromhex(match[1])
    with tempfile.TemporaryFile(mode="w+") as logs:
        child = subprocess.Popen([tools["anvil"]["path"], "--host", "127.0.0.1", "--port", "0", "--hardfork", "osaka"], stdout=logs, stderr=logs)
        try:
            url = None
            for _ in range(150):
                logs.seek(0)
                output = logs.read()
                match = re.search(r"Listening on (127\.0\.0\.1:\d+)", output)
                if match:
                    url = "http://" + match[1]
                    break
                if child.poll() is not None:
                    raise RuntimeError("Anvil failed: " + output)
                time.sleep(0.1)
            if url is None:
                raise RuntimeError("Anvil did not become ready")
            reference = Reference(url, args.output, tools, compiled)
            reference.run()
            print(f"{sum(c['passed'] for c in reference.checks)}/{len(reference.checks)} checks passed")
            return 0 if reference.report["passed"] else 1
        finally:
            child.terminate()
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait()


if __name__ == "__main__":
    raise SystemExit(main())
