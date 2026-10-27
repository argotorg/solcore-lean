#!/usr/bin/env python3
"""Check that Anvil's prestate diffs enumerate committed storage exactly.

The stateful comparisons enumerate EVM storage from `debug_traceTransaction`
with `prestateTracer` in diff mode. This check deploys hand-assembled probe
contracts on an owned local Anvil, using the adapters' flags, whose possible
write set is known from their calldata. For every mined transaction the
diff must report exactly the slots whose committed value changed between the
parent and receipt blocks, with the same values as `eth_getStorageAt`.
Writes that leave a value unchanged inside one transaction may be absent;
the opcode trace confirms that they ran. Finally `anvil_dumpState` must hold
the storage the reported changes imply. Rerun it whenever Anvil changes.
"""
from __future__ import annotations

import argparse
import gzip
import json
from pathlib import Path
import re
import shutil
import subprocess
import threading
import time
import urllib.request

OPS = {"STOP": 0x00, "ADD": 0x01, "GT": 0x11, "ISZERO": 0x15, "AND": 0x16, "CALLDATALOAD": 0x35,
       "CALLDATASIZE": 0x36, "CALLDATACOPY": 0x37, "CODECOPY": 0x39, "POP": 0x50, "SSTORE": 0x55,
       "JUMP": 0x56, "JUMPI": 0x57, "GAS": 0x5a, "JUMPDEST": 0x5b, "DUP1": 0x80, "DUP2": 0x81,
       "CALL": 0xf1, "RETURN": 0xf3, "REVERT": 0xfd}
TOP, HIGH = 2**256 - 1, 2**255


def push(value, width=32):
    return ("push", width, value)


def assemble(program) -> bytes:
    """Opcode names, ("push", width, value), ("label", name) and ("ref", name)."""
    size = lambda item: 1 if isinstance(item, str) or item[0] == "label" else 1 + item[1] if item[0] == "push" else 3
    labels, offset = {}, 0
    for item in program:
        if isinstance(item, tuple) and item[0] == "label":
            labels[item[1]] = offset
        offset += size(item)
    code = bytearray()
    for item in program:
        if isinstance(item, str):
            code.append(OPS[item])
        elif item[0] == "push":
            code += bytes([0x5f + item[1]]) + item[2].to_bytes(item[1], "big")
        elif item[0] == "label":
            code.append(OPS["JUMPDEST"])
        else:
            code += b"\x61" + labels[item[1]].to_bytes(2, "big")
    return bytes(code)


# Calldata: mode (bit 0 reverts at the end, bit 1 calls the target first), the
# call target, the inner calldata length, the inner calldata padded to whole
# Words, then (slot, value) pairs written in order before the call.
RUNTIME = assemble([
    push(0x40, 1), "CALLDATALOAD", push(0x1f, 1), "ADD", push((1 << 256) - 32), "AND", push(0x60, 1), "ADD",
    ("label", "loop"), "DUP1", "CALLDATASIZE", "GT", "ISZERO", ("ref", "after"), "JUMPI",
    "DUP1", push(0x20, 1), "ADD", "CALLDATALOAD", "DUP2", "CALLDATALOAD", "SSTORE",
    push(0x40, 1), "ADD", ("ref", "loop"), "JUMP",
    ("label", "after"), "POP",
    push(0, 1), "CALLDATALOAD", push(2, 1), "AND", "ISZERO", ("ref", "nocall"), "JUMPI",
    push(0, 1), push(0, 1), push(0x40, 1), "CALLDATALOAD", "DUP1", push(0x60, 1), push(0, 1), "CALLDATACOPY",
    push(0, 1), push(0, 1), push(0x20, 1), "CALLDATALOAD", "GAS", "CALL", "POP",
    ("label", "nocall"), push(0, 1), "CALLDATALOAD", push(1, 1), "AND", ("ref", "revert"), "JUMPI", "STOP",
    ("label", "revert"), push(0, 1), push(0, 1), "REVERT"])


def init_code(writes) -> bytes:
    """A constructor that performs `writes` in order, then installs RUNTIME."""
    prefix = [item for slot, value in writes for item in (push(value), push(slot), "SSTORE")]
    tail = lambda offset: [push(len(RUNTIME), 2), "DUP1", push(offset, 2), push(0, 1), "CODECOPY", push(0, 1), "RETURN"]
    return assemble(prefix + tail(len(assemble(prefix + tail(0))))) + RUNTIME


def calldata(mode=0, target=0, inner=b"", pairs=()) -> bytes:
    head = b"".join(value.to_bytes(32, "big") for value in (mode, target, len(inner)))
    return head + inner + bytes(-len(inner) % 32) + b"".join(s.to_bytes(32, "big") + v.to_bytes(32, "big") for s, v in pairs)


class Rpc:
    def __init__(self, url):
        self.url, self.counter = url, 0
        self.opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))

    def call(self, method, params):
        self.counter += 1
        body = json.dumps({"jsonrpc": "2.0", "id": self.counter, "method": method, "params": params}).encode()
        reply = json.loads(self.opener.open(urllib.request.Request(self.url, body, {"Content-Type": "application/json"}), timeout=60).read())
        if "error" in reply:
            raise RuntimeError(f"{method}: {reply['error']}")
        return reply["result"]


class Probe:
    def __init__(self, rpc):
        self.rpc, self.failures, self.checks, self.expected = rpc, [], [], {}
        self.sender = rpc.call("eth_accounts", [])[0]

    def mine(self, data, to=None):
        request = {"from": self.sender, "data": "0x" + data.hex(), "gas": hex(5_000_000)}
        if to:
            request["to"] = to
        tx = self.rpc.call("eth_sendTransaction", [request])
        for _ in range(500):
            receipt = self.rpc.call("eth_getTransactionReceipt", [tx])
            if receipt:
                return tx, receipt
            time.sleep(0.02)
        raise RuntimeError("no receipt")

    def storage(self, address, slot, block):
        return int(self.rpc.call("eth_getStorageAt", [address, hex(slot), hex(block)]), 16)

    def check(self, label, tx, receipt, candidates):
        """`candidates` maps each contract to every slot its calldata could write."""
        block = int(receipt["blockNumber"], 16)
        diff = self.rpc.call("debug_traceTransaction", [tx, {"tracer": "prestateTracer", "tracerConfig": {"diffMode": True}}])
        reported = {}
        for side in ("pre", "post"):
            for account, state in diff[side].items():
                for key, value in state.get("storage", {}).items():
                    reported.setdefault(account.lower(), {}).setdefault(int(key, 16), {})[side] = int(value, 16)
        trace = self.rpc.call("debug_traceTransaction", [tx, {"disableStorage": True, "disableStack": False, "enableMemory": False}])
        written = [int(step["stack"][-1], 16) for step in trace["structLogs"] if step["op"] == "SSTORE"]
        record = {"label": label, "status": receipt["status"], "sstores": len(written), "accounts": {}}
        for address, slots in candidates.items():
            address = address.lower()
            before = {slot: self.storage(address, slot, block - 1) for slot in slots}
            after = {slot: self.storage(address, slot, block) for slot in slots}
            changed = {slot for slot in slots if before[slot] != after[slot]}
            keys = set(reported.get(address, {}))
            for slot in changed:
                if after[slot]:
                    self.expected.setdefault(address, {})[slot] = after[slot]
                else:
                    self.expected.setdefault(address, {}).pop(slot, None)
            record["accounts"][address] = {"changed": sorted(map(str, changed)),
                                           "unchangedWrites": sorted({str(slot) for slot in written if slot in slots and slot not in changed})}
            if keys != changed:
                self.failures.append(f"{label}: {address} diff reports {sorted(keys)}, committed changes {sorted(changed)}")
            if any(entry.get("post", 0) != after[slot] or entry.get("pre", 0) != before[slot]
                   for slot, entry in reported.get(address, {}).items() if slot in slots):
                self.failures.append(f"{label}: {address} diff values disagree with eth_getStorageAt")
        foreign = set(reported) - {address.lower() for address in candidates}
        if foreign:
            self.failures.append(f"{label}: storage changes outside the probe contracts: {sorted(foreign)}")
        self.checks.append(record)


def run(rpc) -> dict:
    probe = Probe(rpc)
    tx, receipt = probe.mine(init_code([(7, 1), (8, 1), (8, 0), (9, 5), (9, 5), (TOP, 3)]))
    parent = receipt["contractAddress"]
    probe.check("constructor-writes", tx, receipt, {parent: [7, 8, 9, TOP, 0, 1]})
    tx, receipt = probe.mine(init_code([]))
    child = receipt["contractAddress"]
    probe.check("empty-constructor", tx, receipt, {child: [0, 1, 7]})
    steps = (
        ("fresh-changed-cleared", calldata(pairs=[(0, 11), (1, 12), (HIGH, 13), (7, 2), (9, 0), (21, 3), (22, 6)]),
         {parent: [0, 1, HIGH, 7, 9, 21, 22, 8, TOP]}),
        ("restored-within-transaction", calldata(pairs=[(20, 5), (20, 0), (21, 4), (21, 3), (22, 6), (30, 9)]),
         {parent: [20, 21, 22, 30]}),
        ("restored-by-later-transaction", calldata(pairs=[(30, 0), (31, 0)]), {parent: [30, 31]}),
        ("same-value-write", calldata(pairs=[(30, 0)]), {parent: [30]}),
        ("reverted", calldata(mode=1, pairs=[(0, 0), (40, 1), (TOP, 0)]), {parent: [0, 40, TOP]}),
        ("child-returns", calldata(mode=2, target=int(child, 16), inner=calldata(pairs=[(50, 1), (51, 2), (0, 0)]), pairs=[(60, 1)]),
         {parent: [60], child: [0, 50, 51]}),
        ("child-reverts", calldata(mode=2, target=int(child, 16), inner=calldata(mode=1, pairs=[(50, 0), (52, 3)]), pairs=[(61, 1)]),
         {parent: [61], child: [50, 52]}),
        ("parent-reverts", calldata(mode=3, target=int(child, 16), inner=calldata(pairs=[(51, 0), (53, 4)]), pairs=[(62, 1)]),
         {parent: [62], child: [51, 53]}),
        ("child-restores", calldata(mode=2, target=int(child, 16), inner=calldata(pairs=[(50, 9), (50, 1)])), {parent: [], child: [50]}))
    for label, data, candidates in steps:
        tx, receipt = probe.mine(data, parent)
        probe.check(label, tx, receipt, candidates)
    raw = bytes.fromhex(rpc.call("anvil_dumpState", [])[2:])
    accounts = json.loads(gzip.decompress(raw) if raw[:2] == b"\x1f\x8b" else raw)["accounts"]
    for address in (parent.lower(), child.lower()):
        dumped = {int(key, 16): int(value, 16) for key, value in accounts[address].get("storage", {}).items() if int(value, 16)}
        if dumped != probe.expected.get(address, {}):
            probe.failures.append(f"state dump of {address} differs from the reported committed changes")
    return {"schema": "solcore-lean.evm-storage-diff-check.v1", "client": rpc.call("web3_clientVersion", []),
            "status": "failed" if probe.failures else "passed", "checks": probe.checks, "failures": probe.failures}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--timeout", type=float, default=60)
    args = parser.parse_args()
    command = [str(args.anvil), "--host", "127.0.0.1", "--port", "0", "--hardfork", "osaka", "--chain-id", "31337",
               "--timestamp", "1700000000", "--gas-limit", "30000000", "--steps-tracing"]
    process = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    try:
        deadline, url = time.monotonic() + args.timeout, None
        for line in process.stdout:
            match = re.search(r"Listening on (127\.0\.0\.1:\d+)", line)
            if match:
                url = "http://" + match[1]
                break
            if time.monotonic() > deadline:
                break
        if url is None:
            raise SystemExit("Anvil did not start")
        # Keep draining Anvil's log so a full pipe never blocks the client.
        threading.Thread(target=lambda: [None for _ in process.stdout], daemon=True).start()
        result = run(Rpc(url))
    finally:
        process.terminate()
        process.wait(timeout=10)
    print(json.dumps(result, sort_keys=True))
    return 0 if result["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
