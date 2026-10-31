#!/usr/bin/env python3
"""Compare the pinned upstream end-to-end fixtures across compiled paths.

Every admitted fixture's recorded directives run on four paths: checked Hull
imported into Lean Core with the Sonatina O0 code images (`hull`), the Sonatina
O0 and O2 code images (`sonatina-o0`, `sonatina-o2`) and the pinned solc's
compilation of the driver's Yul (`yul`), the last three on a local Anvil. The
paths are compared with each other and with the fixture's own recorded
expectation. A mutation run also executes seeded single-change inputs derived
from the recorded calls and compares those across the paths only. A call's
words are classified by its method's standard ABI signature or, for a method
taking user data types, by std's derived layout of the pinned declarations;
every tag, dynamic offset and `bytes` length of such a call gets all of its
boundary Words.

No original Core reference exists for these programs. Agreement here is
agreement among compiled paths and with upstream's recorded expectations; it is
never a comparison with original Core.

Optional budgets bound a run for the fuzz driver: mutants per fixture, wall
time per fixture and per run. An entry reached after a deadline or a stop
signal is not run and has the status `budget`, which is neither a resource
limit nor a finding.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import contextlib
import fcntl
import fnmatch
import importlib.util
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
import threading
import time
import urllib.error
import urllib.request

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


common = load("fixtures_common", "semantic-differential.py")
storage = load("fixtures_storage", "semantic-storage-differential.py")
scenario = load("fixtures_scenario", "rust-scenario-parity.py")
methods = load("fixtures_methods", "rust-method-parity.py")
exporter = load("fixtures_yul", "export-rust-yul.py")
declarations = load("fixtures_declarations", "export-rust-declarations.py")
static = methods.static
hull = scenario.hull

SCHEMA = "solcore-lean.semantic-fixtures.v1"
FIXTURE_SCHEMA = "solcore-lean.semantic-fixture-result.v1"
EXPORT_SCHEMA = "solcore-lean.semantic-fixture-exports.v1"
COMPARISON = ("compiled paths with each other and with each fixture's recorded upstream expectation; "
              "mutated inputs with each other only; no original Core reference")
PATHS = ("hull", "sonatina-o0", "sonatina-o2", "yul")
EVM_PATHS = PATHS[1:]
LEVELS = {"sonatina-o0": "O0", "sonatina-o2": "O2"}
MANIFESTS = (("rust-scenario-parity.json", "raw"), ("rust-method-parity.json", "methods"))
ZERO = "0x" + "0" * 40
RAW_FUNDS = int("10000000000000000000000000", 16)
METHOD_FUNDS = 10000 * 10**18
# Upstream's raw transactions carry 20,000,000 gas; its eth_call and sends get the block gas limit.
RAW_GAS, METHOD_GAS, BLOCK_GAS = 20_000_000, 30_000_000, 30_000_000
DEFAULT_FUEL = 10_000_000
ENVIRONMENT = {"hardfork": "osaka", "chainId": 31337, "timestamp": 1700000000, "blockGasLimit": BLOCK_GAS,
               "baseFeePerGas": 0, "gasPrice": 0, "rawGas": RAW_GAS, "methodGas": METHOD_GAS}
COMPLETED = ("returned", "reverted", "exceptional")
RESOURCE = ("out-of-fuel", "out-of-gas", "resource-limit", "timeout", "output-limit", "memory-range")
# Solcore.Frontend.RustHull.Memory.overflowReason as the Lean runner prints a language failure's reason.
MEMORY_RANGE = "Solcore.Core.Value.word 6"
COMPARED = ("status", "output", "logs", "storage", "balances")
# Entries a path did not run: the deployment failed there, or a time budget or stop signal came first.
UNRUN = ("not-executed", "budget")
BUDGET = {"status": "budget", "detail": "a time budget or stop signal ended the run before this entry"}
VERDICTS = ("match", "mismatch", "inconclusive", "not-executed", "budget")
STOP = threading.Event()
U256 = 2**256
MASK64 = 2**64 - 1
MUTANTS_PER_STEP = 4
DERIVED_MUTANTS = 256
REDUCTION_RUNS = 48
REDUCTION_SECONDS = 900
MAX_ARRAY_ELEMENTS = 4096
OUTPUT_LIMIT = 64 * 1024**2
HULL_OUTPUT_LIMIT = 512 * 1024**2
HULL_TIMEOUT, HULL_ENTRY_TIMEOUT = 600, 120
TRANSACTION_TIMEOUT = 60
PRESTATE_DIFF = {"tracer": "prestateTracer", "tracerConfig": {"diffMode": True}}
CRASH = re.compile(r"panicked at|internal compiler error|process terminated by signal|backtrace:", re.I)
REFUSAL = re.compile(r"Yul profile requires|solc AST|unexpected solc contract output inventory|"
                     r"unsupported solc link references|missing runtime bytes|export EVM code size limit")
EXPORTERS = ("export-rust-hull.py", "export-rust-code-image.py", "export-rust-yul.py", "export-rust-directives.py",
             "build-rust-directive-resolver.py", "export-rust-declarations.py", "rust-hull-export.rs",
             "rust-code-image-export.rs", "rust-directive-export.rs", "rust-directive-resolve.rs",
             "rust-declaration-export.rs")
BINARIES = ("debug/solcore-driver", "debug/solcore-code-image-export", "debug/solcore-directive-export",
            "debug/solcore-directive-resolve", "debug/solcore-declaration-export")


def stopped(deadline: float | None) -> bool:
    """Whether a stop signal arrived or the deadline passed."""
    return STOP.is_set() or (deadline is not None and time.monotonic() >= deadline)


def unrun(count: int) -> list[dict]:
    return [dict(BUDGET) for _ in range(count)]


class Excluded(Exception):
    """A path or fixture that cannot run, with the stage and reason recorded."""

    def __init__(self, stage: str, reason: str, detail: str, paths=PATHS):
        self.stage, self.reason, self.detail, self.paths = stage, reason, detail, tuple(paths)
        super().__init__(detail)


def require(condition, message: str) -> None:
    if not condition:
        raise ValueError(message)


GAMMA = 0x9E3779B97F4A7C15


def finalize(value: int) -> int:
    value = ((value ^ (value >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
    value = ((value ^ (value >> 27)) * 0x94D049BB133111EB) & MASK64
    return value ^ (value >> 31)


def derive(root: int, *parts) -> int:
    """A seed for one fixture or step: the root mixed with each part's FNV-1a hash."""
    value = root & MASK64
    for part in parts:
        text = 0xCBF29CE484222325
        for byte in str(part).encode():
            text = ((text ^ byte) * 0x100000001B3) & MASK64
        value = finalize((value ^ text) + GAMMA & MASK64)
    return value


class Stream:
    """SplitMix64 draws from one derived seed."""

    def __init__(self, seed: int):
        self.state = seed & MASK64

    def next(self) -> int:
        self.state = (self.state + GAMMA) & MASK64
        return finalize(self.state)

    def below(self, bound: int) -> int:
        return self.next() % bound

    def word(self) -> int:
        return sum(self.next() << (64 * index) for index in range(4))


def inventory() -> list[dict]:
    """The 168 pinned fixtures of the two existing parity manifests."""
    fixtures, seen = [], set()
    for name, mode in MANIFESTS:
        document = json.loads((ROOT / "scripts" / name).read_text())
        require(document.get("upstreamCommit") == common.UPSTREAM_COMMIT, f"{name} pins another upstream revision")
        for item in document["fixtures"]:
            require(item["id"] not in seen, "fixture pinned twice: " + item["id"])
            seen.add(item["id"])
            fixtures.append({"id": item["id"], "source": item["source"], "sha256": item["sha256"], "mode": mode,
                             "contract": item["contract"], "calls": item["expectedCallCount"],
                             "availableGas": item.get("availableGas"), "fuel": item.get("coreFuel", DEFAULT_FUEL)})
    return sorted(fixtures, key=lambda item: item["id"])


# Standard ABI types, as trees, classify the words of a recorded input.

def abi_type(param: dict):
    """A standard ABI type, or None for one outside it, such as a derived ADT's source spelling."""
    text = param.get("type") if isinstance(param, dict) else None
    if not isinstance(text, str):
        return None
    array = re.fullmatch(r"(.*)\[(\d*)\]", text)
    if array:
        inner = abi_type({**param, "type": array[1]})
        return None if inner is None else ("array", inner, int(array[2]) if array[2] else None)
    if text == "tuple":
        components = [abi_type(item) for item in param.get("components") or []]
        return None if any(item is None for item in components) else ("tuple", tuple(components))
    if text in ("uint", "word"):
        return ("uint", 256)
    integer = re.fullmatch(r"(u?)int(\d+)", text)
    if integer:
        bits = int(integer[2])
        return ("uint" if integer[1] else "int", bits) if bits % 8 == 0 and 8 <= bits <= 256 else None
    fixed = re.fullmatch(r"bytes(\d+)", text)
    if fixed:
        return ("fixed", int(fixed[1])) if 1 <= int(fixed[1]) <= 32 else None
    return (text,) if text in ("address", "bool", "bytes", "string") else None


def canonical(node) -> str:
    kind = node[0]
    if kind == "array":
        return canonical(node[1]) + "[" + ("" if node[2] is None else str(node[2])) + "]"
    if kind == "tuple":
        return "(" + ",".join(canonical(item) for item in node[1]) + ")"
    if kind in ("uint", "int"):
        return f"{kind}{node[1]}"
    return f"bytes{node[1]}" if kind == "fixed" else kind


def dynamic(node) -> bool:
    if node[0] in ("bytes", "string"):
        return True
    if node[0] == "array":
        return node[2] is None or dynamic(node[1])
    return node[0] == "tuple" and any(dynamic(item) for item in node[1])


def head_size(node) -> int:
    if dynamic(node):
        return 32
    if node[0] == "array":
        return node[2] * head_size(node[1])
    if node[0] == "tuple":
        return sum(head_size(item) for item in node[1])
    return 32


def classify(body: bytes, nodes) -> dict[int, tuple]:
    """Classes of the words of `body` as an ABI encoding of `nodes`: typed leaves,
    offsets, lengths and content words. ValueError when it is not one."""
    classes: dict[int, tuple] = {}

    def word_at(position: int) -> int:
        if position < 0 or position % 32 or position + 32 > len(body):
            raise ValueError("word outside the input")
        return int.from_bytes(body[position:position + 32], "big")

    def mark(position: int, value: tuple) -> None:
        if classes.setdefault(position // 32, value) != value:
            raise ValueError("overlapping encoding")

    def sequence(items, base: int) -> None:
        position = base
        for item in items:
            if dynamic(item):
                offset = word_at(position)
                mark(position, ("offset",))
                if offset % 32 or base + offset > len(body):
                    raise ValueError("offset outside the input")
                value(item, base + offset)
                position += 32
            else:
                value(item, position)
                position += head_size(item)

    def value(node, position: int) -> None:
        kind = node[0]
        if kind in ("bytes", "string"):
            length = word_at(position)
            mark(position, ("length",))
            if position + 32 + length > len(body):
                raise ValueError("content outside the input")
            for index in range((length + 31) // 32):
                if position + 64 + 32 * index <= len(body):
                    mark(position + 32 + 32 * index, ("content",))
        elif kind == "array" and node[2] is None:
            length = word_at(position)
            mark(position, ("length",))
            if length > MAX_ARRAY_ELEMENTS:
                raise ValueError("array exceeds the classification bound")
            sequence([node[1]] * length, position + 32)
        elif kind == "array":
            sequence([node[1]] * node[2], position)
        elif kind == "tuple":
            sequence(node[1], position)
        else:
            word_at(position)
            mark(position, ("leaf", node))

    sequence(list(nodes), 0)
    return classes


# Derived ADT arguments: std's Generic structure of a public method's parameters, from the
# pinned parser's declarations; its structural selector, the constructor tags, and the
# layout std's derived decoder reads.

STD_LEAVES = {"uint256": ("uint", 256), "bytes32": ("fixed", 32), "bytes4": ("fixed", 4), "address": ("address",),
              "bool": ("bool",)}
LEAF_KINDS = ("uint", "int", "fixed", "address", "bool")
STRUCTURE_DEPTH = 16
# Every boundary Word of these classes is a mutant; the other classes are drawn.
EXHAUSTIVE = ("tag", "dynamic-offset", "bytes-length")


class Underived(ValueError):
    """A type outside std's derived signatures, which leaves its method without a derived layout."""


def source_text(ref) -> str:
    """A declared type as written."""
    if not isinstance(ref, dict):
        return "?"
    if "tuple" in ref:
        return "(" + ", ".join(source_text(item) for item in ref["tuple"]) + ")"
    if "named" not in ref:
        return "?"
    args = ref.get("args") or []
    return (ref["qualifier"] + "." if ref.get("qualifier") else "") + ref["named"] + \
        ("<" + ", ".join(source_text(item) for item in args) + ">" if args else "")


def product(nodes: list) -> tuple:
    """std's right-nested product of fields: unit, the one field, or pairs."""
    if not nodes:
        return ("unit",)
    return nodes[0] if len(nodes) == 1 else ("pair", nodes[0], product(nodes[1:]))


def structure(ref, scope: dict, bindings: dict | None = None, depth: int = 0) -> tuple:
    """std's Generic structure of a declared type: a sum of two or more constructors' products, a struct
    of one constructor's product, a pair, unit, a leaf, `bytes`, `string` or a calldata array."""
    if depth > STRUCTURE_DEPTH:
        raise Underived("data types nest deeper than the model's bound")
    bindings = bindings or {}
    if not isinstance(ref, dict):
        raise Underived("an untyped parameter")
    if "tuple" in ref:
        return product([structure(item, scope, bindings, depth + 1) for item in ref["tuple"]])
    if "named" not in ref or ref.get("qualifier") is not None:
        raise Underived("a type outside std's signatures: " + source_text(ref))
    name, args = ref["named"], ref.get("args") or []
    if name in bindings and not args:
        return bindings[name]
    if name in scope:
        kind, item = scope[name]
        if len(item["params"]) != len(args):
            raise Underived(f"{name} takes {len(item['params'])} type arguments")
        inner = dict(zip(item["params"], [structure(arg, scope, bindings, depth + 1) for arg in args]))
        if kind == "alias":
            return structure(item["type"], scope, inner, depth + 1)
        if not item["constructors"]:
            raise Underived(name + " has no constructors")
        reps = tuple((ctor["name"], structure(ctor["fields"], scope, inner, depth + 1)) for ctor in item["constructors"])
        return ("sum", name, reps) if len(reps) > 1 else ("struct", name, reps[0][1])
    if name in STD_LEAVES and not args:
        return STD_LEAVES[name]
    inner = args[0] if len(args) == 1 else {}
    if name == "memory" and inner.get("named") in ("bytes", "string") and not inner.get("args") and \
            inner.get("qualifier") is None:
        return (inner["named"],)
    if name == "calldata" and inner.get("named") == "array" and len(inner.get("args") or []) == 1 and \
            inner.get("qualifier") is None:
        return ("array", structure(inner["args"][0], scope, bindings, depth + 1))
    raise Underived("a type outside std's signatures: " + source_text(ref))


def derived(node) -> bool:
    """Whether a structure holds a user data type, which no standard ABI signature describes."""
    if node[0] in ("sum", "struct"):
        return True
    if node[0] == "pair":
        return derived(node[1]) or derived(node[2])
    return node[0] == "array" and derived(node[1])


def signature_text(node) -> str:
    """std's SigString of a structure."""
    kind = node[0]
    if kind in LEAF_KINDS:
        return canonical(node)
    if kind in ("bytes", "string"):
        return kind
    if kind == "unit":
        return ""
    if kind == "pair":
        return signature_text(node[1]) + "," + signature_text(node[2])
    if kind == "array":
        return element_signature(node[1]) + "[]"
    if kind == "struct":
        return signature_text(node[2])
    reps = [rep for _, rep in node[2]]
    text = signature_text(reps[-1])
    for rep in reversed(reps[:-1]):
        text = "sum(" + signature_text(rep) + "," + text + ")"
    return text


def element_signature(node) -> str:
    """std's ABITypeString of an array element: a unit or a pair signs in parentheses."""
    if node[0] == "unit":
        return "()"
    return "(" + signature_text(node) + ")" if node[0] == "pair" else signature_text(node)


def attribs(node) -> tuple[bool, int]:
    """std's ABIAttribs of a structure: whether it is static, and its head size. A sum's head is one tag
    and its widest constructor's fields when static, else one offset Word."""
    kind = node[0]
    if kind in LEAF_KINDS:
        return True, 32
    if kind in ("bytes", "string", "array"):
        return False, 32
    if kind == "unit":
        return True, 0
    if kind == "pair":
        (first, head), (second, tail) = attribs(node[1]), attribs(node[2])
        return first and second, head + tail
    if kind == "struct":
        return attribs(node[2])
    arms = [attribs(rep) for _, rep in node[2]]
    static = all(arm[0] for arm in arms)
    return static, 32 + max(arm[1] for arm in arms) if static else 32


def element_head(node) -> int:
    """std's ABIElementAttribs: a dynamic tuple element's head is one offset Word."""
    static, head = attribs(node)
    return 32 if node[0] == "pair" and not static else head


def tags(node) -> list[int]:
    """A sum's constructor tags, keccak256("Name(fields)") as Words, in declaration order."""
    return [int.from_bytes(storage.keccak256((name + "(" + signature_text(rep) + ")").encode()), "big")
            for name, rep in node[2]]


def derived_methods(document: dict | None, contract: str) -> dict[bytes, tuple[str, tuple]]:
    """The public methods of `contract` that take a user data type, with their structure, by structural
    selector. A method with a type outside the model has no derived layout."""
    scope, found = {}, [item for item in (document or {}).get("contracts") or [] if item.get("name") == contract]
    for item in ([document] if document else []) + found[:1]:
        for data in item.get("data") or []:
            scope[data["name"]] = ("data", data)
        for alias in item.get("aliases") or []:
            scope[alias["name"]] = ("alias", alias)
    result = {}
    for method in found[0].get("functions") or [] if found else []:
        if method.get("kind") != "function" or not method.get("public"):
            continue
        try:
            node = product([structure(param.get("type"), scope) for param in method["params"]])
        except Underived:
            continue
        if derived(node):
            text = method["name"] + "(" + signature_text(node) + ")"
            result[storage.keccak256(text.encode())[:4]] = (text, node)
    return result


def derived_classify(body: bytes, node) -> dict[int, tuple]:
    """Classes of the words of `body` as std's derived encoding of `node`: typed leaves, tags, dynamic
    offsets with their base, `bytes` and array lengths, content and unused head words. ValueError when
    it is not one."""
    classes: dict[int, tuple] = {}

    def word_at(position: int) -> int:
        if position < 0 or position % 32 or position + 32 > len(body):
            raise ValueError("word outside the input")
        return int.from_bytes(body[position:position + 32], "big")

    def mark(position: int, value: tuple) -> None:
        if classes.setdefault(position // 32, value) != value:
            raise ValueError("overlapping encoding")

    def follow(position: int, base: int, role: str) -> int:
        offset = word_at(position)
        mark(position, ("dynamic-offset", role, base))
        if offset % 32 or base + offset > len(body):
            raise ValueError("offset outside the input")
        return base + offset

    def value(node, base: int, head: int) -> None:
        kind, position = node[0], base + head
        if kind in LEAF_KINDS:
            word_at(position)
            mark(position, ("leaf", node))
        elif kind == "pair":
            value(node[1], base, head)
            value(node[2], base, head + attribs(node[1])[1])
        elif kind == "struct":
            value(node[2], base, head)
        elif kind in ("bytes", "string"):
            start = follow(position, base, "bytes")
            length = word_at(start)
            mark(start, ("bytes-length", start + 32))
            if start + 32 + length > len(body):
                raise ValueError("content outside the input")
            for index in range((length + 31) // 32):
                mark(start + 32 + 32 * index, ("content",))
        elif kind == "array":
            start = follow(position, base, "array")
            length = word_at(start)
            mark(start, ("length",))
            if length > MAX_ARRAY_ELEMENTS:
                raise ValueError("array exceeds the classification bound")
            element, region = node[1], start + 32
            for index in range(length):
                if element[0] == "pair" and not attribs(element)[0]:
                    value(element, follow(region + 32 * index, region, "element"), 0)
                else:
                    value(element, region, index * element_head(element))
        elif kind == "sum":
            static, size = attribs(node)
            start = position if static else follow(position, base, "sum")
            tag, known = word_at(start), tags(node)
            if tag not in known:
                raise ValueError(f"the tag matches no constructor of {node[1]}")
            mark(start, ("tag", node[1], tuple(known)))
            rep = node[2][known.index(tag)][1]
            value(rep, start, 32)
            if static:
                for unused in range(start + 32 + attribs(rep)[1], start + size, 32):
                    word_at(unused)
                    mark(unused, ("unused",))

    value(node, 0, 0)
    return classes


def class_label(value: tuple) -> str:
    if value[0] == "leaf":
        return "leaf:" + canonical(value[1])
    return value[0] + ":" + value[1] if value[0] in ("tag", "dynamic-offset") else value[0]


def boundary_values(value: tuple, recorded: int, body_length: int) -> list[int]:
    """The boundary Words of one position's class, without the recorded Word."""
    kind = value[0]
    if kind == "leaf":
        node = value[1]
        if node[0] == "bool":
            values = [0, 1, 2, U256 - 1]
        elif node[0] == "address":
            values = [0, 1, 2**160 - 1, 2**160, U256 - 1]
        elif node[0] == "uint" and node[1] < 256:
            values = [0, 2**node[1] - 1, 2**node[1], U256 - 1]
        elif node[0] == "int" and node[1] < 256:
            half = 2**(node[1] - 1)
            values = [0, half - 1, U256 - half, half, U256 - half - 1]
        elif node[0] == "int":
            values = [0, 1, U256 - 1, 2**255 - 1, 2**255]
        elif node[0] == "fixed" and node[1] < 32:
            shift = 256 - 8 * node[1]
            values = [0, (2**(8 * node[1]) - 1) << shift, recorded | 1, recorded >> shift]
        else:
            values = [0, 1, 2**255, U256 - 1, recorded + 1, recorded - 1]
    elif kind == "offset":
        values = [0, recorded - 32, recorded + 32, recorded + 1, body_length, body_length - 31, 2**64, U256 - 32, U256 - 1]
    elif kind == "length":
        values = [0, recorded - 1, recorded + 1, 2**32, 2**64, U256 - 1]
    elif kind == "content":
        values = [0, U256 - 1, recorded ^ 1]
    elif kind == "tag":
        values = [tag for tag in value[2] if tag != recorded] + [0, recorded + 1, recorded - 1, U256 - 1]
    elif kind == "dynamic-offset":
        # Relative to its base: one byte past the input's end, and the Word that wraps to the selector.
        base = value[2]
        values = [0, 32, body_length - base + 1, 2**255, U256 - 4 - base, recorded - 32, recorded + 32]
    elif kind == "bytes-length":
        # One more than fits, the largest Word, and into the padding of the content's last word.
        values = [body_length - value[1] + 1, U256 - 1] + ([-(-recorded // 32) * 32] if recorded % 32 else [])
    elif kind == "unused":
        values = [0, 1, U256 - 1]
    else:
        values = [0, 1, 32, recorded + 1, recorded - 1, 2**64, 2**255, U256 - 32, U256 - 1]
    result = []
    for item in values:
        item %= U256
        if item != recorded and item not in result:
            result.append(item)
    return result


def seeded_value(value: tuple, draw: int) -> int:
    """A seeded Word kept inside a typed leaf's valid range; other positions take it whole."""
    if value[0] != "leaf":
        return draw
    node = value[1]
    if node[0] == "bool":
        return draw & 1
    if node[0] == "address":
        return draw % 2**160
    if node[0] in ("uint", "int") and node[1] < 256:
        bounded = draw % 2**node[1]
        if node[0] == "int" and bounded >= 2**(node[1] - 1):
            bounded = (bounded - 2**node[1]) % U256
        return bounded
    if node[0] == "fixed" and node[1] < 32:
        return (draw >> (256 - 8 * node[1])) << (256 - 8 * node[1])
    return draw


def selector_prefix(step: dict) -> int:
    """Deployments mutate their constructor bytes; calls keep their four-byte selector."""
    return 0 if step["kind"] == "deploy" else min(4, (len(step["calldata"]) - 2) // 2)


def candidates(step: dict, classes: dict | None, stream: Stream) -> dict[str, list[dict]]:
    """Every single-change mutant of one step, grouped by operator family."""
    data = bytes.fromhex(step["calldata"][2:])
    body = data[selector_prefix(step):]
    families: dict[str, list[dict]] = {}

    def add(family: str, mutant: dict) -> None:
        families.setdefault(family, []).append(mutant)

    for index in range(len(body) // 32):
        recorded = int.from_bytes(body[32 * index:32 * index + 32], "big")
        position = (classes or {}).get(index, ("unclassified",))
        family = "leaf" if position[0] == "leaf" else position[0]
        for value in [] if position[0] in EXHAUSTIVE else boundary_values(position, recorded, len(body)):
            add(family, {"operator": "word", "class": class_label(position), "word": index,
                         "recorded": hex(recorded), "value": hex(value)})
        seeded = seeded_value(position, stream.word())
        if seeded != recorded:
            add("seeded", {"operator": "seeded-word", "class": class_label(position), "word": index,
                           "recorded": hex(recorded), "value": hex(seeded)})
    # The input's length and the call value form one family, beside the word classes.
    for operator, amount in (("truncate", 1), ("truncate", 32), ("extend-zero", 1), ("extend-ones", 32)):
        if operator != "truncate" or len(body) >= amount:
            add("frame", {"operator": operator, "bytes": amount})
    if body:
        add("frame", {"operator": "drop-arguments", "bytes": len(body)})
    if step["kind"] in ("raw", "send", "deploy"):
        add("frame", {"operator": "value", "recorded": step["value"], "value": 0 if step["value"] else 1})
    return families


def exhaustive(step: dict, classes: dict | None) -> list[dict]:
    """Every boundary Word of a step's tags, dynamic offsets and `bytes` lengths, by word and value."""
    body = bytes.fromhex(step["calldata"][2:])[selector_prefix(step):]
    result = []
    for index, position in sorted((classes or {}).items()):
        if position[0] in EXHAUSTIVE:
            recorded = int.from_bytes(body[32 * index:32 * index + 32], "big")
            result += [{"operator": "word", "class": class_label(position), "word": index, "recorded": hex(recorded),
                        "value": hex(value)} for value in boundary_values(position, recorded, len(body))]
    return result


def derived_boundary(mutant: dict | None) -> bool:
    """Whether a mutant is one of the exhaustive boundary Words; a seeded Word keeps its position's class."""
    return bool(mutant) and mutant["operator"] == "word" and mutant["class"].split(":")[0] in EXHAUSTIVE


def seeded_subset(items: list, limit: int, stream: Stream) -> list:
    """A seeded uniform sample of `limit` items, in their order."""
    order = list(range(len(items)))
    for position in range(min(limit, len(order))):
        other = position + stream.below(len(order) - position)
        order[position], order[other] = order[other], order[position]
    return [items[index] for index in sorted(order[:limit])]


def sample(families: dict[str, list[dict]], stream: Stream, count: int) -> list[dict]:
    """At most `count` mutants, one family at a time in a seeded order."""
    order = sorted(families)
    for index in range(len(order) - 1, 0, -1):
        other = stream.below(index + 1)
        order[index], order[other] = order[other], order[index]
    pools = {family: list(items) for family, items in families.items()}
    chosen = []
    while len(chosen) < count and any(pools.values()):
        for family in order:
            pool = pools[family]
            if pool and len(chosen) < count:
                chosen.append(pool.pop(stream.below(len(pool))))
    return chosen


def apply(step: dict, mutant: dict) -> dict:
    """The recorded step with exactly one change."""
    data = bytearray.fromhex(step["calldata"][2:])
    prefix, value, operator = selector_prefix(step), step["value"], mutant["operator"]
    if operator in ("word", "seeded-word"):
        start = prefix + 32 * mutant["word"]
        require(start + 32 <= len(data), "mutated word outside the recorded input")
        data[start:start + 32] = int(mutant["value"], 16).to_bytes(32, "big")
    elif operator == "truncate":
        require(len(data) - prefix >= mutant["bytes"], "truncation beyond the arguments")
        del data[len(data) - mutant["bytes"]:]
    elif operator == "extend-zero":
        data += bytes(mutant["bytes"])
    elif operator == "extend-ones":
        data += b"\xff" * mutant["bytes"]
    elif operator == "drop-arguments":
        del data[prefix:]
    elif operator == "value":
        value = mutant["value"]
    else:
        raise ValueError("unknown mutation operator: " + operator)
    return {**step, "calldata": "0x" + data.hex(), "value": value}


def step_classes(step: dict, abi: list[dict], derived: dict | None = None) -> tuple[dict | None, str]:
    """Word classes of a step's recorded arguments and where they came from: a standard-ABI method, else
    a method of `derived_methods` with the call's structural selector."""
    data = bytes.fromhex(step["calldata"][2:])
    if step["kind"] == "deploy":
        entries = [item for item in abi if item.get("type") == "constructor"]
        params, body = (entries[0].get("inputs", []) if entries else []), data
    else:
        if len(data) < 4:
            return None, "no selector"
        params, body = None, data[4:]
        for item in abi:
            if item.get("type") != "function":
                continue
            nodes = [abi_type(param) for param in item.get("inputs", [])]
            if any(node is None for node in nodes):
                continue
            signature = item["name"] + "(" + ",".join(canonical(node) for node in nodes) + ")"
            if storage.keccak256(signature.encode())[:4] == data[:4]:
                params = item.get("inputs", [])
                break
        if params is None:
            if data[:4] not in (derived or {}):
                return None, "no standard-ABI method with this selector"
            text, node = derived[data[:4]]
            try:
                return derived_classify(body, node), "derived"
            except ValueError as error:
                return None, f"recorded input is not the derived layout of {text}: {error}"
    nodes = [abi_type(param) for param in params]
    if any(node is None for node in nodes):
        return None, "non-standard ABI type"
    try:
        return classify(body, nodes), "abi"
    except ValueError as error:
        return None, "recorded input is not a canonical encoding: " + str(error)


# Processes, exports and the fixture inventory.

def run_process(command: list[str], timeout: float, limit: int = OUTPUT_LIMIT, cwd: Path = ROOT,
                deadline: float | None = None) -> dict:
    """Bound one command's time and captured output, stopping its owned process group; with a
    deadline, a stop signal or the deadline stops it as `budget`."""
    started = time.monotonic()
    with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
        process = subprocess.Popen(command, cwd=cwd, stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr,
                                   start_new_session=True)
        reason = None
        try:
            while process.poll() is None:
                if deadline is not None and stopped(deadline):
                    reason = "budget"
                    break
                if time.monotonic() - started >= timeout:
                    reason = "timeout"
                    break
                if stdout.tell() + stderr.tell() > limit:
                    reason = "output-limit"
                    break
                time.sleep(0.02)
        finally:
            common.stop_process(process)
        if stdout.tell() + stderr.tell() > limit:
            reason = "output-limit"
        stdout.seek(0)
        stderr.seek(0)
        return {"command": command, "returncode": process.returncode, "resource": reason,
                "seconds": round(time.monotonic() - started, 3),
                "stdout": stdout.read(limit).decode(errors="replace"), "stderr": stderr.read(limit).decode(errors="replace")}


def failure(result: dict, stage: str, paths=PATHS) -> Excluded:
    detail = (result["stderr"] + result["stdout"])[-6000:]
    if result["resource"]:
        return Excluded(stage, "resource", result["resource"] + "\n" + detail, paths)
    if result["returncode"] < 0 or CRASH.search(detail):
        return Excluded(stage, "compiler-crash", detail, paths)
    if stage == "yul-export" and REFUSAL.search(detail):
        return Excluded(stage, "export-refusal", detail, paths)
    return Excluded(stage, "compile-failure", detail, paths)


def tool_identity(args) -> dict:
    """Digests of every script, binary and external tool a run reads."""
    scripts = sorted(path for pattern in ("*.py", "*.rs") for path in (ROOT / "scripts").glob(pattern))
    identity = {"scripts": {path.name: common.file_digest(path) for path in scripts},
                "binaries": {name: common.file_digest(args.target_dir / name) for name in BINARIES},
                "hullRunner": common.file_digest(args.hull_runner)}
    for name in ("solc", "anvil", "cast"):
        identity[name] = {"path": str(getattr(args, name)), "sha256": common.file_digest(getattr(args, name))}
    return identity


def export_identity(identity: dict) -> dict:
    return {"exporters": {name: identity["scripts"][name] for name in EXPORTERS}, "binaries": identity["binaries"],
            "solc": identity["solc"]["sha256"]}


class Exports:
    """Checked Hull, both code images, the Yul artifact and the ABI of one fixture."""

    def __init__(self, args, fixture: dict, identity: dict):
        self.args, self.fixture = args, fixture
        self.source = (args.upstream / fixture["source"]).resolve()
        self.directory = (args.work / fixture["id"]).resolve()
        self.identity = export_identity(identity)
        self.records: dict[str, dict] = {}

    def receipt_valid(self) -> bool:
        receipt = self.directory / "exports.json"
        if not self.args.reuse_exports or not receipt.exists():
            return False
        try:
            record = json.loads(receipt.read_text())
        except ValueError:
            return False
        return record.get("schema") == EXPORT_SCHEMA and record.get("identity") == self.identity and \
            record.get("sources") == self.sources()

    def sources(self) -> dict:
        """Every source file the checked Hull read, by digest."""
        main = {self.source.as_uri(): common.file_digest(self.source)}
        hull_path = self.directory / "hull-O0.json"
        return hull.source_hashes(json.loads(hull_path.read_text())) | main if hull_path.exists() else main

    def prepare(self, directive_build: dict, declaration_build: dict | None = None) -> dict:
        """Export everything once; an export failure excludes only the paths needing it."""
        reuse = self.receipt_valid()
        if not reuse and self.directory.exists():
            shutil.rmtree(self.directory)
        self.directory.mkdir(parents=True, exist_ok=True)
        started = time.monotonic()
        result = {"reused": reuse, "excluded": []}
        try:
            result["directives"] = scenario.extract(self.source, self.directory / "directives.json", self.args.upstream,
                                                    self.args.target_dir, directive_build, reuse, self.args.timeout)
        except (ValueError, OSError, subprocess.SubprocessError) as error:
            raise Excluded("directives", "unsupported-directive", str(error))
        # The declarations only classify words, so a failure on a source the directives parsed is a harness error.
        result["declarations"] = None if declaration_build is None else self.declarations(declaration_build, reuse)
        for path, level in LEVELS.items():
            try:
                result[level] = self.level(level, reuse)
            except Excluded as error:
                # A rejected checked source excludes every path; otherwise Hull needs the O0 images.
                if error.stage == "rust-checked-source" and "O0" not in result:
                    error.paths = PATHS
                    raise
                error.paths = ("hull", "sonatina-o0") if level == "O0" else (path,)
                result["excluded"].append(error)
        if "O0" in result and "O2" in result:
            require(common.file_digest(self.directory / "hull-O0.json") == common.file_digest(self.directory / "hull-O2.json"),
                    "the two code-image exports checked different Hull")
        try:
            result["yul"] = self.yul(reuse)
        except Excluded as error:
            error.paths = ("yul",)
            result["excluded"].append(error)
        try:
            result["abi"] = self.abi(reuse)
        except (RuntimeError, OSError, ValueError, subprocess.SubprocessError) as error:
            raise Excluded("rust-abi", "compile-failure", str(error))
        if not reuse:
            (self.directory / "exports.json").write_text(json.dumps(
                {"schema": EXPORT_SCHEMA, "identity": self.identity, "sources": self.sources()}, indent=2) + "\n")
        result["seconds"] = round(time.monotonic() - started, 3)
        return result

    def declarations(self, build: dict, reuse: bool) -> dict:
        """The pinned parser's declarations of the main source."""
        path = self.directory / "declarations.json"
        record = path.with_suffix(".json.provenance.json")
        if reuse and path.exists() and record.exists():
            provenance = json.loads(record.read_text())
            if provenance.get("schema") == declarations.SCHEMA and provenance.get("toolBuild") == build and \
                    provenance.get("source") == self.source.as_uri() and \
                    provenance.get("sourceSha256") == common.file_digest(self.source) and \
                    provenance.get("outputSha256") == common.file_digest(path):
                return json.loads(path.read_text())
        outcome = run_process([sys.executable, str(ROOT / "scripts/export-rust-declarations.py"), str(self.source),
                               "--output", str(path), "--upstream", str(self.args.upstream),
                               "--target-dir", str(self.args.target_dir)], self.args.timeout)
        require(not outcome["returncode"] and not outcome["resource"],
                "declaration extraction failed: " + (outcome["resource"] or (outcome["stderr"] + outcome["stdout"])[-2000:]))
        return json.loads(path.read_text())

    def level(self, level: str, reuse: bool) -> dict:
        hull_path, image_path = self.directory / f"hull-{level}.json", self.directory / f"images-{level}.json"
        if not (reuse and hull_path.exists() and image_path.exists()):
            for path in (hull_path, image_path, scenario.sidecar(hull_path), scenario.sidecar(image_path)):
                path.unlink(missing_ok=True)
            outcome = run_process([sys.executable, str(ROOT / "scripts/export-rust-code-image.py"), str(self.source),
                "--output", str(image_path), "--hull-output", str(hull_path), "--optimization", level,
                "--upstream", str(self.args.upstream), "--target-dir", str(self.args.target_dir),
                "--timeout", str(self.args.timeout)], self.args.timeout * 3)
            if outcome["returncode"] or outcome["resource"]:
                raise failure(outcome, "rust-checked-source" if not hull_path.exists() else f"rust-code-images-{level}")
        images = common.read_json(image_path, OUTPUT_LIMIT)
        record = common.read_json(scenario.sidecar(image_path), OUTPUT_LIMIT)
        hull_record = common.read_json(scenario.sidecar(hull_path), OUTPUT_LIMIT)
        require(record.get("optimization") == level and record.get("hullProvenance") == hull_record and
                record.get("outputSha256") == common.file_digest(image_path) and
                hull_record.get("outputSha256") == common.file_digest(hull_path) and
                record.get("sources") == hull_record.get("sources"), f"{level} export provenance differs from its files")
        common.validate_image_backend(images, "sonatina-o0" if level == "O0" else "sonatina-o2")
        return {"hull": hull_path, "images": image_path, "document": images, "hullProvenance": hull_record}

    def yul(self, reuse: bool) -> dict:
        directory = self.directory / "yul"
        artifact = directory / "yul.json"
        if not (reuse and artifact.exists()):
            if directory.exists():
                shutil.rmtree(directory)
            directory.mkdir()
            outcome = run_process([sys.executable, str(ROOT / "scripts/export-rust-yul.py"), str(self.source),
                "--fixture", self.fixture["id"], "--solc", str(self.args.solc), "--output", str(artifact),
                "--upstream", str(self.args.upstream), "--target-dir", str(self.args.target_dir),
                "--timeout", str(self.args.timeout)], self.args.timeout * 3)
            if outcome["returncode"] or outcome["resource"]:
                raise failure(outcome, "yul-export", ("yul",))
        document = common.read_json(artifact, OUTPUT_LIMIT)
        exporter.validate_artifact(document, self.fixture["contract"], fixture=self.fixture["id"])
        record = common.read_json(artifact.with_suffix(".json.provenance.json"), OUTPUT_LIMIT)
        require(record.get("outputSha256") == common.file_digest(artifact) and
                record.get("fixture") == {"id": self.fixture["id"], "source": self.fixture["source"],
                                          "sha256": self.fixture["sha256"]} and
                record.get("exporterSha256") == common.file_digest(ROOT / "scripts/export-rust-yul.py"),
                "Yul export provenance differs from its artifact, fixture or exporter")
        o0 = self.directory / "hull-O0.json"
        if o0.exists():
            require(record["hullProvenance"].get("outputSha256") == common.file_digest(o0),
                    "the Yul export checked different Hull from the code images")
        return {"init": common.hex_bytes(document["initCode"], "Yul init code"),
                "runtime": common.hex_bytes(document["runtimeCode"], "Yul runtime code")}

    def abi(self, reuse: bool) -> dict:
        path = self.directory / "abi.json"
        if not (reuse and path.exists()):
            abis = static.compile_abis(self.args.target_dir / "debug/solcore-driver", self.args.upstream, self.source,
                                       self.args.timeout)
            path.write_text(json.dumps(abis, indent=2) + "\n")
        return json.loads(path.read_text())


# Steps, Hull and EVM execution.

def build_steps(fixture: dict, extracted: dict, abis: dict, args) -> tuple[list[dict], dict]:
    """The deployment and every recorded call, with callers, values and expectations."""
    if fixture["mode"] == "raw":
        require(extracted["mode"] == "raw", "fixture is no longer a raw scenario")
        scene = extracted["scenario"]
        require(scene["contract"] == fixture["contract"] and len(scene["calls"]) == fixture["calls"],
                "raw scenario inventory changed")
        constructor = scene["constructor"]
        steps = [{"index": 0, "kind": "deploy", "label": "deploy", "calldata": constructor["calldata"],
                  "value": int(constructor["value"], 16), "caller": scenario.RAW_SENDER, "persist": True, "gas": RAW_GAS,
                  "expected": {"status": "returned" if constructor["expectedSuccess"] else "reverted",
                               "output": constructor["expectedOutput"]}}]
        for index, call in enumerate(scene["calls"], 1):
            steps.append({"index": index, "kind": "raw", "label": call["label"], "calldata": call["calldata"],
                          "value": int(call["value"], 16), "caller": scenario.RAW_SENDER, "persist": True, "gas": RAW_GAS,
                          "expected": call["expected"]})
        return steps, {"address": scenario.RAW_ADDRESS, "accounts": [(scenario.RAW_SENDER, RAW_FUNDS)]}
    require(extracted["mode"] == "methods", "fixture no longer uses method directives")
    resolved = methods.resolve(extracted, abis, args.target_dir / "debug/solcore-directive-resolve", str(args.cast),
                               args.timeout)
    calls = resolved["calls"]
    require(len(calls) == fixture["calls"] and all(call["contract"] == fixture["contract"] for call in calls),
            "method directive inventory changed")
    steps = [{"index": 0, "kind": "deploy", "label": "deploy", "calldata": "0x", "value": 0, "caller": methods.METHOD_SENDER,
              "persist": True, "gas": METHOD_GAS, "expected": {"status": "returned", "output": None}}]
    for index, call in enumerate(calls, 1):
        steps.append({"index": index, "kind": "send" if call["persist"] else "call",
                      "label": f"{call['method']}/{call['vector']}", "signature": call["signature"],
                      "calldata": call["calldata"], "value": 0,
                      "caller": methods.METHOD_SENDER if call["persist"] else ZERO, "persist": call["persist"],
                      "gas": METHOD_GAS, "expected": call["expected"]})
    return steps, {"address": methods.METHOD_ADDRESS, "accounts": [(methods.METHOD_SENDER, METHOD_FUNDS)]}


def balance_addresses(chain: dict) -> list[str]:
    return [str(int(chain["address"], 16))] + [str(int(address, 16)) for address, _ in chain["accounts"]]


def hull_observation(row: dict, chain: dict) -> dict:
    """One Lean Core receipt in the comparison's terms."""
    status = {"returned": "returned", "reverted": "reverted", "invalid": "exceptional"}.get(row.get("status"), row.get("status"))
    observation = {"status": status}
    if status not in COMPLETED:
        observation["detail"] = row.get("detail")
        return observation
    observation["output"] = row.get("output", "0x") if status != "exceptional" else "0x"
    observation["logs"] = row.get("logs", [])
    if status == "returned":
        contract, accounts = str(int(chain["address"], 16)), {}
        for account in row.get("world", []):
            slots = {key: value for key, value in account["storage"] if value != "0"}
            if slots:
                accounts[account["address"]] = slots
        slots = {key: value for key, value in row.get("storage", []) if value != "0"}
        accounts.pop(contract, None)
        if slots:
            accounts[contract] = slots
        observation["storage"] = accounts
        ledger = {address: value for address, value in row.get("balances", [])}
        observation["balances"] = {address: ledger.get(address, "0") for address in balance_addresses(chain)}
    return observation


def hull_invocation(args, fixture: dict, exports: dict, chain: dict, deploy: dict, calls: list[dict],
                    timeout: float, deadline: float | None = None) -> tuple[list[dict], str | None, int]:
    """The deployment and `calls` on Lean Core from one runner invocation: an observation of each,
    a blocked status for each the runner did not report, its resource limit and the reported count."""
    objects = json.loads(exports["O0"]["hull"].read_text())["program"]["objects"]
    selected = [path for path in scenario.paths(objects) if path[-1] == fixture["contract"]]
    require(len(selected) == 1 and len(selected[0]) >= 2, "the runtime object lacks a unique deployment parent")
    address = str(int(chain["address"], 16))

    def context(step: dict) -> dict:
        value = {"calldata": step["calldata"], "value": str(step["value"]), "caller": str(int(step["caller"], 16)),
                 "address": address}
        if fixture["availableGas"] is not None:
            value["availableGas"] = fixture["availableGas"]
        return value

    config = {"schema": "solcore-lean.contract-scenario.v1", "hull": str(exports["O0"]["hull"]),
              "images": str(exports["O0"]["images"]), "deployPath": list(selected[0][:-1]),
              "runtimePath": list(selected[0]), "fuel": fixture["fuel"],
              "accounts": [{"address": str(int(account, 16)), "balance": str(funds), "empty": True}
                           for account, funds in chain["accounts"]],
              "constructor": context(deploy), "calls": [{**context(entry), "persist": entry["persist"]} for entry in calls]}
    with tempfile.TemporaryDirectory(prefix="solcore-fixture-hull-") as temporary:
        path = Path(temporary) / "scenario.json"
        path.write_text(json.dumps(config))
        outcome = run_process([str(args.hull_runner), str(path)], timeout, HULL_OUTPUT_LIMIT, deadline=deadline)
    count = 1 + len(calls)
    lines = outcome["stdout"].split("\n")
    if outcome["resource"]:
        lines = lines[:-1]  # a stopped runner may leave its last row unfinished
    rows = [json.loads(line) for line in lines if line.strip()]
    observations: list[dict] = []
    for row in rows:
        stage = row.get("stage")
        if stage == "preparation":
            reported = len(observations)
            return observations + [{"status": "core-preparation", "detail": row.get("detail")}] * (count - reported), None, reported
        expected = "deployment" if not observations else "execution"
        require(stage == expected and (stage == "deployment" or row.get("index") == len(observations) - 1),
                "unexpected Lean Core result order")
        observations.append(hull_observation(row, chain))
    reported = len(observations)
    if reported < count:
        if outcome["resource"]:
            blocked = {"status": outcome["resource"]}
        elif observations and observations[0]["status"] != "returned":
            blocked = {"status": "not-executed", "detail": "the deployment did not complete"}
        else:
            blocked = {"status": "core-runner-error", "detail": outcome["stderr"][-2000:]}
        observations += [blocked] * (count - reported)
    require(len(observations) == count, "extra Lean Core result rows")
    return observations, outcome["resource"], reported


def run_hull(args, fixture: dict, exports: dict, chain: dict, deploy: dict, entries: list[dict],
             deadline: float | None = None) -> list[dict]:
    """The deployment and every entry on Lean Core, each entry within a time limit.

    Lean Core has no gas, so a mutant can run for long before its fuel runs out. Method entries other than
    sends keep no state, so after the deployment alone each runs in its own invocation after the sends
    before it, within --hull-entry-timeout. A raw scenario's entries run in one invocation within
    --hull-timeout; after a limit it resumes past the reported entries, replaying the persisting steps
    before them, and an entry that stalls when run alone is reported with that limit. Entries reached
    after the deadline or a stop signal are not run."""
    def invoke(calls: list[dict], timeout: float):
        return hull_invocation(args, fixture, exports, chain, deploy, calls, timeout, deadline)

    def persisted(before: int) -> list[dict]:
        """The earlier entries whose changes persist: those that persist and returned."""
        return [item for item, seen in zip(entries[:before], result) if item["persist"] and seen["status"] == "returned"]

    def unexecuted() -> list[dict]:
        return [deployment] + [{"status": "not-executed", "detail": "the deployment did not complete"}] * len(entries)

    # The runner buffers its rows, so a stopped invocation may not report even the deployment;
    # then the deployment runs alone.
    deployment, result = None, []
    if stopped(deadline):
        return unrun(1 + len(entries))
    if not entries or fixture["mode"] == "methods":
        deployment = invoke([], args.hull_timeout)[0][0]
        if deployment["status"] == "budget":
            return unrun(1 + len(entries))
        if deployment["status"] != "returned":
            return unexecuted()
        for index, entry in enumerate(entries):
            if stopped(deadline):
                result += unrun(len(entries) - index)
                break
            observed, _, _ = invoke(persisted(index) + [entry], args.hull_entry_timeout)
            result.append(observed[-1])
        return [deployment] + result
    start = 0
    while start < len(entries):
        if stopped(deadline):
            return [deployment or dict(BUDGET)] + result + unrun(len(entries) - start)
        prefix = persisted(start)
        observed, resource, reported = invoke(prefix + entries[start:], args.hull_timeout)
        if deployment is None:
            deployment = observed[0] if reported else invoke([], args.hull_timeout)[0][0]
        if deployment["status"] == "budget":
            return unrun(1 + len(entries))
        if deployment["status"] != "returned":
            return unexecuted()
        tail, done = observed[1 + len(prefix):], max(0, reported - 1 - len(prefix))
        if not resource:
            return [deployment] + result + tail
        if resource == "budget":
            return [deployment] + result + tail[:done] + unrun(len(entries) - start - done)
        if done:
            result, start = result + tail[:done], start + done
            continue
        # No row of this attempt arrived: the first entry stalled, or its row was still buffered.
        alone, resource, reported = invoke(prefix + [entries[start]], args.hull_timeout)
        if not resource or reported == 2 + len(prefix):
            result.append(alone[-1])
        else:
            result.append(dict(BUDGET) if resource == "budget" else {
                "status": resource, "detail": "the entry did not complete when run alone"})
        start += 1
    return [deployment] + result


class Chain:
    """One local Anvil for one fixture; every backend starts from the same snapshot."""

    def __init__(self, args, chain: dict):
        self.args, self.chain = args, chain
        command = [str(args.anvil), "--host", "127.0.0.1", "--port", "0", "--hardfork", "osaka",
                   "--chain-id", str(ENVIRONMENT["chainId"]), "--timestamp", str(ENVIRONMENT["timestamp"]),
                   "--gas-limit", str(BLOCK_GAS), "--block-base-fee-per-gas", "0"]
        self.log = tempfile.TemporaryFile()
        self.process = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=self.log, stderr=self.log,
                                        start_new_session=True)
        self.opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
        self.counter, self.url = 0, None
        deadline = time.monotonic() + 30
        while self.url is None:
            # Anvil shares this file's offset; pread leaves it where Anvil writes.
            matched = re.search(rb"Listening on (127\.0\.0\.1:\d+)", os.pread(self.log.fileno(), 65536, 0))
            if matched:
                self.url = "http://" + matched[1].decode()
            elif self.process.poll() is not None or time.monotonic() > deadline:
                self.close()
                raise Excluded("anvil-startup", "resource", "Anvil did not start", EVM_PATHS)
            else:
                time.sleep(0.02)
        self.version = self.rpc("web3_clientVersion", [])
        for address, funds in chain["accounts"] + [(ZERO, 0)]:
            self.rpc("anvil_impersonateAccount", [address])
            self.rpc("anvil_setBalance", [address, hex(funds)])
        self.base = self.rpc("evm_snapshot", [])

    def rpc(self, method: str, params):
        self.counter += 1
        payload = json.dumps({"jsonrpc": "2.0", "id": self.counter, "method": method, "params": params}).encode()
        request = urllib.request.Request(self.url, payload, {"Content-Type": "application/json"})
        with self.opener.open(request, timeout=TRANSACTION_TIMEOUT) as response:
            content = response.read(OUTPUT_LIMIT + 1)
        require(len(content) <= OUTPUT_LIMIT, "RPC output limit")
        result = json.loads(content)
        require(result.get("id") == self.counter and result.get("jsonrpc") == "2.0", "invalid JSON-RPC response")
        if "error" in result:
            raise common.RpcError(result["error"])
        return result["result"]

    def reset(self) -> None:
        require(self.rpc("evm_revert", [self.base]) is True, "Anvil did not restore the fixture snapshot")
        self.base = self.rpc("evm_snapshot", [])

    def transact(self, request: dict) -> tuple[dict, dict, dict | None]:
        tx_hash = self.rpc("eth_sendTransaction", [request])
        deadline = time.monotonic() + TRANSACTION_TIMEOUT
        while (receipt := self.rpc("eth_getTransactionReceipt", [tx_hash])) is None:
            if time.monotonic() > deadline:
                raise Excluded("evm-transaction", "resource", "receipt timeout", EVM_PATHS)
            time.sleep(0.005)
        call = self.rpc("debug_traceTransaction", [tx_hash, {"tracer": "callTracer"}])
        diff = self.rpc("debug_traceTransaction", [tx_hash, PRESTATE_DIFF]) if receipt["status"] == "0x1" else None
        return receipt, call, diff

    def close(self) -> None:
        common.stop_process(self.process)
        self.log.close()


def evm_status(receipt: dict, call: dict) -> str:
    if receipt.get("status") == "0x1":
        return "returned"
    error = str(call.get("error", ""))
    if error == "execution reverted":
        return "reverted"
    if common.GAS_RESOURCE.search(error):
        return "out-of-gas"
    return "resource-limit" if common.RESOURCE.search(error) else "exceptional"


def run_evm(evm: Chain, path: str, init: bytes, runtime: bytes, deploy: dict, entries: list[dict],
            deadline: float | None = None) -> list[dict]:
    """The deployment and every entry on one backend; non-persisting entries are rolled back, and
    entries reached after the deadline or a stop signal are not run."""
    if stopped(deadline):
        return unrun(1 + len(entries))
    evm.reset()
    chain, touched = evm.chain, {}

    def note(diff: dict | None) -> None:
        if diff is None:
            return
        for side in ("pre", "post"):
            for account, state in diff[side].items():
                for key in state.get("storage", {}):
                    touched.setdefault(account.lower(), set()).add(int(key, 16))

    def observe(request: dict) -> dict:
        try:
            receipt, call, diff = evm.transact({**request, "gas": hex(request["gas"]), "gasPrice": "0x0"} | {
                "value": hex(request["value"])})
        except common.RpcError as error:
            return {"status": "evm-rejected", "detail": json.dumps(error.error)}
        status = evm_status(receipt, call)
        observation = {"status": status}
        if status not in COMPLETED:
            observation["detail"] = str(call.get("error"))
            return observation
        observation["output"] = call.get("output", "0x") if status != "exceptional" else "0x"
        observation["logs"] = [{"address": str(int(event["address"], 16)),
                                "topics": [str(int(topic, 16)) for topic in event["topics"]],
                                "data": "0x" + common.hex_bytes(event["data"], "log data").hex()} for event in receipt["logs"]]
        if status == "returned":
            note(diff)
            block, accounts = receipt["blockNumber"], {}
            for account in sorted(touched):
                slots = {}
                for slot in sorted(touched[account]):
                    value = int(evm.rpc("eth_getStorageAt", [account, hex(slot), block]), 16)
                    if value:
                        slots[str(slot)] = str(value)
                if slots:
                    accounts[str(int(account, 16))] = slots
            observation["storage"] = accounts
            observation["balances"] = {address: str(int(evm.rpc("eth_getBalance", [f"0x{int(address):040x}", block]), 16))
                                       for address in balance_addresses(chain)}
            observation["block"] = block
        return observation

    deployment = observe({"from": deploy["caller"], "data": "0x" + init.hex() + deploy["calldata"][2:],
                          "value": deploy["value"], "gas": deploy["gas"]})
    observations = [deployment]
    if deployment["status"] == "returned":
        code = common.hex_bytes(evm.rpc("eth_getCode", [chain["address"], deployment["block"]]), "deployed code")
        if code != runtime:
            observations[0] = {"status": "evm-code-mismatch", "detail": f"{path} installed other runtime bytes"}
    for entry in entries:
        if observations[0]["status"] != "returned":
            observations.append({"status": "not-executed", "detail": "the deployment did not complete"})
            continue
        if stopped(deadline):
            observations.append(dict(BUDGET))
            continue
        saved = {account: set(slots) for account, slots in touched.items()}
        snapshot = None if entry["persist"] else evm.rpc("evm_snapshot", [])
        observation = observe({"from": entry["caller"], "to": chain["address"], "data": entry["calldata"],
                               "value": entry["value"], "gas": entry["gas"]})
        observations.append(observation)
        if snapshot is not None:
            require(evm.rpc("evm_revert", [snapshot]) is True, "Anvil did not roll back a non-persisting entry")
        if snapshot is not None or observation["status"] != "returned":
            touched.clear()
            touched.update(saved)
    for observation in observations:
        observation.pop("block", None)
    return observations


# Comparisons, findings and reduction.

def comparable(observation: dict | None, deploy: bool) -> dict | None:
    if observation is None or observation.get("status") not in COMPLETED:
        return None
    keys = [key for key in COMPARED if not (deploy and key == "output")]
    return {key: observation.get(key) for key in keys}


def memory_range(observations: dict[str, dict]) -> dict[str, dict]:
    """Hull memory fails with Memory.overflowReason, before changing memory or its size, for a nonzero-length
    range ending beyond 2^256 - 32, which no EVM transaction can pay to expand. That failure is the Hull path's
    resource limit `memory-range` when every EVM path observed the entry stop at a resource limit; when one
    returned, reverted or halted otherwise, the EVM did not reach that access and the failure stays."""
    hull_observation = observations.get("hull") or {}
    evm = [observation.get("status") for path, observation in observations.items() if path != "hull"]
    if hull_observation.get("status") == "language-failure" and hull_observation.get("detail") == MEMORY_RANGE and \
            evm and all(status in RESOURCE for status in evm):
        return {**observations, "hull": {**hull_observation, "status": "memory-range"}}
    return observations


def agreement(observations: dict[str, dict], deploy: bool) -> dict:
    """Whether every completed path observed the same; resource limits are inconclusive."""
    values = {path: comparable(observation, deploy) for path, observation in observations.items()}
    compared = {path: value for path, value in values.items() if value is not None}
    groups: dict[str, list[str]] = {}
    for path, value in compared.items():
        groups.setdefault(json.dumps(value, sort_keys=True), []).append(path)
    fields = [key for key in COMPARED if len({json.dumps(value.get(key), sort_keys=True) for value in compared.values()}) > 1]
    inconclusive = sorted(path for path, observation in observations.items() if observation.get("status") in RESOURCE)
    failed = sorted(path for path, observation in observations.items()
                    if observation.get("status") not in COMPLETED + RESOURCE + UNRUN)
    if len(groups) > 1:
        status = "disagree"
    elif inconclusive or failed or len(compared) < len(observations):
        status = "incomplete" if compared else "unobserved"
    else:
        status = "agree"
    return {"status": status, "fields": fields, "groups": sorted(sorted(group) for group in groups.values()),
            "inconclusive": inconclusive, "failed": failed}


def expectation(step: dict, observation: dict | None, raw: bool) -> str:
    """Upstream's own check of one recorded step: exact bytes unless any payload is allowed."""
    if observation is None or observation.get("status") in RESOURCE:
        return "inconclusive"
    if observation.get("status") in UNRUN:
        return observation["status"]
    expected, status = step["expected"], observation.get("status")
    if expected["status"] == "returned":
        matched = status == "returned"
    else:
        matched = status == "reverted" or (raw and status == "exceptional")
    if matched and expected.get("output") is not None:
        matched = observation.get("output") == expected["output"]
    return "match" if matched else "mismatch"


def signature(kind: str, entry: dict, observations: dict[str, dict], raw: bool, path: str | None = None):
    """What a finding is, so that a reduced run can be checked to keep it."""
    deploy = entry["kind"] == "deploy"
    if kind == "path-mismatch":
        result = agreement(observations, deploy)
        return [kind, result["fields"], result["groups"]] if result["status"] == "disagree" else None
    observation = observations.get(path) or {}
    if kind == "expectation-mismatch":
        return [kind, path, observation.get("status")] if "mutant" not in entry and \
            expectation(entry, observation, raw) == "mismatch" else None
    status = observation.get("status")
    return [kind, path, status] if status not in COMPLETED + RESOURCE + UNRUN else None


def toward(recorded: int, mutated: int, attempt, spent) -> int:
    """Move a mutated value toward the recorded one while `attempt` keeps the finding:
    the nearest power-of-two distance first, then bisection inside it."""
    sign, distance = (1 if mutated > recorded else -1), abs(mutated - recorded)
    best, low, high = mutated, 0, distance.bit_length()
    while low < high and not spent():
        exponent = (low + high) // 2
        candidate = recorded + sign * min(2**exponent, distance)
        if candidate != best and attempt(candidate):
            best, high = candidate, exponent
        elif candidate == best:
            high = exponent
        else:
            low = exponent + 1
    near = recorded + sign * (2**(high - 1) if high else 0)
    while abs(best - near) > 1 and not spent():
        middle = (near + best) // 2
        if attempt(middle):
            best = middle
        else:
            near = middle
    return best


def entry_findings(fixture: dict, entry: dict, observations: dict[str, dict]) -> list[dict]:
    raw, found = fixture["mode"] == "raw", []
    base = {"fixture": fixture["id"], "entry": entry["id"], "step": entry["step"], "label": entry["label"]}
    if "mutant" in entry:
        base["mutant"] = entry["mutant"]
    for path, observation in observations.items():
        identity = signature("path-failure", entry, observations, raw, path)
        if identity:
            found.append({**base, "category": "path-failure", "path": path, "signature": identity,
                          "detail": observation.get("detail")})
        identity = signature("expectation-mismatch", entry, observations, raw, path)
        if identity:
            found.append({**base, "category": "expectation-mismatch", "path": path, "signature": identity,
                          "expected": entry["expected"], "observed": observation})
    identity = signature("path-mismatch", entry, observations, raw)
    if identity:
        found.append({**base, "category": "path-mismatch", "signature": identity,
                      "observations": {path: comparable(value, entry["kind"] == "deploy") or value
                                       for path, value in observations.items()}})
    return found


class FixtureRun:
    """One fixture: exports, the recorded steps and mutants on every admitted path."""

    def __init__(self, args, fixture: dict, identity: dict, builds: dict, deadline: float | None = None):
        self.args, self.fixture, self.identity, self.builds = args, fixture, identity, builds
        self.raw = fixture["mode"] == "raw"
        # The run's deadline; entries observe the fixture's own, which is never later.
        self.run_deadline = self.deadline = deadline
        self.record = {"schema": FIXTURE_SCHEMA, "id": fixture["id"], "mode": fixture["mode"],
                       "contract": fixture["contract"], "source": fixture["source"], "sha256": fixture["sha256"],
                       "exclusions": [], "findings": [], "admitted": [], "statuses": {}}

    def exclude(self, error: Excluded) -> None:
        self.record["exclusions"].append({"paths": list(error.paths), "stage": error.stage, "reason": error.reason,
                                          "detail": error.detail})
        if error.reason == "compiler-crash":
            self.record["findings"].append({"fixture": self.fixture["id"], "category": "compiler-crash",
                                            "paths": list(error.paths), "stage": error.stage, "detail": error.detail})

    def unexecuted(self) -> dict:
        """A fixture that the run's time budget or a stop signal left unstarted."""
        return {**self.record, "unexecuted": True, "stop": "signal" if STOP.is_set() else "run time budget"}

    @contextlib.contextmanager
    def locked(self):
        """Hold this fixture's export lock, so that a concurrent run never rewrites exports in use."""
        self.args.work.mkdir(parents=True, exist_ok=True)
        with (self.args.work / (self.fixture["id"] + ".lock")).open("a") as handle:
            fcntl.flock(handle, fcntl.LOCK_EX)
            yield

    def run(self) -> dict:
        started = time.monotonic()
        if self.args.fixture_seconds is not None:
            self.deadline = min(started + self.args.fixture_seconds, math.inf if self.run_deadline is None else self.run_deadline)
        try:
            with self.locked():
                self.execute()
        except Excluded as error:
            self.exclude(error)
        except (ValueError, KeyError, OSError, subprocess.SubprocessError, common.RpcError, urllib.error.URLError) as error:
            # A harness failure is neither an exclusion nor a finding; it fails the run.
            self.record["errors"] = [f"{type(error).__name__}: {error}"]
        self.record["seconds"] = round(time.monotonic() - started, 3)
        if any("budget" in seen for seen in self.record["statuses"].values()):
            self.record["stop"] = "signal" if STOP.is_set() else "run time budget" if stopped(self.run_deadline) \
                else "fixture time budget"
        return self.record

    def execute(self) -> None:
        source = (self.args.upstream / self.fixture["source"]).resolve()
        require(source.is_relative_to(self.args.upstream) and common.file_digest(source) == self.fixture["sha256"],
                "fixture differs from its pin: " + self.fixture["id"])
        exports = Exports(self.args, self.fixture, self.identity)
        prepared = exports.prepare(self.builds["directive"], self.builds.get("declaration"))
        for error in prepared["excluded"]:
            self.exclude(error)
        excluded = {path for error in prepared["excluded"] for path in error.paths}
        self.admitted = [path for path in PATHS if path not in excluded]
        self.record["admitted"] = list(self.admitted)
        self.record["exportSeconds"] = prepared["seconds"]
        self.record["exportsReused"] = prepared["reused"]
        try:
            self.steps, self.chain = build_steps(self.fixture, prepared["directives"], prepared["abi"], self.args)
        except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
            raise Excluded("directive-resolution", "unsupported-directive", str(error))
        self.prepared = prepared
        self.abi = prepared["abi"].get(self.fixture["contract"], [])
        self.derived = derived_methods(prepared["declarations"], self.fixture["contract"])
        if self.derived:
            self.record["derivedMethods"] = {"0x" + key.hex(): text for key, (text, _) in self.derived.items()}
        self.bytecode = {}
        for path, level in LEVELS.items():
            if path in self.admitted:
                document = prepared[level]["document"]
                self.bytecode[path] = (common.image_bytes(document, [self.fixture["contract"] + "Deploy"]),
                                       common.image_bytes(document, [self.fixture["contract"] + "Deploy", self.fixture["contract"]]))
        if "yul" in self.admitted:
            self.bytecode["yul"] = (prepared["yul"]["init"], prepared["yul"]["runtime"])
        if not self.admitted:
            return
        self.mutants = self.draw_mutants() if self.args.mode == "mutation" else {}
        entries = self.entries(self.steps[1:], self.mutants)
        self.record["steps"] = [{key: step[key] for key in ("index", "kind", "label", "calldata", "value", "caller",
                                                             "persist", "expected")} for step in self.steps]
        self.evm = Chain(self.args, self.chain) if any(path in EVM_PATHS for path in self.admitted) else None
        try:
            observed = self.observe(self.steps[0], entries)
            self.compare(entries, observed)
            if self.args.mode == "mutation":
                self.deploy_mutants()
            if not self.args.no_reduce:
                self.reduce_findings()
        finally:
            if self.evm is not None:
                self.record["anvil"] = self.evm.version
                self.evm.close()

    def draw_mutants(self) -> dict[int, list[tuple[int, dict]]]:
        """Each step's mutants with their draw numbers: the drawn ones, then every boundary Word of a
        derived layout's tags, dynamic offsets and `bytes` lengths, at most --derived-mutants of those
        per fixture. Over --fixture-mutants, a seeded uniform sample of that many keeps draw order and
        numbers."""
        drawn, sources, boundaries = {}, {}, []
        for step in self.steps:
            if step["kind"] == "deploy" and step["calldata"] == "0x" and step["value"] == 0:
                continue
            stream = Stream(derive(self.args.seed, self.fixture["id"], step["index"]))
            classes, origin = step_classes(step, self.abi, self.derived)
            sources[str(step["index"])] = origin
            drawn[step["index"]] = list(enumerate(sample(candidates(step, classes, stream), stream, self.args.mutants), 1))
            boundaries += [(step["index"], number, mutant) for number, mutant in
                           enumerate(exhaustive(step, classes), len(drawn[step["index"]]) + 1)]
        self.record["classification"] = sources
        if boundaries:
            limit = self.args.derived_mutants
            self.record["derivedMutants"] = {"limit": limit, "drawn": len(boundaries),
                                             "kept": min(limit, len(boundaries))}
            if len(boundaries) > limit:
                boundaries = seeded_subset(boundaries, limit, Stream(derive(self.args.seed, self.fixture["id"],
                                                                            "derived-boundary")))
            for index, number, mutant in boundaries:
                drawn[index].append((number, mutant))
        limit, order = self.args.fixture_mutants, [(index, number) for index, items in drawn.items() for number, _ in items]
        if limit is not None:
            self.record["mutantBudget"] = {"limit": limit, "drawn": len(order), "kept": min(limit, len(order))}
            if len(order) > limit:
                kept = set(seeded_subset(order, limit, Stream(derive(self.args.seed, self.fixture["id"], "mutant-budget"))))
                drawn = {index: [item for item in items if (index, item[0]) in kept] for index, items in drawn.items()}
        return drawn

    def entries(self, steps: list[dict], mutants: dict[int, list[tuple[int, dict]]]) -> list[dict]:
        result = []
        for step in steps:
            for number, mutant in mutants.get(step["index"], []):
                result.append({**apply(step, mutant), "id": f"{step['index']}.{number}", "step": step["index"],
                               "persist": False, "mutant": mutant})
            result.append({**step, "id": str(step["index"]), "step": step["index"]})
        return result

    def observe(self, deploy: dict, entries: list[dict]) -> dict[str, list[dict]]:
        """Run a deployment and its entries on every admitted path, the EVM paths before Hull, so that a time
        budget spent on Hull leaves them compared; a Hull memory-range failure is classified against the
        EVM paths' observations of the same entry."""
        observed = {}
        for path in sorted(self.admitted, key=lambda path: path == "hull"):
            if path == "hull":
                observed[path] = run_hull(self.args, self.fixture, self.prepared, self.chain, deploy, entries,
                                          self.deadline)
            else:
                init, runtime = self.bytecode[path]
                observed[path] = run_evm(self.evm, path, init, runtime, deploy, entries, self.deadline)
        for number in range(1 + len(entries)):
            classified = memory_range({path: rows[number] for path, rows in observed.items()})
            for path, rows in observed.items():
                rows[number] = classified[path]
        return observed

    def compare(self, entries: list[dict], observed: dict[str, list[dict]]) -> None:
        rows, counts = [], {"agree": 0, "disagree": 0, "incomplete": 0, "unobserved": 0}
        expectations = {path: dict.fromkeys(VERDICTS, 0) for path in self.admitted}
        deploy = {**self.steps[0], "id": "0", "step": 0}
        for number, entry in enumerate([deploy] + entries):
            observations = {path: observed[path][number] for path in self.admitted}
            self.tally(observations)
            result = agreement(observations, entry["kind"] == "deploy")
            counts[result["status"]] += 1
            row = {"id": entry["id"], "step": entry["step"], "agreement": result}
            if "mutant" in entry:
                row["mutant"] = entry["mutant"]
            else:
                row["expectation"] = {path: expectation(entry, observations[path], self.raw) for path in self.admitted}
                for path, verdict in row["expectation"].items():
                    expectations[path][verdict] += 1
            if result["status"] == "agree":
                row["observation"] = comparable(observations[self.admitted[0]], entry["kind"] == "deploy")
            else:
                row["observations"] = observations
            rows.append(row)
            self.record["findings"] += entry_findings(self.fixture, entry, observations)
        self.record["entries"] = rows
        self.record["counts"] = {**counts, "recorded": len(self.steps), "mutants": len(entries) + 1 - len(self.steps),
                                 "derivedBoundaries": sum(derived_boundary(entry.get("mutant")) for entry in entries)}
        self.record["expectations"] = expectations

    def tally(self, observations: dict[str, dict]) -> None:
        """Count each path's observed statuses, so that every resource limit stays visible."""
        for path, observation in observations.items():
            seen = self.record["statuses"].setdefault(path, {})
            seen[observation["status"]] = seen.get(observation["status"], 0) + 1

    def deploy_mutants(self) -> None:
        """Each mutant of a deployment with constructor bytes or value is its own fresh deployment."""
        rows = []
        for number, mutant in self.mutants.get(0, []):
            entry = {**apply(self.steps[0], mutant), "id": f"0.{number}", "step": 0, "mutant": mutant}
            observed = self.observe(entry, [])
            observations = {path: observed[path][0] for path in self.admitted}
            self.tally(observations)
            result = agreement(observations, True)
            self.record["counts"][result["status"]] += 1
            self.record["counts"]["mutants"] += 1
            row = {"id": entry["id"], "step": 0, "mutant": mutant, "agreement": result}
            row["observation" if result["status"] == "agree" else "observations"] = \
                comparable(observations[self.admitted[0]], True) if result["status"] == "agree" else observations
            rows.append(row)
            self.record["findings"] += entry_findings(self.fixture, entry, observations)
        self.record["entries"] += rows

    def reduce_findings(self) -> None:
        """Reduce each distinct finding within the run's deadline, not the fixture's own."""
        reduced: dict[str, str] = {}
        self.deadline = self.run_deadline
        for finding in self.record["findings"]:
            if "signature" not in finding:
                continue
            key = json.dumps(finding["signature"])
            if key in reduced:
                finding["reduction"] = {"status": "duplicate", "of": reduced[key]}
                continue
            if stopped(self.run_deadline):
                finding["reduction"] = {"status": "stopped", "detail": BUDGET["detail"]}
                continue
            reduced[key] = finding["entry"]
            try:
                finding["reduction"] = self.reduce(finding)
            except (Excluded, ValueError, KeyError, OSError, subprocess.SubprocessError, common.RpcError,
                    urllib.error.URLError) as error:
                finding["reduction"] = {"status": "failed", "detail": f"{type(error).__name__}: {error}"}

    def reduce(self, finding: dict) -> dict:
        """Fewer directives first, then the mutated input back toward the recorded one."""
        started, runs = time.monotonic(), 0
        step = self.steps[finding["step"]]
        target = {**(apply(step, finding["mutant"]) if "mutant" in finding else step), "id": finding["entry"],
                  "step": finding["step"]}
        if "mutant" in finding:
            target.update(persist=False if step["kind"] != "deploy" else True, mutant=finding["mutant"])

        def holds(prefix: list[dict], entry: dict) -> bool:
            nonlocal runs
            runs += 1
            if entry["kind"] == "deploy":
                observed = self.observe(entry, [])
                observations = {path: observed[path][0] for path in self.admitted}
            else:
                observed = self.observe(self.steps[0], prefix + [entry])
                observations = {path: observed[path][-1] for path in self.admitted}
            return signature(finding["category"], entry, observations, self.raw, finding.get("path")) == finding["signature"]

        def spent() -> bool:
            return runs >= self.args.reduction_runs or time.monotonic() - started >= self.args.reduction_seconds or \
                stopped(self.run_deadline)

        prefix = [{**item, "id": str(item["index"]), "step": item["index"]} for item in self.steps[1:finding["step"]]
                  if item["persist"]] if target["kind"] != "deploy" else []
        if not holds(prefix, target):
            return {"status": "stopped" if stopped(self.run_deadline) else "not-reproduced", "runs": runs}
        for item in reversed(list(prefix)):
            if spent():
                break
            trial = [other for other in prefix if other is not item]
            if holds(trial, target):
                prefix = trial
        mutant = finding.get("mutant")
        if mutant and mutant["operator"] in ("word", "seeded-word", "truncate", "extend-zero", "extend-ones"):
            words = mutant["operator"] in ("word", "seeded-word")
            key = "value" if words else "bytes"

            def attempt(value: int) -> bool:
                nonlocal mutant, target
                trial = {**mutant, key: hex(value) if words else value}
                candidate = {**target, **apply(step, trial), "mutant": trial}
                if not holds(prefix, candidate):
                    return False
                mutant, target = trial, candidate
                return True

            toward(int(mutant["recorded"], 16) if words else 0, int(mutant["value"], 16) if words else mutant["bytes"],
                   attempt, spent)
        return {"status": "stopped" if stopped(self.run_deadline) else "budget-exhausted" if spent() else "reduced",
                "runs": runs,
                "seconds": round(time.monotonic() - started, 3), "steps": [item["index"] for item in prefix],
                "calldata": target["calldata"], "value": target["value"], "mutant": mutant}


def check_tools(args) -> dict:
    """The pinned compiler checkout, tool receipts and binaries this run requires."""
    driver, image, directive = scenario.identities(args.upstream, args.target_dir)
    resolver = methods.resolver.checked_identity(args.upstream, args.target_dir)
    declaration = declarations.checked_identity(args.upstream, args.target_dir)
    version = subprocess.run([str(args.solc), "--version"], capture_output=True, text=True, timeout=30).stdout
    exporter.validate_version(version)
    return {"driver": driver, "image": image, "directive": directive, "resolver": resolver, "declaration": declaration,
            "solcVersion": version.strip()}


def summarize(records: list[dict]) -> dict:
    totals = {"fixtures": len(records), "admitted": {path: 0 for path in PATHS}, "agree": 0, "disagree": 0,
              "incomplete": 0, "unobserved": 0, "recorded": 0, "mutants": 0, "derivedBoundaries": 0, "findings": {},
              "exclusions": {}, "statuses": {}, "unexecuted": 0, "budgetStopped": 0}
    expectations = {path: dict.fromkeys(VERDICTS, 0) for path in PATHS}
    for record in records:
        if record.get("unexecuted"):
            totals["unexecuted"] += 1
        elif record.get("stop"):
            totals["budgetStopped"] += 1
        for path in record.get("admitted") or []:
            totals["admitted"][path] += 1
        for key in ("agree", "disagree", "incomplete", "unobserved", "recorded", "mutants", "derivedBoundaries"):
            totals[key] += (record.get("counts") or {}).get(key, 0)
        for path, verdicts in (record.get("expectations") or {}).items():
            for verdict, count in verdicts.items():
                expectations[path][verdict] += count
        for path, seen in (record.get("statuses") or {}).items():
            merged = totals["statuses"].setdefault(path, {})
            for status, count in seen.items():
                merged[status] = merged.get(status, 0) + count
        for finding in record["findings"]:
            totals["findings"][finding["category"]] = totals["findings"].get(finding["category"], 0) + 1
        for exclusion in record["exclusions"]:
            key = exclusion["stage"] + ":" + exclusion["reason"]
            totals["exclusions"][key] = totals["exclusions"].get(key, 0) + 1
    totals["expectations"] = expectations
    return totals


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="fresh directory for the report; required unless --list or --check")
    parser.add_argument("--mode", choices=("fixed", "mutation"), default="fixed")
    parser.add_argument("--seed", type=int, help="root seed of a mutation run")
    parser.add_argument("--mutants", type=int, default=MUTANTS_PER_STEP, help="mutants drawn per recorded step")
    parser.add_argument("--derived-mutants", type=int, default=DERIVED_MUTANTS,
                        help="at most this many boundary mutants of derived layouts per fixture, a seeded sample")
    parser.add_argument("--fixture", action="append", default=[], help="fixture id glob; repeatable")
    parser.add_argument("--fixture-mutants", type=int, help="at most this many mutants per fixture, a seeded sample of those drawn")
    parser.add_argument("--fixture-seconds", type=float, help="wall time per fixture; entries reached later are not run")
    parser.add_argument("--seconds", type=float, help="wall time of the run; later fixtures do not start and later entries do not run")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--work", type=Path, default=ROOT / ".upstream/semantic-fixtures")
    parser.add_argument("--reuse-exports", action="store_true", help="reuse exports made by the same tools")
    parser.add_argument("--no-reduce", action="store_true")
    parser.add_argument("--reduction-runs", type=int, default=REDUCTION_RUNS)
    parser.add_argument("--reduction-seconds", type=float, default=REDUCTION_SECONDS)
    parser.add_argument("--timeout", type=float, default=300, help="per export process")
    parser.add_argument("--hull-timeout", type=float, default=HULL_TIMEOUT,
                        help="per Lean Core invocation of a raw scenario or a deployment")
    parser.add_argument("--hull-entry-timeout", type=float, default=HULL_ENTRY_TIMEOUT,
                        help="per Lean Core invocation of one method entry")
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--hull-runner", type=Path, default=ROOT / ".lake/build/bin/rust-hull-scenario")
    parser.add_argument("--solc", type=Path, default=Path(shutil.which("solc") or "/opt/homebrew/bin/solc"))
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--cast", type=Path, default=Path(shutil.which("cast") or "cast"))
    parser.add_argument("--list", action="store_true", help="print the pinned inventory and exit")
    parser.add_argument("--check", action="store_true", help="check the tools a run reads, print their identity and exit")
    args = parser.parse_args(argv)
    run_deadline = None if args.seconds is None else time.monotonic() + args.seconds
    if args.mode == "mutation" and args.seed is None:
        parser.error("a mutation run requires --seed")
    if args.mode == "fixed" and args.seed is not None:
        parser.error("--seed applies only to a mutation run")
    if not 1 <= args.mutants <= 64 or not 0 <= args.derived_mutants <= 4096 or not 1 <= args.jobs <= 16 or \
            args.reduction_runs < 1 or \
            min(args.timeout, args.hull_timeout, args.hull_entry_timeout, args.reduction_seconds) <= 0:
        parser.error("invalid mutation, job, time or reduction bounds")
    if args.fixture_mutants is not None and (args.mode != "mutation" or args.fixture_mutants < 1):
        parser.error("--fixture-mutants needs a mutation run and a positive budget")
    if any(value is not None and value <= 0 for value in (args.fixture_seconds, args.seconds)):
        parser.error("time budgets must be positive")
    if args.output is None and not (args.list or args.check):
        parser.error("--output is required unless --list or --check is given")
    for key in ("output", "work", "upstream", "target_dir", "hull_runner", "solc", "anvil", "cast"):
        if getattr(args, key) is not None:
            setattr(args, key, getattr(args, key).resolve())
    fixtures = [item for item in inventory() if not args.fixture or
                any(fnmatch.fnmatchcase(item["id"], pattern) for pattern in args.fixture)]
    require(fixtures, "no pinned fixture matched")
    if args.list:
        for item in fixtures:
            print(item["id"], item["mode"], item["contract"], item["calls"])
        return 0
    if args.check:
        builds = check_tools(args)
        print(json.dumps({"schema": SCHEMA + "/check", "status": "ready", "tools": tool_identity(args), "builds": builds,
                          "manifests": {name: common.file_digest(ROOT / "scripts" / name) for name, _ in MANIFESTS},
                          "fixtures": [item["id"] for item in fixtures]}, sort_keys=True))
        return 0
    require(not args.output.exists() or not any(args.output.iterdir()), "the output directory must be fresh")
    require(args.work.is_relative_to((ROOT / ".upstream").resolve()), "the export cache must stay inside .upstream")
    builds = check_tools(args)
    identity = tool_identity(args)
    (args.output / "fixtures").mkdir(parents=True, exist_ok=True)
    report = {"schema": SCHEMA, "comparison": COMPARISON, "coreReference": False,
              "upstreamCommit": common.UPSTREAM_COMMIT, "backendRevision": common.BACKEND_COMMIT,
              "paths": {"hull": "checked Hull on Lean Core with Sonatina O0 code images",
                        "sonatina-o0": "Sonatina O0 code images on Anvil", "sonatina-o2": "Sonatina O2 code images on Anvil",
                        "yul": "the driver's Yul compiled by solc " + exporter.SOLC_VERSION + " on Anvil"},
              "environment": ENVIRONMENT, "mode": args.mode, "seed": args.seed,
              "mutantsPerStep": args.mutants if args.mode == "mutation" else 0,
              "derivedMutants": args.derived_mutants if args.mode == "mutation" else 0,
              "bounds": {"exportSeconds": args.timeout, "hullSeconds": args.hull_timeout,
                         "hullEntrySeconds": args.hull_entry_timeout, "reductionRuns": args.reduction_runs,
                         "reductionSeconds": args.reduction_seconds, "fixtureMutants": args.fixture_mutants,
                         "fixtureSeconds": args.fixture_seconds, "runSeconds": args.seconds},
              "selection": args.fixture, "tools": identity, "builds": builds, "started": time.time()}
    lock = threading.Lock()
    records = []

    def one(fixture: dict) -> dict:
        run = FixtureRun(args, fixture, identity, builds, run_deadline)
        record = run.unexecuted() if stopped(run_deadline) else run.run()
        with lock:
            (args.output / "fixtures" / (fixture["id"] + ".json")).write_text(json.dumps(record, indent=1) + "\n")
            counts = record.get("counts", {})
            print(f"{fixture['id']}: admitted {','.join(record['admitted']) or '-'}; agree {counts.get('agree', 0)}, "
                  f"disagree {counts.get('disagree', 0)}, incomplete {counts.get('incomplete', 0)}; "
                  f"findings {len(record['findings'])}; {record.get('seconds', 0)} s"
                  + (f"; stopped by the {record['stop']}" if record.get("stop") else ""), flush=True)
        return {key: record.get(key) for key in ("id", "mode", "contract", "admitted", "exclusions", "findings", "counts",
                                                 "expectations", "statuses", "errors", "seconds", "exportSeconds",
                                                 "exportsReused", "mutantBudget", "derivedMutants", "stop", "unexecuted")}

    # A stop signal ends the run at the next entry and still writes the report.
    STOP.clear()
    previous = signal.signal(signal.SIGTERM, lambda *_: STOP.set())
    try:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            records = list(pool.map(one, fixtures))
    finally:
        signal.signal(signal.SIGTERM, previous)
    report["finished"] = time.time()
    report["stop"] = "signal" if STOP.is_set() else \
        "run time budget" if any(record.get("stop") == "run time budget" for record in records) else None
    report["toolsUnchanged"] = tool_identity(args) == identity
    report["fixtures"] = records
    report["exclusions"] = [{"fixture": record["id"], **item} for record in records for item in record["exclusions"]]
    report["findings"] = [finding for record in records for finding in record["findings"]]
    report["errors"] = [{"fixture": record["id"], "detail": item} for record in records for item in record.get("errors") or []]
    report["totals"] = summarize(records)
    (args.output / "report.json").write_text(json.dumps(report, indent=1) + "\n")
    totals = report["totals"]
    print(f"{totals['fixtures']} fixtures; admitted {totals['admitted']}; {totals['agree']} agree, "
          f"{totals['disagree']} disagree, {totals['incomplete']} incomplete; findings {totals['findings']}; "
          f"harness errors {len(report['errors'])}; budget-stopped {totals['budgetStopped']}, "
          f"unexecuted {totals['unexecuted']}; tools unchanged: {report['toolsUnchanged']}")
    if STOP.is_set():
        return 130
    return 0 if report["toolsUnchanged"] and not report["findings"] and not report["errors"] else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print("semantic-fixtures: interrupted", file=sys.stderr)
        raise SystemExit(130)
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(f"semantic-fixtures: {error}", file=sys.stderr)
        raise SystemExit(2)
