#!/usr/bin/env python3
"""Check the fixed memory value corpus using fresh native Core executions.

The corpus takes, from seed 1 upwards at the default budget, every generated
plan that covers a missing required memory value shape, each at the eight
primitive boundary inputs, except a plan whose loop writes a bytes value or
slice, which Sonatina O0 can miscompile; every shape value is required but
the indices `put:counter` and `put8:counter`, which only such loops have.
This test rebuilds that selection, admits every plan with its own scope walk,
recomputes every shape and the shrink measure from the plan alone, re-emits
the source and compares it exactly, evaluates every case's plan with its own
byte-list model of std's memory values, range checks and Keccak-256 against
the recorded Core outcome, and replays, observes and shrinks natively. It
neither compiles Rust nor executes an EVM.
"""
from __future__ import annotations

import argparse
import copy
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("memory_corpus_pure", ROOT / "Tests/scripts/test-semantic-corpus.py")
pure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pure)
generic_spec = importlib.util.spec_from_file_location("memory_corpus_generic",
                                                      ROOT / "Tests/scripts/test-semantic-generic-corpus.py")
generic = importlib.util.module_from_spec(generic_spec)
generic_spec.loader.exec_module(generic)
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
VERSIONS = pure.VERSIONS + ("profileVersion", "boundaryVersion")
BOUNDARIES = (0, 1, 2, 255, 256, (1 << 256) - 1, 1 << 255, (1 << 255) - 1)
CASE_SCHEMA = "solcore-lean.semantic-memory-value-case.v1"
PLAN_SCHEMA = "solcore-lean.memory-value-plan.v1"
PROFILE = "runtime-memory-values"
NAME = "SynthesizedMemoryValues"
NODES = 1024
CASE_LIMIT = 5120
SHRINK_BYTES = 1_500_000
OUT_OF_BOUNDS = "0xb4120f14"
M = 1 << 256
INDICES = sorted(f"{access}:{kind}" for access in ("byte", "element", "put", "put8", "set", "word")
                 for kind in ("counter", "input", "literal"))
SHAPES = {
    "values": ["alias:array", "alias:bytes", "array:allocated", "array:literal", "bytes", "slice"],
    "parts": ["concat:bytes", "concat:slice", "concat:word", "concat:zeros", "to_bytes:bytes", "to_bytes:slice",
              "to_bytes:word", "to_bytes:zeros"],
    "cuts": ["drop:bytes", "drop:slice", "take:bytes", "take:slice", "window:bytes", "window:slice"],
    "writes": ["array:helper", "array:inline", "bytes:byte:helper", "bytes:byte:inline", "bytes:word:helper",
               "bytes:word:inline", "slice:byte:helper", "slice:byte:inline", "slice:word:helper", "slice:word:inline"],
    "observations": ["byte:bytes", "byte:slice", "element:get", "element:index", "hash:bytes", "hash:slice",
                     "length:bytes", "length:slice", "word:bytes", "word:slice"],
    "indices": INDICES,
    "hazards": ["alias", "copy", "helper", "view"],
    "loops": ["nested:counter", "nested:input", "none", "single:1", "single:3", "single:7"],
    "body": ["array", "bytes", "observe", "slice", "write"],
    "hashes": ["0", "1-31", "128", "32", "33-63", "64", "65-95", "96", "97-127"]}
# The fixed corpus skips the only plans with these values.
UNREQUIRED = {"indices": ["put:counter", "put8:counter"]}
REQUIRED = {dimension: [value for value in values if value not in UNREQUIRED.get(dimension, [])]
            for dimension, values in SHAPES.items()}
LIMITS = {"bytes": 4, "slice": 3, "array": 2}
SHIFTS, SCALES, FOLD_CONSTANTS = (0, 1, 3, 8, 128, 252), (1, 2, 3, 11, 32), tuple(range(3, 32, 2))
HELPERS = ("sc_word", "sc_byte", "sc_put", "sc_put8", "sc_aput")


# --- Keccak-256, the Ethereum variant --------------------------------------------

_RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B,
       0x0000000080000001, 0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088,
       0x0000000080008009, 0x000000008000000A, 0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
       0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
       0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
_ROT = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]
_MASK = (1 << 64) - 1


def _rol(value, shift):
    shift %= 64
    return ((value << shift) | (value >> (64 - shift))) & _MASK if shift else value


def keccak256(data: bytes) -> int:
    message = bytearray(data) + b"\x01"
    while len(message) % 136:
        message.append(0)
    message[-1] |= 0x80
    state = [[0] * 5 for _ in range(5)]
    for offset in range(0, len(message), 136):
        for i in range(17):
            state[i % 5][i // 5] ^= int.from_bytes(message[offset + 8 * i:offset + 8 * i + 8], "little")
        for rc in _RC:
            c = [state[x][0] ^ state[x][1] ^ state[x][2] ^ state[x][3] ^ state[x][4] for x in range(5)]
            d = [c[(x - 1) % 5] ^ _rol(c[(x + 1) % 5], 1) for x in range(5)]
            a = [[state[x][y] ^ d[x] for y in range(5)] for x in range(5)]
            b = [[0] * 5 for _ in range(5)]
            for x in range(5):
                for y in range(5):
                    b[y][(2 * x + 3 * y) % 5] = _rol(a[x][y], _ROT[x][y])
            state = [[b[x][y] ^ ((~b[(x + 1) % 5][y]) & b[(x + 2) % 5][y]) for y in range(5)] for x in range(5)]
            state[0][0] ^= rc
    return int.from_bytes(b"".join(state[i % 5][i // 5].to_bytes(8, "little") for i in range(4)), "big")


# --- Variables and the scope ------------------------------------------------------

def ref_of(name):
    require(isinstance(name, str), "a memory value variable is a name")
    for prefix, kind in (("sc_b", "bytes"), ("sc_s", "slice"), ("sc_a", "array")):
        if name.startswith(prefix):
            digits = name[len(prefix):]
            require(digits.isdecimal() and str(int(digits)) == digits, "noncanonical memory value variable")
            return kind, int(digits)
    raise ValueError("unknown memory value variable")


class Scope:
    """Declared variables by kind and number, `None` once out of scope, and the
    values: `(is_array, length)` in creation order."""

    def __init__(self):
        self.vars = {"bytes": [], "slice": [], "array": []}
        self.objects = []

    def copy(self):
        other = Scope()
        other.vars = {kind: list(values) for kind, values in self.vars.items()}
        other.objects = list(self.objects)
        return other

    def var(self, name):
        kind, number = ref_of(name)
        entries = self.vars[kind]
        require(number < len(entries) and entries[number] is not None, "a variable is not in scope")
        return kind, entries[number]

    def declare(self, kind, entry):
        require(len(self.vars[kind]) < LIMITS[kind], f"too many {kind} declarations")
        self.vars[kind].append(entry)

    def close(self, outer):
        for kind in self.vars:
            self.vars[kind] = outer.vars[kind] + [None] * (len(self.vars[kind]) - len(outer.vars[kind]))


def check_operand(operand, in_loop):
    require(isinstance(operand, dict), "an operand is an object")
    kind = operand.get("operand")
    if kind in ("input", "acc"):
        require(set(operand) == {"operand"}, "an operand has extra fields")
    elif kind == "counter":
        require(set(operand) == {"operand"} and in_loop, "the position is a Word only in a loop")
    else:
        require(kind in ("add", "mul", "xor") and set(operand) == {"operand", "constant"}
                and type(operand["constant"]) is int, "unknown operand")
        low = 2 if kind == "mul" else 1
        require(low <= operand["constant"] <= 255, "operand constant out of range")


def check_index(index, in_loop, valid):
    require(isinstance(index, dict) and valid >= 1, "an index needs an in-range position")
    kind = index.get("index")
    if kind == "literal":
        require(set(index) == {"index", "value"} and type(index["value"]) is int and 0 <= index["value"] < valid,
                "a literal index is in range")
    elif kind == "input":
        require(set(index) == {"index", "shift", "modulus"} and index["shift"] in SHIFTS
                and type(index["modulus"]) is int and 1 <= index["modulus"] <= valid + 8, "invalid input index")
    else:
        require(kind == "counter" and set(index) == {"index", "scale", "offset"} and in_loop
                and index["scale"] in SCALES and type(index["offset"]) is int and 0 <= index["offset"] <= 8,
                "invalid position index")


def part_length(part, scope, in_loop):
    kind = part.get("part")
    if kind == "word":
        require(set(part) == {"part", "operand"}, "invalid word part")
        check_operand(part["operand"], in_loop)
        return 32
    if kind == "zeros":
        require(set(part) == {"part", "count"} and type(part["count"]) is int and 0 <= part["count"] <= 40,
                "invalid zeros part")
        return part["count"]
    require(kind == "value" and set(part) == {"part", "value"}, "unknown part")
    ref_kind, entry = scope.var(part["value"])
    require(ref_kind != "array", "an array is not a part")
    return entry[2]


def width_valid(width, length):
    if width == "word":
        return length - 31 if length >= 32 else 0
    return length


def step_scope(scope, action, in_loop):
    """Admit one action against the scope and return the next scope."""
    require(isinstance(action, dict), "an action is an object")
    kind = action.get("kind")
    scope = scope.copy()
    if kind == "bytes":
        require(set(action) == {"kind", "build", "parts"}, "invalid bytes action")
        parts = action["parts"]
        require((action["build"], len(parts)) in (("to_bytes", 1), ("concat", 2)), "invalid build")
        length = sum(part_length(part, scope, in_loop) for part in parts)
        require(length <= 128, "a value over 128 bytes")
        scope.objects.append((False, length))
        scope.declare("bytes", (len(scope.objects) - 1, 0, length))
    elif kind == "slice":
        source_kind, (value, start, length) = scope.var(action.get("source"))
        require(source_kind != "array", "a slice of an array")
        cut = action.get("cut")
        if cut == "drop":
            require(set(action) == {"kind", "source", "cut", "start"} and 0 <= action["start"] <= length, "invalid drop")
            entry = (value, start + action["start"], length - action["start"])
        elif cut == "take":
            require(set(action) == {"kind", "source", "cut", "length"} and 0 <= action["length"] <= length, "invalid take")
            entry = (value, start, action["length"])
        else:
            require(cut == "window" and set(action) == {"kind", "source", "cut", "start", "length"}
                    and action["start"] >= 0 and action["length"] >= 0
                    and action["start"] + action["length"] <= length, "invalid window")
            entry = (value, start + action["start"], action["length"])
        scope.declare("slice", entry)
    elif kind == "alias":
        require(set(action) == {"kind", "source"} and not in_loop, "an alias is a top-level action")
        source_kind, entry = scope.var(action["source"])
        require(source_kind != "slice", "a slice has no second variable")
        scope.declare(source_kind, entry)
    elif kind == "array":
        require(set(action) == {"kind", "form", "elements"} and action["form"] in ("literal", "allocated")
                and isinstance(action["elements"], list) and 1 <= len(action["elements"]) <= 4, "invalid array")
        for element in action["elements"]:
            check_operand(element, in_loop)
        scope.objects.append((True, len(action["elements"])))
        scope.declare("array", (len(scope.objects) - 1, 0, len(action["elements"])))
    elif kind == "write":
        require(set(action) == {"kind", "target", "index", "value", "width", "form"}
                and action["width"] in ("word", "byte") and action["form"] in ("inline", "helper"), "invalid write")
        target_kind, entry = scope.var(action["target"])
        check_operand(action["value"], in_loop)
        if target_kind == "array":
            require(action["width"] == "word", "an element write has a Word")
            valid = entry[2]
        else:
            valid = width_valid(action["width"], entry[2])
        check_index(action["index"], in_loop, valid)
    else:
        require(kind == "observe" and set(action) == {"kind", "fold", "constant", "value", "access"}
                and action["fold"] in ("add", "xor") and action["constant"] in FOLD_CONSTANTS, "invalid action")
        value_kind, entry = scope.var(action["value"])
        access = action["access"]
        require(isinstance(access, dict), "an access is an object")
        name = access.get("access")
        if name in ("length", "hash"):
            require(set(access) == {"access"} and value_kind != "array", "invalid access")
        elif name in ("word", "byte"):
            require(set(access) == {"access", "index"} and value_kind != "array", "invalid access")
            check_index(access["index"], in_loop, width_valid(name, entry[2]))
        else:
            require(name == "element" and set(access) == {"access", "index", "form"} and value_kind == "array"
                    and access["form"] in ("get", "index"), "invalid access")
            check_index(access["index"], in_loop, entry[2])
    return scope


def loop_trips(loop):
    return loop["mask"] if loop["form"] == "single" else loop["outer"] * loop["inner"]


def check_plan(plan):
    require(isinstance(plan, dict) and set(plan) == {"schema", "steps"} and plan["schema"] == PLAN_SCHEMA,
            "unexpected memory value plan schema")
    steps = plan["steps"]
    require(isinstance(steps, list) and 1 <= len(steps) <= 10, "a memory value plan has one to ten steps")
    scope, loops, hashes, observes = Scope(), 0, 0, 0
    for step in steps:
        require(isinstance(step, dict), "a step is an object")
        if set(step) == {"action"}:
            scope = step_scope(scope, step["action"], False)
            hashes += step["action"]["kind"] == "observe" and step["action"]["access"]["access"] == "hash"
            observes += step["action"]["kind"] == "observe"
            continue
        require(set(step) == {"loop", "body"}, "a step is an action or a loop")
        loops += 1
        loop, body = step["loop"], step["body"]
        if loop.get("form") == "single":
            require(set(loop) == {"form", "mask"} and loop["mask"] in (1, 3, 7), "invalid single loop")
        else:
            require(loop.get("form") == "nested" and set(loop) == {"form", "outer", "bound", "inner"}
                    and loop["outer"] in (1, 3) and loop["inner"] in (1, 3) and loop["bound"] in ("input", "counter"),
                    "invalid nested loop")
        require(isinstance(body, list) and 1 <= len(body) <= 3, "a loop has one to three actions")
        inner = scope
        for action in body:
            inner = step_scope(inner, action, True)
            hashes += loop_trips(loop) * (action["kind"] == "observe" and action["access"]["access"] == "hash")
            observes += action["kind"] == "observe"
        inner.close(scope)
        scope = inner
    require(loops <= 1 and observes >= 1 and hashes <= 7, "loop, observation or hash bounds")
    return plan


# --- Shapes, from the plan alone --------------------------------------------------

def hash_class(length):
    for bound, name in ((0, "0"), (31, "1-31"), (32, "32"), (63, "33-63"), (64, "64"), (95, "65-95"), (96, "96"),
                        (127, "97-127")):
        if length <= bound:
            return name
    return "128"


def shapes(plan):
    found = {dimension: set() for dimension in SHAPES}
    writes, copies = [], []  # (value, variable name, helper); (copy, source, writes to the source before it)
    scope = Scope()

    def trace(action, scope):
        kind = action["kind"]
        if kind == "bytes":
            found["values"].add("bytes")
            form = "to_bytes" if action["build"] == "to_bytes" else "concat"
            for part in action["parts"]:
                found["parts"].add(form + ":" + (part["part"] if part["part"] != "value" else ref_of(part["value"])[0]))
                if part["part"] == "value":
                    source = scope.var(part["value"])[1][0]
                    copies.append((len(scope.objects), source, sum(1 for write in writes if write[0] == source)))
        elif kind == "slice":
            found["values"].add("slice")
            found["cuts"].add(action["cut"] + ":" + ref_of(action["source"])[0])
        elif kind == "alias":
            found["values"].add("alias:" + ref_of(action["source"])[0])
        elif kind == "array":
            found["values"].add("array:" + action["form"])
        elif kind == "write":
            target_kind, entry = scope.var(action["target"])
            if target_kind == "array":
                found["writes"].add("array:" + action["form"])
                access = "set"
            else:
                found["writes"].add(f"{target_kind}:{action['width']}:{action['form']}")
                access = "put" if action["width"] == "word" else "put8"
            found["indices"].add(access + ":" + action["index"]["index"])
            writes.append((entry[0], action["target"], action["form"] == "helper"))
        else:
            value_kind, entry = scope.var(action["value"])
            access = action["access"]
            name = access["access"]
            if name == "element":
                found["observations"].add("element:" + access["form"])
            else:
                found["observations"].add(name + ":" + value_kind)
            if "index" in access:
                found["indices"].add(name + ":" + access["index"]["index"])
            if name == "hash":
                found["hashes"].add(hash_class(entry[2]))
            for value, writer, helper in writes:
                if value != entry[0]:
                    continue
                if writer != action["value"]:
                    found["hazards"].add("view" if "slice" in (ref_of(writer)[0], value_kind) else "alias")
                if helper:
                    found["hazards"].add("helper")
            if any(copy == entry[0] and sum(1 for write in writes if write[0] == source) > before
                   for copy, source, before in copies):
                found["hazards"].add("copy")

    loops = []
    for step in plan["steps"]:
        if "action" in step:
            trace(step["action"], scope)
            scope = step_scope(scope, step["action"], False)
            continue
        loop = step["loop"]
        loops.append(f"single:{loop['mask']}" if loop["form"] == "single" else f"nested:{loop['bound']}")
        inner = scope
        for action in step["body"]:
            found["body"].add(action["kind"])
            trace(action, inner)
            inner = step_scope(inner, action, True)
        inner.close(scope)
        scope = inner
    found["loops"] = set(loops) if loops else {"none"}
    return found


def skipped(plan):
    """A loop that writes a bytes value or slice; the fixed corpus skips it."""
    return any("loop" in step and any(action["kind"] == "write" and ref_of(action["target"])[0] != "array"
                                      for action in step["body"]) for step in plan["steps"])


# --- The plan's size, as the shrink measure counts it -----------------------------

def plan_size(plan):
    """Constructors, then the sum of numeric literals, independently."""
    def operand(o):
        return (1, 0) if o["operand"] == "input" else (2, o.get("constant", 0))

    def index(i):
        return {"literal": lambda: (1, i["value"]), "input": lambda: (2, i["shift"] + i["modulus"]),
                "counter": lambda: (2, i["scale"] + i["offset"])}[i["index"]]()

    def plus(*sizes):
        return (sum(size[0] for size in sizes), sum(size[1] for size in sizes))

    def part(p):
        if p["part"] == "word":
            return plus((1, 0), operand(p["operand"]))
        return (1, p["count"]) if p["part"] == "zeros" else (1, 0)

    def access(a):
        name = a["access"]
        if name == "length":
            return (1, 0)
        if name == "hash":
            return (2, 0)
        if name == "element":
            return plus((3 if a["form"] == "get" else 2, 0), index(a["index"]))
        return plus((2, 0), index(a["index"]))

    def action(a):
        kind = a["kind"]
        if kind == "bytes":
            build = (1, 0) if a["build"] == "to_bytes" else (2, 0)
            return plus((1, 0), build, *(part(p) for p in a["parts"]))
        if kind == "slice":
            cut = {"drop": lambda: (1, a.get("start", 0)), "take": lambda: (1, a.get("length", 0)),
                   "window": lambda: (2, a["start"] + a["length"])}[a["cut"]]()
            return plus((1, 0), cut)
        if kind == "alias":
            return (1, 0)
        if kind == "array":
            return plus((2 if a["form"] == "allocated" else 1, 0), *(operand(o) for o in a["elements"]))
        if kind == "write":
            return plus((2 if a["form"] == "helper" else 1, 0), index(a["index"]), operand(a["value"]))
        return plus((2 if a["fold"] == "xor" else 1, a["constant"]), access(a["access"]))

    total = (0, 0)
    for step in plan["steps"]:
        if "action" in step:
            total = plus(total, (1, 0), action(step["action"]))
        else:
            loop = step["loop"]
            shape = (1, loop["mask"]) if loop["form"] == "single" else (3, loop["outer"] + loop["inner"])
            total = plus(total, (1, 0), shape, *(plus((1, 0), action(a)) for a in step["body"]))
    return total[0] * (1 << 16) + total[1]


# --- The source, re-emitted --------------------------------------------------------

def operand_text(o, position):
    kind = o["operand"]
    return {"input": "sc_x", "acc": "sc_r", "counter": position}.get(kind) or \
        f"(sc_x {'+' if kind == 'add' else '*' if kind == 'mul' else '^'} {o['constant']})"


def index_text(i, position):
    if i["index"] == "literal":
        return str(i["value"])
    if i["index"] == "input":
        return f"mod(shr({i['shift']}, sc_x), {i['modulus']})"
    scaled = position if i["scale"] == 1 else f"({position} * {i['scale']})"
    return scaled if i["offset"] == 0 else f"({scaled} + {i['offset']})"


def part_text(p, position):
    if p["part"] == "word":
        return f"bytes32({operand_text(p['operand'], position)})"
    return f"empty({p['count']})" if p["part"] == "zeros" else p["value"]


def action_lines(a, position, counts, used):
    kind = a["kind"]
    if kind == "bytes":
        parts = ", ".join(part_text(p, position) for p in a["parts"])
        line = f"let sc_b{counts['bytes']}: memory<bytes> = {a['build']}({parts});"
        counts["bytes"] += 1
        return [line]
    if kind == "slice":
        source = a["source"]
        cut = {"drop": lambda: f"slice_({source}, {a.get('start')})", "take": lambda: f"truncate({source}, {a.get('length')})",
               "window": lambda: f"truncate(slice_({source}, {a['start']}), {a['length']})"}[a["cut"]]()
        line = f"let sc_s{counts['slice']}: memory_ref = {cut};"
        counts["slice"] += 1
        return [line]
    if kind == "alias":
        source_kind = ref_of(a["source"])[0]
        if source_kind == "array":
            line = f"let sc_a{counts['array']}: memory<DynArray<uint256>> = {a['source']};"
        else:
            line = f"let sc_b{counts['bytes']}: memory<bytes> = {a['source']};"
        counts[source_kind] += 1
        return [line]
    if kind == "array":
        name = f"sc_a{counts['array']}"
        counts["array"] += 1
        words = [operand_text(o, position) for o in a["elements"]]
        if a["form"] == "allocated":
            return ([f"let {name}: memory<DynArray<uint256>> = allocateDynamicArray(@uint256, {len(words)});"] +
                    [f"IndexAccess.set({name}, uint256({k}), uint256({w}));" for k, w in enumerate(words)])
        return [f"let {name}: memory<DynArray<uint256>> = [{', '.join(f'uint256({w})' for w in words)}];"]
    if kind == "write":
        target, index = a["target"], index_text(a["index"], position)
        value = operand_text(a["value"], position)
        if ref_of(target)[0] == "array":
            if a["form"] == "inline":
                return [f"IndexAccess.set({target}, uint256({index}), uint256({value}));"]
            used.add("sc_aput")
            return [f"sc_aput({target}, {index}, {value});"]
        if a["form"] == "helper":
            helper = "sc_put" if a["width"] == "word" else "sc_put8"
            used.add(helper)
            return [f"{helper}({target}, {index}, {value});"]
        if a["width"] == "word":
            return [f"mstore(MemoryPointer.ptr(truncate(slice_({target}, {index}), 32)), {value});"]
        return [f"mstore8(MemoryPointer.ptr(truncate(slice_({target}, {index}), 1)), {value});"]
    access, value = a["access"], a["value"]
    name = access["access"]
    if name == "length":
        observed = f"MemorySize.len({value})"
    elif name == "hash":
        observed = f"Typedef.rep(keccak256_({value}))"
    elif name in ("word", "byte"):
        used.add("sc_" + name)
        observed = f"sc_{name}({value}, {index_text(access['index'], position)})"
    elif access["form"] == "get":
        observed = f"Typedef.rep(IndexAccess.get({value}, uint256({index_text(access['index'], position)})))"
    else:
        observed = f"Typedef.rep({value}[uint256({index_text(access['index'], position)})])"
    operator = "+" if a["fold"] == "add" else "^"
    return [f"sc_r = ((sc_r * {a['constant']}) {operator} {observed});"]


HELPER_LINES = {
    "sc_word": ["function sc_word<a>(sc_v: a, sc_i: word) returns (word) where a: MemorySize, a: MemoryPointer {",
                "    return mload(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 32)));", "}", ""],
    "sc_byte": ["function sc_byte<a>(sc_v: a, sc_i: word) returns (word) where a: MemorySize, a: MemoryPointer {",
                "    return shr(248, mload(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 1))));", "}", ""],
    "sc_put": ["function sc_put<a>(sc_v: a, sc_i: word, sc_w: word) returns (()) where a: MemorySize, a: MemoryPointer {",
               "    mstore(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 32)), sc_w);", "}", ""],
    "sc_put8": ["function sc_put8<a>(sc_v: a, sc_i: word, sc_w: word) returns (()) where a: MemorySize, a: MemoryPointer {",
                "    mstore8(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 1)), sc_w);", "}", ""],
    "sc_aput": ["function sc_aput(sc_a: memory<DynArray<uint256>>, sc_i: word, sc_w: word) returns (()) {",
                "    IndexAccess.set(sc_a, uint256(sc_i), uint256(sc_w));", "}", ""]}


def emitted_source(plan):
    counts, used, lines = {"bytes": 0, "slice": 0, "array": 0}, set(), []
    for step in plan["steps"]:
        if "action" in step:
            lines += action_lines(step["action"], "sc_counter", counts, used)
            continue
        loop = step["loop"]
        position = "sc_counter" if loop["form"] == "single" else "(sc_i + sc_j)"
        body = [line for action in step["body"] for line in action_lines(action, position, counts, used)]
        if loop["form"] == "single":
            lines += ([f"let sc_limit: word = (sc_x & {loop['mask']});", "let sc_counter: word = 0;",
                       "while (sc_limit > sc_counter) {"] + ["    " + line for line in body] +
                      ["    sc_counter = (sc_counter + 1);", "}"])
        else:
            bound = f"(sc_x & {loop['inner']})" if loop["bound"] == "input" else f"((sc_i + 1) & {loop['inner']})"
            lines += ([f"let sc_outer: word = (sc_x & {loop['outer']});", "let sc_i: word = 0;",
                       "let sc_inner: word = 0;", "let sc_j: word = 0;", "while (sc_outer > sc_i) {",
                       f"    sc_inner = {bound};", "    sc_j = 0;", "    while (sc_inner > sc_j) {"] +
                      ["        " + line for line in body] +
                      ["        sc_j = (sc_j + 1);", "    }", "    sc_i = (sc_i + 1);", "}"])
    source = (["import * from std;", "import * from std.dispatch;",
               "import { mload, mstore, mstore8, shr, mod } from std.opcodes;", ""] +
              [line for helper in HELPERS if helper in used for line in HELPER_LINES[helper]] +
              [f"contract {NAME} {{", "    function run(input: uint256) public returns (uint256) {",
               "        let sc_x: word = Typedef.rep(input);", "        let sc_r: word = 0;"] +
              ["        " + line for line in lines] + ["        return uint256(sc_r);", "    }", "}"])
    return "\n".join(source) + "\n"


# --- A byte-list model of std's memory values -------------------------------------

class OutOfBounds(Exception):
    pass


class Machine:
    def __init__(self, x):
        self.x, self.values, self.vars, self.counts = x, [], {}, {"bytes": 0, "slice": 0, "array": 0}
        self.acc, self.position = 0, 0

    def operand(self, o):
        kind = o["operand"]
        return {"input": lambda: self.x, "add": lambda: (self.x + o["constant"]) % M,
                "mul": lambda: (self.x * o["constant"]) % M, "xor": lambda: self.x ^ o["constant"],
                "acc": lambda: self.acc, "counter": lambda: self.position % M}[kind]()

    def index(self, i):
        if i["index"] == "literal":
            return i["value"]
        if i["index"] == "input":
            return (self.x >> i["shift"]) % i["modulus"]
        return (self.position * i["scale"] + i["offset"]) % M

    def declare(self, kind, entry):
        self.vars[(kind, self.counts[kind])] = entry
        self.counts[kind] += 1

    def view(self, name):
        return self.vars[ref_of(name)]

    def contents(self, name):
        value, start, length = self.view(name)
        return bytes(self.values[value][start:start + length])

    @staticmethod
    def check(length, position, width):
        # std's slice_(v, i) then truncate(·, width)
        if position > length or length - position < width:
            raise OutOfBounds

    def act(self, a):
        kind = a["kind"]
        if kind == "bytes":
            data = b"".join(self.operand(p["operand"]).to_bytes(32, "big") if p["part"] == "word"
                            else bytes(p["count"]) if p["part"] == "zeros" else self.contents(p["value"])
                            for p in a["parts"])
            self.values.append(bytearray(data))
            self.declare("bytes", (len(self.values) - 1, 0, len(data)))
        elif kind == "slice":
            value, start, length = self.view(a["source"])
            cut = a["cut"]
            self.declare("slice", (value, start + a["start"], length - a["start"]) if cut == "drop"
                         else (value, start, a["length"]) if cut == "take"
                         else (value, start + a["start"], a["length"]))
        elif kind == "alias":
            self.declare(ref_of(a["source"])[0], self.view(a["source"]))
        elif kind == "array":
            self.values.append([self.operand(o) for o in a["elements"]])
            self.declare("array", (len(self.values) - 1, 0, len(a["elements"])))
        elif kind == "write":
            value, start, length = self.view(a["target"])
            position, word = self.index(a["index"]), self.operand(a["value"])
            if ref_of(a["target"])[0] == "array":
                if position >= length:
                    raise OutOfBounds
                self.values[value][position] = word
            elif a["width"] == "word":
                self.check(length, position, 32)
                self.values[value][start + position:start + position + 32] = word.to_bytes(32, "big")
            else:
                self.check(length, position, 1)
                self.values[value][start + position] = word & 0xFF
        else:
            observed = self.access(a["value"], a["access"])
            scaled = self.acc * a["constant"] % M
            self.acc = (scaled + observed) % M if a["fold"] == "add" else scaled ^ observed

    def access(self, name, access):
        value, start, length = self.view(name)
        kind = access["access"]
        if kind == "length":
            return length
        if kind == "hash":
            return keccak256(self.contents(name))
        position = self.index(access["index"])
        if kind == "word":
            self.check(length, position, 32)
            return int.from_bytes(bytes(self.values[value][start + position:start + position + 32]), "big")
        if kind == "byte":
            self.check(length, position, 1)
            return self.values[value][start + position]
        if position >= length:
            raise OutOfBounds
        return self.values[value][position]

    def body(self, actions):
        counts = dict(self.counts)
        for a in actions:
            self.act(a)
        self.counts = counts

    def step(self, s):
        if "action" in s:
            self.act(s["action"])
            return
        loop, actions = s["loop"], s["body"]
        before = dict(self.counts)
        if loop["form"] == "single":
            for counter in range(self.x & loop["mask"]):
                self.position = counter
                self.body(actions)
        else:
            for i in range(self.x & loop["outer"]):
                for j in range((self.x & loop["inner"]) if loop["bound"] == "input" else ((i + 1) & loop["inner"])):
                    self.position = i + j
                    self.body(actions)
        for kind in before:
            self.counts[kind] = before[kind] + sum(
                1 for a in actions if (a["kind"] == kind) or (a["kind"] == "alias" and ref_of(a["source"])[0] == kind))


def model_outcome(plan, x):
    machine = Machine(x)
    try:
        for s in plan["steps"]:
            machine.step(s)
    except OutOfBounds:
        return {"stage": "execution", "status": "reverted", "output": OUT_OF_BOUNDS}
    return {"stage": "execution", "status": "returned", "word": str(machine.acc)}


def outcome(observation):
    """A completed Core outcome: a returned Word, or std's OutOfBounds() revert."""
    require(isinstance(observation, dict) and observation.get("stage") == "execution", "missing Core outcome")
    if observation.get("status") == "reverted":
        require(observation == {"stage": "execution", "status": "reverted", "output": OUT_OF_BOUNDS},
                "an out-of-range access must be std's OutOfBounds() revert")
        return "reverted"
    require(observation.get("status") == "returned", "original Core did not complete within the native budget")
    canonical_word(observation.get("word"))
    return observation["word"]


# --- Cases and the manifest ---------------------------------------------------------

def check_case(case, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected memory value case schema")
    plan = check_plan(case["memoryValuePlan"])
    number = canonical_word(case["input"])
    program = case["program"]
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == {"tag": "sum", "left": "word", "right": "unit"},
            "the memory value reference is a closed program returning a Word or an out-of-range access")
    require(generic.complexity(program["body"])[0] <= CASE_LIMIT, "reference exceeds the case limit")
    require(1 <= case["provenance"]["referenceNodes"] <= CASE_LIMIT, "recorded reference size exceeds the case limit")
    require(case["contract"] == {"name": NAME, "method": "run", "signature": "run(uint256)",
            "deployPath": [NAME + "Deploy"], "runtimePath": [NAME + "Deploy", NAME],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "memory value ABI, runtime input, or contract metadata changed")
    require(case.get("executionFuel") == fuel, "invalid execution fuel")
    require(case.get("source") == emitted_source(plan), "the emitted source differs from the plan's re-emission")
    recorded = case["provenance"]["memoryValueShapes"]
    require({dimension: set(values) for dimension, values in recorded.items()} == shapes(plan),
            "recorded memory value shapes differ from the plan")
    require(all(values == sorted(set(values)) for values in recorded.values()), "memory value shapes are not sorted")
    require(case["provenance"]["features"] == [], "the memory value profile records no G0 step features")
    require(model_outcome(plan, number) == case["directCore"],
            "the byte-list model differs from the recorded Core outcome")
    return plan


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals", "requiredInputs",
              "memoryValueRequirements", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == PROFILE, "unexpected memory value manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "memory value coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    require(manifest["requiredFeatures"] == [] and manifest["requiredWordLiterals"] == [],
            "the memory value corpus requires shapes, not step features or literals")
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "the memory value corpus must require all eight boundary inputs")
    require(manifest["memoryValueRequirements"] == REQUIRED,
            "the memory value corpus must require every shape value but the skipped loops' indices")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "the memory value corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"id", "generation", "input", "expectedFeatures"},
                "a memory value corpus entry is a generation recipe with its input")
        identifier = entry["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        require(canonical_word(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        require(entry["expectedFeatures"] == [], "memory value entries expect no step features")
        recipe = entry["generation"]
        require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
        require(canonical_word(recipe["seed"]) < 1 << 64 and recipe["maxProgramNodes"] == NODES,
                "fixed recipes use a uint64 seed and the default budget")
    return entries


def generated_plan(tool, seed, fuel):
    """The seed's plan, or None for an excluded seed."""
    corpus = run(tool, "memory-values-generate", str(seed), str(NODES), "1", "1", str(fuel))
    cases = corpus.get("cases")
    require(isinstance(cases, list) and len(cases) <= 1, "invalid generation response")
    return check_plan(cases[0]["memoryValuePlan"]) if cases else None


def selection(tool, fuel, last):
    """The roadmap's construction: from seed 1 upwards, every accepted seed
    whose plan covers a missing required value and has no bytes write in a
    loop, until nothing is missing."""
    missing = {dimension: set(values) for dimension, values in REQUIRED.items()}
    chosen = []
    for seed in range(1, last + 1):
        if not any(missing.values()):
            break
        plan = generated_plan(tool, seed, fuel)
        if plan is None or skipped(plan):
            continue
        found = shapes(plan)
        if any(missing[dimension] & found[dimension] for dimension in missing):
            chosen.append(seed)
            for dimension in missing:
                missing[dimension] -= found[dimension]
    require(not any(missing.values()), "seeds up to the last chosen one leave a requirement missing")
    return chosen


def materialize(entry, tool, fuel):
    recipe = entry["generation"]
    corpus = run(tool, "memory-values-generate", recipe["seed"], str(recipe["maxProgramNodes"]), "8", "1", str(fuel))
    require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
            and corpus.get("requested") == 8 and corpus.get("attempted") == 1
            and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 8,
            "fixed memory value seed did not emit eight cases in one attempt")
    cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
    require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
    case = cases[0]
    origin = case["provenance"]["origin"]
    require(origin == {"kind": "memory-generated", "seed": recipe["seed"], "maxProgramNodes": recipe["maxProgramNodes"],
                       "inputIndex": BOUNDARIES.index(int(entry["input"])), "validationFuel": fuel},
            "generated recipe differs from manifest")
    check_case(case, fuel)
    require(not skipped(case["memoryValuePlan"]), "a fixed plan writes a bytes value or slice in a loop")
    return case


def checked_shrinks(case, tool, directory, fuel):
    path = directory / "shrink-parent.json"
    path.write_text(json.dumps(case))
    reduced = run(tool, "shrink", str(path), "64", str(fuel))
    require(reduced == run(tool, "shrink", str(path), "64", str(fuel)), "native shrink order changed")
    candidates = reduced.get("cases")
    require(isinstance(candidates, list) and candidates, "fixed memory value case has no shrink candidate")
    require(sum(len(json.dumps(candidate, separators=(",", ":"))) for candidate in candidates) <= SHRINK_BYTES,
            "a shrink response exceeds its byte cap")
    parent = (plan_size(case["memoryValuePlan"]), int(case["input"]))
    seen = set()
    for candidate in candidates:
        check_case(candidate, fuel)
        require(candidate["provenance"]["origin"] == {"kind": "reduced", "parentPlan": case["memoryValuePlan"],
                                                      "parentInput": case["input"]},
                "a shrink candidate is not a reduction of its parent")
        require((plan_size(candidate["memoryValuePlan"]), int(candidate["input"])) < parent,
                "a shrink candidate is not strictly smaller")
        encoded = json.dumps([candidate["memoryValuePlan"], candidate["input"]], sort_keys=True)
        require(encoded not in seen, "duplicate canonical shrink")
        seen.add(encoded)
        target = directory / "shrunk.json"
        target.write_text(json.dumps(candidate))
        require(run(tool, "replay", str(target), str(fuel)) == candidate,
                "native shrink lost canonical source/program/provenance")
        fresh = run(tool, "observe", str(target), str(fuel))
        outcome(fresh)
        require(fresh == candidate["directCore"], "shrunk observation differs from fresh Core execution")
    return len(candidates)


def policy_checks(manifest, sample, tool, directory, fuel):
    count = 0

    def rejects(action, label):
        nonlocal count
        try:
            action()
        except (ValueError, KeyError, TypeError):
            count += 1
        else:
            raise ValueError("negative check accepted " + label)

    for field, value in (("profile", "runtime-traits"), ("requiredInputs", ["0"]), ("requiredFeatures", ["let"]),
                         *(("memoryValueRequirements", {**REQUIRED, dimension: REQUIRED[dimension][1:]})
                           for dimension in REQUIRED),
                         ("memoryValueRequirements", {**REQUIRED, "indices": INDICES})):
        changed = copy.deepcopy(manifest)
        changed[field] = value
        rejects(lambda: check_manifest(changed), field)
    plan = sample["memoryValuePlan"]
    first = plan["steps"][0]
    observe = {"action": {"kind": "observe", "fold": "add", "constant": 3, "value": "sc_b0", "access": {"access": "length"}}}
    loop = {"loop": {"form": "single", "mask": 1}, "body": [observe["action"]]}
    for label, broken in (("no steps", {**plan, "steps": []}), ("eleven steps", {**plan, "steps": plan["steps"] + [observe] * 11}),
                          ("two loops", {**plan, "steps": [first, loop, loop]}),
                          ("an unknown kind", {**plan, "steps": [{"action": {**first["action"], "kind": "free"}}]}),
                          ("a variable out of scope", {**plan, "steps": [{"action": {**observe["action"], "value": "sc_b7"}}]}),
                          ("an alias in a loop", {**plan, "steps": [first, {"loop": loop["loop"],
                                                                            "body": [{"kind": "alias", "source": "sc_b0"}]}]}),
                          ("no observation", {**plan, "steps": [first]})):
        rejects(lambda: check_plan(broken), label)
    path = directory / "negative.json"
    observing = next(index for index, step in enumerate(plan["steps"]) if "action" in step
                     and step["action"]["kind"] == "observe")
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("a fold constant", lambda value: value["memoryValuePlan"]["steps"][observing]["action"].update(
            constant=5 if value["memoryValuePlan"]["steps"][observing]["action"]["constant"] != 5 else 7)),
        ("a removed step", lambda value: value["memoryValuePlan"]["steps"].pop(observing)),
        ("an even fold constant", lambda value: value["memoryValuePlan"]["steps"][observing]["action"].update(constant=4)),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="1" if value["input"] != "1" else "2")),
        ("wrapper", lambda value: value["contract"].update(name="AnotherContract")),
        ("memory value shapes", lambda value: value["provenance"]["memoryValueShapes"].update(values=[])),
        ("generator version", lambda value: value["provenance"].update(generatorVersion="another-version")),
    ):
        changed = copy.deepcopy(sample)
        change(changed)
        path.write_text(json.dumps(changed))
        result = subprocess.run([str(tool), "replay", str(path), str(fuel)], cwd=ROOT,
                                text=True, capture_output=True, timeout=60, check=False)
        require(result.returncode != 0, "native replay accepted altered " + label)
        count += 1
    forged = copy.deepcopy(sample)
    forged["directCore"] = {"stage": "execution", "status": "returned", "word": "999"}
    path.write_text(json.dumps(forged))
    require(run(tool, "replay", str(path), str(fuel)) == sample, "native replay trusted saved execution evidence")
    count += 1
    path.write_text(json.dumps(sample))
    lower = run(tool, "replay", str(path), "0")
    require(lower["program"] == sample["program"] and lower["source"] == sample["source"]
            and lower["directCore"].get("status") == "out-of-fuel", "zero budget changed canonical code or invented completion")
    rejects(lambda: outcome(lower["directCore"]), "resource result as shape coverage")
    for args in (("memory-values-generate", str(1 << 64), "1024", "8", "1", str(fuel)),
                 ("memory-values-generate", "1", "2049", "8", "1", str(fuel)),
                 ("memory-values-generate", "1", "255", "8", "1", str(fuel)),
                 ("shrink", str(path), "4097", str(fuel))):
        result = subprocess.run([str(tool), *args], cwd=ROOT, text=True, capture_output=True, timeout=60, check=False)
        generated = result.returncode == 0 and json.loads(result.stdout).get("cases")
        require(result.returncode != 0 or not generated, "native CLI accepted an out-of-range budget")
        count += 1
    return count


def validate(manifest, tool, fuel):
    require(type(fuel) is int and 0 < fuel <= 10_000_000, "invalid positive execution fuel")
    entries = check_manifest(manifest)
    groups, seeds, inputs, samples = {}, [], set(), []
    found = {dimension: set() for dimension in SHAPES}
    reverted = 0
    with tempfile.TemporaryDirectory(prefix="memory-value-corpus-") as name:
        directory = Path(name)
        for entry in entries:
            case = materialize(entry, tool, fuel)
            require(case == materialize(entry, tool, fuel), "materialization is not deterministic")
            for version in VERSIONS:
                require(case["provenance"][version] == manifest[version], f"{version} changed")
            plan = check_case(case, fuel)
            path = directory / "case.json"
            path.write_text(json.dumps(case))
            before = run(tool, "observe", str(path), str(fuel))
            result = outcome(before)
            require(before == case["directCore"], "saved observation differs from fresh original Core")
            replayed = run(tool, "replay", str(path), str(fuel))
            require(replayed == case, "native canonical replay changed the case")
            reverted += result == "reverted"
            plan_key = json.dumps(plan, sort_keys=True)
            if plan_key not in groups:
                seeds.append(int(entry["generation"]["seed"]))
                samples.append(case)
            group = groups.setdefault(plan_key, {"inputs": set(), "source": case["source"], "results": set()})
            require(group["source"] == case["source"], "identical memory value plan emitted input-dependent source")
            group["inputs"].add(int(case["input"]))
            group["results"].add(result)
            # Only completed, replayed native cases contribute coverage.
            inputs.add(int(case["input"]))
            for dimension, values in shapes(plan).items():
                found[dimension] |= values
        require(inputs == set(BOUNDARIES), "lost completed input coverage")
        for dimension, values in REQUIRED.items():
            require(set(values) <= found[dimension], f"lost completed {dimension} coverage")
        for group in groups.values():
            require(group["inputs"] == set(BOUNDARIES), "memory value plan lacks a completed boundary input")
            require(len(group["results"]) > 1, "fixed memory value plan had one outcome for every boundary input")
        require(seeds == selection(tool, fuel, max(seeds)), "the corpus is not every covering seed in order")
        looped = next(case for case in samples if any("loop" in step for step in case["memoryValuePlan"]["steps"]))
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in [samples[0], looped])
        checks = policy_checks(manifest, samples[0], tool, directory, fuel)
    return {"status": "passed", "profile": PROFILE, "cases": len(entries), "plans": len(groups),
            "seeds": seeds, "outOfRange": reverted, "completedInputs": [str(value) for value in sorted(inputs)],
            "memoryValueCoverage": {"classification": "specified-by-the-plan-not-measured-memory-traffic",
                                    **{dimension: sorted(values) for dimension, values in found.items()}},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path,
                        default=ROOT / "scripts/semantic-memory-value-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
