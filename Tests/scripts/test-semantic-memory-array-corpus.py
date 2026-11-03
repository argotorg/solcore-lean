#!/usr/bin/env python3
"""Check the fixed memory array corpus using fresh native Core executions.

The corpus takes, from seed 1 upwards at the default budget, every generated
plan that covers a missing shape value, each at the eight primitive boundary
inputs; every value is required. This test rebuilds that selection, admits
every plan with its own walk over the element type, values, indices,
parameters and steps with their static bounds, recomputes every shape and the
shrink measure from the plan and its own interpreter, which runs arrays,
slices, grids and the storage array over Python lists with std's checks,
re-emits the source and compares it exactly, encodes the calldata and the
selectors from keccak256 of the signatures, evaluates every case's plan
against the recorded Core outcome, and replays, observes and shrinks
natively. It neither compiles Rust nor executes an EVM.
`test-semantic-array-abi-corpus.py` runs the same walk for the array ABI
corpus.
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


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


pure = load("array_corpus_pure", "Tests/scripts/test-semantic-corpus.py")
m2 = load("array_corpus_adapter", "scripts/semantic-differential.py")
storage = load("array_corpus_keccak", "scripts/semantic-storage-differential.py")
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
VERSIONS = ("generatorVersion", "profileVersion", "emitterVersion", "wrapperVersion", "boundaryVersion")
BOUNDARIES = tuple(int(value) for value in ("0", "1", "2", "255", "256", str(2**256 - 1), str(2**255), str(2**255 - 1)))
M = 2 ** 256
NODES = 1024
CASE_LIMIT = 4096
SHRINK_BYTES = 1_500_000
FOLD = 1099511628211
OPS = ("add", "sub", "mul", "div", "mod")
SYMBOLS = {"add": "+", "sub": "-", "mul": "*", "div": "/", "mod": "%"}
INDEX_SHIFTS = (0, 1, 2, 3, 8, 128, 253)
INDEX_MASKS = (1, 3, 7)
FLAG = 2 ** 255
ALLOCATION_LIMIT = 2 ** 251 - 1
MAX_STEPS, MAX_BOUND, MAX_ARRAYS, MAX_SLICES, MAX_GRIDS = 12, 8, 4, 3, 2
MAX_VALUES, MAX_INDICES, MAX_PARAMS, MAX_LITERAL, MAX_ROWS = 3, 3, 2, 4, 3
MAX_INDEX_LITERAL, LOOP_BOUND, MAX_BODY = 7, 4, 2
RETURN_WORDS = 2 + MAX_BOUND
PANIC = "4e487b71"
DIRTY = "6cc54a63"

MEMORY = {"profile": "runtime-memory-arrays", "schema": m2.MEMORY_ARRAY_CASE_SCHEMA,
          "planSchema": "solcore-lean.memory-array-plan.v1", "planKey": "memoryArrayPlan",
          "shapesKey": "memoryArrayShapes", "requirements": "memoryArrayRequirements",
          "command": "memory-arrays-generate", "origin": "memory-array-generated",
          "contract": "SynthesizedMemoryArrays", "manifest": "scripts/semantic-memory-array-corpus.json",
          "shapes": m2.MEMORY_ARRAY_SHAPES, "abi": False, "minimum": 256}
ABI = {"profile": "runtime-array-abi", "schema": m2.ARRAY_ABI_CASE_SCHEMA,
       "planSchema": "solcore-lean.array-abi-plan.v1", "planKey": "arrayAbiPlan",
       "shapesKey": "arrayAbiShapes", "requirements": "arrayAbiRequirements",
       "command": "array-abi-generate", "origin": "array-abi-generated",
       "contract": "SynthesizedArrayAbi", "manifest": "scripts/semantic-array-abi-corpus.json",
       "shapes": m2.ARRAY_ABI_SHAPES, "abi": True, "minimum": 512}


def required(profile):
    return {key: list(values) for key, values in profile["shapes"].items()}


class Type:
    """One of std's twelve integer types: its range, conversion of a Word and literals."""

    def __init__(self, name):
        require(name in m2.INTEGER_TYPES, "unknown array element type")
        self.name = name
        self.signed = name.startswith("int")
        self.bits = int(name.lstrip("uint"))
        self.min = -(2 ** (self.bits - 1)) if self.signed else 0
        self.max = 2 ** (self.bits - 1) - 1 if self.signed else 2 ** self.bits - 1
        self.literals = ([self.min, self.min + 1, -1] if self.signed else []) + [
            0, 1, 2, 3, 7, 2 ** (self.bits // 2), self.max - 1, self.max]
        self.offsets = [0, 1, 3, 2 ** (self.bits - 1) - 1, 2 ** (self.bits - 1), 2 ** self.bits - 1]

    def convert(self, word):
        word %= M
        if self.bits == 256:
            return word
        low = word % 2 ** self.bits
        if self.signed and low >= 2 ** (self.bits - 1):
            return (low - 2 ** self.bits) % M
        return low

    def canonical(self, word):
        return self.convert(word) == word

    def value(self, rep):
        return rep - M if self.signed and rep >= 2 ** 255 else rep

    def wrap(self, value):
        return (value - self.min) % 2 ** self.bits + self.min


def tdiv(left, right):
    quotient = abs(left) // abs(right)
    return quotient if (left >= 0) == (right >= 0) else -quotient


class Stop(Exception):
    def __init__(self, kind, code, site):
        super().__init__(site)
        self.kind, self.code, self.site = kind, code, site


def panic(code, site):
    return Stop("panic", code, site)


def operate(kind, unchecked, op, left, right, overflow):
    """A checked or unchecked operation on two representation Words."""
    a, b = kind.value(left), kind.value(right)
    if op in ("div", "mod") and b == 0:
        raise panic(0x12, "compound-zero")
    exact = {"add": a + b, "sub": a - b, "mul": a * b, "div": tdiv(a, b) if b else 0,
             "mod": a - b * tdiv(a, b) if b else 0}[op]
    if kind.min <= exact <= kind.max:
        return exact % M
    if unchecked:
        return kind.wrap(exact) % M
    raise panic(0x11, overflow)


def fold(acc, word):
    return ((acc * FOLD) % M) ^ word


# The plan walk: names, operands and static bounds.

def keys(value, expected, label):
    require(isinstance(value, dict) and set(value) == set(expected), f"malformed array {label}")


def one_of(value, options, label):
    """A tagged object with one of the keys, or one of the string tags."""
    if isinstance(value, str):
        require(value in options, f"unknown array {label}")
        return value, None
    require(isinstance(value, dict) and len(value) == 1, f"malformed array {label}")
    (tag, body), = value.items()
    require(tag in options, f"unknown array {label}")
    return tag, body


def nat(value, label):
    require(type(value) is int and value >= 0, f"array {label} must be a natural number")
    return value


class Walk:
    """The plan's static scope while its steps are admitted."""

    def __init__(self, plan, kind, storage):
        self.plan, self.kind, self.storage = plan, kind, storage
        self.arrays, self.slices, self.grids, self.stored = [], [], [], 0

    def index(self, index, in_loop):
        tag, body = one_of(index, ("literal", "input", "counter"), "index")
        if tag == "literal":
            require(nat(body, "index") <= MAX_INDEX_LITERAL, "array index literal past 7")
        elif tag == "input":
            require(nat(body, "index") < len(self.plan["indices"]), "array index past the indices")
        else:
            require(in_loop, "the loop counter outside the loop")

    def value(self, value):
        tag, body = one_of(value, ("input", "literal"), "value")
        limit = len(self.plan["values"]) if tag == "input" else len(self.kind.literals)
        require(nat(body, "value") < limit, "array value past its table")

    def length(self, length, flagged):
        tag, body = one_of(length, ("literal", "input"), "length")
        if tag == "literal":
            require(nat(body, "length") <= MAX_LITERAL, "array length literal past 4")
            return body
        require(nat(body, "length") < len(self.plan["indices"]), "array length past the indices")
        entry = self.plan["indices"][body]
        require(flagged or not entry["flagged"], "a flagged length where only a masked one is admitted")
        return entry["mask"]

    def name(self, name):
        tag, body = one_of(name, ("var", "param"), "name")
        if tag == "var":
            require(nat(body, "name") < len(self.arrays), "array name before its declaration")
            return self.arrays[body]
        require(nat(body, "name") < len(self.plan["params"]) and not self.plan["params"][body]["calldata"],
                "array name of no memory parameter")
        return param_bound(self.plan["params"][body])

    def coll(self, coll, in_loop):
        tag, body = one_of(coll, ("array", "slice", "storage", "row", "calldata"), "collection")
        if tag == "array":
            return self.name(body)
        if tag == "slice":
            require(nat(body, "slice") < len(self.slices), "slice before its declaration")
            return self.slices[body]["bound"]
        if tag == "storage":
            require(self.storage, "the storage array outside its profile")
            return self.stored
        if tag == "row":
            keys(body, ("grid", "index"), "row")
            self.index(body["index"], in_loop)
            require(nat(body["grid"], "grid") < len(self.grids), "grid before its declaration")
            return self.grids[body["grid"]]["rows"]
        require(nat(body, "parameter") < len(self.plan["params"]) and self.plan["params"][body]["calldata"],
                "calldata collection of no calldata parameter")
        return param_bound(self.plan["params"][body])

    def target(self, target, in_loop):
        tag, body = one_of(target, ("array", "storage", "row"), "target")
        return self.coll(target, in_loop)

    def observation(self, observation, in_loop):
        tag, body = one_of(observation, ("length", "element", "gridLength", "sum", "get", "len"), "observation")
        if tag in ("length", "len"):
            self.coll(body, in_loop)
        elif tag in ("element", "get"):
            keys(body, ("coll", "index"), "read")
            self.coll(body["coll"], in_loop)
            self.index(body["index"], in_loop)
        elif tag == "gridLength":
            require(nat(body, "grid") < len(self.grids), "grid before its declaration")
        else:
            self.name(body)

    def action(self, action, in_loop):
        tag, body = one_of(action, ("write", "observe"), "action")
        if tag == "observe":
            self.observation(body, in_loop)
            return
        keys(body, ("target", "index", "value", "form"), "write")
        self.target(body["target"], in_loop)
        self.index(body["index"], in_loop)
        self.value(body["value"])
        form, detail = one_of(body["form"], ("plain", "compound", "put", "inc"), "write form")
        if form == "compound":
            keys(detail, ("op", "unchecked"), "compound write")
            require(detail["op"] in OPS and type(detail["unchecked"]) is bool, "unknown compound write")
        if form in ("put", "inc"):
            require(body["target"] != "storage", "a memref write to the storage array")

    def array(self, bound):
        require(len(self.arrays) < MAX_ARRAYS and bound <= MAX_BOUND, "too many arrays or elements")
        self.arrays.append(bound)

    def slice(self, info):
        require(len(self.slices) < MAX_SLICES, "too many slices")
        self.slices.append(info)

    def grid(self, info):
        require(len(self.grids) < MAX_GRIDS and info["bound"] <= MAX_BOUND, "too many grids or rows")
        self.grids.append(info)

    def cut(self, cut):
        tag, body = one_of(cut, ("range", "start", "stop", "all"), "slice")
        if tag == "range":
            require(isinstance(body, list) and len(body) == 2, "a slice range has two bounds")
            for bound in body:
                self.index(bound, False)
        elif tag in ("start", "stop"):
            self.index(body, False)

    def step(self, step):
        if step == "pop":
            require(self.storage, "pop outside its profile")
            return
        tag, body = one_of(step, ("alloc", "literal", "alias", "copy", "made", "slice", "tail", "grid", "gridOf",
                                  "gridLiteral", "setRow", "write", "observe", "fill", "push", "setLength",
                                  "loop"), "step")
        if tag == "alloc":
            self.array(self.length(body, True))
        elif tag == "literal":
            require(isinstance(body, list) and 1 <= len(body) <= MAX_LITERAL, "a literal holds one to four values")
            for value in body:
                self.value(value)
            self.array(len(body))
        elif tag == "alias":
            self.array(self.name(body))
        elif tag == "copy":
            require(nat(body, "slice") < len(self.slices), "copy of no slice")
            self.array(self.slices[body]["bound"])
        elif tag == "made":
            require(isinstance(body, list) and len(body) == 2, "a helper takes two values")
            for value in body:
                self.value(value)
            self.array(2)
        elif tag == "slice":
            keys(body, ("base", "cut"), "slice")
            self.cut(body["cut"])
            bound = self.coll(body["base"], False)
            base, inner = one_of(body["base"], ("array", "slice", "storage", "row", "calldata"), "base")
            if base == "slice":
                info = dict(self.slices[inner], bound=bound)
            else:
                info = {"bound": bound, "storage": base == "storage", "calldata": inner if base == "calldata" else None}
            self.slice(info)
        elif tag == "tail":
            keys(body, ("source", "start"), "tail")
            self.index(body["start"], False)
            self.slice({"bound": self.name(body["source"]), "storage": False, "calldata": None})
        elif tag == "grid":
            self.grid({"bound": self.length(body, True), "rows": 0})
        elif tag == "gridOf":
            require(isinstance(body, list) and 1 <= len(body) <= MAX_ROWS, "a grid of one to three arrays")
            self.grid({"bound": len(body), "rows": max(self.name(name) for name in body)})
        elif tag == "gridLiteral":
            require(isinstance(body, list) and 1 <= len(body) <= MAX_ROWS
                    and all(isinstance(row, list) and 1 <= len(row) <= MAX_ROWS for row in body),
                    "a grid literal of one to three rows of one to three values")
            for row in body:
                for value in row:
                    self.value(value)
            self.grid({"bound": len(body), "rows": max(len(row) for row in body)})
        elif tag == "setRow":
            keys(body, ("grid", "index", "source"), "row replacement")
            require(nat(body["grid"], "grid") < len(self.grids), "row replacement of no grid")
            bound = self.name(body["source"])
            self.index(body["index"], False)
            self.grids[body["grid"]]["rows"] = max(self.grids[body["grid"]]["rows"], bound)
        elif tag in ("write", "observe"):
            self.action(step, False)
        elif tag == "fill":
            keys(body, ("target", "value"), "fill")
            self.name(body["target"])
            self.value(body["value"])
        elif tag == "push":
            require(self.storage and self.stored < MAX_BOUND, "push outside its profile or past eight elements")
            self.value(body)
            self.stored += 1
        elif tag == "setLength":
            require(self.storage, "setLength outside its profile")
            self.stored = self.length(body, False)
        else:
            keys(body, ("over", "body"), "loop")
            require(self.coll(body["over"], False) <= LOOP_BOUND, "a loop over more than four elements")
            require(isinstance(body["body"], list) and 1 <= len(body["body"]) <= MAX_BODY, "a loop of one or two actions")
            for action in body["body"]:
                self.action(action, True)


def param_bound(param):
    length = param["length"]
    return length["literal"] if "literal" in length else length["mask"]


def actions(step):
    if step == "pop" or not isinstance(step, dict):
        return []
    if "loop" in step:
        return step["loop"]["body"]
    if "write" in step or "observe" in step:
        return [step]
    return []


def observes(plan):
    return any("observe" in action for step in plan["steps"] for action in actions(step))


def adds(action):
    if "write" in action:
        form = action["write"]["form"]
        return form == "inc" or (isinstance(form, dict) and "compound" in form)
    return "sum" in action["observe"]


def check_plan(plan, profile):
    """The profile's admission, walked here without the native checker."""
    keys(plan, ("schema", "element", "values", "indices", "params", "steps", "result"), "plan")
    require(plan["schema"] == profile["planSchema"], "unexpected array plan schema")
    kind = Type(plan["element"])
    values, indices, params, steps = plan["values"], plan["indices"], plan["params"], plan["steps"]
    require(isinstance(values, list) and 1 <= len(values) <= MAX_VALUES, "one to three values")
    for position, value in enumerate(values):
        keys(value, ("offset", "raw"), "value input")
        offset = canonical_word(value["offset"])
        require(offset in kind.offsets and (position > 0 or offset == 0) and type(value["raw"]) is bool,
                "a value offset outside the type's table, or a first offset")
    require(isinstance(indices, list) and len(indices) <= MAX_INDICES, "at most three indices")
    for index in indices:
        keys(index, ("shift", "mask", "flagged"), "index input")
        require(index["shift"] in INDEX_SHIFTS and index["mask"] in INDEX_MASKS and type(index["flagged"]) is bool
                and (not index["flagged"] or index["shift"] == 0), "an index outside its table")
    require(isinstance(steps, list) and 1 <= len(steps) <= MAX_STEPS, "one to twelve steps")
    require(sum(isinstance(step, dict) and "loop" in step for step in steps) <= 1, "at most one loop")
    require(isinstance(params, list), "array parameters must be a list")
    if profile["abi"]:
        require(1 <= len(params) <= MAX_PARAMS, "one or two parameters")
        for param in params:
            keys(param, ("calldata", "length", "offset", "raw"), "parameter")
            length = param["length"]
            require(type(param["calldata"]) is bool and type(param["raw"]) is bool, "malformed parameter")
            if set(length) == {"literal"}:
                require(nat(length["literal"], "length") <= MAX_LITERAL, "a parameter length literal past 4")
            else:
                keys(length, ("shift", "mask"), "parameter length")
                require(length["shift"] in INDEX_SHIFTS and length["mask"] in INDEX_MASKS, "a parameter length outside its table")
            require(canonical_word(param["offset"]) in kind.offsets, "a parameter offset outside the type's table")
            require(not param["raw"] or kind.bits < 256, "raw elements of a 256-bit type")
    else:
        require(params == [] and plan["result"] == "word" and not any(value["raw"] for value in values) and observes(plan),
                "a memory array plan has no parameter, folds an observation and has no raw value")
    walk = Walk(plan, kind, not profile["abi"])
    for step in steps:
        walk.step(step)
    result = plan["result"]
    tag, body = one_of(result, ("word", "array", "copy"), "result")
    if tag == "word":
        require(observes(plan), "a fold without an observation")
    elif tag == "array":
        walk.name(body)
    else:
        require(nat(body, "slice") < len(walk.slices), "a copied result of no slice")
    if any(value["raw"] for value in values):
        require(kind.bits < 256 and tag != "word"
                and not any(adds(action) for step in steps for action in actions(step)),
                "a raw value needs a narrow type, an array result and no element addition")
    return plan


# The interpreter, over Python lists.

class Machine:
    def __init__(self, plan, kind, x):
        self.plan, self.kind, self.x = plan, kind, x
        self.values = [value_word(kind, value, x) for value in plan["values"]]
        self.indices = [index_word(index, x) for index in plan["indices"]]
        self.heap = [[0, []]]
        self.names, self.params, self.slices, self.grids = [], [], [], []
        self.storage = [0, [0] * MAX_BOUND]
        self.acc = 0
        self.normalized = False

    def index(self, index, counter):
        if index == "counter":
            return counter
        return index["literal"] if "literal" in index else self.indices[index["input"]]

    def value(self, value):
        return self.values[value["input"]] if "input" in value else self.kind.literals[value["literal"]] % M

    def length(self, length):
        return length["literal"] if "literal" in length else self.indices[length["input"]]

    def param_length(self, number):
        length = self.plan["params"][number]["length"]
        return length["literal"] if "literal" in length else (self.x >> length["shift"]) & length["mask"]

    def param_word(self, number, k):
        param = self.plan["params"][number]
        word = (self.x + canonical_word(param["offset"]) + k) % M
        return word if param["raw"] else self.kind.convert(word)

    def named(self, name):
        return self.names[name["var"]] if "var" in name else self.params[name["param"]]

    def allocate(self, items):
        self.heap.append([len(items), list(items)])
        return len(self.heap) - 1

    def resolve(self, coll, counter):
        if coll == "storage":
            return ("storage",)
        (tag, body), = coll.items()
        if tag == "array":
            return ("heap", self.named(body))
        if tag == "slice":
            return ("slice", self.slices[body])
        if tag == "calldata":
            return ("calldata", body)
        slots = self.grids[body["grid"]]
        position = self.index(body["index"], counter)
        if position >= len(slots):
            raise panic(0x32, "row")
        return ("heap", slots[position])

    def length_of(self, resolved):
        if resolved[0] == "heap":
            return self.heap[resolved[1]][0]
        if resolved[0] == "storage":
            return self.storage[0]
        if resolved[0] == "slice":
            return resolved[1]["length"]
        return self.param_length(resolved[1])

    def calldata_element(self, number, position, site):
        word = self.param_word(number, position)
        if not self.kind.canonical(word):
            raise Stop("dirty", None, site)
        return word

    def read(self, resolved, position, site, dirty_site="read"):
        if resolved[0] in ("heap", "storage"):
            length, items = self.heap[resolved[1]] if resolved[0] == "heap" else self.storage
            if position >= length:
                raise panic(0x32, site)
            return items[position]
        if resolved[0] == "calldata":
            if position >= self.param_length(resolved[1]):
                raise panic(0x32, site)
            return self.calldata_element(resolved[1], position, dirty_site)
        view = resolved[1]
        if position >= view["length"]:
            raise panic(0x32, "slice-read")
        inner = view["start"] + position
        base = view["base"]
        if base[0] == "heap":
            return self.heap[base[1]][1][inner]
        if base[0] == "storage":
            if inner >= self.storage[0]:
                raise panic(0x32, "stale")
            return self.storage[1][inner]
        return self.calldata_element(base[1], inner, dirty_site)

    def store(self, resolved, position, value):
        items = self.heap[resolved[1]][1] if resolved[0] == "heap" else self.storage[1]
        items[position] = value

    def write(self, body, counter):
        target = body["target"]
        resolved = ("storage",) if target == "storage" else self.resolve(target, counter)
        position = self.index(body["index"], counter)
        if self.length_of(resolved) <= position:
            raise panic(0x32, "write")
        operand = self.value(body["value"])
        form = body["form"]
        if form in ("plain", "put"):
            result = operand
        elif form == "inc":
            result = operate(self.kind, False, "add", self.read(resolved, position, "write"), operand, "inc")
        else:
            detail = form["compound"]
            result = operate(self.kind, detail["unchecked"], detail["op"], self.read(resolved, position, "write"),
                             operand, "compound-overflow")
        self.store(resolved, position, result)

    def total(self, name):
        length, items = self.heap[self.named(name)]
        total = 0
        for position in range(length):
            total = operate(self.kind, False, "add", total, items[position], "sum")
        return total

    def observe(self, observation, counter):
        (tag, body), = observation.items()
        if tag in ("length", "len"):
            return self.length_of(self.resolve(body, counter))
        if tag in ("element", "get"):
            return self.read(self.resolve(body["coll"], counter), self.index(body["index"], counter), "read")
        if tag == "gridLength":
            return len(self.grids[body])
        return self.total(body)

    def act(self, action, counter):
        if "write" in action:
            self.write(action["write"], counter)
        else:
            self.acc = fold(self.acc, self.observe(action["observe"], counter))

    def slice(self, base, cut):
        resolved = self.resolve(base, 0)
        length = self.length_of(resolved)
        tag, body = one_of(cut, ("range", "start", "stop", "all"), "slice")
        start = self.index(body[0], 0) if tag == "range" else self.index(body, 0) if tag == "start" else 0
        stop = self.index(body[1], 0) if tag == "range" else self.index(body, 0) if tag == "stop" else length
        if stop < start:
            raise panic(0x32, "slice-start")
        if length < stop:
            raise panic(0x32, "slice-end")
        if resolved[0] == "slice":
            inner = resolved[1]
            return {"base": inner["base"], "start": inner["start"] + start, "length": stop - start}
        base = ("heap", resolved[1]) if resolved[0] == "heap" else ("calldata", resolved[1]) \
            if resolved[0] == "calldata" else ("storage",)
        return {"base": base, "start": start, "length": stop - start}

    def copy(self, view, dirty_site):
        return self.allocate([self.read(("slice", view), position, "read", dirty_site) for position in range(view["length"])])

    def step(self, step):
        if step == "pop":
            if self.storage[0] == 0:
                raise panic(0x31, "pop")
            self.storage[0] -= 1
            self.storage[1][self.storage[0]] = 0
            return
        (tag, body), = step.items()
        if tag == "alloc":
            size = self.length(body)
            if size >= ALLOCATION_LIMIT:
                raise panic(0x41, "new")
            self.names.append(self.allocate([0] * size))
        elif tag == "literal":
            self.names.append(self.allocate([self.value(value) for value in body]))
        elif tag == "alias":
            self.names.append(self.named(body))
        elif tag == "copy":
            self.names.append(self.copy(self.slices[body], "copy"))
        elif tag == "made":
            self.names.append(self.allocate([self.value(value) for value in body]))
        elif tag == "slice":
            self.slices.append(self.slice(body["base"], body["cut"]))
        elif tag == "tail":
            self.slices.append(self.slice({"array": body["source"]}, {"start": body["start"]}))
        elif tag == "grid":
            size = self.length(body)
            if size >= ALLOCATION_LIMIT:
                raise panic(0x41, "grid-new")
            self.grids.append([0] * size)
        elif tag == "gridOf":
            self.grids.append([self.named(name) for name in body])
        elif tag == "gridLiteral":
            self.grids.append([self.allocate([self.value(value) for value in row]) for row in body])
        elif tag == "setRow":
            slots = self.grids[body["grid"]]
            position = self.index(body["index"], 0)
            if position >= len(slots):
                raise panic(0x32, "row")
            slots[position] = self.named(body["source"])
        elif tag in ("write", "observe"):
            self.act(step, 0)
        elif tag == "fill":
            length, items = self.heap[self.named(body["target"])]
            for position in range(length):
                items[position] = self.value(body["value"])
        elif tag == "push":
            self.storage[1][self.storage[0]] = self.value(body)
            self.storage[0] += 1
        elif tag == "setLength":
            size = self.length(body)
            self.storage[0] = size
            self.storage[1] = [item if position < size else 0 for position, item in enumerate(self.storage[1])]
        else:
            counter = 0
            while counter < self.length_of(self.resolve(body["over"], counter)):
                for action in body["body"]:
                    self.act(action, counter)
                counter += 1

    def encode(self, slot):
        length, items = self.heap[slot]
        elements = items[:length]
        self.normalized = any(not self.kind.canonical(element) for element in elements)
        words = [32, length] + [self.kind.convert(element) for element in elements]
        return b"".join(word.to_bytes(32, "big") for word in words)


def value_word(kind, value, x):
    word = (x + canonical_word(value["offset"])) % M
    return word if value["raw"] else kind.convert(word)


def index_word(index, x):
    return x & (FLAG + index["mask"]) if index["flagged"] else (x >> index["shift"]) & index["mask"]


def interpret(plan, x):
    """('word', acc), ('output', bytes), ('panic', code) or ('dirty', None), with the deciding site
    and whether an encoded element needed its type's conversion."""
    kind = Type(plan["element"])
    machine = Machine(plan, kind, x % M)
    try:
        for number, param in enumerate(plan["params"]):
            if param["calldata"]:
                machine.params.append(None)
                continue
            items = [machine.param_word(number, k) for k in range(machine.param_length(number))]
            if not all(kind.canonical(item) for item in items):
                raise Stop("dirty", None, "memory")
            machine.params.append(machine.allocate(items))
        for step in plan["steps"]:
            machine.step(step)
        result = plan["result"]
        if result == "word":
            outcome = ("word", machine.acc) if not plan["params"] else ("output", machine.acc.to_bytes(32, "big"))
        elif "array" in result:
            outcome = ("output", machine.encode(machine.named(result["array"])))
        else:
            outcome = ("output", machine.encode(machine.copy(machine.slices[result["copy"]], "copy")))
        return outcome, None, machine.normalized
    except Stop as stop:
        return (stop.kind, stop.code), stop.site, False


def outcome_text(outcome):
    kind, value = outcome
    if kind == "word":
        return str(value)
    if kind == "output":
        return "0x" + value.hex()
    if kind == "panic":
        return "0x" + PANIC + f"{value:064x}"
    return "0x" + DIRTY


def observed_text(observation):
    require(isinstance(observation, dict) and observation.get("stage") == "execution", "missing Core observation")
    if observation.get("status") == "returned" and "word" in observation:
        require(set(observation) == {"stage", "status", "word"}, "malformed returned Word")
        return str(canonical_word(observation["word"]))
    require(observation.get("status") in ("returned", "reverted") and set(observation) == {"stage", "status", "output"},
            "an array case returns a Word, return data, or revert data")
    data = observation["output"]
    require(isinstance(data, str) and re.fullmatch(r"0x(?:[0-9a-f]{2})*", data), "malformed array output")
    return data


# Shapes.

def sorted_unique(values):
    return sorted(set(values))


def coll_shape(coll):
    return coll if coll == "storage" else next(iter(coll))


def index_shape(plan, index):
    if index == "counter":
        return "counter"
    if "literal" in index:
        return "literal"
    return "flagged" if plan["indices"][index["input"]]["flagged"] else "input"


def coll_indices(coll):
    return [coll["row"]["index"]] if isinstance(coll, dict) and "row" in coll else []


def observation_coll(observation):
    (tag, body), = observation.items()
    if tag in ("length", "len"):
        return body
    if tag in ("element", "get"):
        return body["coll"]
    return None


def action_indices(action):
    if "write" in action:
        body = action["write"]
        return coll_indices(body["target"]) + [body["index"]]
    observation = action["observe"]
    coll = observation_coll(observation)
    (tag, body), = observation.items()
    return (coll_indices(coll) if coll is not None else []) + ([body["index"]] if tag in ("element", "get") else [])


def step_indices(step):
    if not isinstance(step, dict):
        return []
    (tag, body), = step.items()
    if tag == "slice":
        cut = body["cut"]
        cuts = [] if cut == "all" else (cut["range"] if "range" in cut else [next(iter(cut.values()))])
        return coll_indices(body["base"]) + cuts
    if tag == "tail":
        return [body["start"]]
    if tag == "setRow":
        return [body["index"]]
    if tag in ("write", "observe"):
        return action_indices(step)
    if tag == "loop":
        return coll_indices(body["over"]) + [index for action in body["body"] for index in action_indices(action)]
    return []


DECLARATIONS = {"alloc": "new", "literal": "literal", "alias": "alias", "copy": "copy", "made": "helper",
                "tail": "tail", "grid": "grid-new", "gridOf": "grid-arrays", "gridLiteral": "grid-literal"}
CUTS = {"range": "slice-range", "start": "slice-from", "stop": "slice-to", "all": "slice-all"}


def form_shape(form):
    if form in ("plain", "put", "inc"):
        return form
    detail = form["compound"]
    return ("unchecked-" if detail["unchecked"] else "") + detail["op"]


def boundary_runs(plan):
    return [interpret(plan, x) for x in BOUNDARIES]


def outcome_name(outcome):
    if outcome[0] in ("word", "output"):
        return "returned"
    return f"panic-0x{outcome[1]:x}" if outcome[0] == "panic" else "dirty"


def identities(plan):
    arrays, fresh = [], len(plan["params"])
    for step in plan["steps"]:
        if not isinstance(step, dict):
            continue
        (tag, body), = step.items()
        if tag == "alias":
            arrays.append(arrays[body["var"]] if "var" in body else body["param"])
        elif tag in ("alloc", "literal", "copy", "made"):
            arrays.append(fresh)
            fresh += 1
    return arrays


def sharing(plan):
    """The plan's static sharing, by step position."""
    known = identities(plan)

    def identity(name):
        return known[name["var"]] if "var" in name else name["param"]

    writes, observations, grids = [], [], []
    for position, step in enumerate(plan["steps"]):
        for action in actions(step):
            if "write" in action:
                writes.append((position, action["write"]["target"]))
            else:
                observation = action["observe"]
                coll = observation_coll(observation)
                if coll is not None:
                    observations.append((position, coll))
                elif "sum" in observation:
                    observations.append((position, {"array": observation["sum"]}))
        if isinstance(step, dict) and "fill" in step:
            writes.append((position, {"array": step["fill"]["target"]}))
        if step == "pop" or (isinstance(step, dict) and ("push" in step or "setLength" in step)):
            writes.append((position, "storage"))
        if isinstance(step, dict):
            (tag, body), = step.items()
            if tag in ("grid", "gridLiteral"):
                grids.append([])
            elif tag == "gridOf":
                grids.append([identity(name) for name in body])
            elif tag == "setRow" and body["grid"] < len(grids):
                grids[body["grid"]].append(identity(body["source"]))
    found = []

    def array_of(coll):
        return coll["array"] if isinstance(coll, dict) and "array" in coll else None

    for position, step in enumerate(plan["steps"]):
        if not isinstance(step, dict):
            continue
        (tag, body), = step.items()
        if tag == "alias":
            alias = identity(body)
            if any(position < written and array_of(target) is not None and identity(array_of(target)) == alias
                   and any(written < seen and array_of(coll) is not None and identity(array_of(coll)) == alias
                           and array_of(coll) != array_of(target) for seen, coll in observations)
                   for written, target in writes):
                found.append("alias")
        elif tag == "slice":
            base = body["base"]

            def same(target):
                if base == "storage":
                    return target == "storage"
                return (array_of(base) is not None and array_of(target) is not None
                        and identity(array_of(base)) == identity(array_of(target)))

            if any(position < written and same(target)
                   and any(written < seen and isinstance(coll, dict) and "slice" in coll for seen, coll in observations)
                   for written, target in writes):
                found.append("view")
        elif tag == "copy":
            if any(position < written for written, _ in writes) and any(position < seen for seen, _ in observations):
                found.append("copy")
    rows = False
    for grid in range(MAX_GRIDS):
        arrays = grids[grid] if grid < len(grids) else []
        for at, target in writes:
            if isinstance(target, dict) and "row" in target:
                if target["row"]["grid"] == grid and any(
                        at < seen and array_of(coll) is not None and identity(array_of(coll)) in arrays
                        for seen, coll in observations):
                    rows = True
            elif array_of(target) is not None and identity(array_of(target)) in arrays and any(
                    at < seen and isinstance(coll, dict) and "row" in coll and coll["row"]["grid"] == grid
                    for seen, coll in observations):
                rows = True
    return sorted_unique(found + (["row"] if rows else []))


def memory_shapes(plan):
    steps = plan["steps"]
    acts = [action for step in steps for action in actions(step)]
    runs = boundary_runs(plan)
    declarations, writes, members, lengths, loops, bases, collections = [], [], [], [], [], [], []
    for step in steps:
        if step == "pop":
            members.append("pop")
            continue
        (tag, body), = step.items()
        if tag in DECLARATIONS:
            declarations.append(DECLARATIONS[tag])
        elif tag == "slice":
            declarations.append(CUTS[body["cut"] if body["cut"] == "all" else next(iter(body["cut"]))])
        if tag == "fill":
            writes.append("fill")
        elif tag == "setRow":
            writes.append("set-row")
        elif tag == "push":
            members.append("push")
        elif tag == "setLength":
            members.append("set-length")
        if tag in ("alloc", "grid", "setLength"):
            lengths.append(body)
        if tag == "loop":
            loops.append(coll_shape(body["over"]))
            collections.append(coll_shape(body["over"]))
        if tag == "slice":
            bases.append(coll_shape(body["base"]))
        elif tag == "tail":
            bases.append("array")
        for action in actions(step):
            if "write" in action:
                writes.append(form_shape(action["write"]["form"]))
            else:
                coll = observation_coll(action["observe"])
                if coll is not None:
                    collections.append(coll_shape(coll))

    def length_shape(length):
        if "literal" in length:
            return "literal"
        return "flagged" if plan["indices"][length["input"]]["flagged"] else "input"

    observations = {"length": "length", "element": "element", "gridLength": "grid-length", "sum": "sum", "get": "get",
                    "len": "len"}
    return {"types": [plan["element"]], "declarations": sorted_unique(declarations), "writes": sorted_unique(writes),
            "targets": sorted_unique(coll_shape(action["write"]["target"]) for action in acts if "write" in action),
            "members": sorted_unique(members),
            "observations": sorted_unique(observations[next(iter(action["observe"]))] for action in acts
                                          if "observe" in action),
            "collections": sorted_unique(collections), "bases": sorted_unique(bases),
            "indices": sorted_unique(index_shape(plan, index) for step in steps for index in step_indices(step)),
            "lengths": sorted_unique(length_shape(length) for length in lengths), "loops": sorted_unique(loops),
            "sharing": sharing(plan), "outcomes": sorted_unique(outcome_name(outcome) for outcome, _, _ in runs),
            "panics": sorted_unique(site for outcome, site, _ in runs if outcome[0] == "panic")}


def calldata_reads(plan):
    """What reads a calldata parameter: by the steps, and a copy of a slice over one."""
    reads, slices, copies = [], [], False
    for step in plan["steps"]:
        if isinstance(step, dict) and "copy" in step and slices[step["copy"]]:
            copies = True
        if isinstance(step, dict) and "slice" in step:
            base = step["slice"]["base"]
            if isinstance(base, dict) and "calldata" in base:
                reads.append("slice")
                slices.append(True)
            elif isinstance(base, dict) and "slice" in base:
                slices.append(slices[base["slice"]])
            else:
                slices.append(False)
            continue
        if isinstance(step, dict) and "tail" in step:
            slices.append(False)
            continue
        if isinstance(step, dict) and "loop" in step and isinstance(step["loop"]["over"], dict) \
                and "calldata" in step["loop"]["over"]:
            reads.append("loop")
            for action in step["loop"]["body"]:
                observation = action.get("observe")
                if observation and "element" in observation and isinstance(observation["element"]["coll"], dict) \
                        and "calldata" in observation["element"]["coll"]:
                    reads.append("element")
            continue
        for action in actions(step):
            observation = action.get("observe")
            if not observation:
                continue
            (tag, body), = observation.items()
            coll = observation_coll(observation)
            if isinstance(coll, dict) and "calldata" in coll:
                reads.append({"length": "length", "len": "length", "element": "element", "get": "get"}[tag])
    result = plan["result"]
    if isinstance(result, dict) and "copy" in result and slices[result["copy"]]:
        copies = True
    return reads + (["copy"] if copies else [])


def parameter_writes(plan):
    found = []
    for step in plan["steps"]:
        if isinstance(step, dict) and "fill" in step and "param" in step["fill"]["target"]:
            found.append("fill")
            continue
        for action in actions(step):
            write = action.get("write")
            if write and isinstance(write["target"], dict) and "array" in write["target"] \
                    and "param" in write["target"]["array"]:
                form = write["form"]
                found.append("plain" if form == "plain" else "memref" if form in ("put", "inc") else "compound")
    return found


def abi_shapes(plan):
    runs = boundary_runs(plan)
    params = plan["params"]
    result = plan["result"]
    results = ("word" if result == "word" else "copy" if "copy" in result
               else "parameter" if "param" in result["array"] else "array")
    return {"types": [plan["element"]],
            "parameters": sorted_unique(["calldata" if param["calldata"] else "memory" for param in params] +
                                        (["two"] if len(params) == 2 else [])),
            "lengths": sorted_unique("literal" if "literal" in param["length"] else "input" for param in params),
            "elements": sorted_unique("raw" if param["raw"] else "clean" for param in params),
            "values": sorted_unique("raw" if value["raw"] else "clean" for value in plan["values"]),
            "results": [results], "calldataReads": sorted_unique(calldata_reads(plan)),
            "parameterWrites": sorted_unique(parameter_writes(plan)),
            "encodings": sorted_unique(("normalized" if normalized else "canonical") for outcome, _, normalized in runs
                                       if outcome[0] == "output" and result != "word"),
            "outcomes": sorted_unique(outcome_name(outcome) for outcome, _, _ in runs),
            "dirty": sorted_unique(site for outcome, site, _ in runs if outcome[0] == "dirty")}


def shapes(plan, profile):
    return abi_shapes(plan) if profile["abi"] else memory_shapes(plan)


# The shrink measure.

def index_weight(index):
    if index == "counter":
        return 8
    return index["literal"] if "literal" in index else 8 + index["input"]


def value_weight(value):
    return value["input"] if "input" in value else 3 + value["literal"]


def length_weight(length):
    return length["literal"] if "literal" in length else 5 + length["input"]


def name_weight(name):
    return next(iter(name.values()))


def coll_weight(coll):
    if coll == "storage":
        return 2
    (tag, body), = coll.items()
    if tag == "array":
        return 1 + name_weight(body)
    if tag == "slice":
        return 2 + body
    if tag == "row":
        return 3 + body["grid"] + index_weight(body["index"])
    return 1 + body


def form_weight(form):
    if form in ("plain", "put", "inc"):
        return {"plain": 0, "put": 1, "inc": 2}[form]
    detail = form["compound"]
    return 2 + OPS.index(detail["op"]) + (1 if detail["unchecked"] else 0)


def cut_weight(cut):
    if cut == "all":
        return 0
    (tag, body), = cut.items()
    if tag == "range":
        return 2 + index_weight(body[0]) + index_weight(body[1])
    return 1 + index_weight(body)


def observation_weight(observation):
    (tag, body), = observation.items()
    if tag == "length":
        return 1 + coll_weight(body)
    if tag == "element":
        return 2 + coll_weight(body["coll"]) + index_weight(body["index"])
    if tag == "gridLength":
        return 1 + body
    if tag == "sum":
        return 3 + name_weight(body)
    if tag == "get":
        return 3 + coll_weight(body["coll"]) + index_weight(body["index"])
    return 2 + coll_weight(body)


def action_weight(action):
    if "observe" in action:
        return 1 + observation_weight(action["observe"])
    body = action["write"]
    return 2 + coll_weight(body["target"]) + index_weight(body["index"]) + value_weight(body["value"]) + \
        form_weight(body["form"])


def step_weight(step):
    if step == "pop":
        return 2
    (tag, body), = step.items()
    if tag == "alloc":
        return 2 + length_weight(body)
    if tag == "literal":
        return 1 + sum(1 + value_weight(value) for value in body)
    if tag == "alias":
        return 2 + name_weight(body)
    if tag == "copy":
        return 3 + body
    if tag == "made":
        return 4 + value_weight(body[0]) + value_weight(body[1])
    if tag == "slice":
        return 3 + coll_weight(body["base"]) + cut_weight(body["cut"])
    if tag == "tail":
        return 5 + name_weight(body["source"]) + index_weight(body["start"])
    if tag == "grid":
        return 3 + length_weight(body)
    if tag == "gridOf":
        return 3 + sum(1 + name_weight(name) for name in body)
    if tag == "gridLiteral":
        return 4 + sum(1 + sum(1 + value_weight(value) for value in row) for row in body)
    if tag == "setRow":
        return 3 + body["grid"] + index_weight(body["index"]) + name_weight(body["source"])
    if tag in ("write", "observe"):
        return action_weight(step)
    if tag == "fill":
        return 3 + name_weight(body["target"]) + value_weight(body["value"])
    if tag == "push":
        return 2 + value_weight(body)
    if tag == "setLength":
        return 2 + length_weight(body)
    return 4 + coll_weight(body["over"]) + sum(1 + action_weight(action) for action in body["body"])


def plan_size(plan):
    kind = Type(plan["element"])

    def offset_weight(offset):
        value = int(offset)
        return kind.offsets.index(value) if value in kind.offsets else 0

    result = plan["result"]
    result_weight = 0 if result == "word" else 1 + name_weight(result["array"]) if "array" in result else 2 + result["copy"]
    return (sum(step_weight(step) for step in plan["steps"]) +
            sum(1 + offset_weight(value["offset"]) + value["raw"] for value in plan["values"]) +
            sum(1 + INDEX_SHIFTS.index(index["shift"]) + INDEX_MASKS.index(index["mask"]) + 2 * index["flagged"]
                for index in plan["indices"]) +
            sum(1 + param["calldata"] + (param["length"]["literal"] if "literal" in param["length"] else 5) +
                offset_weight(param["offset"]) + param["raw"] for param in plan["params"]) + result_weight)


# Emission, written here from the definitions.

def indent(count, lines):
    return [" " * count + line for line in lines]


def hex_text(value):
    return "0x" + format(value, "x")


def convert_text(kind, word):
    if kind.bits == 256:
        return word
    if kind.signed:
        return f"sc_signextend({kind.bits // 8 - 1}, {word})"
    return f"({word} & {hex_text(2 ** kind.bits - 1)})"


def offset_text(offset):
    return "sc_x" if offset == 0 else f"(sc_x + {offset})"


def int_text(value):
    return f"({value})" if value < 0 else str(value)


def index_text(index):
    if index == "counter":
        return "sc_i"
    return str(index["literal"]) if "literal" in index else f"sc_k{index['input']}"


def element_index_text(coll, index):
    if isinstance(coll, dict) and ("slice" in coll or "calldata" in coll) and isinstance(index, dict) and "literal" in index:
        return f"uint256({index['literal']})"
    return index_text(index)


def value_text(kind, value):
    return f"sc_v{value['input']}" if "input" in value else int_text(kind.literals[value["literal"]])


def length_text(length):
    return str(length["literal"]) if "literal" in length else f"sc_k{length['input']}"


def name_text(name):
    return f"sc_a{name['var']}" if "var" in name else f"sc_p{name['param']}"


def coll_text(coll):
    if coll == "storage":
        return "sc_st"
    (tag, body), = coll.items()
    if tag == "array":
        return name_text(body)
    if tag == "slice":
        return f"sc_s{body}"
    if tag == "row":
        return f"sc_g{body['grid']}[{index_text(body['index'])}]"
    return f"sc_p{body}"


def cut_text(cut):
    if cut == "all":
        return "[:]"
    (tag, body), = cut.items()
    if tag == "range":
        return f"[{index_text(body[0])}:{index_text(body[1])}]"
    return f"[{index_text(body)}:]" if tag == "start" else f"[:{index_text(body)}]"


def observation_text(observation):
    (tag, body), = observation.items()
    if tag == "length":
        return coll_text(body) + ".length"
    if tag == "element":
        return f"{coll_text(body['coll'])}[{element_index_text(body['coll'], body['index'])}]"
    if tag == "gridLength":
        return f"sc_g{body}.length"
    if tag == "sum":
        return f"sc_sum({name_text(body)})"
    if tag == "get":
        return f"sc_get({coll_text(body['coll'])}, {index_text(body['index'])})"
    return f"sc_len({coll_text(body)})"


def action_lines(kind, action):
    if "observe" in action:
        return [f"sc_r = ((sc_r * 1099511628211) ^ Typedef.rep({observation_text(action['observe'])}));"]
    body = action["write"]
    target, index, value = coll_text(body["target"]), index_text(body["index"]), value_text(kind, body["value"])
    form = body["form"]
    if form == "plain":
        return [f"{target}[{index}] = {value};"]
    if form in ("put", "inc"):
        return [f"sc_{form}(lidx({target}, {index}), {value});"]
    detail = form["compound"]
    statement = f"{target}[{index}] {SYMBOLS[detail['op']]}= {value};"
    return ["unchecked {", "    " + statement, "}"] if detail["unchecked"] else [statement]


def step_lines(kind, counts, step):
    arrays, slices, grids = counts
    name = kind.name
    if step == "pop":
        return ["sc_st.pop();"]
    (tag, body), = step.items()
    if tag == "alloc":
        return [f"let sc_a{arrays}: {name}[] = new {name}[]({length_text(body)});"]
    if tag == "literal":
        return [f"let sc_a{arrays}: {name}[] = [{', '.join(value_text(kind, value) for value in body)}];"]
    if tag == "alias":
        return [f"let sc_a{arrays}: {name}[] = {name_text(body)};"]
    if tag == "copy":
        return [f"let sc_a{arrays}: {name}[] = toArray(sc_s{body});"]
    if tag == "made":
        return [f"let sc_a{arrays}: {name}[] = sc_mk({value_text(kind, body[0])}, {value_text(kind, body[1])});"]
    if tag == "slice":
        return [f"let sc_s{slices} = {coll_text(body['base'])}{cut_text(body['cut'])};"]
    if tag == "tail":
        return [f"let sc_s{slices} = sc_tail({name_text(body['source'])}, {index_text(body['start'])});"]
    if tag == "grid":
        return [f"let sc_g{grids}: {name}[][] = new {name}[][]({length_text(body)});"]
    if tag == "gridOf":
        return [f"let sc_g{grids}: {name}[][] = [{', '.join(name_text(source) for source in body)}];"]
    if tag == "gridLiteral":
        rows = ", ".join("[" + ", ".join(value_text(kind, value) for value in row) + "]" for row in body)
        return [f"let sc_g{grids}: {name}[][] = [{rows}];"]
    if tag == "setRow":
        return [f"sc_g{body['grid']}[{index_text(body['index'])}] = {name_text(body['source'])};"]
    if tag in ("write", "observe"):
        return action_lines(kind, step)
    if tag == "fill":
        return [f"sc_fill({name_text(body['target'])}, {value_text(kind, body['value'])});"]
    if tag == "push":
        return [f"sc_st.push({value_text(kind, body)});"]
    if tag == "setLength":
        return [f"sc_st.setLength({length_text(body)});"]
    return ([f"for (let sc_i: uint256 = 0; sc_i < {coll_text(body['over'])}.length; sc_i += 1) {{"] +
            indent(4, [line for action in body["body"] for line in action_lines(kind, action)]) + ["}"])


def uses_storage(plan):
    def in_storage(action):
        if "write" in action:
            return action["write"]["target"] == "storage"
        return observation_coll(action["observe"]) == "storage"

    for step in plan["steps"]:
        if step == "pop" or (isinstance(step, dict) and ("push" in step or "setLength" in step)):
            return True
        if isinstance(step, dict) and (("slice" in step and step["slice"]["base"] == "storage")
                                       or ("loop" in step and step["loop"]["over"] == "storage")):
            return True
        if any(in_storage(action) for action in actions(step)):
            return True
    return False


def emit(plan, profile):
    kind = Type(plan["element"])
    name = kind.name
    acts = [action for step in plan["steps"] for action in actions(step)]
    unchecked = any("write" in action and isinstance(action["write"]["form"], dict)
                    and action["write"]["form"]["compound"]["unchecked"] for action in acts)
    imports = ["import * from std;", "import * from std.unsigned;"]
    imports += ["import * from std.signed;"] if kind.signed else []
    if unchecked:
        imports.append("import * from std.unchecked.signed;" if kind.signed else "import * from std.unchecked.unsigned;")
    imports.append("import * from std.dispatch;")
    if kind.signed and kind.bits < 256:
        imports.append("import { signextend as sc_signextend } from std.opcodes;")
    loop = "for (let sc_i: uint256 = 0; sc_i < sc_v.length; sc_i += 1) {"
    steps = [step for step in plan["steps"] if isinstance(step, dict)]
    used = {"sc_put": any("write" in action and action["write"]["form"] == "put" for action in acts),
            "sc_inc": any("write" in action and action["write"]["form"] == "inc" for action in acts),
            "sc_sum": any("observe" in action and "sum" in action["observe"] for action in acts),
            "sc_fill": any("fill" in step for step in steps), "sc_mk": any("made" in step for step in steps),
            "sc_tail": any("tail" in step for step in steps),
            "sc_get": any("observe" in action and "get" in action["observe"] for action in acts),
            "sc_len": any("observe" in action and "len" in action["observe"] for action in acts)}
    helpers = {
        "sc_put": [f"function sc_put(sc_c: memref<{name}>, sc_w: {name}) {{", "    CanStore.store(sc_c, sc_w);", "}"],
        "sc_inc": [f"function sc_inc(sc_c: memref<{name}>, sc_w: {name}) {{",
                   "    CanStore.store(sc_c, (CanStore.load(sc_c) + sc_w));", "}"],
        "sc_sum": [f"function sc_sum(sc_v: {name}[]) returns ({name}) {{", f"    let sc_t: {name} = 0;", "    " + loop,
                   "        sc_t += sc_v[sc_i];", "    }", "    return sc_t;", "}"],
        "sc_fill": [f"function sc_fill(sc_v: {name}[], sc_w: {name}) {{", "    " + loop, "        sc_v[sc_i] = sc_w;",
                    "    }", "}"],
        "sc_mk": [f"function sc_mk(sc_p: {name}, sc_q: {name}) returns ({name}[]) {{", "    return [sc_p, sc_q];", "}"],
        "sc_tail": [f"function sc_tail(sc_v: {name}[], sc_s: uint256) returns (arraySlice<{name}[]>) {{",
                    "    return sc_v[sc_s:];", "}"],
        "sc_get": [f"function sc_get<c>(sc_c: c, sc_i: uint256) returns ({name}) where (c, uint256): "
                   f"RValueIdxAccess<{name}> {{", "    return ridx(sc_c, sc_i);", "}"],
        "sc_len": ["function sc_len<c>(sc_c: c) returns (uint256) where c: Length {", "    return sc_c.length;", "}"]}
    helper_lines = [line for key, lines in helpers.items() if used[key] for line in lines + [""]]
    values = [f"let sc_v{position}: {name} = Typedef.abs(" +
              (offset_text(int(value["offset"])) if value["raw"] else convert_text(kind, offset_text(int(value["offset"])))) +
              ");" for position, value in enumerate(plan["values"])]
    indices = []
    for position, index in enumerate(plan["indices"]):
        if index["flagged"]:
            word = f"(sc_x & {hex_text(FLAG + index['mask'])})"
        elif index["shift"] == 0:
            word = f"(sc_x & {index['mask']})"
        else:
            word = f"((sc_x >> {index['shift']}) & {index['mask']})"
        indices.append(f"let sc_k{position}: uint256 = uint256({word});")
    body, counts = [], [0, 0, 0]
    for step in plan["steps"]:
        body += step_lines(kind, tuple(counts), step)
        if isinstance(step, dict):
            tag = next(iter(step))
            if tag in ("alloc", "literal", "alias", "copy", "made"):
                counts[0] += 1
            elif tag in ("slice", "tail"):
                counts[1] += 1
            elif tag in ("grid", "gridOf", "gridLiteral"):
                counts[2] += 1
    result = plan["result"]
    if result == "word":
        returned, result_type = ["return uint256(sc_r);"], "uint256"
    else:
        returned = [f"return {name_text(result['array'])};" if "array" in result else f"return toArray(sc_s{result['copy']});"]
        result_type = name + "[]"
    parameters = [f"sc_p{position}: " + (f"calldata<{name}[]>" if param["calldata"] else f"{name}[]")
                  for position, param in enumerate(plan["params"])]
    lines = (imports + [""] + helper_lines + [f"contract {profile['contract']} {{"] +
             ([f"    sc_st: {name}[];", ""] if uses_storage(plan) else []) +
             [f"    function run({', '.join(parameters + ['input: uint256'])}) public returns ({result_type}) {{"] +
             indent(8, ["let sc_x: word = Typedef.rep(input);"] + values + indices + ["let sc_r: word = 0;"] + body + returned) +
             ["    }", "}"])
    return "\n".join(lines) + "\n"


# Calldata, encoded here from the ABI specification.

def signature(plan):
    return "run(" + ",".join([plan["element"] + "[]"] * len(plan["params"]) + ["uint256"]) + ")"


def calldata(plan, x):
    selector = storage.keccak256(signature(plan).encode())[:4]
    if not plan["params"]:
        return selector + x.to_bytes(32, "big")
    kind = Type(plan["element"])
    machine = Machine(plan, kind, x)
    head, tail = [], b""
    position = 32 * (len(plan["params"]) + 1)
    for number in range(len(plan["params"])):
        head.append(position)
        length = machine.param_length(number)
        encoded = length.to_bytes(32, "big") + b"".join(machine.param_word(number, k).to_bytes(32, "big")
                                                       for k in range(length))
        tail += encoded
        position += len(encoded)
    return selector + b"".join(offset.to_bytes(32, "big") for offset in head) + x.to_bytes(32, "big") + tail


def nodes(value):
    """An upper bound on the reference's Wire nodes: every tagged object, its types included."""
    if isinstance(value, dict):
        return ("tag" in value) + sum(nodes(child) for child in value.values())
    if isinstance(value, list):
        return sum(nodes(child) for child in value)
    return 0


def words_type(count):
    if count == 1:
        return "word"
    return {"tag": "product", "left": "word", "right": words_type(count - 1)}


def check_case(case, fuel, profile):
    require(isinstance(case, dict) and case.get("schema") == profile["schema"], "unexpected array case schema")
    plan = check_plan(case[profile["planKey"]], profile)
    number = canonical_word(case["input"])
    program = case["program"]
    payload = {"tag": "product", "left": "word", "right": {"tag": "product", "left": "word", "right": "word"}}
    left = words_type(1 + RETURN_WORDS) if profile["abi"] else "word"
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == {"tag": "sum", "left": left, "right": payload},
            "the array reference is a closed program returning a Word or return data, or revert data")
    require(nodes(program["body"]) <= CASE_LIMIT, "reference exceeds the case limit")
    require(1 <= case["provenance"]["referenceNodes"] <= CASE_LIMIT, "recorded reference size exceeds the case limit")
    name = profile["contract"]
    require(case["contract"] == {"name": name, "method": "run", "signature": signature(plan),
            "deployPath": [name + "Deploy"], "runtimePath": [name + "Deploy", name],
            "calldata": "0x" + calldata(plan, number).hex(), "constructorCalldata": "0x"},
            "unexpected array wrapper or calldata")
    require(case["source"] == emit(plan, profile), "the source differs from the plan's emission")
    require(case["provenance"][profile["shapesKey"]] == shapes(plan, profile), "recorded shapes differ from the plan")
    require(observed_text(case["directCore"]) == outcome_text(interpret(plan, number)[0]),
            "the recorded Core outcome differs from the plan's interpreter")
    return plan


def check_manifest(manifest, profile):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals", "requiredInputs",
              profile["requirements"], "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == profile["profile"], "unexpected array manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "array coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    require(manifest["requiredFeatures"] == [] and manifest["requiredWordLiterals"] == [],
            "the array corpus requires shapes, not step features or literals")
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "the array corpus must require all eight boundary inputs")
    require(manifest[profile["requirements"]] == required(profile), "the array corpus must require its shape values")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "the array corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"id", "generation", "input", "expectedFeatures"},
                "an array corpus entry is a generation recipe with its input")
        identifier = entry["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        require(canonical_word(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        require(entry["expectedFeatures"] == [], "array entries expect no step features")
        recipe = entry["generation"]
        require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
        require(canonical_word(recipe["seed"]) < 1 << 64 and recipe["maxProgramNodes"] == NODES,
                "fixed recipes use a uint64 seed and the default budget")
    return entries


def generated_plan(tool, seed, fuel, profile):
    """The seed's plan, or None for an excluded seed."""
    corpus = run(tool, profile["command"], str(seed), str(NODES), "1", "1", str(fuel))
    cases = corpus.get("cases")
    require(isinstance(cases, list) and len(cases) <= 1, "invalid generation response")
    return check_plan(cases[0][profile["planKey"]], profile) if cases else None


def selection(tool, fuel, last, profile):
    """The roadmap's construction: from seed 1 upwards, every accepted seed
    whose plan covers a missing value, until nothing is missing. One request
    generates a run of seeds, the attempts in order."""
    missing = {dimension: set(values) for dimension, values in required(profile).items()}
    chosen, seed = [], 1
    while seed <= last and any(missing.values()):
        count = min(128, last - seed + 1)
        corpus = run(tool, profile["command"], str(seed), str(NODES), str(8 * count), str(count), str(fuel))
        require(corpus.get("attempted") == count, "a selection request skipped attempts")
        plans = {}
        for case in corpus.get("cases", []):
            plans.setdefault(int(case["provenance"]["origin"]["seed"]), case[profile["planKey"]])
        for plan_seed in sorted(plans):
            if not any(missing.values()):
                break
            plan = check_plan(plans[plan_seed], profile)
            found = shapes(plan, profile)
            if any(missing[dimension] & set(found[dimension]) for dimension in missing):
                chosen.append(plan_seed)
                for dimension in missing:
                    missing[dimension] -= set(found[dimension])
        seed += count
    require(not any(missing.values()), "seeds up to the last chosen one leave a requirement missing")
    return chosen


def materialize(entry, tool, fuel, profile):
    recipe = entry["generation"]
    corpus = run(tool, profile["command"], recipe["seed"], str(recipe["maxProgramNodes"]), "8", "1", str(fuel))
    require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
            and corpus.get("requested") == 8 and corpus.get("attempted") == 1
            and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 8,
            "fixed array seed did not emit eight cases in one attempt")
    cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
    require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
    case = cases[0]
    origin = case["provenance"]["origin"]
    require(origin == {"kind": profile["origin"], "seed": recipe["seed"], "maxProgramNodes": recipe["maxProgramNodes"],
                       "inputIndex": BOUNDARIES.index(int(entry["input"])), "validationFuel": fuel},
            "generated recipe differs from manifest")
    check_case(case, fuel, profile)
    return case


def checked_shrinks(case, tool, directory, fuel, profile):
    path = directory / "shrink-parent.json"
    path.write_text(json.dumps(case))
    reduced = run(tool, "shrink", str(path), "64", str(fuel))
    require(reduced == run(tool, "shrink", str(path), "64", str(fuel)), "native shrink order changed")
    candidates = reduced.get("cases")
    require(isinstance(candidates, list) and candidates, "fixed array case has no shrink candidate")
    require(sum(len(json.dumps(candidate, separators=(",", ":"))) for candidate in candidates) <= SHRINK_BYTES,
            "a shrink response exceeds its byte cap")
    key = profile["planKey"]
    parent = (plan_size(case[key]), int(case["input"]))
    seen = set()
    for candidate in candidates:
        check_case(candidate, fuel, profile)
        require(candidate["provenance"]["origin"] == {"kind": "reduced", "parentPlan": case[key],
                                                      "parentInput": case["input"]},
                "a shrink candidate is not a reduction of its parent")
        require((plan_size(candidate[key]), int(candidate["input"])) < parent, "a shrink candidate is not strictly smaller")
        encoded = json.dumps([candidate[key], candidate["input"]], sort_keys=True)
        require(encoded not in seen, "duplicate canonical shrink")
        seen.add(encoded)
        target = directory / "shrunk.json"
        target.write_text(json.dumps(candidate))
        require(run(tool, "replay", str(target), str(fuel)) == candidate,
                "native shrink lost canonical source/program/provenance")
        fresh = run(tool, "observe", str(target), str(fuel))
        observed_text(fresh)
        require(fresh == candidate["directCore"], "shrunk observation differs from fresh Core execution")
    return len(candidates)


def policy_checks(manifest, sample, tool, directory, fuel, profile):
    count = 0

    def rejects(action, label):
        nonlocal count
        try:
            action()
        except (ValueError, KeyError, TypeError, IndexError):
            count += 1
        else:
            raise ValueError("negative check accepted " + label)

    needed = required(profile)
    for field, value in (("profile", "runtime-revert-data"), ("requiredInputs", ["0"]), ("requiredFeatures", ["let"]),
                         *((profile["requirements"], {**needed, dimension: needed[dimension][1:]})
                           for dimension in needed if needed[dimension])):
        changed = copy.deepcopy(manifest)
        changed[field] = value
        rejects(lambda: check_manifest(changed, profile), field)
    plan = sample[profile["planKey"]]
    observe = {"observe": {"length": {"array": {"var": 0}}}}
    literal = {"literal": [{"input": 0}]}
    write = {"write": {"target": {"array": {"var": 0}}, "index": {"literal": 0}, "value": {"input": 0}, "form": "plain"}}
    broken_plans = [
        ("no step", {**plan, "steps": []}),
        ("thirteen steps", {**plan, "steps": [literal, observe] + [observe] * 11}),
        ("a name before its declaration", {**plan, "steps": [observe] + plan["steps"]}),
        ("five arrays", {**plan, "steps": [literal] * 5 + [observe]}),
        ("five literal values", {**plan, "steps": [{"literal": [{"input": 0}] * 5}, observe]}),
        ("an index literal past 7", {**plan, "steps": [literal, {"write": {**write["write"], "index": {"literal": 8}}}, observe]}),
        ("the counter outside the loop", {**plan, "steps": [literal, {"write": {**write["write"], "index": "counter"}}, observe]}),
        ("a value past the literals", {**plan, "steps": [{"literal": [{"literal": 11}]}, observe]}),
        ("a loop over more than four elements", {**plan, "indices": [{"shift": 0, "mask": 7, "flagged": False}],
                                                 "steps": [{"alloc": {"input": 0}},
                                                           {"loop": {"over": {"array": {"var": 0}}, "body": [observe]}}]}),
        ("two loops", {**plan, "steps": [literal] + [{"loop": {"over": {"array": {"var": 0}}, "body": [observe]}}] * 2}),
        ("a loop of three actions", {**plan, "steps": [literal, {"loop": {"over": {"array": {"var": 0}}, "body": [observe] * 3}}]}),
        ("a memref write to storage", {**plan, "steps": [{"push": {"input": 0}},
            {"write": {**write["write"], "target": "storage", "form": "put"}}, observe]}),
        ("a first value offset", {**plan, "values": [{"offset": "1", "raw": False}]}),
        ("four values", {**plan, "values": [{"offset": "0", "raw": False}] + [{"offset": "1", "raw": False}] * 3}),
        ("a flagged shifted index", {**plan, "indices": [{"shift": 1, "mask": 1, "flagged": True}]}),
        ("an index mask outside the table", {**plan, "indices": [{"shift": 0, "mask": 2, "flagged": False}]}),
        ("an unknown type", {**plan, "element": "uint7"}),
        ("the other plan schema", {**plan, "schema": (MEMORY if profile["abi"] else ABI)["planSchema"]})]
    if profile["abi"]:
        broken_plans += [
            ("no parameter", {**plan, "params": []}),
            ("three parameters", {**plan, "params": plan["params"] * 3}),
            ("a parameter length past 4", {**plan, "params": [{**plan["params"][0], "length": {"literal": 5}}]}),
            ("the storage array", {**plan, "steps": [{"push": {"input": 0}}, observe]}),
            ("a raw value with the fold", {**plan, "element": "uint8", "values": [{"offset": "0", "raw": True}],
                                           "result": "word"}),
            ("raw elements of a 256-bit type", {**plan, "element": "uint256",
                                               "params": [{**plan["params"][0], "raw": True, "offset": "0"}]})]
    else:
        broken_plans += [
            ("a parameter", {**plan, "params": [{"calldata": True, "length": {"literal": 1}, "offset": "0", "raw": False}]}),
            ("an array result", {**plan, "result": {"array": {"var": 0}}}),
            ("no observation", {**plan, "steps": [literal]}),
            ("a raw value", {**plan, "values": [{"offset": "0", "raw": True}]}),
            ("nine pushes", {**plan, "steps": [{"push": {"input": 0}}] * 9 + [observe]}),
            ("a flagged setLength", {**plan, "indices": [{"shift": 0, "mask": 1, "flagged": True}],
                                     "steps": [{"setLength": {"input": 0}}, observe]})]
    for label, broken in broken_plans:
        rejects(lambda: check_plan(broken, profile), label)
    path = directory / "negative.json"
    key = profile["planKey"]
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("a removed step", lambda value: value[key]["steps"].pop() if len(value[key]["steps"]) > 1 else
            value[key]["steps"].append(observe)),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="1" if value["input"] != "1" else "2")),
        ("wrapper", lambda value: value["contract"].update(name="SynthesizedRevertData")),
        ("calldata", lambda value: value["contract"].update(calldata=value["contract"]["calldata"] + "00")),
        ("shapes", lambda value: value["provenance"][profile["shapesKey"]].update(types=[])),
        ("generator version", lambda value: value["provenance"].update(generatorVersion="core-integers-v1")),
    ):
        changed = copy.deepcopy(sample)
        change(changed)
        path.write_text(json.dumps(changed))
        result = subprocess.run([str(tool), "replay", str(path), str(fuel)], cwd=ROOT,
                                text=True, capture_output=True, timeout=60, check=False)
        require(result.returncode != 0, "native replay accepted altered " + label)
        count += 1
    forged = copy.deepcopy(sample)
    forged["directCore"] = {"stage": "execution", "status": "returned", "word": "7"}
    path.write_text(json.dumps(forged))
    require(run(tool, "replay", str(path), str(fuel)) == sample, "native replay trusted saved execution evidence")
    count += 1
    path.write_text(json.dumps(sample))
    lower = run(tool, "replay", str(path), "0")
    require(lower["program"] == sample["program"] and lower["source"] == sample["source"]
            and lower["directCore"].get("status") == "out-of-fuel", "zero budget changed canonical code or invented completion")
    rejects(lambda: observed_text(lower["directCore"]), "resource result as shape coverage")
    for args in ((profile["command"], str(1 << 64), "1024", "8", "1", str(fuel)),
                 (profile["command"], "1", "2049", "8", "1", str(fuel)),
                 (profile["command"], "1", str(profile["minimum"] - 1), "8", "1", str(fuel)),
                 ("shrink", str(path), "4097", str(fuel))):
        result = subprocess.run([str(tool), *args], cwd=ROOT, text=True, capture_output=True, timeout=60, check=False)
        generated = result.returncode == 0 and json.loads(result.stdout).get("cases")
        require(result.returncode != 0 or not generated, "native CLI accepted an out-of-range budget")
        count += 1
    return count


def validate(manifest, tool, fuel, profile):
    require(type(fuel) is int and 0 < fuel <= 10_000_000, "invalid positive execution fuel")
    entries = check_manifest(manifest, profile)
    groups, seeds, inputs, samples = {}, [], set(), []
    found = {dimension: set() for dimension in profile["shapes"]}
    outcomes = {}
    with tempfile.TemporaryDirectory(prefix="array-corpus-") as name:
        directory = Path(name)
        for entry in entries:
            case = materialize(entry, tool, fuel, profile)
            require(case == materialize(entry, tool, fuel, profile), "materialization is not deterministic")
            for version in VERSIONS:
                require(case["provenance"][version] == manifest[version], f"{version} changed")
            plan = check_case(case, fuel, profile)
            path = directory / "case.json"
            path.write_text(json.dumps(case))
            before = run(tool, "observe", str(path), str(fuel))
            result = observed_text(before)
            require(before == case["directCore"], "saved observation differs from fresh original Core")
            require(run(tool, "replay", str(path), str(fuel)) == case, "native canonical replay changed the case")
            label = "returned" if before["status"] == "returned" else result
            outcomes[label] = outcomes.get(label, 0) + 1
            plan_key = json.dumps(plan, sort_keys=True)
            if plan_key not in groups:
                seeds.append(int(entry["generation"]["seed"]))
                samples.append(case)
            group = groups.setdefault(plan_key, {"inputs": set(), "source": case["source"], "results": set()})
            require(group["source"] == case["source"], "identical array plan emitted input-dependent source")
            group["inputs"].add(int(case["input"]))
            group["results"].add(result)
            # Only completed, replayed native cases contribute coverage.
            inputs.add(int(case["input"]))
            for dimension, values in shapes(plan, profile).items():
                found[dimension] |= set(values)
        require(inputs == set(BOUNDARIES), "lost completed input coverage")
        for dimension, values in required(profile).items():
            require(set(values) <= found[dimension], f"lost completed {dimension} coverage")
        for group in groups.values():
            require(group["inputs"] == set(BOUNDARIES), "array plan lacks a completed boundary input")
            require(len(group["results"]) > 1, "fixed array plan had one outcome for every boundary input")
        require(seeds == selection(tool, fuel, max(seeds), profile), "the corpus is not every covering seed in order")
        shrinks = sum(checked_shrinks(case, tool, directory, fuel, profile) for case in samples[:2])
        checks = policy_checks(manifest, samples[0], tool, directory, fuel, profile)
    return {"status": "passed", "profile": profile["profile"], "cases": len(entries), "plans": len(groups),
            "seeds": seeds, "outcomes": dict(sorted(outcomes.items())),
            "completedInputs": [str(value) for value in sorted(inputs)],
            "coverage": {"classification": "specified-by-the-plan-and-its-boundary-runs-not-measured",
                         **{dimension: sorted(values) for dimension, values in found.items()}},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main(profile=MEMORY):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path, default=ROOT / profile["manifest"])
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel, profile),
                     sort_keys=True))


if __name__ == "__main__":
    main()
