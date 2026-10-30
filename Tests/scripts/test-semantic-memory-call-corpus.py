#!/usr/bin/env python3
"""Check the fixed memory call corpus using fresh native Core executions.

The corpus takes, from seed 1 upwards at the default budget, every generated
plan that covers a missing memory call shape, each at the eight primitive
boundary inputs; every shape value is required. This test rebuilds that
selection, admits every plan with its own walk over the helpers and the
scope, recomputes every shape and the shrink measure from the plan alone,
re-emits the source and compares it exactly, evaluates every case's plan with
its own model, which runs each helper as a function over byte lists with
std's range checks and Keccak-256, against the recorded Core outcome, and
replays, observes and shrinks natively. It neither compiles Rust nor executes
an EVM. The memory value corpus's checker supplies `runtime-memory-values`'
actions: their admission, text and byte-list model.
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


pure = load("memory_call_corpus_pure", "Tests/scripts/test-semantic-corpus.py")
generic = load("memory_call_corpus_generic", "Tests/scripts/test-semantic-generic-corpus.py")
memory = load("memory_call_corpus_values", "Tests/scripts/test-semantic-memory-value-corpus.py")
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
ref_of, keccak256, OutOfBounds = memory.ref_of, memory.keccak256, memory.OutOfBounds
VERSIONS = pure.VERSIONS + ("profileVersion", "boundaryVersion")
BOUNDARIES = memory.BOUNDARIES
CASE_SCHEMA = "solcore-lean.semantic-memory-call-case.v1"
PLAN_SCHEMA = "solcore-lean.memory-call-plan.v1"
PROFILE = "runtime-memory-calls"
NAME = "SynthesizedMemoryCalls"
NODES = 1024
CASE_LIMIT = 5120
SHRINK_BYTES = 1_500_000
OUT_OF_BOUNDS = memory.OUT_OF_BOUNDS
M = 1 << 256
FOLD_CONSTANTS = memory.FOLD_CONSTANTS
PARAMS = ("bytes", "slice", "generic", "array", "pair", "sum", "enum")
MEMORY_PARAMS = ("bytes", "slice", "generic")
DATA_PARAMS = ("pair", "sum", "enum")
OBSERVATIONS = ("length", "word", "byte", "hash", "element")
SHAPES = {
    "helpers": sorted(f"{kind}:{param}" for kind, params in (
        ("read", ("bytes", "slice", "generic", "array")), ("write", ("bytes", "slice", "generic", "array")),
        ("view", MEMORY_PARAMS), ("copy", MEMORY_PARAMS), ("call", PARAMS), ("pack", ("bytes",)), ("take", DATA_PARAMS))
        for param in params),
    "calls": sorted(f"{form}:{result}" for form in ("direct", "value") for result in ("word", "bytes", "slice", "array", "pair")),
    "passes": ["array", "bytes", "pair", "slice"],
    "instances": ["bytes", "several", "slice"],
    "data": ["enum0", "enum1", "inl", "inr", "pair"],
    "closures": sorted([f"{obs}:{kind}" for obs in ("length", "word", "byte", "hash") for kind in ("bytes", "slice")] +
                       ["element:array"]),
    "observations": sorted([f"{obs}:{kind}" for obs in ("length", "word", "byte", "hash")
                            for kind in ("bytes", "slice", "pair", "sum", "enum")] +
                           ["carried:enum", "carried:sum", "element:array"]),
    "indices": sorted(f"{access}:{kind}" for access in ("byte", "element", "put", "put8", "set", "word")
                      for kind in ("input", "literal")),
    "ranges": ["apply", "call"],
    "hazards": ["alias", "closure", "copy", "helper"],
    "steps": sorted([f"action:{kind}" for kind in ("alias", "array", "bytes", "observe", "slice", "write")] +
                    ["apply", "call", "closure", "data"])}
REQUIRED = SHAPES
HELPERS = memory.HELPERS


# --- Helpers ----------------------------------------------------------------------

def check_helpers(helpers):
    require(isinstance(helpers, list) and 1 <= len(helpers) <= 3, "a memory call plan has one to three helpers")
    for index, helper in enumerate(helpers):
        require(isinstance(helper, dict) and helper.get("param") in PARAMS, "unknown helper parameter")
        param, kind = helper["param"], helper.get("kind")
        fields = {"read": {"obs", "fold"}, "write": {"width"}, "view": {"start"}, "copy": set(),
                  "call": {"callee", "constant"}, "pack": {"constant"}, "take": {"obs", "fold", "written"}}
        require(kind in fields and set(helper) == {"param", "kind"} | fields[kind], "invalid helper fields")
        if kind in ("read", "take"):
            require(helper["obs"] in OBSERVATIONS and helper["fold"] in ("add", "xor"), "invalid helper observation")
        if kind == "read":
            require((helper["obs"] == "element") == (param == "array") and param not in DATA_PARAMS,
                    "a read observes an array's element or a memory value")
        elif kind == "write":
            require(param in MEMORY_PARAMS + ("array",) and helper["width"] in ("word", "byte")
                    and (param != "array" or helper["width"] == "word"), "invalid helper write")
        elif kind == "view":
            require(param in MEMORY_PARAMS and type(helper["start"]) is int and 0 <= helper["start"] <= 32,
                    "invalid helper view")
        elif kind == "copy":
            require(param in MEMORY_PARAMS, "a copy takes a memory value")
        elif kind == "call":
            callee, constant = helper["callee"], helper["constant"]
            require(type(callee) is int and 0 <= callee < index and type(constant) is int and 1 <= constant <= 255,
                    "a call calls an earlier helper with a constant from 1 to 255")
            target = helpers[callee]["param"]
            require(target == param or (target == "generic" and param in MEMORY_PARAMS),
                    "a called helper takes the caller's parameter")
        elif kind == "pack":
            require(param == "bytes" and type(helper["constant"]) is int and 1 <= helper["constant"] <= 255,
                    "a pack takes a bytes value and a constant from 1 to 255")
        else:
            require(param in DATA_PARAMS and helper["obs"] != "element" and type(helper["written"]) is bool,
                    "a take takes a pair, sum or enum")
    return helpers


def resolve(helpers, index):
    """The base helper a call reaches through `call` helpers, the constants
    added on the way, and the helpers it runs."""
    added, chain = 0, []
    while helpers[index]["kind"] == "call":
        chain.append(index)
        added += helpers[index]["constant"]
        index = helpers[index]["callee"]
    return helpers[index], added, chain + [index]


def result_of(helpers, index, arg_kind):
    kind = resolve(helpers, index)[0]["kind"]
    return {"read": "word", "take": "word", "write": arg_kind, "view": "slice", "copy": "bytes", "pack": "pair"}[kind]


def accepts(param, kind):
    return param == kind or (param == "generic" and kind in ("bytes", "slice"))


# --- The scope --------------------------------------------------------------------

class Env:
    """`runtime-memory-values`' scope, then the data values and closures:
    a pair holds a value, `inl` and `Sc_E0` a value, `inr` and `Sc_E1` none."""

    def __init__(self):
        self.scope = memory.Scope()
        self.pairs, self.sums, self.enums, self.closures, self.values = [], [], [], [], 0

    def copy(self):
        other = Env()
        other.scope = self.scope.copy()
        other.pairs, other.sums, other.enums = list(self.pairs), list(self.sums), list(self.enums)
        other.closures, other.values = list(self.closures), self.values
        return other

    def argument(self, name):
        """The argument's kind and the value it reaches, or None."""
        require(isinstance(name, str), "an argument is a name")
        for prefix, kind, values in (("sc_t", "pair", self.pairs), ("sc_u", "sum", self.sums),
                                     ("sc_e", "enum", self.enums)):
            if name.startswith(prefix):
                digits = name[len(prefix):]
                require(digits.isdecimal() and str(int(digits)) == digits and int(digits) < len(values),
                        "a data variable is not in scope")
                return kind, values[int(digits)]
        kind, entry = self.scope.var(name)
        return kind, entry

    def declare(self, kind, entry):
        if kind == "pair":
            require(len(self.pairs) < 2, "too many pairs")
            self.pairs.append(entry)
        else:
            self.scope.declare(kind, entry)


def obs_valid(obs, entry):
    """In-range positions of an observation of `entry`, at least one, or 0."""
    length = entry[2]
    if obs in ("length", "hash"):
        return 1
    if obs == "word":
        return length - 31 if length >= 32 else 0
    return length


def call_valid(base, entry):
    """The in-range positions of what a base kind does at an index, or None
    when it uses no index."""
    kind = base["kind"]
    if entry is None:
        return None
    if kind in ("read", "take"):
        valid = obs_valid(base["obs"], entry) if base["obs"] in ("word", "byte", "element") else None
        if kind == "take" and base["written"]:
            byte = entry[2]
            return byte if valid is None else min(byte, valid)
        return valid
    if kind == "write":
        return entry[2] if base["param"] == "array" else memory.width_valid(base["width"], entry[2])
    return None


def check_call_index(base, entry, index):
    kind = base["kind"]
    if entry is not None and kind == "take" and base["written"]:
        memory.check_index(index, False, entry[2])
        if base["obs"] in ("word", "byte"):
            memory.check_index(index, False, obs_valid(base["obs"], entry))
        return
    valid = call_valid(base, entry)
    if valid is None:
        require(index == {"index": "literal", "value": 0}, "an unused index is the literal 0")
    else:
        memory.check_index(index, False, valid)


def held(value):
    """The entry a data value holds, or None."""
    if isinstance(value, tuple) and len(value) == 3 and all(type(part) is int for part in value):
        return value
    if isinstance(value, tuple) and value[0] in ("inl", "first"):
        return value[1]
    if isinstance(value, tuple) and value[0] == "pair":
        return value[1]
    return None


def check_call(env, helpers, call):
    """Admit a call; return the next scope, whether it hashes and whether it
    observes."""
    require(isinstance(call, dict) and set(call) == {"helper", "arg", "index", "word", "form", "fold", "constant"},
            "invalid call fields")
    index = call["helper"]
    require(type(index) is int and 0 <= index < len(helpers), "a call names a helper")
    arg_kind, value = env.argument(call["arg"])
    require(accepts(helpers[index]["param"], arg_kind), "a helper does not take the argument")
    memory.check_operand(call["word"], False)
    require(call["form"] in ("direct", "value") and call["fold"] in ("add", "xor"), "invalid call form or fold")
    base, _, _ = resolve(helpers, index)
    result = result_of(helpers, index, arg_kind)
    entry = held(value) if arg_kind in DATA_PARAMS else value
    check_call_index(base, entry, call["index"])
    if result == "word":
        require(call["constant"] in FOLD_CONSTANTS, "a Word result's fold constant is odd from 3 to 31")
    else:
        require(call["fold"] == "add" and call["constant"] == 3, "a value result keeps the fold + with constant 3")
    env = env.copy()
    kind = base["kind"]
    if kind == "view":
        require(base["start"] <= entry[2], "a view starts past the value's end")
        env.declare("slice", (entry[0], entry[1] + base["start"], entry[2] - base["start"]))
    elif kind == "copy":
        require(entry[2] + 32 <= 128, "a copy over 128 bytes")
        env.scope.objects.append((False, entry[2] + 32))
        env.declare("bytes", (len(env.scope.objects) - 1, 0, entry[2] + 32))
    elif kind == "write":
        env.declare(result, entry)
    elif kind == "pack":
        env.declare("pair", ("pair", entry))
    if call["form"] == "value":
        require(env.values < 3, "too many function values")
        env.values += 1
    hashes = (kind == "read" and base["obs"] == "hash") or (kind == "take" and base["obs"] == "hash" and entry is not None)
    return env, hashes, result == "word"


def check_datum(env, datum):
    require(isinstance(datum, dict), "a datum is an object")
    env = env.copy()
    kind = datum.get("datum")
    if kind in ("pair", "inl", "enum0"):
        require(set(datum) == ({"datum", "value"} if kind == "inl" else {"datum", "value", "word"}), "invalid datum")
        ref_kind, entry = env.scope.var(datum["value"])
        require(ref_kind == "bytes", "a data value holds a bytes value")
        if kind != "inl":
            memory.check_operand(datum["word"], False)
        if kind == "pair":
            env.declare("pair", ("pair", entry))
        elif kind == "inl":
            require(len(env.sums) < 2, "too many sums")
            env.sums.append(("inl", entry))
        else:
            require(len(env.enums) < 2, "too many enums")
            env.enums.append(("first", entry))
    else:
        require(kind in ("inr", "enum1") and set(datum) == {"datum", "word"}, "invalid datum")
        memory.check_operand(datum["word"], False)
        values = env.sums if kind == "inr" else env.enums
        require(len(values) < 2, "too many sums or enums")
        values.append(("word",))
    return env


def check_step(env, helpers, step):
    """Admit a step; return the next scope, whether it hashes and whether it
    observes."""
    require(isinstance(step, dict) and len(step) == 1, "a step is an object of one kind")
    if "action" in step:
        action = step["action"]
        env = env.copy()
        env.scope = memory.step_scope(env.scope, action, False)
        observes = action["kind"] == "observe"
        return env, observes and action["access"]["access"] == "hash", observes
    if "call" in step:
        return check_call(env, helpers, step["call"])
    if "data" in step:
        return check_datum(env, step["data"]), False, False
    if "closure" in step:
        closure = step["closure"]
        require(isinstance(closure, dict) and set(closure) == {"value", "obs"}, "invalid closure")
        kind, entry = env.scope.var(closure["value"])
        require((closure["obs"] == "element") == (kind == "array") and closure["obs"] in OBSERVATIONS,
                "a closure observes an array's element or a memory value")
        require(len(env.closures) < 2 and obs_valid(closure["obs"], entry) >= 1, "too many closures or no position")
        env = env.copy()
        env.closures.append((closure["value"], entry, closure["obs"]))
        return env, False, False
    require("apply" in step, "unknown step")
    applied = step["apply"]
    require(isinstance(applied, dict) and set(applied) == {"closure", "index", "fold", "constant"}, "invalid application")
    number = applied["closure"]
    require(type(number) is int and 0 <= number < len(env.closures), "an application names a closure")
    _, entry, obs = env.closures[number]
    require(applied["fold"] in ("add", "xor") and applied["constant"] in FOLD_CONSTANTS, "invalid application fold")
    if obs in ("word", "byte", "element"):
        memory.check_index(applied["index"], False, obs_valid(obs, entry))
    else:
        require(applied["index"] == {"index": "literal", "value": 0}, "an unused index is the literal 0")
    return env, obs == "hash", True


def check_plan(plan):
    require(isinstance(plan, dict) and set(plan) == {"schema", "helpers", "steps"} and plan["schema"] == PLAN_SCHEMA,
            "unexpected memory call plan schema")
    helpers = check_helpers(plan["helpers"])
    steps = plan["steps"]
    require(isinstance(steps, list) and 1 <= len(steps) <= 12, "a memory call plan has one to twelve steps")
    env, hashes, observes, calls = Env(), 0, 0, 0
    for step in steps:
        env, hashing, observing = check_step(env, helpers, step)
        hashes += hashing
        observes += observing
        calls += "call" in step
    require(calls >= 1 and observes >= 1 and hashes <= 7, "call, observation or hash bounds")
    return plan


# --- Shapes, from the plan alone --------------------------------------------------

def index_kind(index):
    return index["index"]


def wide(index, valid):
    return index["index"] == "input" and valid is not None and index["modulus"] > valid


def shapes(plan):
    helpers = plan["helpers"]
    found = {dimension: set() for dimension in SHAPES}
    writes, copies, captures, instances = [], [], [], []
    returned = []  # the variables value results were declared as
    env = Env()

    def writes_to(value):
        return sum(1 for written, _, _ in writes if written == value)

    def observe(value, through):
        for written, writer, helper in writes:
            if written != value:
                continue
            if writer != through:
                found["hazards"].add("alias")
            if helper:
                found["hazards"].add("helper")
        if any(copied == value and writes_to(source) > before for copied, source, before in copies):
            found["hazards"].add("copy")

    for helper in helpers:
        found["helpers"].add(f"{helper['kind']}:{helper['param']}")
    for step in plan["steps"]:
        if "action" in step:
            action = step["action"]
            found["steps"].add("action:" + action["kind"])
            if action["kind"] == "write":
                writes.append((env.scope.var(action["target"])[1][0], action["target"], False))
            elif action["kind"] == "observe":
                observe(env.scope.var(action["value"])[1][0], action["value"])
            elif action["kind"] == "bytes":
                sources = [part["value"] for part in action["parts"] if part["part"] == "value"]
                if sources:
                    source = env.scope.var(sources[0])[1][0]
                    copies.append((len(env.scope.objects), source, writes_to(source)))
        elif "call" in step:
            call = step["call"]
            arg_kind, value = env.argument(call["arg"])
            result = result_of(helpers, call["helper"], arg_kind)
            found["calls"].add(f"{call['form']}:{result}")
            found["steps"].add("call")
            if call["arg"] in returned:
                found["passes"].add(arg_kind)
            base, _, chain = resolve(helpers, call["helper"])
            for number in chain:
                if helpers[number]["param"] == "generic":
                    found["instances"].add(arg_kind)
                    instances.append((number, arg_kind))
            entry = held(value) if arg_kind in DATA_PARAMS else value
            kind, index = base["kind"], call["index"]
            if entry is not None and kind == "read":
                if base["obs"] in ("word", "byte", "element"):
                    found["indices"].add(f"{base['obs']}:{index_kind(index)}")
                    if wide(index, obs_valid(base["obs"], entry)):
                        found["ranges"].add("call")
                found["observations"].add(f"{base['obs']}:{arg_kind}")
                observe(entry[0], call["arg"])
            elif entry is not None and kind == "write":
                access = "set" if base["param"] == "array" else "put" if base["width"] == "word" else "put8"
                found["indices"].add(f"{access}:{index_kind(index)}")
                if wide(index, call_valid(base, entry)):
                    found["ranges"].add("call")
                writes.append((entry[0], call["arg"], True))
            elif entry is not None and kind == "copy":
                copies.append((len(env.scope.objects), entry[0], writes_to(entry[0])))
            elif entry is not None and kind == "take":
                if base["written"]:
                    found["indices"].add(f"put8:{index_kind(index)}")
                    if wide(index, entry[2]):
                        found["ranges"].add("call")
                    writes.append((entry[0], call["arg"], True))
                if base["obs"] in ("word", "byte"):
                    found["indices"].add(f"{base['obs']}:{index_kind(index)}")
                    if wide(index, obs_valid(base["obs"], entry)):
                        found["ranges"].add("call")
                found["observations"].add(f"{base['obs']}:{arg_kind}")
                observe(entry[0], call["arg"])
            elif kind == "take":
                found["observations"].add(f"carried:{arg_kind}")
        elif "data" in step:
            found["data"].add(step["data"]["datum"])
            found["steps"].add("data")
        elif "closure" in step:
            closure = step["closure"]
            kind, entry = env.scope.var(closure["value"])
            found["closures"].add(f"{closure['obs']}:{kind}")
            found["steps"].add("closure")
            captures.append((entry[0], writes_to(entry[0])))
        else:
            applied = step["apply"]
            found["steps"].add("apply")
            name, entry, obs = env.closures[applied["closure"]]
            if obs in ("word", "byte", "element"):
                found["indices"].add(f"{obs}:{index_kind(applied['index'])}")
                if wide(applied["index"], obs_valid(obs, entry)):
                    found["ranges"].add("apply")
            value, before = captures[applied["closure"]]
            if writes_to(value) > before:
                found["hazards"].add("closure")
            observe(entry[0], name)
        env = check_step(env, helpers, step)[0]
        if "call" in step:
            result = result_of(helpers, step["call"]["helper"], env.argument(step["call"]["arg"])[0])
            if result in ("bytes", "slice", "array"):
                returned.append(f"{dict(bytes='sc_b', slice='sc_s', array='sc_a')[result]}"
                                f"{len(env.scope.vars[result]) - 1}")
            elif result == "pair":
                returned.append(f"sc_t{len(env.pairs) - 1}")
    if any(number == other and kind != other_kind for number, kind in instances for other, other_kind in instances):
        found["instances"].add("several")
    return found


# --- The plan's size, as the shrink measure counts it -----------------------------

def plus(*sizes):
    return (sum(size[0] for size in sizes), sum(size[1] for size in sizes))


def operand_size(o):
    return (1, 0) if o["operand"] == "input" else (2, o.get("constant", 0))


def index_size(i):
    return {"literal": lambda: (1, i["value"]), "input": lambda: (2, i["shift"] + i["modulus"]),
            "counter": lambda: (2, i["scale"] + i["offset"])}[i["index"]]()


def action_size(a):
    """`runtime-memory-values`' action measure, independently."""
    kind = a["kind"]
    if kind == "bytes":
        def part(p):
            if p["part"] == "word":
                return plus((1, 0), operand_size(p["operand"]))
            return (1, p["count"]) if p["part"] == "zeros" else (1, 0)
        return plus((1, 0), (1, 0) if a["build"] == "to_bytes" else (2, 0), *(part(p) for p in a["parts"]))
    if kind == "slice":
        cut = {"drop": lambda: (1, a.get("start", 0)), "take": lambda: (1, a.get("length", 0)),
               "window": lambda: (2, a["start"] + a["length"])}[a["cut"]]()
        return plus((1, 0), cut)
    if kind == "alias":
        return (1, 0)
    if kind == "array":
        return plus((2 if a["form"] == "allocated" else 1, 0), *(operand_size(o) for o in a["elements"]))
    if kind == "write":
        return plus((2 if a["form"] == "helper" else 1, 0), index_size(a["index"]), operand_size(a["value"]))
    access = a["access"]
    name = access["access"]
    observed = {"length": lambda: (1, 0), "hash": lambda: (2, 0),
                "element": lambda: plus((3 if access.get("form") == "get" else 2, 0), index_size(access["index"]))}.get(
        name, lambda: plus((2, 0), index_size(access["index"])))()
    return plus((2 if a["fold"] == "xor" else 1, a["constant"]), observed)


def plan_size(plan):
    """Constructors, then the sum of numeric literals; a call weighs more than
    the actions it amounts to."""
    def observed(obs, fold):
        return (1 if obs == "length" else 2) + (fold == "xor")

    def helper(h):
        kind = h["kind"]
        size = {"read": lambda: (observed(h["obs"], h["fold"]), 0), "write": lambda: (2 if h["width"] == "byte" else 1, 0),
                "view": lambda: (1, h["start"]), "copy": lambda: (1, 0),
                "call": lambda: (2, h["callee"] + h["constant"]), "pack": lambda: (1, h["constant"]),
                "take": lambda: (observed(h["obs"], h["fold"]) + h["written"], 0)}[kind]()
        return plus((1 + (2 if h["param"] == "generic" else 1), 0), size)

    def step(s):
        if "action" in s:
            return plus((1, 0), action_size(s["action"]))
        if "call" in s:
            c = s["call"]
            return plus((6 + (c["form"] == "value") + (c["fold"] == "xor"), c["helper"] + c["constant"]),
                        index_size(c["index"]), operand_size(c["word"]))
        if "data" in s:
            d = s["data"]
            if d["datum"] == "inl":
                return (4, 0)
            return plus((4 if d["datum"] in ("pair", "enum0") else 2, 0), operand_size(d["word"]))
        if "closure" in s:
            return (2 if s["closure"]["obs"] == "length" else 3, 0)
        a = s["apply"]
        return plus((2 + (a["fold"] == "xor"), a["closure"] + a["constant"]), index_size(a["index"]))

    total = plus(*(helper(h) for h in plan["helpers"]), *(step(s) for s in plan["steps"]))
    return total[0] * (1 << 16) + total[1]


# --- The source, re-emitted --------------------------------------------------------

TYPES = {"bytes": "memory<bytes>", "slice": "memory_ref", "generic": "a", "array": "memory<DynArray<uint256>>",
         "pair": "(memory<bytes>, word)", "sum": "sum<memory<bytes>, word>", "enum": "Sc_E", "word": "word"}
FOLD_TEXT = {"add": " + ", "xor": " ^ "}


def obs_text(value, index, obs):
    return {"length": f"MemorySize.len({value})", "word": f"sc_word({value}, {index})",
            "byte": f"sc_byte({value}, {index})", "hash": f"Typedef.rep(keccak256_({value}))",
            "element": f"Typedef.rep({value}[uint256({index})])"}[obs]


def helper_lines(helpers, index, helper):
    value = TYPES[helper["param"]]
    base = resolve(helpers, index)[0]
    result = {"read": "word", "take": "word", "write": value, "view": "memory_ref", "copy": "memory<bytes>",
              "pack": "(memory<bytes>, word)"}[base["kind"]]
    if helper["param"] == "generic":
        header = (f"function sc_h{index}<a>(sc_v: a, sc_i: word, sc_w: word) returns ({result}) "
                  "where a: MemorySize, a: MemoryPointer, a: MemoryEncode {")
    else:
        header = f"function sc_h{index}(sc_v: {value}, sc_i: word, sc_w: word) returns ({result}) {{"
    kind = helper["kind"]
    if kind == "read":
        body = [f"return ({obs_text('sc_v', 'sc_i', helper['obs'])}{FOLD_TEXT[helper['fold']]}sc_w);"]
    elif kind == "write":
        if helper["param"] == "array":
            body = ["IndexAccess.set(sc_v, uint256(sc_i), uint256(sc_w));"]
        else:
            body = [f"{'sc_put' if helper['width'] == 'word' else 'sc_put8'}(sc_v, sc_i, sc_w);"]
        body.append("return sc_v;")
    elif kind == "view":
        body = [f"return slice_(sc_v, {helper['start']});"]
    elif kind == "copy":
        body = ["return concat(sc_v, bytes32(sc_w));"]
    elif kind == "call":
        body = [f"return sc_h{helper['callee']}(sc_v, sc_i, (sc_w + {helper['constant']}));"]
    elif kind == "pack":
        body = [f"return (sc_v, (sc_w + {helper['constant']}));"]
    else:
        fold = FOLD_TEXT[helper["fold"]]

        def memory_arm(written_word):
            return ([f"sc_put8(sc_p, sc_i, {written_word});"] if helper["written"] else []) + \
                [f"return ({obs_text('sc_p', 'sc_i', helper['obs'])}{fold}sc_w);"]

        def arm(pattern, lines):
            return [f"case {pattern} {{"] + ["    " + line for line in lines] + ["}"]

        word_arm = [f"return (sc_q{fold}sc_w);"]
        if helper["param"] == "pair":
            arms = arm("(sc_p, sc_q)", memory_arm("sc_q"))
        elif helper["param"] == "sum":
            arms = arm("inl(sc_p)", memory_arm("sc_w")) + arm("inr(sc_q)", word_arm)
        else:
            arms = arm("Sc_E.Sc_E0(sc_p, sc_q)", memory_arm("sc_q")) + arm("Sc_E.Sc_E1(sc_q)", word_arm)
        body = ["match (sc_v) {"] + ["    " + line for line in arms] + ["}"]
    return [header] + ["    " + line for line in body] + ["}", ""]


def emitted_source(plan):
    helpers = plan["helpers"]
    counts, used, lines = {"bytes": 0, "slice": 0, "array": 0}, set(), []
    data = {"pair": 0, "sum": 0, "enum": 0, "closure": 0, "value": 0}
    env = Env()
    position = "sc_counter"

    def declare(kind):
        if kind in counts:
            prefix = {"bytes": "sc_b", "slice": "sc_s", "array": "sc_a"}[kind]
            text = f"let {prefix}{counts[kind]}: {TYPES[kind]}"
            counts[kind] += 1
        else:
            prefix = {"pair": "sc_t", "sum": "sc_u", "enum": "sc_e"}[kind]
            text = f"let {prefix}{data[kind]}: {TYPES[kind]}"
            data[kind] += 1
        return text

    for step in plan["steps"]:
        if "action" in step:
            lines += memory.action_lines(step["action"], position, counts, used)
        elif "call" in step:
            call = step["call"]
            arg_kind = env.argument(call["arg"])[0]
            result = result_of(helpers, call["helper"], arg_kind)
            arguments = (f"{call['arg']}, {memory.index_text(call['index'], position)}, "
                         f"{memory.operand_text(call['word'], position)}")
            callee = f"sc_h{call['helper']}"
            if call["form"] == "value":
                name = f"sc_f{data['value']}"
                data["value"] += 1
                lines.append(f"let {name}: function ({TYPES[arg_kind]}, word, word) returns ({TYPES[result]}) = {callee};")
                callee = name
            if result == "word":
                lines.append(f"sc_r = ((sc_r * {call['constant']}){FOLD_TEXT[call['fold']]}{callee}({arguments}));")
            else:
                lines.append(f"{declare(result)} = {callee}({arguments});")
        elif "data" in step:
            datum = step["data"]
            word = memory.operand_text(datum["word"], position) if "word" in datum else None
            kind = datum["datum"]
            if kind == "pair":
                lines.append(f"{declare('pair')} = ({datum['value']}, {word});")
            elif kind == "inl":
                lines.append(f"{declare('sum')} = inl({datum['value']});")
            elif kind == "inr":
                lines.append(f"{declare('sum')} = inr({word});")
            elif kind == "enum0":
                lines.append(f"{declare('enum')} = Sc_E.Sc_E0({datum['value']}, {word});")
            else:
                lines.append(f"{declare('enum')} = Sc_E.Sc_E1({word});")
        elif "closure" in step:
            closure = step["closure"]
            lines += [f"let sc_c{data['closure']}: function (word) returns (word) = lam (sc_j: word) -> word {{",
                      f"    return {obs_text(closure['value'], 'sc_j', closure['obs'])};", "};"]
            data["closure"] += 1
        else:
            applied = step["apply"]
            lines.append(f"sc_r = ((sc_r * {applied['constant']}){FOLD_TEXT[applied['fold']]}sc_c{applied['closure']}"
                         f"({memory.index_text(applied['index'], position)}));")
        env = check_step(env, helpers, step)[0]
    for step in plan["steps"]:
        if "closure" in step and step["closure"]["obs"] in ("word", "byte"):
            used.add("sc_" + step["closure"]["obs"])
    for helper in helpers:
        if helper["kind"] in ("read", "take") and helper["obs"] in ("word", "byte"):
            used.add("sc_" + helper["obs"])
        if helper["kind"] == "write" and helper["param"] != "array":
            used.add("sc_put" if helper["width"] == "word" else "sc_put8")
        if helper["kind"] == "take" and helper["written"]:
            used.add("sc_put8")
    enum = any(h["param"] == "enum" for h in helpers) or any(
        "data" in s and s["data"]["datum"] in ("enum0", "enum1") for s in plan["steps"])
    source = (["import * from std;", "import * from std.dispatch;",
               "import { mload, mstore, mstore8, shr, mod } from std.opcodes;", ""] +
              [line for helper in HELPERS if helper in used for line in memory.HELPER_LINES[helper]] +
              (["enum Sc_E {", "    Sc_E0(memory<bytes>, word),", "    Sc_E1(word)", "}", ""] if enum else []) +
              [line for index, helper in enumerate(helpers) for line in helper_lines(helpers, index, helper)] +
              [f"contract {NAME} {{", "    function run(input: uint256) public returns (uint256) {",
               "        let sc_x: word = Typedef.rep(input);", "        let sc_r: word = 0;"] +
              ["        " + line for line in lines] + ["        return uint256(sc_r);", "    }", "}"])
    return "\n".join(source) + "\n"


# --- A model that runs each helper as a function ----------------------------------

class Machine(memory.Machine):
    """`runtime-memory-values`' byte-list machine with helpers, data values and
    closures. A memory value is `(kind, (value, start, length))`; a pair is
    `("pair", entry, word)`, a sum `("inl", entry)` or `("inr", word)`, an enum
    `("first", entry, word)` or `("second", word)`."""

    def __init__(self, x, helpers):
        super().__init__(x)
        self.helpers = helpers
        self.pairs, self.sums, self.enums, self.closures = [], [], [], []

    def observed(self, entry, obs, position):
        value, start, length = entry
        if obs == "length":
            return length
        if obs == "hash":
            return keccak256(bytes(self.values[value][start:start + length]))
        if obs == "word":
            self.check(length, position, 32)
            return int.from_bytes(bytes(self.values[value][start + position:start + position + 32]), "big")
        if obs == "byte":
            self.check(length, position, 1)
            return self.values[value][start + position]
        if position >= length:
            raise OutOfBounds
        return self.values[value][start + position]

    def put(self, entry, position, word, width):
        value, start, length = entry
        if width == "word":
            self.check(length, position, 32)
            self.values[value][start + position:start + position + 32] = word.to_bytes(32, "big")
        else:
            self.check(length, position, 1)
            self.values[value][start + position] = word & 0xFF

    def call(self, index, argument, position, word):
        """Run helper `index` on `argument`; a Word or a value."""
        helper = self.helpers[index]
        kind = helper["kind"]
        fold = (lambda left, right: (left + right) % M) if helper.get("fold") == "add" else (lambda left, right: left ^ right)
        if kind == "read":
            return ("word", fold(self.observed(argument[1], helper["obs"], position), word))
        if kind == "write":
            value, start, length = argument[1]
            if argument[0] == "array":
                if position >= length:
                    raise OutOfBounds
                self.values[value][start + position] = word
            else:
                self.put(argument[1], position, word, helper["width"])
            return argument
        if kind == "view":
            value, start, length = argument[1]
            return ("slice", (value, start + helper["start"], length - helper["start"]))
        if kind == "copy":
            value, start, length = argument[1]
            self.values.append(bytearray(bytes(self.values[value][start:start + length]) + word.to_bytes(32, "big")))
            return ("bytes", (len(self.values) - 1, 0, length + 32))
        if kind == "call":
            return self.call(helper["callee"], argument, position, (word + helper["constant"]) % M)
        if kind == "pack":
            return ("pair", argument[1], (word + helper["constant"]) % M)
        held_value = argument[1]
        tag = held_value[0]
        if tag in ("inr", "second"):
            return ("word", fold(held_value[1], word))
        entry = held_value[1]
        carried = word if tag == "inl" else held_value[2]
        if helper["written"]:
            self.put(entry, position, carried, "byte")
        return ("word", fold(self.observed(entry, helper["obs"], position), word))

    def argument(self, name):
        for prefix, kind, values in (("sc_t", "pair", self.pairs), ("sc_u", "sum", self.sums),
                                     ("sc_e", "enum", self.enums)):
            if name.startswith(prefix):
                return (kind, values[int(name[len(prefix):])])
        return (ref_of(name)[0], self.view(name))

    def accumulate(self, fold, constant, observed):
        scaled = self.acc * constant % M
        self.acc = (scaled + observed) % M if fold == "add" else scaled ^ observed

    def step(self, s):
        if "action" in s:
            self.act(s["action"])
        elif "call" in s:
            c = s["call"]
            argument = self.argument(c["arg"])
            position, word = self.index(c["index"]), self.operand(c["word"])
            returned = self.call(c["helper"], argument, position, word)
            if returned[0] == "word":
                self.accumulate(c["fold"], c["constant"], returned[1])
            elif returned[0] == "pair":
                self.pairs.append(returned)
            else:
                self.declare(*returned)
        elif "data" in s:
            d = s["data"]
            kind = d["datum"]
            if kind == "pair":
                self.pairs.append(("pair", self.view(d["value"]), self.operand(d["word"])))
            elif kind == "inl":
                self.sums.append(("inl", self.view(d["value"])))
            elif kind == "inr":
                self.sums.append(("inr", self.operand(d["word"])))
            elif kind == "enum0":
                self.enums.append(("first", self.view(d["value"]), self.operand(d["word"])))
            else:
                self.enums.append(("second", self.operand(d["word"])))
        elif "closure" in s:
            self.closures.append((self.view(s["closure"]["value"]), s["closure"]["obs"]))
        else:
            a = s["apply"]
            entry, obs = self.closures[a["closure"]]
            self.accumulate(a["fold"], a["constant"], self.observed(entry, obs, self.index(a["index"])))


def model_outcome(plan, x):
    machine = Machine(x, plan["helpers"])
    try:
        for s in plan["steps"]:
            machine.step(s)
    except OutOfBounds:
        return {"stage": "execution", "status": "reverted", "output": OUT_OF_BOUNDS}
    return {"stage": "execution", "status": "returned", "word": str(machine.acc)}


outcome = memory.outcome


# --- Cases and the manifest ---------------------------------------------------------

def check_case(case, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected memory call case schema")
    plan = check_plan(case["memoryCallPlan"])
    number = canonical_word(case["input"])
    program = case["program"]
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == {"tag": "sum", "left": "word", "right": "unit"},
            "the memory call reference is a closed program returning a Word or an out-of-range access")
    require(generic.complexity(program["body"])[0] <= CASE_LIMIT, "reference exceeds the case limit")
    require(1 <= case["provenance"]["referenceNodes"] <= CASE_LIMIT, "recorded reference size exceeds the case limit")
    require(case["contract"] == {"name": NAME, "method": "run", "signature": "run(uint256)",
            "deployPath": [NAME + "Deploy"], "runtimePath": [NAME + "Deploy", NAME],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "memory call ABI, runtime input, or contract metadata changed")
    require(case.get("executionFuel") == fuel, "invalid execution fuel")
    require(case.get("source") == emitted_source(plan), "the emitted source differs from the plan's re-emission")
    recorded = case["provenance"]["memoryCallShapes"]
    require(set(recorded) == set(SHAPES) and {dimension: set(values) for dimension, values in recorded.items()} == shapes(plan),
            "recorded memory call shapes differ from the plan")
    require(all(values == sorted(set(values)) for values in recorded.values()), "memory call shapes are not sorted")
    require(case["provenance"]["features"] == [], "the memory call profile records no G0 step features")
    require(model_outcome(plan, number) == case["directCore"], "the call model differs from the recorded Core outcome")
    return plan


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals", "requiredInputs",
              "memoryCallRequirements", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == PROFILE, "unexpected memory call manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "memory call coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    require(manifest["requiredFeatures"] == [] and manifest["requiredWordLiterals"] == [],
            "the memory call corpus requires shapes, not step features or literals")
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "the memory call corpus must require all eight boundary inputs")
    require(manifest["memoryCallRequirements"] == REQUIRED, "the memory call corpus must require every shape value")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "the memory call corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"id", "generation", "input", "expectedFeatures"},
                "a memory call corpus entry is a generation recipe with its input")
        identifier = entry["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        require(canonical_word(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        require(entry["expectedFeatures"] == [], "memory call entries expect no step features")
        recipe = entry["generation"]
        require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
        require(canonical_word(recipe["seed"]) < 1 << 64 and recipe["maxProgramNodes"] == NODES,
                "fixed recipes use a uint64 seed and the default budget")
    return entries


def generated_plan(tool, seed, fuel):
    """The seed's plan, or None for an excluded seed."""
    corpus = run(tool, "memory-calls-generate", str(seed), str(NODES), "1", "1", str(fuel))
    cases = corpus.get("cases")
    require(isinstance(cases, list) and len(cases) <= 1, "invalid generation response")
    return check_plan(cases[0]["memoryCallPlan"]) if cases else None


def selection(tool, fuel, last):
    """The roadmap's construction: from seed 1 upwards, every accepted seed
    whose plan covers a missing value, until nothing is missing."""
    missing = {dimension: set(values) for dimension, values in REQUIRED.items()}
    chosen = []
    for seed in range(1, last + 1):
        if not any(missing.values()):
            break
        plan = generated_plan(tool, seed, fuel)
        if plan is None:
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
    corpus = run(tool, "memory-calls-generate", recipe["seed"], str(recipe["maxProgramNodes"]), "8", "1", str(fuel))
    require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
            and corpus.get("requested") == 8 and corpus.get("attempted") == 1
            and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 8,
            "fixed memory call seed did not emit eight cases in one attempt")
    cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
    require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
    case = cases[0]
    origin = case["provenance"]["origin"]
    require(origin == {"kind": "memory-call-generated", "seed": recipe["seed"],
                       "maxProgramNodes": recipe["maxProgramNodes"],
                       "inputIndex": BOUNDARIES.index(int(entry["input"])), "validationFuel": fuel},
            "generated recipe differs from manifest")
    check_case(case, fuel)
    return case


def checked_shrinks(case, tool, directory, fuel):
    path = directory / "shrink-parent.json"
    path.write_text(json.dumps(case))
    reduced = run(tool, "shrink", str(path), "64", str(fuel))
    require(reduced == run(tool, "shrink", str(path), "64", str(fuel)), "native shrink order changed")
    candidates = reduced.get("cases")
    require(isinstance(candidates, list) and candidates, "fixed memory call case has no shrink candidate")
    require(sum(len(json.dumps(candidate, separators=(",", ":"))) for candidate in candidates) <= SHRINK_BYTES,
            "a shrink response exceeds its byte cap")
    parent = (plan_size(case["memoryCallPlan"]), int(case["input"]))
    seen = set()
    for candidate in candidates:
        check_case(candidate, fuel)
        require(candidate["provenance"]["origin"] == {"kind": "reduced", "parentPlan": case["memoryCallPlan"],
                                                      "parentInput": case["input"]},
                "a shrink candidate is not a reduction of its parent")
        require((plan_size(candidate["memoryCallPlan"]), int(candidate["input"])) < parent,
                "a shrink candidate is not strictly smaller")
        encoded = json.dumps([candidate["memoryCallPlan"], candidate["input"]], sort_keys=True)
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
        except (ValueError, KeyError, TypeError, IndexError):
            count += 1
        else:
            raise ValueError("negative check accepted " + label)

    for field, value in (("profile", "runtime-memory-values"), ("requiredInputs", ["0"]), ("requiredFeatures", ["let"]),
                         *(("memoryCallRequirements", {**REQUIRED, dimension: REQUIRED[dimension][1:]})
                           for dimension in REQUIRED)):
        changed = copy.deepcopy(manifest)
        changed[field] = value
        rejects(lambda: check_manifest(changed), field)
    plan = sample["memoryCallPlan"]
    call = next(step for step in plan["steps"] if "call" in step)
    observe = {"action": {"kind": "observe", "fold": "add", "constant": 3, "value": "sc_b0", "access": {"access": "length"}}}
    helper = plan["helpers"][0]
    for label, broken in (
            ("no helper", {**plan, "helpers": []}),
            ("four helpers", {**plan, "helpers": plan["helpers"] + [helper] * (4 - len(plan["helpers"]))}),
            ("no steps", {**plan, "steps": []}),
            ("thirteen steps", {**plan, "steps": plan["steps"] + [observe] * (13 - len(plan["steps"]))}),
            ("an unknown step", {**plan, "steps": [{"loop": {"form": "single", "mask": 1}, "body": []}]}),
            ("a helper calling itself", {**plan, "helpers": [{"param": "bytes", "kind": "call", "callee": 0, "constant": 1}]}),
            ("no call", {**plan, "steps": [step for step in plan["steps"] if "call" not in step]}),
            ("a call of a missing helper", {**plan, "steps": [{"call": {**call["call"], "helper": 3}}]}),
            ("a variable out of scope", {**plan, "steps": [{"call": {**call["call"], "arg": "sc_b9"}}]})):
        rejects(lambda: check_plan(broken), label)
    path = directory / "negative.json"
    calling = next(index for index, step in enumerate(sample["memoryCallPlan"]["steps"]) if "call" in step)
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("a called helper", lambda value: value["memoryCallPlan"]["steps"][calling]["call"].update(helper=7)),
        ("a removed step", lambda value: value["memoryCallPlan"]["steps"].pop(calling)),
        ("an even fold constant", lambda value: value["memoryCallPlan"]["steps"][calling]["call"].update(constant=4)),
        ("a helper parameter", lambda value: value["memoryCallPlan"]["helpers"][0].update(param="free")),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="1" if value["input"] != "1" else "2")),
        ("wrapper", lambda value: value["contract"].update(name="AnotherContract")),
        ("memory call shapes", lambda value: value["provenance"]["memoryCallShapes"].update(helpers=[])),
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
    for args in (("memory-calls-generate", str(1 << 64), "1024", "8", "1", str(fuel)),
                 ("memory-calls-generate", "1", "2049", "8", "1", str(fuel)),
                 ("memory-calls-generate", "1", "255", "8", "1", str(fuel)),
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
    with tempfile.TemporaryDirectory(prefix="memory-call-corpus-") as name:
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
            require(group["source"] == case["source"], "identical memory call plan emitted input-dependent source")
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
            require(group["inputs"] == set(BOUNDARIES), "memory call plan lacks a completed boundary input")
            require(len(group["results"]) > 1, "fixed memory call plan had one outcome for every boundary input")
        require(seeds == selection(tool, fuel, max(seeds)), "the corpus is not every covering seed in order")
        data = next(case for case in samples if any("data" in step for step in case["memoryCallPlan"]["steps"]))
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in [samples[0], data])
        checks = policy_checks(manifest, samples[0], tool, directory, fuel)
    return {"status": "passed", "profile": PROFILE, "cases": len(entries), "plans": len(groups),
            "seeds": seeds, "outOfRange": reverted, "completedInputs": [str(value) for value in sorted(inputs)],
            "memoryCallCoverage": {"classification": "specified-by-the-plan-not-measured-memory-traffic",
                                   **{dimension: sorted(values) for dimension, values in found.items()}},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path,
                        default=ROOT / "scripts/semantic-memory-call-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
