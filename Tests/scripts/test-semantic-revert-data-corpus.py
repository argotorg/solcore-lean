#!/usr/bin/env python3
"""Check the fixed revert data corpus using fresh native Core executions.

The corpus takes, from seed 1 upwards at the default budget, every generated
plan that covers a missing revert data shape, each at the eight primitive
boundary inputs; every shape value is required. This test rebuilds that
selection, admits every plan with its own walk over the helpers, sites and
scope, recomputes every shape and the shrink measure from the plan alone,
re-emits the source and compares it exactly, evaluates every case's plan with
its own model, which runs each helper and closure as a function over byte
lists and raises each site's revert data, against the recorded Core outcome,
and replays, observes and shrinks natively. It neither compiles Rust nor
executes an EVM. The memory value corpus's checker supplies
`runtime-memory-values`' actions: their admission and text.
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


pure = load("revert_data_corpus_pure", "Tests/scripts/test-semantic-corpus.py")
generic = load("revert_data_corpus_generic", "Tests/scripts/test-semantic-generic-corpus.py")
memory = load("revert_data_corpus_values", "Tests/scripts/test-semantic-memory-value-corpus.py")
m2 = load("revert_data_corpus_adapter", "scripts/semantic-differential.py")
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
VERSIONS = pure.VERSIONS + ("profileVersion", "boundaryVersion")
BOUNDARIES = memory.BOUNDARIES
CASE_SCHEMA = "solcore-lean.semantic-revert-data-case.v1"
PLAN_SCHEMA = "solcore-lean.revert-data-plan.v1"
PROFILE = "runtime-revert-data"
NAME = "SynthesizedRevertData"
NODES = 1024
CASE_LIMIT = 4096
SHRINK_BYTES = 1_500_000
M = 1 << 256
FOLD_CONSTANTS = memory.FOLD_CONSTANTS
SHAPES = {key: list(values) for key, values in m2.REVERT_DATA_SHAPES.items()}
REQUIRED = SHAPES
ORDER_CONSTANTS = (0, 1, 2, 3, 5, 255, 256, 1000, 1 << 255)
EQUAL_CONSTANTS = (0, 1, 2, 3, 255, 256)
BIT_MASKS = (1, 2, 3, 7)
MASKS = (1, 3, 7)
LITERALS = (
    "", "x", "no", "too large", "revert data",
    "abcdefghijklmnopqrstuvwxyz01234",
    "abcdefghijklmnopqrstuvwxyz012345",
    "abcdefghijklmnopqrstuvwxyz0123456",
    "the quick brown fox jumps over the lazy dog 0123456789 abcdefgh",
    "the quick brown fox jumps over the lazy dog 0123456789 abcdefghi")
LIMITS = {"errors": 3, "data": 2, "closures": 2, "values": 2}


# --- Admission ------------------------------------------------------------------------

def check_test(test):
    require(isinstance(test, dict), "a test is an object")
    kind = test.get("test")
    if kind in ("lt", "gt"):
        require(set(test) == {"test", "constant"} and test["constant"] in ORDER_CONSTANTS, "invalid order test")
    elif kind in ("eq", "ne"):
        require(set(test) == {"test", "constant"} and test["constant"] in EQUAL_CONSTANTS, "invalid equality test")
    else:
        require(kind == "bits" and set(test) == {"test", "mask", "value"} and test["mask"] in BIT_MASKS
                and type(test["value"]) is int and 0 <= test["value"] <= test["mask"], "invalid bit test")


def check_word(word, context):
    """`context` is `run`, `loop`, `arm`, `helper` or `closure`."""
    memory.check_operand(word, context == "loop")
    if context in ("helper", "closure"):
        require(word["operand"] in ("input", "add", "mul", "xor"), "a helper or closure tests its own Word")


class Env:
    def __init__(self):
        self.scope = memory.Scope()
        self.errors = []          # kinds: ("selector",), ("empty",), ("message", object), ("picked",)
        self.pairs, self.sums, self.enums = [], [], []
        self.closures = []        # (site, fold, constant)
        self.values = 0
        self.loops = 0

    def copy(self):
        other = Env()
        other.scope = self.scope.copy()
        other.errors, other.pairs, other.sums, other.enums = list(self.errors), list(self.pairs), list(self.sums), list(self.enums)
        other.closures, other.values, other.loops = list(self.closures), self.values, self.loops
        return other

    def message(self, value):
        require(type(value) is int, "a message names a bytes variable")
        kind, entry = self.scope.var(f"sc_b{value}")
        require(kind == "bytes" and entry[2] <= 64, "a message is a bytes value of at most 64 bytes")
        return entry

    def make(self, made, context):
        require(isinstance(made, dict), "an Error is an object")
        kind = made.get("make")
        if kind == "selector":
            require(set(made) == {"make", "word"}, "invalid selector")
            check_word(made["word"], context)
            return ("selector",)
        if kind == "empty":
            require(set(made) == {"make"}, "invalid empty Error")
            return ("empty",)
        require(kind == "message" and set(made) == {"make", "value"} and context != "helper", "invalid message")
        return ("message", self.message(made["value"])[0])

    def source(self, source, context, arm=None):
        require(isinstance(source, dict), "a source is an object")
        kind = source.get("source")
        if kind == "make":
            require(set(source) == {"source", "make"}, "invalid made source")
            return self.make(source["make"], context)
        if kind == "named":
            require(set(source) == {"source", "number"} and context != "helper"
                    and type(source["number"]) is int and source["number"] < len(self.errors), "an Error variable out of scope")
            return self.errors[source["number"]]
        require(kind == "param" and set(source) == {"source"} and context in ("helper", "arm"), "no Error parameter here")
        return ("picked",) if context == "helper" else arm

    def site(self, site, context, arm=None):
        require(isinstance(site, dict) and set(site) == {"form", "cond", "payload"} and site["form"] in ("when", "require"),
                "invalid site")
        cond = site["cond"]
        require(isinstance(cond, dict) and set(cond) == {"word", "test"}, "invalid condition")
        check_word(cond["word"], context)
        check_test(cond["test"])
        payload = site["payload"]
        require(isinstance(payload, dict), "a payload is an object")
        kind = payload.get("payload")
        if kind == "error":
            require(set(payload) == {"payload", "source"}, "invalid Error payload")
            self.source(payload["source"], context, arm)
        elif kind == "literal":
            require(set(payload) == {"payload", "text"} and type(payload["text"]) is int
                    and 0 <= payload["text"] < len(LITERALS), "unknown literal")
            if site["form"] == "when":
                require(len(LITERALS[payload["text"]].encode()) <= 32, "revertLit takes at most 32 bytes")
        else:
            require(kind == "none" and set(payload) == {"payload"} and site["form"] == "when", "revertEmpty is an if site")


def action_admitted(action, in_loop):
    require(isinstance(action, dict), "an action is an object")
    kind = action.get("kind")
    if in_loop:
        require(kind == "bytes", "a loop body allocates and raises only")
    if kind == "bytes":
        for part in action.get("parts", []):
            require(part.get("part") in ("word", "zeros") or str(part.get("value", "")).startswith("sc_b"),
                    "a part is a Word, zeros or a bytes value")
    elif kind == "alias":
        require(str(action.get("source", "")).startswith("sc_b"), "a second variable of a bytes value")
    elif kind == "write":
        require(str(action.get("target", "")).startswith("sc_b") and action.get("index", {}).get("index") == "literal",
                "a write into a bytes value at a literal position")
    else:
        require(kind == "observe" and str(action.get("value", "")).startswith("sc_b")
                and (action.get("access", {}).get("access") == "length"
                     or (action.get("access", {}).get("access") in ("word", "byte")
                         and action["access"].get("index", {}).get("index") == "literal")),
                "an observation of a length, Word or byte at a literal position")


def check_helpers(helpers):
    require(isinstance(helpers, list) and len(helpers) <= 3, "at most three helpers")
    for index, helper in enumerate(helpers):
        require(isinstance(helper, dict), "a helper is an object")
        kind = helper.get("kind")
        if kind == "raise":
            require(set(helper) == {"kind", "site", "fold", "constant"} and helper["fold"] in ("add", "xor")
                    and helper["constant"] in FOLD_CONSTANTS, "invalid raise helper")
            Env().site(helper["site"], "helper")
        elif kind == "make":
            require(set(helper) == {"kind", "constant"} and type(helper["constant"]) is int
                    and 1 <= helper["constant"] <= 255, "invalid make helper")
        elif kind == "message":
            require(set(helper) == {"kind"}, "invalid message helper")
        elif kind == "pick":
            require(set(helper) == {"kind", "test"}, "invalid pick helper")
            check_test(helper["test"])
        else:
            require(kind == "call" and set(helper) == {"kind", "callee", "constant"} and type(helper["callee"]) is int
                    and helper["callee"] < index and 1 <= helper["constant"] <= 255
                    and helpers[helper["callee"]]["kind"] in ("raise", "call"), "invalid call helper")


def resolve(helpers, index):
    """The raise helper a call reaches and the constants added on the way."""
    added = 0
    for _ in range(4):
        helper = helpers[index]
        if helper["kind"] == "raise":
            return helper, added
        require(helper["kind"] == "call", "a call reaches a raise helper")
        added += helper["constant"]
        index = helper["callee"]
    raise ValueError("a call chain is too deep")


def held_of(env, held):
    require(isinstance(held, dict) and set(held) == {"held", "number"} and held["held"] in ("pair", "sum", "enum")
            and type(held["number"]) is int, "invalid data variable")
    values = {"pair": env.pairs, "sum": env.sums, "enum": env.enums}[held["held"]]
    require(held["number"] < len(values), "a data variable out of scope")
    return values[held["number"]]


def check_step(env, helpers, step):
    """Admit one step and return the next environment with its site count and fold."""
    require(isinstance(step, dict) and len(step) == 1, "a step is a one-field object")
    key, value = next(iter(step.items()))
    env = env.copy()
    sites, folds = 0, False
    if key == "action":
        action_admitted(value, False)
        env.scope = memory.step_scope(env.scope, value, False)
        folds = value["kind"] == "observe"
    elif key == "error":
        require(len(env.errors) < LIMITS["errors"], "at most three Error variables")
        kind = value.get("decl")
        if kind == "make":
            require(set(value) == {"decl", "make"}, "invalid declaration")
            env.errors.append(env.make(value["make"], "run"))
        elif kind == "helper":
            require(set(value) == {"decl", "helper", "word"} and helpers[value["helper"]]["kind"] == "make",
                    "a made Error needs a make helper")
            check_word(value["word"], "run")
            env.errors.append(("selector",))
        elif kind == "message":
            require(set(value) == {"decl", "helper", "value"} and helpers[value["helper"]]["kind"] == "message",
                    "a message Error needs a message helper")
            env.errors.append(("message", env.message(value["value"])[0]))
        else:
            require(kind == "pick" and set(value) == {"decl", "helper", "word", "first", "second"}
                    and helpers[value["helper"]]["kind"] == "pick", "a picked Error needs a pick helper")
            check_word(value["word"], "run")
            env.source(value["first"], "run")
            env.source(value["second"], "run")
            env.errors.append(("picked",))
    elif key == "data":
        kind = value.get("datum")
        lists = {"pair": env.pairs, "inl": env.sums, "inr": env.sums, "enum0": env.enums, "enum1": env.enums}
        require(kind in lists and len(lists[kind]) < LIMITS["data"], "invalid or too many data values")
        if kind in ("pair", "enum0"):
            require(set(value) == {"datum", "error", "word"}, "invalid data value")
            held = ("error", env.source(value["error"], "run"))
            check_word(value["word"], "run")
        elif kind == "inl":
            require(set(value) == {"datum", "error"}, "invalid data value")
            held = ("error", env.source(value["error"], "run"))
        else:
            require(set(value) == {"datum", "word"}, "invalid data value")
            check_word(value["word"], "run")
            held = ("word",)
        lists[kind].append(held)
    elif key == "site":
        env.site(value, "run")
        sites = 1
    elif key == "call":
        require(set(value) == {"helper", "error", "word", "form", "fold", "constant"} and type(value["helper"]) is int
                and value["helper"] < len(helpers) and helpers[value["helper"]]["kind"] in ("raise", "call")
                and value["form"] in ("direct", "value") and value["fold"] in ("add", "xor")
                and value["constant"] in FOLD_CONSTANTS, "invalid call")
        env.source(value["error"], "run")
        check_word(value["word"], "run")
        if value["form"] == "value":
            require(env.values < LIMITS["values"], "at most two function values")
            env.values += 1
        resolve(helpers, value["helper"])
        sites, folds = 1, True
    elif key == "take":
        require(set(value) == {"held", "site", "fold", "constant"} and value["fold"] in ("add", "xor")
                and value["constant"] in FOLD_CONSTANTS, "invalid match")
        held = held_of(env, value["held"])
        env.site(value["site"], "arm", held[1] if held[0] == "error" else ("selector",))
        sites = 1 if held[0] == "error" else 0
        folds = held[0] == "word" or value["held"]["held"] != "sum"
    elif key == "closure":
        require(set(value) == {"site", "fold", "constant"} and value["fold"] in ("add", "xor")
                and value["constant"] in FOLD_CONSTANTS and len(env.closures) < LIMITS["closures"], "invalid closure")
        env.site(value["site"], "closure")
        env.closures.append(value)
    elif key == "apply":
        require(set(value) == {"closure", "word", "fold", "constant"} and type(value["closure"]) is int
                and value["closure"] < len(env.closures) and value["fold"] in ("add", "xor")
                and value["constant"] in FOLD_CONSTANTS, "invalid application")
        check_word(value["word"], "run")
        sites, folds = 1, True
    else:
        require(key == "loop" and set(value) == {"mask", "body"} and value["mask"] in MASKS and env.loops == 0
                and isinstance(value["body"], list) and 1 <= len(value["body"]) <= 3, "invalid loop")
        inner = env.copy()
        for item in value["body"]:
            require(isinstance(item, dict) and len(item) == 1 and next(iter(item)) in ("action", "site"), "invalid loop item")
            if "action" in item:
                action_admitted(item["action"], True)
                inner.scope = memory.step_scope(inner.scope, item["action"], True)
            else:
                inner.site(item["site"], "loop")
                sites += 1
        inner.scope.close(env.scope)
        env.scope = inner.scope
        env.loops = 1
    return env, sites, folds


def check_plan(plan):
    require(isinstance(plan, dict) and set(plan) == {"schema", "helpers", "steps"} and plan["schema"] == PLAN_SCHEMA,
            "unexpected revert data plan schema")
    check_helpers(plan["helpers"])
    steps = plan["steps"]
    require(isinstance(steps, list) and 1 <= len(steps) <= 12, "one to twelve steps")
    env, sites, folds = Env(), 0, False
    for step in steps:
        env, more, folded = check_step(env, plan["helpers"], step)
        sites += more
        folds = folds or folded
    require(sites >= 1 and folds, "a plan has a site it reaches and a fold")
    return plan


# --- Shapes ---------------------------------------------------------------------------

def length_class(length):
    if length == 0:
        return "0"
    if length < 32:
        return "1-31"
    if length == 32:
        return "32"
    return "33-63" if length < 64 else "64"


def form_name(site):
    kind = site["payload"]["payload"]
    if kind == "error":
        return "revertWithError" if site["form"] == "when" else "require"
    if kind == "literal":
        return "revertLit" if site["form"] == "when" else "requireLiteral"
    return "revertEmpty"


def word_kind(context, word):
    kind = word["operand"]
    if kind in ("acc", "counter"):
        return kind
    if context in ("helper", "closure"):
        return "local"
    return "input" if kind == "input" else "constant"


def shapes(plan):
    found = {dimension: set() for dimension in SHAPES}
    writes, allocations = [], 0
    errors, held = [], {"pair": [], "sum": [], "enum": []}

    def made_of(env, source, outer=None):
        kind = source["source"]
        if kind == "make":
            made = source["make"]
            if made["make"] == "selector":
                return ({"kind": "selector", "lengths": [4], "written": None}, "inline")
            if made["make"] == "empty":
                return ({"kind": "empty", "lengths": [0], "written": None}, "inline")
            _, (obj, _, length) = env.scope.var(f"sc_b{made['value']}")
            fresh = outer is not None and made["value"] >= outer
            return ({"kind": "message", "lengths": [length], "written": None}, "loop" if fresh else "inline")
        if kind == "named":
            return (errors[source["number"]], "variable")
        return None

    def message_made(env, value):
        _, (obj, _, length) = env.scope.var(f"sc_b{value}")
        return {"kind": "message", "lengths": [length], "written": (obj, f"sc_b{value}", len(writes), allocations)}

    def site(context, word, spec, raised):
        found["forms"].add(form_name(spec))
        found["contexts"].add(context)
        found["tests"].add(spec["cond"]["test"]["test"])
        found["words"].add(word)
        payload = spec["payload"]
        if payload["payload"] == "error":
            if raised is not None:
                made, carrier = raised
                found["errors"].add(made["kind"])
                found["carriers"].add(carrier)
                for length in made["lengths"]:
                    found["lengths"].add(length_class(length))
                if made["written"] is not None:
                    obj, through, before, allocated = made["written"]
                    later = writes[before:]
                    if any(written == obj for written, _ in later):
                        found["hazards"].add("written")
                    if any(written == obj and writer != through for written, writer in later):
                        found["hazards"].add("alias")
                    if allocations > allocated:
                        found["hazards"].add("allocated")
        elif payload["payload"] == "literal":
            found["lengths"].add(length_class(len(LITERALS[payload["text"]].encode())))
        else:
            found["lengths"].add("0")

    def note_action(env, action):
        nonlocal allocations
        if action["kind"] == "write":
            _, (obj, _, _) = env.scope.var(action["target"])
            writes.append((obj, action["target"]))
        elif action["kind"] == "bytes":
            allocations += 1

    for helper in plan["helpers"]:
        found["helpers"].add(helper["kind"])
    env = Env()
    for step in plan["steps"]:
        key, value = next(iter(step.items()))
        found["steps"].add(key)
        if key == "action":
            note_action(env, value)
        elif key == "error":
            kind = value["decl"]
            if kind == "make":
                made = value["make"]
                if made["make"] == "message":
                    entry = message_made(env, made["value"])
                else:
                    entry = {"kind": made["make"], "lengths": [4 if made["make"] == "selector" else 0], "written": None}
                carrier = "variable"
            elif kind == "helper":
                entry, carrier = {"kind": "selector", "lengths": [4], "written": None}, "made"
            elif kind == "message":
                entry, carrier = message_made(env, value["value"]), "messaged"
            else:
                options = [made_of(env, source) for source in (value["first"], value["second"])]
                entry = {"kind": "picked", "lengths": [length for option in options if option for length in option[0]["lengths"]],
                         "written": None}
                carrier = "picked"
            errors.append(entry)
            found["declarations"].add(carrier)
        elif key == "data":
            kind = value["datum"]
            found["data"].add(kind)
            target = {"pair": "pair", "inl": "sum", "inr": "sum", "enum0": "enum", "enum1": "enum"}[kind]
            entry = made_of(env, value["error"]) if "error" in value else None
            held[target].append(entry[0] if entry else None)
        elif key == "site":
            raised = made_of(env, value["payload"]["source"]) if value["payload"]["payload"] == "error" else None
            site("run", word_kind("run", value["cond"]["word"]), value, raised)
        elif key == "call":
            chain, current = 0, value["helper"]
            for _ in range(4):
                if plan["helpers"][current]["kind"] == "call":
                    chain, current = chain + 1, plan["helpers"][current]["callee"]
            base, _ = resolve(plan["helpers"], value["helper"])
            inner = base["site"]
            passed = made_of(env, value["error"])
            if inner["payload"]["payload"] == "error":
                source = inner["payload"]["source"]
                if source["source"] == "param":
                    raised = (passed[0], "passed" if value["form"] == "direct" else "value") if passed else None
                else:
                    raised = made_of(env, source)
            else:
                raised = None
            site("call" if chain > 0 else "helper", word_kind("helper", inner["cond"]["word"]), inner, raised)
        elif key == "take":
            target = value["held"]["held"]
            entry = held[target][value["held"]["number"]]
            if entry is not None:
                inner = value["site"]
                if inner["payload"]["payload"] == "error":
                    source = inner["payload"]["source"]
                    raised = (entry, "held") if source["source"] == "param" else made_of(env, source)
                else:
                    raised = None
                site(target, word_kind("arm", inner["cond"]["word"]), inner, raised)
        elif key == "apply":
            inner = env.closures[value["closure"]]["site"]
            if inner["payload"]["payload"] == "error":
                source = inner["payload"]["source"]
                raised = (errors[source["number"]], "captured") if source["source"] == "named" else made_of(env, source)
            else:
                raised = None
            site("closure", word_kind("closure", inner["cond"]["word"]), inner, raised)
        elif key == "loop":
            inner_env = env.copy()
            outer = len(env.scope.vars["bytes"])
            for item in value["body"]:
                if "action" in item:
                    note_action(inner_env, item["action"])
                    inner_env.scope = memory.step_scope(inner_env.scope, item["action"], True)
                else:
                    spec = item["site"]
                    raised = made_of(inner_env, spec["payload"]["source"], outer) if spec["payload"]["payload"] == "error" else None
                    site("loop", word_kind("loop", spec["cond"]["word"]), spec, raised)
        env, _, _ = check_step(env, plan["helpers"], step)
    return found


# --- The shrink measure -----------------------------------------------------------------

def operand_size(o):
    kind = o["operand"]
    if kind == "input":
        return 0
    if kind in ("acc", "counter"):
        return 1
    return 1 + (0 if o["constant"] == 1 else 1)


def constant_size(c):
    return 0 if c == 0 else 1 if c <= 3 else 2


def test_size(t):
    if t["test"] == "eq":
        return constant_size(t["constant"])
    if t["test"] in ("ne", "lt", "gt"):
        return 1 + constant_size(t["constant"])
    return 1 + constant_size(t["mask"]) + constant_size(t["value"])


def make_size(m):
    return {"empty": 1, "message": 3}.get(m["make"]) or 2 + operand_size(m["word"])


def source_size(s):
    return make_size(s["make"]) if s["source"] == "make" else 2


def payload_size(p):
    if p["payload"] == "none":
        return 0
    if p["payload"] == "literal":
        return 1 + p["text"]
    return 1 + source_size(p["source"])


def site_size(s):
    return (1 + (1 if s["form"] == "require" else 0) + operand_size(s["cond"]["word"]) + test_size(s["cond"]["test"])
            + payload_size(s["payload"]))


def fold_size(fold, constant):
    return (1 if fold == "xor" else 0) + (0 if constant == 3 else 1)


def action_size(a):
    if a["kind"] == "bytes":
        return 2 if a["build"] == "to_bytes" else 3
    return 2 if a["kind"] == "alias" else 3


def plan_size(plan):
    def helper(h):
        kind = h["kind"]
        if kind == "raise":
            return 4 + site_size(h["site"]) + fold_size(h["fold"], h["constant"])
        if kind == "make":
            return 2 + constant_size(h["constant"])
        if kind == "message":
            return 2
        if kind == "pick":
            return 3 + test_size(h["test"])
        return 3 + constant_size(h["constant"])

    def decl(d):
        kind = d["decl"]
        if kind == "make":
            return make_size(d["make"])
        if kind == "helper":
            return 4 + operand_size(d["word"])
        if kind == "message":
            return 4
        return 5 + operand_size(d["word"]) + source_size(d["first"]) + source_size(d["second"])

    def datum(d):
        kind = d["datum"]
        if kind in ("pair", "enum0"):
            return 3 + source_size(d["error"]) + operand_size(d["word"])
        if kind == "inl":
            return 2 + source_size(d["error"])
        return 2 + operand_size(d["word"])

    def step(s):
        key, v = next(iter(s.items()))
        if key == "action":
            return action_size(v)
        if key == "error":
            return 2 + decl(v)
        if key == "data":
            return datum(v)
        if key == "site":
            return 2 + site_size(v)
        if key == "call":
            return (20 + source_size(v["error"]) + operand_size(v["word"]) + (0 if v["form"] == "direct" else 2)
                    + fold_size(v["fold"], v["constant"]))
        if key in ("take", "closure"):
            return 4 + site_size(v["site"]) + fold_size(v["fold"], v["constant"])
        if key == "apply":
            return 3 + operand_size(v["word"]) + fold_size(v["fold"], v["constant"])
        return 4 + v["mask"] + sum(action_size(i["action"]) if "action" in i else site_size(i["site"]) for i in v["body"])

    return sum(helper(h) for h in plan["helpers"]) + sum(step(s) for s in plan["steps"])


# --- The source, re-emitted --------------------------------------------------------------

FOLD_TEXT = {"add": " + ", "xor": " ^ "}


def test_text(word, t):
    kind = t["test"]
    if kind == "bits":
        return f"(({word} & {t['mask']}) == {t['value']})"
    operator = {"lt": "<", "gt": ">", "eq": "==", "ne": "!="}[kind]
    return f"({word} {operator} {t['constant']})"


def local_word(base, o):
    kind = o["operand"]
    if kind == "input":
        return base
    return f"({base} {'+' if kind == 'add' else '*' if kind == 'mul' else '^'} {o['constant']})"


def run_word(o):
    return memory.operand_text(o, "sc_counter")


def make_text(word, m):
    if m["make"] == "selector":
        return f"Error({word(m['word'])})"
    if m["make"] == "empty":
        return "Error.Empty"
    return f"Error.Msg(memory(Typedef.rep(sc_b{m['value']})))"


def source_text(word, s):
    if s["source"] == "make":
        return make_text(word, s["make"])
    return f"sc_e{s['number']}" if s["source"] == "named" else "sc_e"


def site_lines(word, s):
    condition = test_text(word(s["cond"]["word"]), s["cond"]["test"])
    payload = s["payload"]

    def guarded(line):
        return [f"if {condition} {{", "    " + line, "}"]

    if payload["payload"] == "error":
        text = source_text(word, payload["source"])
        return guarded(f"revertWithError({text});") if s["form"] == "when" else [f"require({condition}, {text});"]
    if payload["payload"] == "literal":
        literal = '"' + LITERALS[payload["text"]] + '"'
        return guarded(f"revertLit({literal});") if s["form"] == "when" else [f"require({condition}, {literal});"]
    return guarded("revertEmpty();")


def indent(count, lines):
    return [" " * count + line for line in lines]


def helper_lines(index, h):
    name = f"sc_h{index}"
    kind = h["kind"]
    if kind == "raise":
        return ([f"function {name}(sc_e: Error, sc_w: word) returns (word) {{"]
                + indent(4, site_lines(lambda o: local_word("sc_w", o), h["site"]))
                + [f"    return (sc_w{FOLD_TEXT[h['fold']]}{h['constant']});", "}"])
    if kind == "make":
        return [f"function {name}(sc_w: word) returns (Error) {{", f"    return Error((sc_w + {h['constant']}));", "}"]
    if kind == "message":
        return [f"function {name}(sc_v: memory<bytes>) returns (Error) {{",
                "    return Error.Msg(memory(Typedef.rep(sc_v)));", "}"]
    if kind == "pick":
        return [f"function {name}(sc_w: word, sc_a: Error, sc_b: Error) returns (Error) {{",
                f"    if {test_text('sc_w', h['test'])} {{", "        return sc_a;", "    }", "    return sc_b;", "}"]
    return [f"function {name}(sc_e: Error, sc_w: word) returns (word) {{",
            f"    return sc_h{h['callee']}(sc_e, (sc_w + {h['constant']}));", "}"]


def fold_line(fold, constant, value):
    return f"sc_r = ((sc_r * {constant}){FOLD_TEXT[fold]}{value});"


def emitted_source(plan):
    counts, used = {"bytes": 0, "slice": 0, "array": 0}, set()
    names = {"errors": 0, "pairs": 0, "sums": 0, "enums": 0, "closures": 0, "functions": 0}
    lines, enum = [], False
    for step in plan["steps"]:
        key, v = next(iter(step.items()))
        if key == "action":
            lines += memory.action_lines(v, "sc_counter", counts, used)
        elif key == "error":
            kind = v["decl"]
            if kind == "make":
                text = make_text(run_word, v["make"])
            elif kind == "helper":
                text = f"sc_h{v['helper']}({run_word(v['word'])})"
            elif kind == "message":
                text = f"sc_h{v['helper']}(sc_b{v['value']})"
            else:
                text = (f"sc_h{v['helper']}({run_word(v['word'])}, {source_text(run_word, v['first'])}, "
                        f"{source_text(run_word, v['second'])})")
            lines.append(f"let sc_e{names['errors']}: Error = {text};")
            names["errors"] += 1
        elif key == "data":
            kind = v["datum"]
            if kind == "pair":
                lines.append(f"let sc_t{names['pairs']}: (Error, word) = ({source_text(run_word, v['error'])}, "
                             f"{run_word(v['word'])});")
                names["pairs"] += 1
            elif kind in ("inl", "inr"):
                inner = f"inl({source_text(run_word, v['error'])})" if kind == "inl" else f"inr({run_word(v['word'])})"
                lines.append(f"let sc_u{names['sums']}: sum<Error, word> = {inner};")
                names["sums"] += 1
            else:
                enum = True
                inner = (f"Sc_F.Sc_F0({source_text(run_word, v['error'])}, {run_word(v['word'])})" if kind == "enum0"
                         else f"Sc_F.Sc_F1({run_word(v['word'])})")
                lines.append(f"let sc_g{names['enums']}: Sc_F = {inner};")
                names["enums"] += 1
        elif key == "site":
            lines += site_lines(run_word, v)
        elif key == "call":
            arguments = f"({source_text(run_word, v['error'])}, {run_word(v['word'])})"
            if v["form"] == "direct":
                lines.append(fold_line(v["fold"], v["constant"], f"sc_h{v['helper']}{arguments}"))
            else:
                name = f"sc_f{names['functions']}"
                names["functions"] += 1
                lines += [f"let {name}: function (Error, word) returns (word) = sc_h{v['helper']};",
                          fold_line(v["fold"], v["constant"], name + arguments)]
        elif key == "take":
            arm = site_lines(run_word, v["site"])
            folded = [fold_line(v["fold"], v["constant"], "sc_w")]
            number = v["held"]["number"]
            target = v["held"]["held"]
            if target == "pair":
                lines += [f"match (sc_t{number}) {{", "    case (sc_e, sc_w) {"] + indent(8, arm + folded) + ["    }", "}"]
            elif target == "sum":
                lines += ([f"match (sc_u{number}) {{", "    case inl(sc_e) {"] + indent(8, arm) +
                          ["    }", "    case inr(sc_w) {"] + indent(8, folded) + ["    }", "}"])
            else:
                lines += ([f"match (sc_g{number}) {{", "    case Sc_F.Sc_F0(sc_e, sc_w) {"] + indent(8, arm + folded) +
                          ["    }", "    case Sc_F.Sc_F1(sc_w) {"] + indent(8, folded) + ["    }", "}"])
        elif key == "closure":
            lines += ([f"let sc_c{names['closures']}: function (word) returns (word) = lam (sc_j: word) -> word {{"]
                      + indent(4, site_lines(lambda o: local_word("sc_j", o), v["site"]))
                      + [f"    return (sc_j{FOLD_TEXT[v['fold']]}{v['constant']});", "};"])
            names["closures"] += 1
        elif key == "apply":
            lines.append(fold_line(v["fold"], v["constant"], f"sc_c{v['closure']}({run_word(v['word'])})"))
        else:
            inner = []
            for item in v["body"]:
                inner += (memory.action_lines(item["action"], "sc_counter", counts, used) if "action" in item
                          else site_lines(run_word, item["site"]))
            lines += ([f"let sc_limit: word = (sc_x & {v['mask']});", "let sc_counter: word = 0;",
                       "while (sc_limit > sc_counter) {"] + indent(4, inner) +
                      ["    sc_counter = (sc_counter + 1);", "}"])
    helpers = [line for name in memory.HELPERS if name in used for line in memory.HELPER_LINES[name]]
    enum_lines = ["enum Sc_F {", "    Sc_F0(Error, word),", "    Sc_F1(word)", "}", ""] if enum else []
    own = [line for index, h in enumerate(plan["helpers"]) for line in helper_lines(index, h) + [""]]
    source = (["import * from std;", "import * from std.dispatch;",
               "import { mload, mstore, mstore8, shr, mod } from std.opcodes;", ""] + helpers + enum_lines + own +
              [f"contract {NAME} {{", "    function run(input: uint256) public returns (uint256) {",
               "        let sc_x: word = Typedef.rep(input);", "        let sc_r: word = 0;"] + indent(8, lines) +
              ["        return uint256(sc_r);", "    }", "}"])
    return "\n".join(source) + "\n"


# --- The model --------------------------------------------------------------------------

class Revert(Exception):
    def __init__(self, data):
        super().__init__(data.hex())
        self.data = bytes(data)


def b32(word):
    return (word % M).to_bytes(32, "big")


def holds(word, t):
    kind = t["test"]
    if kind == "lt":
        return word < t["constant"]
    if kind == "gt":
        return word > t["constant"]
    if kind == "eq":
        return word == t["constant"]
    if kind == "ne":
        return word != t["constant"]
    return (word & t["mask"]) == t["value"]


def fold(left, op, right):
    return (left + right) % M if op == "add" else (left ^ right) % M


class Machine:
    """Each helper and closure a function over byte lists; each site raises its
    revert data: a selector's low four bytes, a message's bytes at the site, a
    literal's bytes, or none."""

    def __init__(self, plan, x):
        self.plan, self.x, self.r = plan, x % M, 0
        self.objects, self.bytes, self.errors = [], [], []
        self.pairs, self.sums, self.enums, self.closures = [], [], [], []
        self.counter = None

    def word(self, o, base=None):
        kind = o["operand"]
        value = self.x if base is None else base
        if kind == "input":
            return value
        if kind == "add":
            return (value + o["constant"]) % M
        if kind == "mul":
            return (value * o["constant"]) % M
        if kind == "xor":
            return value ^ o["constant"]
        return self.r if kind == "acc" else self.counter

    def make(self, m, base=None):
        if m["make"] == "selector":
            return ("selector", self.word(m["word"], base))
        if m["make"] == "empty":
            return ("empty",)
        return ("message", self.bytes[m["value"]])

    def source(self, s, base=None, param=None):
        if s["source"] == "make":
            return self.make(s["make"], base)
        return self.errors[s["number"]] if s["source"] == "named" else param

    def data(self, error):
        if error[0] == "selector":
            return b32(error[1])[28:]
        return b"" if error[0] == "empty" else bytes(self.objects[error[1]])

    def site(self, s, base=None, param=None):
        payload = s["payload"]
        if payload["payload"] == "error":
            data = self.data(self.source(payload["source"], base, param))
        elif payload["payload"] == "literal":
            data = LITERALS[payload["text"]].encode()
        else:
            data = b""
        condition = holds(self.word(s["cond"]["word"], base), s["cond"]["test"])
        if condition == (s["form"] == "when"):
            raise Revert(data)

    def part(self, p):
        if p["part"] == "word":
            return b32(self.word(p["operand"]))
        if p["part"] == "zeros":
            return bytes(p["count"])
        return bytes(self.objects[self.bytes[int(p["value"][4:])]])

    def action(self, a, slot=None):
        kind = a["kind"]
        if kind == "bytes":
            self.objects.append(bytearray(b"".join(self.part(p) for p in a["parts"])))
            if slot is None:
                self.bytes.append(len(self.objects) - 1)
            else:
                self.bytes[slot] = len(self.objects) - 1
        elif kind == "alias":
            self.bytes.append(self.bytes[int(a["source"][4:])])
        elif kind == "write":
            target = self.objects[self.bytes[int(a["target"][4:])]]
            index, value = a["index"]["value"], self.word(a["value"])
            if a["width"] == "word":
                target[index:index + 32] = b32(value)
            else:
                target[index] = value & 0xFF
        else:
            target = self.objects[self.bytes[int(a["value"][4:])]]
            access = a["access"]
            if access["access"] == "length":
                observed = len(target)
            elif access["access"] == "word":
                index = access["index"]["value"]
                observed = int.from_bytes(bytes(target[index:index + 32]), "big")
            else:
                observed = target[access["index"]["value"]]
            self.r = fold((self.r * a["constant"]) % M, a["fold"], observed)

    def raise_call(self, index, error, word):
        helper = self.plan["helpers"][index]
        if helper["kind"] == "call":
            return self.raise_call(helper["callee"], error, (word + helper["constant"]) % M)
        self.site(helper["site"], word, error)
        return fold(word, helper["fold"], helper["constant"])

    def decl(self, d):
        if d["decl"] == "make":
            return self.make(d["make"])
        helper = self.plan["helpers"][d["helper"]]
        if d["decl"] == "helper":
            return ("selector", (self.word(d["word"]) + helper["constant"]) % M)
        if d["decl"] == "message":
            return ("message", self.bytes[d["value"]])
        first, second = self.source(d["first"]), self.source(d["second"])
        return first if holds(self.word(d["word"]), helper["test"]) else second

    def step(self, s):
        key, v = next(iter(s.items()))
        if key == "action":
            self.action(v)
        elif key == "error":
            self.errors.append(self.decl(v))
        elif key == "data":
            kind = v["datum"]
            if kind in ("pair", "enum0"):
                entry = (self.source(v["error"]), self.word(v["word"]))
            elif kind == "inl":
                entry = (self.source(v["error"]), None)
            else:
                entry = (None, self.word(v["word"]))
            {"pair": self.pairs, "inl": self.sums, "inr": self.sums, "enum0": self.enums, "enum1": self.enums}[kind].append(entry)
        elif key == "site":
            self.site(v)
        elif key == "call":
            result = self.raise_call(v["helper"], self.source(v["error"]), self.word(v["word"]))
            self.r = fold((self.r * v["constant"]) % M, v["fold"], result)
        elif key == "take":
            error, word = {"pair": self.pairs, "sum": self.sums, "enum": self.enums}[v["held"]["held"]][v["held"]["number"]]
            if error is not None:
                self.site(v["site"], None, error)
            if word is not None:
                self.r = fold((self.r * v["constant"]) % M, v["fold"], word)
        elif key == "closure":
            self.closures.append(v)
        elif key == "apply":
            closure = self.closures[v["closure"]]
            word = self.word(v["word"])
            self.site(closure["site"], word)
            self.r = fold((self.r * v["constant"]) % M, v["fold"], fold(word, closure["fold"], closure["constant"]))
        else:
            outer = len(self.bytes)
            slots, count = [], outer
            for item in v["body"]:
                slots.append(count if "action" in item else None)
                count += 1 if "action" in item else 0
            self.bytes.extend([None] * (count - outer))
            for counter in range(self.x & v["mask"]):
                self.counter = counter
                for item, slot in zip(v["body"], slots):
                    if "action" in item:
                        self.action(item["action"], slot)
                    else:
                        self.site(item["site"])
            self.counter = None
            for slot in range(outer, count):
                self.bytes[slot] = None

    def run(self):
        try:
            for s in self.plan["steps"]:
                self.step(s)
        except Revert as revert:
            return {"stage": "execution", "status": "reverted", "output": "0x" + revert.data.hex()}
        return {"stage": "execution", "status": "returned", "word": str(self.r)}


def model_outcome(plan, x):
    return Machine(plan, x).run()


def outcome(observation):
    """A completed Core outcome: a returned Word, or revert data of at most 64 bytes."""
    require(isinstance(observation, dict) and observation.get("stage") == "execution", "missing Core outcome")
    if observation.get("status") == "reverted":
        output = observation.get("output")
        require(set(observation) == {"stage", "status", "output"} and isinstance(output, str)
                and re.fullmatch(r"0x(?:[0-9a-f]{2}){0,64}", output) is not None, "revert data of at most 64 bytes")
        return "reverted:" + output
    require(observation.get("status") == "returned", "original Core did not complete within the native budget")
    canonical_word(observation.get("word"))
    return observation["word"]


# --- Cases and the manifest ---------------------------------------------------------------

def check_case(case, fuel):
    require(isinstance(case, dict) and case.get("schema") == CASE_SCHEMA, "unexpected revert data case schema")
    plan = check_plan(case["revertDataPlan"])
    number = canonical_word(case["input"])
    program = case["program"]
    payload = {"tag": "product", "left": "word", "right": {"tag": "product", "left": "word", "right": "word"}}
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == {"tag": "sum", "left": "word", "right": payload},
            "the revert data reference is a closed program returning a Word or revert data")
    require(generic.complexity(program["body"])[0] <= CASE_LIMIT, "reference exceeds the case limit")
    require(1 <= case["provenance"]["referenceNodes"] <= CASE_LIMIT, "recorded reference size exceeds the case limit")
    require(case["contract"] == {"name": NAME, "method": "run", "signature": "run(uint256)",
            "deployPath": [NAME + "Deploy"], "runtimePath": [NAME + "Deploy", NAME],
            "calldata": "0xa444f5e9" + f"{number:064x}", "constructorCalldata": "0x"},
            "revert data ABI, runtime input, or contract metadata changed")
    require(case.get("executionFuel") == fuel, "invalid execution fuel")
    require(case.get("source") == emitted_source(plan), "the emitted source differs from the plan's re-emission")
    recorded = case["provenance"]["revertDataShapes"]
    require(set(recorded) == set(SHAPES) and {dimension: set(values) for dimension, values in recorded.items()} == shapes(plan),
            "recorded revert data shapes differ from the plan")
    require(all(values == sorted(set(values)) for values in recorded.values()), "revert data shapes are not sorted")
    require(case["provenance"]["features"] == [], "the revert data profile records no G0 step features")
    require(model_outcome(plan, number) == case["directCore"], "the revert data model differs from the recorded Core outcome")
    return plan


def check_manifest(manifest):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals", "requiredInputs",
              "revertDataRequirements", "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == PROFILE, "unexpected revert data manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "revert data coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    require(manifest["requiredFeatures"] == [] and manifest["requiredWordLiterals"] == [],
            "the revert data corpus requires shapes, not step features or literals")
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "the revert data corpus must require all eight boundary inputs")
    require(manifest["revertDataRequirements"] == REQUIRED, "the revert data corpus must require every shape value")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "the revert data corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"id", "generation", "input", "expectedFeatures"},
                "a revert data corpus entry is a generation recipe with its input")
        identifier = entry["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        require(canonical_word(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        require(entry["expectedFeatures"] == [], "revert data entries expect no step features")
        recipe = entry["generation"]
        require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
        require(canonical_word(recipe["seed"]) < 1 << 64 and recipe["maxProgramNodes"] == NODES,
                "fixed recipes use a uint64 seed and the default budget")
    return entries


def generated_plan(tool, seed, fuel):
    """The seed's plan, or None for an excluded seed."""
    corpus = run(tool, "revert-data-generate", str(seed), str(NODES), "1", "1", str(fuel))
    cases = corpus.get("cases")
    require(isinstance(cases, list) and len(cases) <= 1, "invalid generation response")
    return check_plan(cases[0]["revertDataPlan"]) if cases else None


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
    corpus = run(tool, "revert-data-generate", recipe["seed"], str(recipe["maxProgramNodes"]), "8", "1", str(fuel))
    require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
            and corpus.get("requested") == 8 and corpus.get("attempted") == 1
            and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 8,
            "fixed revert data seed did not emit eight cases in one attempt")
    cases = [case for case in corpus["cases"] if case.get("input") == entry["input"]]
    require(len(cases) == 1, "fixed seed did not emit the requested input exactly once")
    case = cases[0]
    origin = case["provenance"]["origin"]
    require(origin == {"kind": "revert-data-generated", "seed": recipe["seed"],
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
    require(isinstance(candidates, list) and candidates, "fixed revert data case has no shrink candidate")
    require(sum(len(json.dumps(candidate, separators=(",", ":"))) for candidate in candidates) <= SHRINK_BYTES,
            "a shrink response exceeds its byte cap")
    parent = (plan_size(case["revertDataPlan"]), int(case["input"]))
    seen = set()
    for candidate in candidates:
        check_case(candidate, fuel)
        require(candidate["provenance"]["origin"] == {"kind": "reduced", "parentPlan": case["revertDataPlan"],
                                                      "parentInput": case["input"]},
                "a shrink candidate is not a reduction of its parent")
        require((plan_size(candidate["revertDataPlan"]), int(candidate["input"])) < parent,
                "a shrink candidate is not strictly smaller")
        encoded = json.dumps([candidate["revertDataPlan"], candidate["input"]], sort_keys=True)
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

    for field, value in (("profile", "runtime-memory-calls"), ("requiredInputs", ["0"]), ("requiredFeatures", ["let"]),
                         *(("revertDataRequirements", {**REQUIRED, dimension: REQUIRED[dimension][1:]})
                           for dimension in REQUIRED)):
        changed = copy.deepcopy(manifest)
        changed[field] = value
        rejects(lambda: check_manifest(changed), field)
    plan = sample["revertDataPlan"]
    observe = {"action": {"kind": "observe", "fold": "add", "constant": 3, "value": "sc_b0", "access": {"access": "length"}}}
    site = {"form": "when", "cond": {"word": {"operand": "input"}, "test": {"test": "eq", "constant": 0}},
            "payload": {"payload": "none"}}
    raising = {"kind": "raise", "site": site, "fold": "add", "constant": 3}
    for label, broken in (
            ("four helpers", {**plan, "helpers": [raising] * 4}),
            ("no steps", {**plan, "steps": []}),
            ("thirteen steps", {**plan, "steps": plan["steps"] + [observe] * (13 - len(plan["steps"]))}),
            ("an unknown step", {**plan, "steps": [{"sleep": {}}]}),
            ("a helper calling itself", {**plan, "helpers": [{"kind": "call", "callee": 0, "constant": 1}]}),
            ("no site", {**plan, "helpers": [], "steps": [{"action": {"kind": "bytes", "build": "to_bytes",
                "parts": [{"part": "word", "operand": {"operand": "input"}}]}}, observe]}),
            ("no fold", {**plan, "helpers": [], "steps": [{"site": site}]}),
            ("require without data", {**plan, "steps": [{"site": {**site, "form": "require"}}, observe]}),
            ("a 33-byte revertLit", {**plan, "steps": [{"site": {**site, "payload": {"payload": "literal", "text": 7}}}]}),
            ("an unknown literal", {**plan, "steps": [{"site": {**site, "payload": {"payload": "literal", "text": 10}}}]}),
            ("a message out of scope", {**plan, "steps": [{"site": {**site, "payload": {"payload": "error",
                "source": {"source": "make", "make": {"make": "message", "value": 9}}}}}]}),
            ("an Error parameter in run", {**plan, "steps": [{"site": {**site, "payload": {"payload": "error",
                "source": {"source": "param"}}}}]}),
            ("a test constant outside the list", {**plan, "steps": [{"site": {**site, "cond": {**site["cond"],
                "test": {"test": "eq", "constant": 4}}}}]}),
            ("a loop that reads", {**plan, "steps": [{"loop": {"mask": 1, "body": [observe]}}]})):
        rejects(lambda: check_plan(broken), label)
    path = directory / "negative.json"
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("a removed step", lambda value: value["revertDataPlan"]["steps"].pop(0)),
        ("a literal past the table", lambda value: value["revertDataPlan"]["steps"].append(
            {"site": {**site, "payload": {"payload": "literal", "text": 10}}})),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="1" if value["input"] != "1" else "2")),
        ("wrapper", lambda value: value["contract"].update(name="AnotherContract")),
        ("revert data shapes", lambda value: value["provenance"]["revertDataShapes"].update(helpers=[])),
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
    forged["directCore"] = {"stage": "execution", "status": "reverted", "output": "0x00"}
    path.write_text(json.dumps(forged))
    require(run(tool, "replay", str(path), str(fuel)) == sample, "native replay trusted saved execution evidence")
    count += 1
    path.write_text(json.dumps(sample))
    lower = run(tool, "replay", str(path), "0")
    require(lower["program"] == sample["program"] and lower["source"] == sample["source"]
            and lower["directCore"].get("status") == "out-of-fuel", "zero budget changed canonical code or invented completion")
    rejects(lambda: outcome(lower["directCore"]), "resource result as shape coverage")
    for args in (("revert-data-generate", str(1 << 64), "1024", "8", "1", str(fuel)),
                 ("revert-data-generate", "1", "2049", "8", "1", str(fuel)),
                 ("revert-data-generate", "1", "255", "8", "1", str(fuel)),
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
    with tempfile.TemporaryDirectory(prefix="revert-data-corpus-") as name:
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
            reverted += result.startswith("reverted:")
            plan_key = json.dumps(plan, sort_keys=True)
            if plan_key not in groups:
                seeds.append(int(entry["generation"]["seed"]))
                samples.append(case)
            group = groups.setdefault(plan_key, {"inputs": set(), "source": case["source"], "results": set()})
            require(group["source"] == case["source"], "identical revert data plan emitted input-dependent source")
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
            require(group["inputs"] == set(BOUNDARIES), "revert data plan lacks a completed boundary input")
            require(len(group["results"]) > 1, "fixed revert data plan had one outcome for every boundary input")
        require(seeds == selection(tool, fuel, max(seeds)), "the corpus is not every covering seed in order")
        looped = next(case for case in samples if any("loop" in step for step in case["revertDataPlan"]["steps"]))
        shrinks = sum(checked_shrinks(case, tool, directory, fuel) for case in [samples[0], looped])
        checks = policy_checks(manifest, samples[0], tool, directory, fuel)
    return {"status": "passed", "profile": PROFILE, "cases": len(entries), "plans": len(groups),
            "seeds": seeds, "reverted": reverted, "completedInputs": [str(value) for value in sorted(inputs)],
            "revertDataCoverage": {"classification": "specified-by-the-plan-not-measured-revert-traffic",
                                   **{dimension: sorted(values) for dimension, values in found.items()}},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path,
                        default=ROOT / "scripts/semantic-revert-data-corpus.json")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel), sort_keys=True))


if __name__ == "__main__":
    main()
