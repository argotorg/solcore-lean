#!/usr/bin/env python3
"""Check the fixed closure capture corpus using fresh native Core executions.

The corpus takes, from seed 1 upwards at the default budget, every generated
plan that covers a missing shape value, each at the eight primitive boundary
inputs; every value is required. This test rebuilds that selection, admits
every plan with its own walk over factories, statements, lambdas and their
scopes, recomputes every shape and the shrink measure from the plan and its own
interpreter, which runs closures by value over Python tuples (a snapshot at
creation, a fresh copy at each call, the field and the fold shared), re-emits
the source and compares it exactly, evaluates every case's plan against the
recorded Core outcome, and replays, observes and shrinks natively. It neither
compiles Rust nor executes an EVM. `test-semantic-closure-factories-corpus.py`
runs the same walk for the closure factory corpus.
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


pure = load("closure_corpus_pure", "Tests/scripts/test-semantic-corpus.py")
m2 = load("closure_corpus_adapter", "scripts/semantic-differential.py")
require, run, canonical_word = pure.require, pure.run, pure.canonical_word
VERSIONS = ("generatorVersion", "profileVersion", "emitterVersion", "wrapperVersion", "boundaryVersion")
BOUNDARIES = tuple(int(value) for value in ("0", "1", "2", "255", "256", str(2**256 - 1), str(2**255), str(2**255 - 1)))
M = 2 ** 256
NODES = 1024
CASE_LIMIT = 4096
SHRINK_BYTES = 1_500_000
FOLD = 1099511628211
MAX_STEPS, MAX_FACTORIES, MAX_FACTORY_STEPS, MAX_BODY, MAX_DEPTH = 10, 2, 3, 3, 2
MAX_VALUES, MAX_CLOSURES, MAX_LOOP, MAX_LOOP_BODY = 4, 4, 3, 2
OPS = {"add": "+", "sub": "-", "mul": "*", "xor": "^"}
VIAS = ("direct", "apply", "twice")
FN = "function (word) returns (word)"
PANIC = "4e487b71"

CAPTURES = {"profile": "runtime-closure-captures", "schema": m2.CLOSURE_CAPTURES_CASE_SCHEMA,
            "planSchema": "solcore-lean.closure-captures-plan.v1", "planKey": "closureCapturesPlan",
            "shapesKey": "closureCapturesShapes", "requirements": "closureCapturesRequirements",
            "command": "closure-captures-generate", "origin": "closure-captures-generated",
            "contract": "SynthesizedClosureCaptures", "manifest": "scripts/semantic-closure-captures-corpus.json",
            "shapes": m2.CLOSURE_CAPTURES_SHAPES, "factories": False, "minimum": 256}
FACTORIES = {"profile": "runtime-closure-factories", "schema": m2.CLOSURE_FACTORIES_CASE_SCHEMA,
             "planSchema": "solcore-lean.closure-factories-plan.v1", "planKey": "closureFactoriesPlan",
             "shapesKey": "closureFactoriesShapes", "requirements": "closureFactoriesRequirements",
             "command": "closure-factories-generate", "origin": "closure-factories-generated",
             "contract": "SynthesizedClosureFactories", "manifest": "scripts/semantic-closure-factories-corpus.json",
             "shapes": m2.CLOSURE_FACTORIES_SHAPES, "factories": True, "minimum": 256}


def required(profile):
    return {key: list(values) for key, values in profile["shapes"].items()}


def keys(value, expected, label):
    require(isinstance(value, dict) and set(value) == set(expected), f"closure plan {label} has unexpected fields")


def nat(value, label):
    require(type(value) is int and value >= 0, f"closure plan {label} is not a natural number")
    return value


# Plans are decoded into tuples: a term is ("lit", n), ("var", var), ("op", name, l, r),
# ("checked", name, l, r) or ("call", via, ref, argument); a var ("param", up), ("value", ref)
# or ("field",); a ref (up, index); a statement one of the kinds below.

def decode_ref(value):
    require(isinstance(value, list) and len(value) == 2, "closure plan reference is not a pair")
    return (nat(value[0], "reference scope"), nat(value[1], "reference index"))


def decode_var(value):
    if value == "field":
        return ("field",)
    require(isinstance(value, dict) and len(value) == 1, "unknown closure plan variable")
    if "param" in value:
        return ("param", nat(value["param"], "parameter scope"))
    keys(value, {"value"}, "variable")
    return ("value", decode_ref(value["value"]))


def decode_term(value):
    require(isinstance(value, dict), "unknown closure plan term")
    if "lit" in value:
        keys(value, {"lit"}, "literal")
        text = value["lit"]
        require(isinstance(text, str) and text.isascii() and text.isdecimal() and str(int(text)) == text,
                "noncanonical closure plan number")
        return ("lit", int(text))
    if "var" in value:
        keys(value, {"var"}, "variable term")
        return ("var", decode_var(value["var"]))
    if "op" in value:
        keys(value, {"op", "left", "right"}, "operation")
        require(value["op"] in OPS, "unknown closure plan operation")
        return ("op", value["op"], decode_term(value["left"]), decode_term(value["right"]))
    if "checked" in value:
        keys(value, {"checked", "left", "right"}, "checked operation")
        require(value["checked"] in ("add", "div"), "unknown checked operation")
        return ("checked", value["checked"], decode_term(value["left"]), decode_term(value["right"]))
    keys(value, {"call", "closure", "argument"}, "call")
    require(value["call"] in VIAS, "unknown closure call")
    return ("call", value["call"], decode_ref(value["closure"]), decode_term(value["argument"]))


def decode_stmts(value):
    require(isinstance(value, list), "closure plan statements are not a list")
    return [decode_stmt(item) for item in value]


def decode_stmt(value):
    require(isinstance(value, dict), "unknown closure plan statement")
    if "value" in value:
        keys(value, {"value"}, "value")
        return ("value", decode_term(value["value"]))
    if "assign" in value:
        keys(value, {"assign", "term"}, "assignment")
        return ("assign", decode_var(value["assign"]), decode_term(value["term"]))
    if "lambda" in value:
        keys(value, {"lambda", "result"}, "lambda")
        return ("lambda", decode_stmts(value["lambda"]), decode_term(value["result"]))
    if "alias" in value:
        keys(value, {"alias"}, "alias")
        return ("alias", decode_ref(value["alias"]))
    if "make" in value:
        keys(value, {"make", "argument"}, "factory call")
        return ("make", nat(value["make"], "factory"), decode_term(value["argument"]))
    if "discard" in value:
        keys(value, {"discard", "argument"}, "discarded factory call")
        return ("discard", nat(value["discard"], "factory"), decode_term(value["argument"]))
    if "relambda" in value:
        keys(value, {"relambda", "body", "result"}, "rebinding to a lambda")
        return ("relambda", decode_ref(value["relambda"]), decode_stmts(value["body"]), decode_term(value["result"]))
    if "realias" in value:
        keys(value, {"realias", "source"}, "rebinding to a closure")
        return ("realias", decode_ref(value["realias"]), decode_ref(value["source"]))
    if "remake" in value:
        keys(value, {"remake", "factory", "argument"}, "rebinding to a factory")
        return ("remake", decode_ref(value["remake"]), nat(value["factory"], "factory"), decode_term(value["argument"]))
    if "observe" in value:
        keys(value, {"observe"}, "observation")
        return ("observe", decode_term(value["observe"]))
    keys(value, {"loop", "body"}, "loop")
    return ("loop", nat(value["loop"], "loop count"), decode_stmts(value["body"]))


def decode_factory(value):
    keys(value, {"method", "body", "returns"}, "factory")
    require(type(value["method"]) is bool, "a factory's method flag is not a Boolean")
    returns = value["returns"]
    if isinstance(returns, dict) and "closure" in returns:
        keys(returns, {"closure"}, "closure result")
        decoded = ("closure", nat(returns["closure"], "result closure"))
    else:
        keys(returns, {"lambda", "result"}, "lambda result")
        decoded = ("lambda", decode_stmts(returns["lambda"]), decode_term(returns["result"]))
    return {"method": value["method"], "body": decode_stmts(value["body"]), "returns": decoded}


def decode_plan(plan, profile):
    keys(plan, {"schema", "factories", "steps"}, "envelope")
    require(plan["schema"] == profile["planSchema"], "unsupported closure plan schema")
    require(isinstance(plan["factories"], list), "closure plan factories are not a list")
    return {"factories": [decode_factory(item) for item in plan["factories"]], "steps": decode_stmts(plan["steps"])}


# Captures: what a term `level` scopes inside a lambda's body names outside it, relative to
# the scope creating the lambda.

def var_caps(level, var):
    if var[0] == "param" and level < var[1]:
        return [("param", var[1] - level - 1)]
    if var[0] == "value" and level < var[1][0]:
        return [("value", var[1][0] - level - 1, var[1][1])]
    return []


def ref_caps(level, ref):
    return [("closure", ref[0] - level - 1, ref[1])] if level < ref[0] else []


def term_caps(level, term):
    if term[0] == "lit":
        return []
    if term[0] == "var":
        return var_caps(level, term[1])
    if term[0] in ("op", "checked"):
        return term_caps(level, term[2]) + term_caps(level, term[3])
    return ref_caps(level, term[2]) + term_caps(level, term[3])


def stmt_caps(level, stmt):
    kind = stmt[0]
    if kind in ("value", "observe"):
        return term_caps(level, stmt[1])
    if kind == "assign":
        return var_caps(level, stmt[1]) + term_caps(level, stmt[2])
    if kind == "lambda":
        return list_caps(level + 1, stmt[1]) + term_caps(level + 1, stmt[2])
    if kind == "alias":
        return ref_caps(level, stmt[1])
    if kind in ("make", "discard"):
        return term_caps(level, stmt[2])
    if kind == "relambda":
        return ref_caps(level, stmt[1]) + list_caps(level + 1, stmt[2]) + term_caps(level + 1, stmt[3])
    if kind == "realias":
        return ref_caps(level, stmt[1]) + ref_caps(level, stmt[2])
    if kind == "remake":
        return ref_caps(level, stmt[1]) + term_caps(level, stmt[3])
    return list_caps(level, stmt[2])


def list_caps(level, stmts):
    return [cap for stmt in stmts for cap in stmt_caps(level, stmt)]


def lambda_caps(body, result):
    caps = []
    for cap in list_caps(0, body) + term_caps(0, result):
        if cap not in caps:
            caps.append(cap)
    return caps


def lambda_holds(body, result):
    return any(cap[0] == "closure" for cap in lambda_caps(body, result))


def subterms(term):
    found = [term]
    if term[0] in ("op", "checked"):
        found += subterms(term[2]) + subterms(term[3])
    elif term[0] == "call":
        found += subterms(term[3])
    return found


def own_terms(stmt):
    kind = stmt[0]
    if kind in ("value", "observe"):
        return [stmt[1]]
    if kind in ("assign", "make", "discard"):
        return [stmt[2]]
    if kind == "remake":
        return [stmt[3]]
    return []


def effectful_term(term):
    return any(sub == ("var", ("field",)) or sub[0] in ("checked", "call") for sub in subterms(term))


def effectful(factory):
    return any((stmt[0] == "assign" and stmt[1] == ("field",)) or any(effectful_term(term) for term in own_terms(stmt))
               for stmt in factory["body"])


def returns_local(factory):
    returns = factory["returns"]
    return returns[0] == "closure" or lambda_holds(returns[1], returns[2])


class Walk:
    """The static scope: scopes innermost first, each a kind, a method flag, a count of Word
    locals and, per closure, whether it captures a closure."""

    def __init__(self, factories, within=None):
        self.factories, self.within = factories, within

    @staticmethod
    def field_visible(stack):
        return stack[-1]["kind"] == "run" or (stack[-1]["kind"] == "factory" and stack[-1]["method"])

    def factory_admitted(self, stack, index):
        if index >= len(self.factories):
            return False
        method = self.factories[index][0]
        return (self.within is None or index < self.within) and (not method or self.field_visible(stack))

    def call_admitted(self, stack, index, argument):
        """A factory that returns one of its own closures is called with an argument without effects."""
        return self.factory_admitted(stack, index) and not (self.factories[index][1] and effectful_term(argument))

    @staticmethod
    def var(stack, var):
        if var[0] == "param":
            return var[1] < len(stack)
        if var[0] == "value":
            up, index = var[1]
            return up < len(stack) and index < stack[up]["values"]
        return Walk.field_visible(stack)

    @staticmethod
    def ref(stack, ref):
        up, index = ref
        return up < len(stack) and index < len(stack[up]["closures"])

    @staticmethod
    def holds(stack, ref):
        return stack[ref[0]]["closures"][ref[1]]

    def term(self, stack, term):
        if term[0] == "lit":
            return term[1] < M
        if term[0] == "var":
            return self.var(stack, term[1])
        if term[0] in ("op", "checked"):
            return self.term(stack, term[2]) and self.term(stack, term[3])
        return (self.ref(stack, term[2]) and (term[1] == "direct" or not self.holds(stack, term[2]))
                and self.term(stack, term[3]))

    @staticmethod
    def in_body(stack):
        return stack[0]["kind"] == "lambda"

    @staticmethod
    def with_head(stack, head):
        return [head] + stack[1:]

    @staticmethod
    def set_holds(stack, ref, holds):
        changed = copy.deepcopy(stack)
        changed[ref[0]]["closures"][ref[1]] = holds
        return changed

    def push_closure(self, stack, holds):
        head = stack[0]
        require(len(head["closures"]) < MAX_CLOSURES, "a scope declares more than four closures")
        return self.with_head(stack, {**head, "closures": head["closures"] + [holds]})

    def stmt(self, stack, stmt):
        kind = stmt[0]
        run_top = len(stack) == 1 and stack[0]["kind"] == "run"
        if kind == "value":
            require(self.term(stack, stmt[1]), "a value names an undeclared local")
            require(stack[0]["values"] < MAX_VALUES, "a scope declares more than four Word locals")
            return self.with_head(stack, {**stack[0], "values": stack[0]["values"] + 1})
        if kind == "assign":
            require(self.var(stack, stmt[1]) and self.term(stack, stmt[2]), "an assignment names an undeclared local")
            return stack
        if kind == "lambda":
            return self.push_closure(stack, self.lambda_holds(stack, stmt[1], stmt[2]))
        if kind == "alias":
            require(self.ref(stack, stmt[1]), "an alias names an undeclared closure")
            return self.push_closure(stack, self.holds(stack, stmt[1]))
        if kind in ("make", "discard"):
            require(self.call_admitted(stack, stmt[1], stmt[2]) and self.term(stack, stmt[2]),
                    "a factory call outside the callable factories")
            return self.push_closure(stack, False) if kind == "make" else stack
        if kind == "relambda":
            require(self.ref(stack, stmt[1]), "a rebinding names an undeclared closure")
            holds = self.lambda_holds(stack, stmt[2], stmt[3])
            require(not (self.in_body(stack) and holds), "a body rebinds a closure to one that captures a closure")
            return self.set_holds(stack, stmt[1], holds)
        if kind == "realias":
            require(self.ref(stack, stmt[1]) and self.ref(stack, stmt[2]), "a rebinding names an undeclared closure")
            holds = self.holds(stack, stmt[2])
            require(not (self.in_body(stack) and holds), "a body rebinds a closure to one that captures a closure")
            return self.set_holds(stack, stmt[1], holds)
        if kind == "remake":
            require(self.ref(stack, stmt[1]) and self.call_admitted(stack, stmt[2], stmt[3]) and self.term(stack, stmt[3]),
                    "a factory rebinding outside the callable factories")
            return self.set_holds(stack, stmt[1], False)
        if kind == "observe":
            require(run_top and self.term(stack, stmt[1]), "an observation outside run's own statements")
            return stack
        require(run_top, "a loop outside run's own statements")
        require(1 <= stmt[1] <= MAX_LOOP and 1 <= len(stmt[2]) <= MAX_LOOP_BODY, "a loop's count or body is out of range")
        require(all(item[0] in ("assign", "observe") for item in stmt[2]), "a loop body declares or rebinds")
        return self.stmts(stack, stmt[2])

    def stmts(self, stack, stmts):
        for stmt in stmts:
            stack = self.stmt(stack, stmt)
        return stack

    def lambda_holds(self, stack, body, result):
        depth = sum(scope["kind"] == "lambda" for scope in stack)
        require(depth < MAX_DEPTH and len(body) <= MAX_BODY, "a lambda nests too deeply or its body is too long")
        require(all(not (cap[0] == "closure" and self.ref(stack, cap[1:]) and self.holds(stack, cap[1:]))
                    for cap in lambda_caps(body, result)), "a lambda captures a closure that captures a closure")
        inner = self.stmts([{"kind": "lambda", "method": False, "values": 0, "closures": []}] + stack, body)
        require(self.term(inner, result), "a lambda's result names an undeclared local")
        return lambda_holds(body, result)


def factory_info(factories):
    require(len(factories) <= MAX_FACTORIES, "more than two factories")
    info = []
    for index, factory in enumerate(factories):
        require(len(factory["body"]) <= MAX_FACTORY_STEPS, "a factory has more than three statements")
        require(not (returns_local(factory) and effectful(factory)),
                "a factory that returns one of its closures has effects of its own")
        walk = Walk(info + [(factory["method"], False)], index)
        stack = walk.stmts([{"kind": "factory", "method": factory["method"], "values": 0, "closures": []}],
                           factory["body"])
        returns = factory["returns"]
        if returns[0] == "closure":
            require(returns[1] < len(stack[0]["closures"]), "a factory returns an undeclared closure")
            holds = stack[0]["closures"][returns[1]]
        else:
            holds = walk.lambda_holds(stack, returns[1], returns[2])
        require(not holds, "a factory returns a closure that captures a closure")
        info.append((factory["method"], returns_local(factory)))
    return info


def contains(stmts, kinds):
    for stmt in stmts:
        if stmt[0] in kinds:
            return True
        if stmt[0] == "lambda" and contains(stmt[1], kinds):
            return True
        if stmt[0] == "relambda" and contains(stmt[2], kinds):
            return True
        if stmt[0] == "loop" and contains(stmt[2], kinds):
            return True
    return False


def observes(stmts):
    return any(stmt[0] == "observe" or (stmt[0] == "loop" and observes(stmt[2])) for stmt in stmts)


def check_plan(value, profile):
    plan = decode_plan(value, profile)
    require(1 <= len(plan["steps"]) <= MAX_STEPS, "a plan has one to ten steps")
    info = factory_info(plan["factories"])
    Walk(info).stmts([{"kind": "run", "method": False, "values": 0, "closures": []}], plan["steps"])
    require(observes(plan["steps"]), "a plan observes nothing")
    if profile["factories"]:
        require(plan["factories"] and contains(plan["steps"], ("make", "discard", "remake")),
                "a closure factory plan calls no factory")
    else:
        require(not plan["factories"], "a closure capture plan has a factory")
    return plan


# The interpreter. A closure is ("closure", body, result, params, values, closures) with the
# scopes it captured as tuples; a call starts from them, so its writes stay in the call.

class Stop(Exception):
    def __init__(self, code, site):
        super().__init__(code)
        self.code, self.site = code, site


def replace(items, index, value):
    return items[:index] + (value,) + items[index + 1:]


class Machine:
    def __init__(self, plan):
        self.plan, self.field, self.fold = plan, 0, 0

    def read(self, frames, var):
        if var[0] == "param":
            return frames[0][var[1]]
        if var[0] == "value":
            return frames[1][var[1][0]][var[1][1]]
        return self.field

    def write(self, frames, var, value):
        params, values, closures = frames
        if var[0] == "param":
            return (replace(params, var[1], value), values, closures)
        if var[0] == "value":
            up, index = var[1]
            return (params, replace(values, up, replace(values[up], index, value)), closures)
        self.field = value
        return frames

    @staticmethod
    def close(frames, body, result):
        return ("closure", body, result) + frames

    @staticmethod
    def closure_at(frames, ref):
        return frames[2][ref[0]][ref[1]]

    @staticmethod
    def push(frames, slot, item):
        parts = list(frames)
        parts[slot] = replace(parts[slot], 0, parts[slot][0] + (item,))
        return tuple(parts)

    def term(self, site, frames, term):
        kind = term[0]
        if kind == "lit":
            return term[1] % M
        if kind == "var":
            return self.read(frames, term[1])
        if kind == "op":
            left = self.term(site, frames, term[2])
            right = self.term(site, frames, term[3])
            return {"add": (left + right) % M, "sub": (left - right) % M, "mul": (left * right) % M,
                    "xor": left ^ right}[term[1]]
        if kind == "checked":
            left = self.term(site, frames, term[2])
            right = self.term(site, frames, term[3])
            if term[1] == "add":
                if left + right >= M:
                    raise Stop(0x11, site)
                return left + right
            if right == 0:
                raise Stop(0x12, site)
            return left // right
        closure = self.closure_at(frames, term[2])
        argument = self.term(site, frames, term[3])
        if term[1] == "twice":
            return self.call(closure, self.call(closure, argument))
        return self.call(closure, argument)

    def call(self, closure, argument):
        _, body, result, params, values, closures = closure
        frames = ((argument,) + params, ((),) + values, ((),) + closures)
        frames = self.stmts("body", frames, body)
        return self.term("body", frames, result)

    def stmts(self, site, frames, stmts):
        for stmt in stmts:
            frames = self.stmt(site, frames, stmt)
        return frames

    def stmt(self, site, frames, stmt):
        kind = stmt[0]
        if kind == "value":
            return self.push(frames, 1, self.term(site, frames, stmt[1]))
        if kind == "assign":
            return self.write(frames, stmt[1], self.term(site, frames, stmt[2]))
        if kind == "lambda":
            return self.push(frames, 2, self.close(frames, stmt[1], stmt[2]))
        if kind == "alias":
            return self.push(frames, 2, self.closure_at(frames, stmt[1]))
        if kind == "make":
            return self.push(frames, 2, self.factory(stmt[1], self.term(site, frames, stmt[2])))
        if kind == "discard":
            self.factory(stmt[1], self.term(site, frames, stmt[2]))
            return frames
        if kind in ("relambda", "realias", "remake"):
            up, index = stmt[1]
            if kind == "relambda":
                made = self.close(frames, stmt[2], stmt[3])
            elif kind == "realias":
                made = self.closure_at(frames, stmt[2])
            else:
                made = self.factory(stmt[2], self.term(site, frames, stmt[3]))
            params, values, closures = frames
            return (params, values, replace(closures, up, replace(closures[up], index, made)))
        if kind == "observe":
            observed = self.term(site, frames, stmt[1])
            self.fold = ((self.fold * FOLD) % M) ^ observed
            return frames
        for _ in range(stmt[1]):
            frames = self.stmts(site, frames, stmt[2])
        return frames

    def factory(self, index, argument):
        factory = self.plan["factories"][index]
        frames = self.stmts("factory", ((argument,), ((),), ((),)), factory["body"])
        returns = factory["returns"]
        if returns[0] == "closure":
            return self.closure_at(frames, (0, returns[1]))
        return self.close(frames, returns[1], returns[2])


def interpret(plan, x):
    """The outcome at an input, ("word", fold) or ("panic", code), and a panic's site."""
    machine = Machine(plan)
    try:
        machine.stmts("run", ((x % M,), ((),), ((),)), plan["steps"])
    except Stop as stop:
        return ("panic", stop.code), stop.site
    return ("word", machine.fold), None


def outcome_text(outcome):
    if outcome[0] == "word":
        return str(outcome[1])
    return "0x" + PANIC + f"{outcome[1]:064x}"


def observed_text(observation):
    require(isinstance(observation, dict) and observation.get("stage") == "execution", "invalid Core observation")
    if observation.get("status") == "returned":
        require(set(observation) == {"stage", "status", "word"}, "a returned closure observation holds one Word")
        return str(canonical_word(observation["word"]))
    require(observation.get("status") == "reverted" and set(observation) == {"stage", "status", "output"}
            and re.fullmatch(r"0x" + PANIC + r"[0-9a-f]{64}", observation["output"]),
            "a closure observation returns a Word or reverts with a panic")
    return observation["output"]


# Shapes, from the plan and its boundary runs.

def visits(stmts, lam, factory, loop, before):
    found = []
    for stmt in stmts:
        found.append((stmt, lam, factory, loop, before))
        if stmt[0] == "lambda":
            found += visits(stmt[1], lam + 1, factory, False, [])
        elif stmt[0] == "relambda":
            found += visits(stmt[2], lam + 1, factory, False, [])
        elif stmt[0] == "loop":
            found += visits(stmt[2], lam, factory, True, before)
        before = [stmt] + before
    return found


def plan_visits(plan):
    found = visits(plan["steps"], 0, False, False, [])
    for factory in plan["factories"]:
        returns = factory["returns"]
        extra = [("lambda", returns[1], returns[2])] if returns[0] == "lambda" else []
        found += visits(factory["body"] + extra, 0, True, False, [])
    return found


def stmt_terms(stmt):
    kind = stmt[0]
    if kind in ("value", "observe"):
        return [stmt[1]]
    if kind in ("assign", "lambda", "make", "discard"):
        return [stmt[2]]
    if kind in ("relambda", "remake"):
        return [stmt[3]]
    return []


def lambda_parts(stmt):
    if stmt[0] == "lambda":
        return stmt[1], stmt[2]
    if stmt[0] == "relambda":
        return stmt[2], stmt[3]
    return None


def cap_shape(lam, factory, cap):
    if cap[0] == "param":
        return ("param" if factory else "input") if lam == cap[1] else "arg"
    if cap[0] == "value":
        return "value" if lam == cap[1] else "body-value"
    return "closure"


def captured_before(before, cap):
    return any(lambda_parts(stmt) is not None and cap in lambda_caps(*lambda_parts(stmt)) for stmt in before)


def sorted_unique(values):
    return sorted(set(values))


def capture_shapes(plan):
    found = []
    for stmt, lam, factory, _, _ in plan_visits(plan):
        parts = lambda_parts(stmt)
        if parts is not None:
            caps = lambda_caps(*parts)
            found += [cap_shape(lam, factory, cap) for cap in caps] if caps else ["nothing"]
    return sorted_unique(found)


def field_shapes(plan):
    found = []
    for stmt, lam, factory, _, _ in plan_visits(plan):
        place = "body" if lam > 0 else "factory" if factory else "run"
        if any(("var", ("field",)) in subterms(term) for term in stmt_terms(stmt)):
            found.append(place + "-read")
        if stmt[0] == "assign" and stmt[1] == ("field",):
            found.append(place + "-write")
    return sorted_unique(found)


def write_shapes(plan):
    found = []
    for stmt, lam, _, _, _ in plan_visits(plan):
        if lam == 0:
            continue
        if stmt[0] == "assign" and stmt[1][0] == "param":
            found.append("own-param" if stmt[1][1] == 0 else "captured-param")
        elif stmt[0] == "assign" and stmt[1][0] == "value":
            found.append("own-value" if stmt[1][1][0] == 0 else "captured-value")
        elif stmt[0] in ("relambda", "realias", "remake"):
            found.append("own-closure" if stmt[1][0] == 0 else "captured-closure")
    return sorted_unique(found)


def later_write(stmt, before):
    if stmt[0] != "assign":
        return False
    if stmt[1] == ("param", 0):
        return captured_before(before, ("param", 0))
    if stmt[1][0] == "value" and stmt[1][1][0] == 0:
        return captured_before(before, ("value", 0, stmt[1][1][1]))
    return False


def outer_shapes(plan):
    found = []
    for stmt, _, _, _, before in plan_visits(plan):
        if later_write(stmt, before):
            found.append("later-write")
        elif stmt[0] in ("relambda", "realias", "remake") and stmt[1][0] == 0 \
                and captured_before(before, ("closure", 0, stmt[1][1])):
            found.append("later-rebind")
    return sorted_unique(found)


def calls(stmt):
    return [(term[1], term[2]) for top in stmt_terms(stmt) for term in subterms(top) if term[0] == "call"]


def call_shapes(plan):
    found, own = [], []
    for stmt, lam, factory, loop, _ in plan_visits(plan):
        for via, ref in calls(stmt):
            found.append(via)
            if loop:
                found += ["loop", "repeat"]
            if lam > 0:
                found.append("in-body")
            if lam > 0 and ref[0] > 0:
                found.append("captured")
            if via == "twice":
                found.append("repeat")
            if lam == 0 and not factory and ref[0] == 0:
                own.append(ref[1])
    if any(own.count(index) >= 2 for index in own):
        found.append("repeat")
    return sorted_unique(found)


CLOSURE_FORMS = {"alias": "alias", "relambda": "relambda", "realias": "realias", "make": "make", "discard": "discard",
                 "remake": "remake", "loop": "loop"}


def closure_shapes(plan):
    found = []
    for stmt, lam, _, _, _ in plan_visits(plan):
        if stmt[0] == "lambda":
            found.append("nested" if lam > 0 else "lambda")
        elif stmt[0] in CLOSURE_FORMS:
            found.append(CLOSURE_FORMS[stmt[0]])
    return sorted_unique(found)


def factory_argument(stmt):
    if stmt[0] in ("make", "discard"):
        return stmt[1], stmt[2]
    if stmt[0] == "remake":
        return stmt[2], stmt[3]
    return None


def factory_shapes(plan):
    found = []
    for factory in plan["factories"]:
        found.append("method" if factory["method"] else "free")
        found.append("closure-result" if factory["returns"][0] == "closure" else "lambda-result")
        direct = [stmt for stmt, lam, _, _, _ in visits(factory["body"], 0, True, False, []) if lam == 0]
        if any(any(sub[0] == "checked" for sub in subterms(term)) for stmt in direct for term in own_terms(stmt)):
            found.append("checked-effect")
        if any(factory_argument(stmt) is not None for stmt in direct):
            found.append("chained")
    made = []
    for stmt, lam, factory, _, before in plan_visits(plan):
        if factory:
            parts = lambda_parts(stmt)
            if parts is not None:
                for cap in lambda_caps(*parts):
                    shape = cap_shape(lam, True, cap)
                    if shape in ("param", "value"):
                        found.append("captures-" + shape)
            if later_write(stmt, before):
                found.append("later-write")
        else:
            argument = factory_argument(stmt)
            if argument is not None:
                made.append(argument[0])
                found.append("literal-argument" if argument[1][0] == "lit" else "runtime-argument")
                if lam > 0:
                    found.append("in-body")
    if any(made.count(index) >= 2 for index in made):
        found.append("instances")
    return sorted_unique(found)


def boundary_runs(plan):
    return [interpret(plan, x) for x in BOUNDARIES]


def outcome_name(outcome):
    if outcome[0] == "word":
        return "return"
    return {0x11: "panic-0x11", 0x12: "panic-0x12"}.get(outcome[1], "panic-other")


def shapes(plan, profile):
    runs = boundary_runs(plan)
    found = {"capture": capture_shapes(plan), "field": field_shapes(plan), "write": write_shapes(plan),
             "outer": outer_shapes(plan), "call": call_shapes(plan), "closure": closure_shapes(plan)}
    if profile["factories"]:
        found["factory"] = factory_shapes(plan)
    found["outcome"] = sorted_unique(outcome_name(outcome) for outcome, _ in runs)
    found["panicSite"] = sorted_unique(site for _, site in runs if site is not None)
    return found


# The shrink measure.

def term_size(term):
    if term[0] in ("lit", "var"):
        return 1
    if term[0] in ("op", "checked"):
        return 1 + term_size(term[2]) + term_size(term[3])
    return 2 + term_size(term[3])


def stmt_size(stmt):
    kind = stmt[0]
    if kind in ("value", "observe"):
        return 1 + term_size(stmt[1])
    if kind == "assign":
        return 1 + term_size(stmt[2])
    if kind == "lambda":
        return 2 + sum(map(stmt_size, stmt[1])) + term_size(stmt[2])
    if kind == "relambda":
        return 2 + sum(map(stmt_size, stmt[2])) + term_size(stmt[3])
    if kind in ("alias", "realias"):
        return 1
    if kind in ("make", "discard"):
        return 2 + term_size(stmt[2])
    if kind == "remake":
        return 2 + term_size(stmt[3])
    return stmt[1] + sum(map(stmt_size, stmt[2]))


def returns_size(returns):
    return 1 if returns[0] == "closure" else 2 + sum(map(stmt_size, returns[1])) + term_size(returns[2])


def plan_size(value, profile):
    plan = decode_plan(value, profile)
    return sum(map(stmt_size, plan["steps"])) + sum(1 + sum(map(stmt_size, factory["body"])) +
                                                     returns_size(factory["returns"]) for factory in plan["factories"])


# The emitter.

def indent(count, lines):
    return [" " * count + line for line in lines]


def param_name(is_run, depth):
    return ("sc_x" if is_run else "sc_p") if depth == 0 else "sc_a" if depth == 1 else "sc_b"


def value_name(depth, index):
    return ("sc_v", "sc_w", "sc_u")[min(depth, 2)] + str(index)


def closure_name(depth, index):
    return ("sc_f", "sc_g", "sc_h")[min(depth, 2)] + str(index)


def var_text(is_run, depth, var):
    if var[0] == "param":
        return param_name(is_run, depth - var[1])
    if var[0] == "value":
        return value_name(depth - var[1][0], var[1][1])
    return "sc_n"


def ref_text(depth, ref):
    return closure_name(depth - ref[0], ref[1])


def term_text(is_run, depth, term):
    kind = term[0]
    if kind == "lit":
        return str(term[1])
    if kind == "var":
        return var_text(is_run, depth, term[1])
    if kind == "op":
        return "(" + term_text(is_run, depth, term[2]) + " " + OPS[term[1]] + " " + term_text(is_run, depth, term[3]) + ")"
    if kind == "checked":
        symbol = "+" if term[1] == "add" else "/"
        return ("Typedef.rep(uint256(" + term_text(is_run, depth, term[2]) + ") " + symbol + " uint256(" +
                term_text(is_run, depth, term[3]) + "))")
    name, argument = ref_text(depth, term[2]), term_text(is_run, depth, term[3])
    if term[1] == "direct":
        return name + "(" + argument + ")"
    return "sc_" + term[1] + "(" + name + ", " + argument + ")"


def make_text(is_run, depth, factory, argument):
    return "sc_mk" + str(factory) + "(" + term_text(is_run, depth, argument) + ")"


def lambda_wrap(is_run, depth, lead, inner, result):
    return ([lead + "lam (" + param_name(is_run, depth + 1) + ": word) -> word {"] +
            indent(4, inner + ["return " + term_text(is_run, depth + 1, result) + ";"]) + ["};"])


def block_lines(is_run, depth, counts, stmts):
    lines = []
    for stmt in stmts:
        kind = stmt[0]
        if kind == "value":
            lines.append("let " + value_name(depth, counts["values"]) + ": word = " +
                         term_text(is_run, depth, stmt[1]) + ";")
            counts["values"] += 1
        elif kind == "assign":
            lines.append(var_text(is_run, depth, stmt[1]) + " = " + term_text(is_run, depth, stmt[2]) + ";")
        elif kind == "lambda":
            lead = "let " + closure_name(depth, counts["closures"]) + ": " + FN + " = "
            lines += lambda_wrap(is_run, depth, lead, block_lines(is_run, depth + 1, fresh(), stmt[1]), stmt[2])
            counts["closures"] += 1
        elif kind == "alias":
            lines.append("let " + closure_name(depth, counts["closures"]) + ": " + FN + " = " +
                         ref_text(depth, stmt[1]) + ";")
            counts["closures"] += 1
        elif kind == "make":
            lines.append("let " + closure_name(depth, counts["closures"]) + ": " + FN + " = " +
                         make_text(is_run, depth, stmt[1], stmt[2]) + ";")
            counts["closures"] += 1
        elif kind == "discard":
            lines.append(make_text(is_run, depth, stmt[1], stmt[2]) + ";")
        elif kind == "relambda":
            lines += lambda_wrap(is_run, depth, ref_text(depth, stmt[1]) + " = ",
                                 block_lines(is_run, depth + 1, fresh(), stmt[2]), stmt[3])
        elif kind == "realias":
            lines.append(ref_text(depth, stmt[1]) + " = " + ref_text(depth, stmt[2]) + ";")
        elif kind == "remake":
            lines.append(ref_text(depth, stmt[1]) + " = " + make_text(is_run, depth, stmt[2], stmt[3]) + ";")
        elif kind == "observe":
            lines.append("sc_r = ((sc_r * 1099511628211) ^ " + term_text(is_run, depth, stmt[1]) + ");")
        else:
            counter = "sc_i" + str(counts["loops"])
            counts["loops"] += 1
            inner = block_lines(is_run, depth, {**counts}, stmt[2])
            lines += (["let " + counter + ": word = 0;", "while (" + counter + " < " + str(stmt[1]) + ") {"] +
                      indent(4, inner + [counter + " = " + counter + " + 1;"]) + ["}"])
    return lines


def fresh():
    return {"values": 0, "closures": 0, "loops": 0}


def factory_lines(index, factory):
    inner = block_lines(False, 0, fresh(), factory["body"])
    returns = factory["returns"]
    if returns[0] == "closure":
        tail = ["return " + closure_name(0, returns[1]) + ";"]
    else:
        tail = lambda_wrap(False, 0, "return ", block_lines(False, 1, fresh(), returns[1]), returns[2])
    return ["function sc_mk" + str(index) + "(sc_p: word) returns (" + FN + ") {"] + indent(4, inner + tail) + ["}"]


def all_terms(plan):
    return [sub for stmt, _, _, _, _ in plan_visits(plan) for term in stmt_terms(stmt) for sub in subterms(term)]


def uses_via(plan, via):
    return any(term[0] == "call" and term[1] == via for term in all_terms(plan))


def uses_field(plan):
    return (("var", ("field",)) in all_terms(plan) or
            any(stmt[0] == "assign" and stmt[1] == ("field",) for stmt, _, _, _, _ in plan_visits(plan)))


def emit(value, profile):
    plan = decode_plan(value, profile)
    helpers = []
    if uses_via(plan, "apply"):
        helpers += ["function sc_apply<a>(f: function (a) returns (a), x: a) returns (a) {", "    return f(x);", "}", ""]
    if uses_via(plan, "twice"):
        helpers += ["function sc_twice<a>(f: function (a) returns (a), x: a) returns (a) {", "    return f(f(x));", "}",
                    ""]
    free, methods = [], []
    for index, factory in enumerate(plan["factories"]):
        lines = factory_lines(index, factory)
        if factory["method"]:
            methods += indent(4, lines) + [""]
        else:
            free += lines + [""]
    field = ["    sc_n: word;", ""] if uses_field(plan) else []
    body = (["let sc_x: word = Typedef.rep(input);", "let sc_r: word = 0;"] +
            block_lines(True, 0, fresh(), plan["steps"]) + ["return uint256(sc_r);"])
    name = profile["contract"]
    lines = (["pragma solcore;", "import * from std;", "import * from std.dispatch;", ""] + helpers + free + ["contract " + name + " {"] +
             field + methods + ["    function run(input: uint256) public returns (uint256) {"] + indent(8, body) +
             ["    }", "}"])
    return "\n".join(lines) + "\n"


def calldata(x):
    return "0xa444f5e9" + f"{x:064x}"


def nodes(value):
    """An upper bound on the reference's Wire nodes: every tagged object, its types included."""
    if isinstance(value, dict):
        return ("tag" in value) + sum(nodes(child) for child in value.values())
    if isinstance(value, list):
        return sum(nodes(child) for child in value)
    return 0


def check_case(case, fuel, profile):
    require(isinstance(case, dict) and case.get("schema") == profile["schema"], "unexpected closure case schema")
    plan = check_plan(case[profile["planKey"]], profile)
    number = canonical_word(case["input"])
    program = case["program"]
    payload = {"tag": "product", "left": "word", "right": {"tag": "product", "left": "word", "right": "word"}}
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == {"tag": "sum", "left": "word", "right": payload},
            "the closure reference is a closed program returning a Word or revert data")
    require(nodes(program["body"]) <= CASE_LIMIT, "reference exceeds the case limit")
    require(1 <= case["provenance"]["referenceNodes"] <= CASE_LIMIT, "recorded reference size exceeds the case limit")
    name = profile["contract"]
    require(case["contract"] == {"name": name, "method": "run", "signature": "run(uint256)",
            "deployPath": [name + "Deploy"], "runtimePath": [name + "Deploy", name],
            "calldata": calldata(number), "constructorCalldata": "0x"}, "unexpected closure wrapper or calldata")
    require(case["source"] == emit(case[profile["planKey"]], profile), "the source differs from the plan's emission")
    require(case["provenance"][profile["shapesKey"]] == shapes(plan, profile), "recorded shapes differ from the plan")
    require(observed_text(case["directCore"]) == outcome_text(interpret(plan, number)[0]),
            "the recorded Core outcome differs from the plan's interpreter")
    return plan


def check_manifest(manifest, profile):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals", "requiredInputs",
              profile["requirements"], "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == profile["profile"], "unexpected closure manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "closure coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    require(manifest["requiredFeatures"] == [] and manifest["requiredWordLiterals"] == [],
            "the closure corpus requires shapes, not step features or literals")
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "the closure corpus must require all eight boundary inputs")
    require(manifest[profile["requirements"]] == required(profile), "the closure corpus must require its shape values")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "the closure corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"id", "generation", "input", "expectedFeatures"},
                "a closure corpus entry is a generation recipe with its input")
        identifier = entry["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        require(canonical_word(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        require(entry["expectedFeatures"] == [], "closure entries expect no step features")
        recipe = entry["generation"]
        require(isinstance(recipe, dict) and set(recipe) == {"seed", "maxProgramNodes"}, "invalid generation recipe")
        require(canonical_word(recipe["seed"]) < 1 << 64 and recipe["maxProgramNodes"] == NODES,
                "fixed recipes use a uint64 seed and the default budget")
    return entries


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
            "fixed closure seed did not emit eight cases in one attempt")
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
    require(isinstance(candidates, list) and candidates, "fixed closure case has no shrink candidate")
    require(sum(len(json.dumps(candidate, separators=(",", ":"))) for candidate in candidates) <= SHRINK_BYTES,
            "a shrink response exceeds its byte cap")
    key = profile["planKey"]
    parent = (plan_size(case[key], profile), int(case["input"]))
    seen = set()
    for candidate in candidates:
        check_case(candidate, fuel, profile)
        require(candidate["provenance"]["origin"] == {"kind": "reduced", "parentPlan": case[key],
                                                      "parentInput": case["input"]},
                "a shrink candidate is not a reduction of its parent")
        require((plan_size(candidate[key], profile), int(candidate["input"])) < parent,
                "a shrink candidate is not strictly smaller")
        encoded = json.dumps([candidate[key], candidate["input"]], sort_keys=True)
        require(encoded not in seen, "duplicate canonical shrink")
        seen.add(encoded)
        target = directory / "shrunk.json"
        target.write_text(json.dumps(candidate))
        require(run(tool, "replay", str(target), str(fuel)) == candidate,
                "native shrink lost canonical source/program/provenance")
        fresh_observation = run(tool, "observe", str(target), str(fuel))
        observed_text(fresh_observation)
        require(fresh_observation == candidate["directCore"], "shrunk observation differs from fresh Core execution")
    return len(candidates)


def lit(value):
    return {"lit": str(value)}


def param(up):
    return {"var": {"param": up}}


def call(via, up, index, argument):
    return {"call": via, "closure": [up, index], "argument": argument}


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
    observe = {"observe": param(0)}
    lam = {"lambda": [], "result": param(0)}
    holder = {"lambda": [], "result": call("direct", 1, 0, param(0))}
    free = {"method": False, "body": [], "returns": {"lambda": [], "result": param(0)}}
    method = {**free, "method": True}
    make = {"make": 0, "argument": param(0)}
    broken_plans = [
        ("no step", {**plan, "steps": []}),
        ("eleven steps", {**plan, "steps": [observe] * 11}),
        ("an undeclared local", {**plan, "steps": [{"observe": {"var": {"value": [0, 0]}}}]}),
        ("an undeclared closure", {**plan, "steps": [{"observe": call("direct", 0, 0, lit(1))}]}),
        ("five Word locals", {**plan, "steps": [{"value": lit(1)}] * 5 + [observe]}),
        ("five closures", {**plan, "steps": [lam] * 5 + [observe]}),
        ("a lambda naming its own closure", {**plan, "steps": [{"lambda": [], "result": call("direct", 1, 0, lit(1))},
                                                              observe]}),
        ("an observation in a lambda", {**plan, "steps": [{"lambda": [observe], "result": lit(0)}, observe]}),
        ("a loop in a lambda", {**plan, "steps": [{"lambda": [{"loop": 2, "body": [observe]}], "result": lit(0)}, observe]}),
        ("a closure in a loop", {**plan, "steps": [{"loop": 2, "body": [lam]}, observe]}),
        ("a loop of four", {**plan, "steps": [{"loop": 4, "body": [observe]}]}),
        ("an empty loop", {**plan, "steps": [{"loop": 2, "body": []}, observe]}),
        ("a depth-three lambda", {**plan, "steps": [{"lambda": [{"lambda": [{"lambda": [], "result": lit(0)}],
                                                                  "result": lit(0)}], "result": lit(0)}, observe]}),
        ("a body of four", {**plan, "steps": [{"lambda": [{"value": lit(1)}] * 4, "result": lit(0)}, observe]}),
        ("a holder passed to sc_apply", {**plan, "steps": [lam, holder, {"observe": call("apply", 0, 1, lit(1))}]}),
        ("a body rebinding to a holder", {**plan, "steps": [lam, holder, {"lambda": [{"realias": [1, 0], "source": [1, 1]}],
                                                                          "result": lit(0)}, observe]}),
        ("a noncanonical literal", {**plan, "steps": [{"observe": {"lit": "007"}}]}),
        ("an unknown operation", {**plan, "steps": [{"observe": {"op": "div", "left": lit(1), "right": lit(2)}}]}),
        ("the other plan schema", {**plan, "schema": (CAPTURES if profile["factories"] else FACTORIES)["planSchema"]})]
    if profile["factories"]:
        broken_plans += [
            ("no factory", {**plan, "factories": [], "steps": [observe]}),
            ("no factory call", {**plan, "factories": [free], "steps": [observe]}),
            ("three factories", {**plan, "factories": [free] * 3, "steps": [make, observe]}),
            ("a field in a free factory", {**plan, "factories": [{**free, "body": [{"assign": "field", "term": lit(1)}]}],
                                           "steps": [make, observe]}),
            ("a method called from a free factory", {**plan, "factories": [method, {**free, "body": [make]}],
                                                     "steps": [make, observe]}),
            ("a later factory", {**plan, "factories": [{**free, "body": [{"make": 1, "argument": lit(1)}]}, free],
                                 "steps": [make, observe]}),
            ("an effectful factory returning a closure", {**plan, "factories": [{**method, "body": [
                lam, {"assign": "field", "term": lit(1)}], "returns": {"closure": 0}}], "steps": [make, observe]}),
            ("a factory returning a holder", {**plan, "factories": [{**free, "body": [lam],
                                                                     "returns": {"lambda": [], "result": call(
                                                                         "direct", 1, 0, param(0))}}],
                                              "steps": [make, observe]}),
            ("a factory of four statements", {**plan, "factories": [{**free, "body": [{"value": lit(1)}] * 4}],
                                              "steps": [make, observe]})]
    else:
        broken_plans += [("a factory", {**plan, "factories": [free], "steps": [make, observe]})]
    for label, broken in broken_plans:
        rejects(lambda: check_plan(broken, profile), label)
    path = directory / "negative.json"
    key = profile["planKey"]
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("an added step", lambda value: value[key]["steps"].append(observe) if len(value[key]["steps"]) < MAX_STEPS
            else value[key]["steps"].pop()),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="1" if value["input"] != "1" else "2")),
        ("wrapper", lambda value: value["contract"].update(name="SynthesizedRevertData")),
        ("calldata", lambda value: value["contract"].update(calldata=value["contract"]["calldata"] + "00")),
        ("shapes", lambda value: value["provenance"][profile["shapesKey"]].update(capture=[])),
        ("generator version", lambda value: value["provenance"].update(generatorVersion="core-arrays-v1")),
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
    with tempfile.TemporaryDirectory(prefix="closure-corpus-") as name:
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
            plan_key = json.dumps(case[profile["planKey"]], sort_keys=True)
            if plan_key not in groups:
                seeds.append(int(entry["generation"]["seed"]))
                samples.append(case)
            group = groups.setdefault(plan_key, {"inputs": set(), "source": case["source"], "results": set()})
            require(group["source"] == case["source"], "identical closure plan emitted input-dependent source")
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
            require(group["inputs"] == set(BOUNDARIES), "closure plan lacks a completed boundary input")
            require(len(group["results"]) > 1, "fixed closure plan had one outcome for every boundary input")
        require(seeds == selection(tool, fuel, max(seeds), profile), "the corpus is not every covering seed in order")
        shrinks = sum(checked_shrinks(case, tool, directory, fuel, profile) for case in samples[:2])
        checks = policy_checks(manifest, samples[0], tool, directory, fuel, profile)
    return {"status": "passed", "profile": profile["profile"], "cases": len(entries), "plans": len(groups),
            "seeds": seeds, "outcomes": dict(sorted(outcomes.items())),
            "completedInputs": [str(value) for value in sorted(inputs)],
            "coverage": {"classification": "specified-by-the-plan-and-its-boundary-runs-not-measured",
                         **{dimension: sorted(values) for dimension, values in found.items()}},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main(profile=CAPTURES):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path, default=ROOT / profile["manifest"])
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel, profile),
                     sort_keys=True))


if __name__ == "__main__":
    main()
