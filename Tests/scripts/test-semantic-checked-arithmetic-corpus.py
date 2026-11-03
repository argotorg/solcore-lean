#!/usr/bin/env python3
"""Check the fixed checked arithmetic corpus using fresh native Core executions.

The corpus takes, from seed 1 upwards at the default budget, every generated
plan that covers a missing shape value, each at the eight primitive boundary
inputs; every value but the per-type outcomes is required. This test rebuilds
that selection, admits every plan with its own walk over the types, inputs,
helpers, groups and steps, recomputes every shape and the shrink measure from
the plan and its own interpreter, which computes each operation on Python
integers with a range check or a wrap, re-emits the source and compares it
exactly, evaluates every case's plan against the recorded Core outcome, and
replays, observes and shrinks natively. It neither compiles Rust nor executes
an EVM. `test-semantic-shift-corpus.py` runs the same walk for the shift corpus.
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


pure = load("integer_corpus_pure", "Tests/scripts/test-semantic-corpus.py")
m2 = load("integer_corpus_adapter", "scripts/semantic-differential.py")
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
TEST_CONSTANTS = (0, 1, 2, 7, 255, 256, 2**255)
TEST_MASKS = (1, 3, 7)
AMOUNT_LITERALS = (0, 1, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257, 300)
AMOUNT_OFFSETS = (0, 1, 3, 7, 8, 31, 64, 127, 128, 254, 255, 256, 300)
PANIC = "4e487b71"
DIRTY = "6cc54a63"

ARITHMETIC = {"profile": "runtime-checked-arithmetic", "schema": m2.CHECKED_ARITHMETIC_CASE_SCHEMA,
              "planSchema": "solcore-lean.checked-arithmetic-plan.v1", "planKey": "checkedArithmeticPlan",
              "shapesKey": "checkedArithmeticShapes", "requirements": "checkedArithmeticRequirements",
              "command": "checked-arithmetic-generate", "origin": "checked-arithmetic-generated",
              "contract": "SynthesizedCheckedArithmetic", "shapes": m2.CHECKED_ARITHMETIC_SHAPES,
              "manifest": "scripts/semantic-checked-arithmetic-corpus.json", "shifts": False}
SHIFTS = {"profile": "runtime-shifts", "schema": m2.SHIFT_CASE_SCHEMA, "planSchema": "solcore-lean.shift-plan.v1",
          "planKey": "shiftPlan", "shapesKey": "shiftShapes", "requirements": "shiftRequirements",
          "command": "shift-generate", "origin": "shift-generated", "contract": "SynthesizedShifts",
          "shapes": m2.SHIFT_SHAPES, "manifest": "scripts/semantic-shift-corpus.json", "shifts": True}


def required(profile):
    """Every value, but the checked arithmetic profile's per-type outcomes are recorded only."""
    return {key: (list(values) if key != "typeOutcomes" else []) for key, values in profile["shapes"].items()}


class Type:
    """An integer type, or a Word as `uint256` written as itself."""

    def __init__(self, name):
        self.name = name
        require(name == "word" or name in m2.INTEGER_TYPES, "unknown integer type")
        self.word = name == "word"
        self.signed = name.startswith("int")
        self.bits = 256 if self.word else int(name.lstrip("uint"))
        self.bytes = self.bits // 8
        self.min = -(1 << (self.bits - 1)) if self.signed else 0
        self.max = (1 << (self.bits - 1)) - 1 if self.signed else (1 << self.bits) - 1

    def wrap(self, value):
        return (value - self.min) % (1 << self.bits) + self.min

    def value(self, rep):
        return rep - M if self.signed and rep >= 1 << 255 else rep

    def convert(self, word):
        word %= M
        if self.bits == 256:
            return word
        return self.wrap(word % (1 << self.bits)) % M if self.signed else word % (1 << self.bits)

    def literals(self):
        return ([self.min, self.min + 1, -1] if self.signed else []) + [0, 1, 2, 3, 7, 1 << (self.bits // 2),
                                                                      self.max - 1, self.max]

    def literal_class(self, index):
        names = (["min", "min1", "minus1"] if self.signed else []) + ["zero", "one", "small", "small", "small", "half",
                                                                       "max1", "max"]
        return names[index]

    def offsets(self):
        return (0, 1, 3, (1 << (self.bits - 1)) - 1, 1 << (self.bits - 1), (1 << self.bits) - 1)


UINT256 = Type("uint256")


def operand(value):
    require(isinstance(value, dict) and len(value) == 1 and next(iter(value)) in ("input", "var", "literal")
            and type(next(iter(value.values()))) is int and next(iter(value.values())) >= 0, "invalid integer operand")
    return value


def check_plan(plan, profile):
    """The profile's admission: types, inputs, amounts, helpers, groups and steps in scope."""
    require(isinstance(plan, dict) and plan.get("schema") == profile["planSchema"]
            and set(plan) == {"schema", "value", "abi", "raw", "inputs", "amounts", "helpers", "groups"},
            "unexpected integer plan schema")
    shifts = profile["shifts"]
    kind = Type(plan["value"])
    require(shifts or not kind.word, "a checked arithmetic plan has an integer type")
    require(type(plan["abi"]) is bool and type(plan["raw"]) is bool, "invalid parameter or result form")
    require(not shifts or (not plan["abi"] and not plan["raw"]), "a shift plan takes and returns uint256")
    require(not plan["raw"] or kind.bits < 256, "only a narrow type returns its own type")
    inputs = plan["inputs"]
    require(isinstance(inputs, list) and 1 <= len(inputs) <= 3 and inputs[0] == "0", "one to three inputs, the first 0")
    for value in inputs:
        require(isinstance(value, str) and canonical_word(value) in kind.offsets(), "input offset outside the table")
    amounts = plan["amounts"]
    require(isinstance(amounts, list) and (1 <= len(amounts) <= 3 if shifts else not amounts), "amount count outside the profile")
    for amount in amounts:
        require(isinstance(amount, dict) and set(amount) == {"type", "offset"}, "invalid amount")
        amount_type = Type(amount["type"])
        require(not amount_type.signed and amount["offset"] in AMOUNT_OFFSETS, "amount type or offset outside the profile")
    helpers = plan["helpers"]
    require(isinstance(helpers, list) and len(helpers) <= (0 if shifts else 2), "helper count outside the profile")
    for helper in helpers:
        require(isinstance(helper, dict) and set(helper) == {"op", "unchecked"} and helper["op"] in OPS
                and type(helper["unchecked"]) is bool, "invalid helper")
    groups = plan["groups"]
    require(isinstance(groups, list) and groups, "a plan has groups")
    for group in groups:
        require(isinstance(group, dict) and set(group) == {"unchecked", "steps"} and type(group["unchecked"]) is bool
                and isinstance(group["steps"], list) and group["steps"], "groups are nonempty contexts")
    require(all(first["unchecked"] != second["unchecked"] for first, second in zip(groups, groups[1:])),
            "group contexts alternate")
    require(sum(group["unchecked"] for group in groups) <= 3, "at most three blocks")
    steps = [(group["unchecked"], step) for group in groups for step in group["steps"]]
    require(1 <= len(steps) <= 10, "one to ten steps")
    variables = defaults = 0
    called = set()
    literal_count = len(kind.literals())

    def in_scope(value):
        value = operand(value)
        key, index = next(iter(value.items()))
        return index < {"input": len(inputs), "var": variables, "literal": literal_count}[key]

    for unchecked, step in steps:
        require(isinstance(step, dict) and len(step) == 1, "a step is an assignment, a defaulted result or a shift")
        tag, body = next(iter(step.items()))
        if tag == "assign":
            require(not shifts, "a shift plan has only shifts")
            form = body.get("form")
            if form in ("binary", "compound", "call", "apply"):
                require(in_scope(body["left"]) and in_scope(body["right"]), "operand out of scope")
            if form in ("binary", "compound"):
                require(set(body) == {"form", "op", "left", "right"} and body["op"] in OPS, "invalid operation")
            elif form == "neg":
                require(set(body) == {"form", "operand"} and in_scope(body["operand"])
                        and "literal" not in body["operand"], "a negation of an input or a variable")
            elif form == "call":
                require(set(body) == {"form", "helper", "left", "right"} and type(body["helper"]) is int
                        and 0 <= body["helper"] < len(helpers), "a call of a helper")
                called.add(body["helper"])
            elif form == "apply":
                require(set(body) == {"form", "op", "unchecked", "left", "right"} and body["op"] in OPS
                        and type(body["unchecked"]) is bool, "invalid application")
                require(not (unchecked and body["unchecked"]), "no lambda with its own block inside a block")
            else:
                raise ValueError("unknown integer form")
            variables += 1
        elif tag == "default":
            require(not shifts, "a shift plan has only shifts")
            require(set(body) == {"initial", "test", "chosen", "op", "operand"} and body["op"] in OPS
                    and all(type(body[key]) is int and 0 <= body[key] < 8 for key in ("initial", "chosen", "operand")),
                    "invalid defaulted result")
            test = body["test"]
            if test.get("test") == "bits":
                require(set(test) == {"test", "mask", "value"} and test["mask"] in TEST_MASKS
                        and type(test["value"]) is int and 0 <= test["value"] <= test["mask"], "invalid bit test")
            else:
                require(set(test) == {"test", "constant"} and test["test"] in ("lt", "gt", "eq")
                        and canonical_word(test["constant"]) in TEST_CONSTANTS, "invalid test")
            defaults += 1
        elif tag == "shift":
            require(shifts, "a checked arithmetic plan has no shifts")
            require(set(body) == {"direction", "compound", "value", "amount"} and body["direction"] in ("left", "right")
                    and type(body["compound"]) is bool and in_scope(body["value"]), "invalid shift")
            amount = body["amount"]
            require(isinstance(amount, dict) and len(amount) == 1, "invalid shift amount")
            key, index = next(iter(amount.items()))
            require(type(index) is int and 0 <= index < (len(amounts) if key == "input" else len(AMOUNT_LITERALS))
                    and key in ("input", "literal"), "shift amount out of scope")
            variables += 1
        else:
            raise ValueError("unknown integer step")
    require(variables >= 1 and defaults <= 2, "a plan makes a variable and at most two defaulted results")
    require(called == set(range(len(helpers))), "every helper is called")
    return plan


def plan_steps(plan):
    return [(group["unchecked"], step) for group in plan["groups"] for step in group["steps"]]


def tdiv(left, right):
    quotient = abs(left) // abs(right)
    return quotient if (left < 0) == (right < 0) else -quotient


def operate(kind, unchecked, op, left, right):
    """A representation Word and whether it wrapped, or a panic code."""
    if op in ("div", "mod") and right == 0:
        return 0x12
    exact = {"add": left + right, "sub": left - right, "mul": left * right,
             "div": tdiv(left, right) if right else 0, "mod": left - right * tdiv(left, right) if right else 0}[op]
    if kind.min <= exact <= kind.max:
        return exact % M, False
    return (kind.wrap(exact) % M, True) if unchecked else 0x11


def shift(kind, direction, value, amount):
    if direction == "left":
        return 0 if amount >= kind.bits else kind.wrap(value << amount)
    if amount >= 256:
        return -1 if value < 0 else 0
    return value >> amount


def test_holds(test, word):
    if test["test"] == "bits":
        return word & test["mask"] == test["value"]
    constant = int(test["constant"])
    return {"lt": word < constant, "gt": word > constant, "eq": word == constant}[test["test"]]


def interpret(plan, word):
    """The plan's outcome at an input Word, with its events: ('word', w), ('panic', code) or ('dirty',)."""
    kind = Type(plan["value"])
    word %= M
    if plan["abi"] and kind.convert(word) != word:
        return ("dirty",), []
    inputs = [kind.convert(word + int(offset)) for offset in plan["inputs"]]
    variables, results, events = [], [], []

    def rep(value):
        key, index = next(iter(value.items()))
        return {"input": inputs, "var": variables}[key][index] if key != "literal" else kind.literals()[index] % M

    def val(value):
        return kind.value(rep(value))

    for unchecked, step in plan_steps(plan):
        tag, body = next(iter(step.items()))
        if tag == "assign":
            form = body["form"]
            if form == "neg":
                name, context, left, right = "neg", unchecked, 0, val(body["operand"])
                op = "sub"
            elif form == "call":
                helper = plan["helpers"][body["helper"]]
                name, context, op = helper["op"], helper["unchecked"], helper["op"]
                left, right = val(body["left"]), val(body["right"])
            else:
                name, op = body["op"], body["op"]
                context = body["unchecked"] if form == "apply" else unchecked
                left, right = val(body["left"]), val(body["right"])
            result = operate(kind, context, op, left, right)
            if isinstance(result, int):
                return ("panic", result), events + [("panic", name, context, True, result)]
            variables.append(result[0])
            results.append(result[0])
            events.append(("operation", name, context, True, result[1]))
        elif tag == "default":
            literals = UINT256.literals()
            chosen = literals[body["chosen"]] if test_holds(body["test"], word) else literals[body["initial"]]
            result = operate(UINT256, unchecked, body["op"], chosen, literals[body["operand"]])
            if isinstance(result, int):
                return ("panic", result), events + [("panic", body["op"], unchecked, False, result)]
            results.append(result[0])
            events.append(("operation", body["op"], unchecked, False, result[1]))
        else:
            amount = body["amount"]
            if "input" in amount:
                spec = plan["amounts"][amount["input"]]
                distance = Type(spec["type"]).convert(word + spec["offset"])
            else:
                distance = AMOUNT_LITERALS[amount["literal"]]
            value = shift(kind, body["direction"], val(body["value"]), distance)
            variables.append(value % M)
            results.append(value % M)
            name = "shl" if body["direction"] == "left" else "sar" if kind.signed else "shr"
            events.append(("shift", name, distance, value))
    acc = 0
    for value in results:
        acc = ((acc * FOLD) % M) ^ value
    return ("word", kind.convert(acc) if plan["raw"] else acc), events


def outcome_text(result):
    """A returned Word in decimal, a panic or the ABI revert as its revert data."""
    if result[0] == "word":
        return str(result[1])
    if result[0] == "panic":
        return "0x" + PANIC + f"{result[1]:064x}"
    return "0x" + DIRTY


def observed_text(observation):
    require(isinstance(observation, dict) and observation.get("stage") == "execution", "missing Core outcome")
    if observation.get("status") == "returned":
        require(set(observation) == {"stage", "status", "word"}, "a return has one Word")
        return str(canonical_word(observation["word"]))
    require(observation.get("status") == "reverted" and set(observation) == {"stage", "status", "output"},
            "an integer case returns a Word or reverts")
    output = observation["output"]
    require(output in ("0x" + DIRTY,) or re.fullmatch("0x" + PANIC + "0{62}1[12]", output), "unexpected revert data")
    return output


def sorted_unique(values):
    return sorted(set(values))


def range_name(bits, amount):
    if amount == 0:
        return "zero"
    if amount + 1 < bits:
        return "inside"
    if amount + 1 == bits:
        return "last"
    if amount == bits:
        return "width"
    return "beyond" if amount < 256 else "huge"


def operand_shape(value):
    key, index = next(iter(value.items()))
    return {"input": "input" if index == 0 else "offset", "var": "variable", "literal": "literal"}[key]


def shapes(plan, profile):
    kind = Type(plan["value"])
    steps = plan_steps(plan)
    runs = [interpret(plan, word) for word in BOUNDARIES]
    events = [event for _, run_events in runs for event in run_events]
    if profile["shifts"]:
        shifts = [(unchecked, body["shift"]) for unchecked, body in steps]
        reached = [(event[2], event[3]) for event in events if event[0] == "shift"]
        return {"values": [kind.name],
                "amounts": sorted_unique(plan["amounts"][s["amount"]["input"]]["type"] if "input" in s["amount"]
                                         else "literal" for _, s in shifts),
                "operators": sorted_unique("shl" if s["direction"] == "left" else "sar" if kind.signed else "shr"
                                           for _, s in shifts),
                "forms": sorted_unique("compound" if s["compound"] else "inline" for _, s in shifts),
                "contexts": sorted_unique("unchecked" if unchecked else "checked" for unchecked, _ in shifts),
                "operands": sorted_unique(operand_shape(s["value"]) for _, s in shifts),
                "ranges": sorted_unique(range_name(kind.bits, amount) for amount, _ in reached),
                "results": sorted_unique("zero" if result == 0 else "minus-one" for amount, result in reached
                                         if amount >= kind.bits and result in (0, -1)),
                "typeRanges": sorted_unique(kind.name + ":width" for amount, _ in reached if amount >= kind.bits)}
    forms = [(unchecked, step["assign"]) for unchecked, step in steps if "assign" in step]
    operands = [value for _, form in forms for value in
                ((form["operand"],) if form["form"] == "neg" else (form["left"], form["right"]))]

    def op_name(form):
        return "neg" if form["form"] == "neg" else plan["helpers"][form["helper"]]["op"] if form["form"] == "call" \
            else form["op"]

    def context(unchecked, step):
        if "assign" not in step:
            return unchecked
        form = step["assign"]
        if form["form"] == "call":
            return plan["helpers"][form["helper"]]["unchecked"]
        return form["unchecked"] if form["form"] == "apply" else unchecked

    def scope(unchecked, step):
        if "assign" in step and step["assign"]["form"] == "call":
            if plan["helpers"][step["assign"]["helper"]]["unchecked"]:
                return ["unchecked-helper"]
            return ["call-in-block"] if unchecked else []
        if "assign" in step and step["assign"]["form"] == "apply":
            return ["unchecked-lambda"] if step["assign"]["unchecked"] else ["apply-in-block"] if unchecked else []
        return ["block"] if unchecked else []

    def panic_name(event):
        name, unchecked, code = event[1], event[2], event[4]
        if name == "div" and code == 0x12:
            return "unchecked-div-zero" if unchecked else "div-zero"
        if name == "mod":
            return "unchecked-mod-zero" if unchecked else "mod-zero"
        return "div-overflow" if name == "div" else name

    outcomes = {"word": "returned", "dirty": "dirty"}
    return {"types": [kind.name],
            "operators": sorted_unique([op_name(form) for _, form in forms] +
                                       [step["default"]["op"] for _, step in steps if "default" in step]),
            "forms": sorted_unique({"binary": "inline", "neg": "inline"}.get(step["assign"]["form"], step["assign"]["form"])
                                   if "assign" in step else "default" for _, step in steps),
            "contexts": sorted_unique("unchecked" if context(unchecked, step) else "checked" for unchecked, step in steps),
            "scopes": sorted_unique(value for unchecked, step in steps for value in scope(unchecked, step)),
            "operands": sorted_unique(operand_shape(value) for value in operands),
            "literals": sorted_unique(kind.literal_class(value["literal"]) for value in operands if "literal" in value),
            "parameters": ["abi" if plan["abi"] else "word"],
            "returns": ["raw" if plan["raw"] else "word"],
            "outcomes": sorted_unique(outcomes.get(result[0]) or ("panic-0x11" if result[1] == 0x11 else "panic-0x12")
                                      for result, _ in runs),
            "panics": sorted_unique(panic_name(event) for event in events if event[0] == "panic"),
            "wraps": sorted_unique(event[1] for event in events if event[0] == "operation" and event[2] and event[4]),
            "typeOutcomes": sorted_unique(
                [kind.name + (":0x11" if event[4] == 0x11 else ":0x12") for event in events
                 if event[0] == "panic" and event[3]] +
                [kind.name + ":wrap" for event in events if event[0] == "operation" and event[3] and event[4]] +
                [kind.name + ":dirty" for result, _ in runs if result[0] == "dirty"])}


def plan_size(plan):
    """The shrink measure: every step's weight, one more in a block, each later input, amount and helper."""
    kind = Type(plan["value"])

    def op_weight(op):
        return 0 if op == "add" else 1

    def operand_weight(value):
        key, index = next(iter(value.items()))
        if key == "input":
            return 0 if index == 0 else 1
        if key == "var":
            return 1
        return 1 if kind.literals()[index] == 0 else 2

    def weight(step):
        tag, body = next(iter(step.items()))
        if tag == "default":
            return 5 + op_weight(body["op"])
        if tag == "shift":
            amount = body["amount"]
            return 3 + body["compound"] + operand_weight(body["value"]) + (0 if amount == {"literal": 0} else 1)
        form = body["form"]
        if form == "neg":
            return 3 + operand_weight(body["operand"])
        operands = operand_weight(body["left"]) + operand_weight(body["right"])
        if form == "binary":
            return 3 + op_weight(body["op"]) + operands
        if form == "compound":
            return 4 + op_weight(body["op"]) + operands
        if form == "call":
            return 6 + operands
        return 6 + op_weight(body["op"]) + body["unchecked"] + operands

    return (sum(weight(step) + unchecked for unchecked, step in plan_steps(plan)) + len(plan["inputs"]) - 1
            + len(plan["amounts"]) + sum(1 + op_weight(helper["op"]) + helper["unchecked"] for helper in plan["helpers"])
            + plan["abi"] + plan["raw"])


def indent(count, lines):
    return [" " * count + line for line in lines]


def emit(plan, profile):
    """The source exactly as the Lean emitter writes it."""
    kind = Type(plan["value"])
    name = kind.name
    literals = kind.literals()

    def convert(word):
        if kind.bits == 256:
            return word
        return f"sc_signextend({kind.bytes - 1}, {word})" if kind.signed else f"({word} & {hex((1 << kind.bits) - 1)})"

    def offset_text(offset):
        return "sc_x" if offset == 0 else f"(sc_x + {offset})"

    def declaration(target, type_name, offset):
        if type_name == "word":
            return f"let {target}: word = {offset_text(offset)};"
        other = Type(type_name)
        text = offset_text(offset)
        if other.bits < 256:
            text = (f"sc_signextend({other.bytes - 1}, {text})" if other.signed
                    else f"({text} & {hex((1 << other.bits) - 1)})")
        return f"let {target}: {type_name} = Typedef.abs({text});"

    def literal(value):
        return f"({value})" if value < 0 else str(value)

    def operand_text(value):
        key, index = next(iter(value.items()))
        return {"input": f"sc_a{index}", "var": f"sc_v{index}"}.get(key) or literal(literals[index])

    def amount_text(value):
        key, index = next(iter(value.items()))
        return f"sc_k{index}" if key == "input" else str(AMOUNT_LITERALS[index])

    def test_text(test):
        if test["test"] == "bits":
            return f"((sc_x & {test['mask']}) == {test['value']})"
        return f"(sc_x {({'lt': '<', 'gt': '>', 'eq': '=='})[test['test']]} {test['constant']})"

    def step_lines(variables, defaults, declared, step):
        tag, body = next(iter(step.items()))
        if tag == "default":
            result = f"(sc_d{defaults} {SYMBOLS[body['op']]} {UINT256.literals()[body['operand']]})"
            return [f"sc_e{defaults} = {result};" if declared else f"let sc_e{defaults} = {result};"]
        variable = f"sc_v{variables}"
        target = f"{variable} = " if declared else f"let {variable}: {name} = "
        if tag == "shift":
            symbol = "<<" if body["direction"] == "left" else ">>"
            if body["compound"]:
                return [target + operand_text(body["value"]) + ";", f"{variable} {symbol}= {amount_text(body['amount'])};"]
            return [target + f"({operand_text(body['value'])} {symbol} {amount_text(body['amount'])});"]
        form = body["form"]
        if form == "binary":
            return [target + f"({operand_text(body['left'])} {SYMBOLS[body['op']]} {operand_text(body['right'])});"]
        if form == "neg":
            return [target + f"(-{operand_text(body['operand'])});"]
        if form == "compound":
            return [target + operand_text(body["left"]) + ";",
                    f"{variable} {SYMBOLS[body['op']]}= {operand_text(body['right'])};"]
        if form == "call":
            return [target + f"sc_h{body['helper']}({operand_text(body['left'])}, {operand_text(body['right'])});"]
        result = f"return (sc_l {SYMBOLS[body['op']]} {operand_text(body['right'])});"
        return ([target + f"sc_apply(lam (sc_l: {name}) -> {name} {{"] +
                indent(4, ["unchecked {", "    " + result, "}"] if body["unchecked"] else [result]) +
                [f"}}, {operand_text(body['left'])});"])

    group_lines, words, variables, defaults = [], [], 0, 0
    for group in plan["groups"]:
        before, inside = [], []
        for step in group["steps"]:
            if "default" in step:
                made = step["default"]
                before += [f"let sc_d{defaults} = {UINT256.literals()[made['initial']]};",
                           f"if {test_text(made['test'])} {{", f"    sc_d{defaults} = {UINT256.literals()[made['chosen']]};", "}"]
                if group["unchecked"]:
                    before.append(f"let sc_e{defaults} = 0;")
                inside += step_lines(variables, defaults, group["unchecked"], step)
                words.append(f"Typedef.rep(sc_e{defaults})")
                defaults += 1
            else:
                if group["unchecked"]:
                    before.append(f"let sc_v{variables}: {name} = 0;")
                inside += step_lines(variables, defaults, group["unchecked"], step)
                words.append(f"sc_v{variables}" if kind.word else f"Typedef.rep(sc_v{variables})")
                variables += 1
        group_lines += before + (["unchecked {"] + indent(4, inside) + ["}"] if group["unchecked"] else inside)
    steps = plan_steps(plan)
    unchecked = (any(group["unchecked"] for group in plan["groups"]) or any(helper["unchecked"] for helper in plan["helpers"])
                 or any("assign" in step and step["assign"]["form"] == "apply" and step["assign"]["unchecked"]
                        for _, step in steps))
    applies = any("assign" in step and step["assign"]["form"] == "apply" for _, step in steps)
    imports = ["import * from std;", "import * from std.unsigned;"] + (["import * from std.signed;"] if kind.signed else [])
    if unchecked:
        imports.append("import * from std.unchecked.signed;" if kind.signed else "import * from std.unchecked.unsigned;")
    imports.append("import * from std.dispatch;")
    if kind.signed and kind.bits < 256:
        imports.append("import { signextend as sc_signextend } from std.opcodes;")
    helpers = []
    for index, helper in enumerate(plan["helpers"]):
        result = f"return (sc_p {SYMBOLS[helper['op']]} sc_q);"
        helpers += ([f"function sc_h{index}(sc_p: {name}, sc_q: {name}) returns ({name}) {{"] +
                    indent(4, ["unchecked {", "    " + result, "}"] if helper["unchecked"] else [result]) + ["}", ""])
    if applies:
        helpers += [f"function sc_apply(sc_f: function ({name}) returns ({name}), sc_v: {name}) returns ({name}) {{",
                    "    return sc_f(sc_v);", "}", ""]
    inputs = [f"let sc_a0: {name} = input;" if plan["abi"] and index == 0 else declaration(f"sc_a{index}", name, int(offset))
              for index, offset in enumerate(plan["inputs"])]
    amounts = [declaration(f"sc_k{index}", amount["type"], amount["offset"]) for index, amount in enumerate(plan["amounts"])]
    body = (["let sc_x: word = Typedef.rep(input);"] + inputs + amounts + ["let sc_acc: word = 0;"] + group_lines +
            [f"sc_acc = ((sc_acc * 1099511628211) ^ {word});" for word in words] +
            ["return Typedef.abs(sc_acc);" if plan["raw"] else "return uint256(sc_acc);"])
    parameter = name if plan["abi"] else "uint256"
    result = name if plan["raw"] else "uint256"
    contract = profile["contract"]
    lines = (imports + [""] + helpers + [f"contract {contract} {{",
             f"    function run(input: {parameter}) public returns ({result}) {{"] + indent(8, body) + ["    }", "}"])
    return "\n".join(lines) + "\n"


def nodes(value):
    """An upper bound on the reference's Wire nodes: every tagged object, its types included."""
    if isinstance(value, dict):
        return ("tag" in value) + sum(nodes(child) for child in value.values())
    if isinstance(value, list):
        return sum(nodes(child) for child in value)
    return 0


def signature(plan):
    return f"run({plan['value']})" if plan["abi"] else "run(uint256)"


def check_case(case, fuel, profile):
    require(isinstance(case, dict) and case.get("schema") == profile["schema"], "unexpected integer case schema")
    plan = check_plan(case[profile["planKey"]], profile)
    number = canonical_word(case["input"])
    program = case["program"]
    payload = {"tag": "product", "left": "word", "right": {"tag": "product", "left": "word", "right": "word"}}
    require(program.get("schema") == "solcore-semantic-core" and program.get("dataDefinitions") == []
            and program.get("resultType") == {"tag": "sum", "left": "word", "right": payload},
            "the integer reference is a closed program returning a Word or revert data")
    require(nodes(program["body"]) <= CASE_LIMIT, "reference exceeds the case limit")
    require(1 <= case["provenance"]["referenceNodes"] <= CASE_LIMIT, "recorded reference size exceeds the case limit")
    name = profile["contract"]
    selector = m2.RUN_SELECTORS[plan["value"] if plan["abi"] else "uint256"]
    require(case["contract"] == {"name": name, "method": "run", "signature": signature(plan),
            "deployPath": [name + "Deploy"], "runtimePath": [name + "Deploy", name],
            "calldata": "0x" + selector + f"{number:064x}", "constructorCalldata": "0x"},
            "unexpected integer wrapper")
    require(case["source"] == emit(plan, profile), "the source differs from the plan's emission")
    require(case["provenance"][profile["shapesKey"]] == shapes(plan, profile), "recorded shapes differ from the plan")
    require(observed_text(case["directCore"]) == outcome_text(interpret(plan, number)[0]),
            "the recorded Core outcome differs from the plan's interpreter")
    if profile["shifts"]:
        require(case["directCore"]["status"] == "returned", "a shift case never reverts")
    return plan


def check_manifest(manifest, profile):
    fields = {"schema", "profile", "coverageKind", "requiredFeatures", "requiredWordLiterals", "requiredInputs",
              profile["requirements"], "cases"} | set(VERSIONS)
    require(isinstance(manifest, dict) and set(manifest) == fields
            and manifest["schema"] == "solcore-lean.semantic-corpus-manifest.v1"
            and manifest["profile"] == profile["profile"], "unexpected integer manifest schema/profile/fields")
    require(manifest["coverageKind"] == "core-ast-features", "integer coverage scope changed")
    for version in VERSIONS:
        require(isinstance(manifest[version], str) and manifest[version], f"missing {version}")
    require(manifest["requiredFeatures"] == [] and manifest["requiredWordLiterals"] == [],
            "the integer corpus requires shapes, not step features or literals")
    require([canonical_word(value) for value in manifest["requiredInputs"]] == list(BOUNDARIES),
            "the integer corpus must require all eight boundary inputs")
    require(manifest[profile["requirements"]] == required(profile), "the integer corpus must require its shape values")
    entries, identifiers = manifest["cases"], set()
    require(isinstance(entries, list) and entries, "the integer corpus must contain cases")
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {"id", "generation", "input", "expectedFeatures"},
                "an integer corpus entry is a generation recipe with its input")
        identifier = entry["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_-]{1,80}", identifier)
                and identifier not in identifiers, "corpus IDs must be unique bounded identifiers")
        identifiers.add(identifier)
        require(canonical_word(entry["input"]) in BOUNDARIES, "generated input must be a boundary value")
        require(entry["expectedFeatures"] == [], "integer entries expect no step features")
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
    whose plan covers a missing value, until nothing is missing."""
    missing = {dimension: set(values) for dimension, values in required(profile).items()}
    chosen = []
    for seed in range(1, last + 1):
        if not any(missing.values()):
            break
        plan = generated_plan(tool, seed, fuel, profile)
        if plan is None:
            continue
        found = shapes(plan, profile)
        if any(missing[dimension] & set(found[dimension]) for dimension in missing):
            chosen.append(seed)
            for dimension in missing:
                missing[dimension] -= set(found[dimension])
    require(not any(missing.values()), "seeds up to the last chosen one leave a requirement missing")
    return chosen


def materialize(entry, tool, fuel, profile):
    recipe = entry["generation"]
    corpus = run(tool, profile["command"], recipe["seed"], str(recipe["maxProgramNodes"]), "8", "1", str(fuel))
    require(corpus.get("schema") == "solcore-lean.semantic-corpus.v1" and corpus.get("status") == "complete"
            and corpus.get("requested") == 8 and corpus.get("attempted") == 1
            and corpus.get("excluded") == [] and len(corpus.get("cases", [])) == 8,
            "fixed integer seed did not emit eight cases in one attempt")
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
    require(isinstance(candidates, list) and candidates, "fixed integer case has no shrink candidate")
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
    binary = {"assign": {"form": "binary", "op": "add", "left": {"input": 0}, "right": {"input": 0}}}
    shifted = {"shift": {"direction": "left", "compound": False, "value": {"input": 0}, "amount": {"literal": 1}}}
    step = shifted if profile["shifts"] else binary
    other = binary if profile["shifts"] else shifted
    broken_plans = [
        ("no step", {**plan, "groups": []}),
        ("an empty group", {**plan, "groups": [{"unchecked": False, "steps": []}]}),
        ("eleven steps", {**plan, "groups": [{"unchecked": False, "steps": [step] * 11}]}),
        ("adjacent blocks", {**plan, "groups": [{"unchecked": True, "steps": [step]}, {"unchecked": True, "steps": [step]}]}),
        ("four blocks", {**plan, "groups": [{"unchecked": index % 2 == 0, "steps": [step]} for index in range(7)]}),
        ("the other profile's step", {**plan, "groups": [{"unchecked": False, "steps": [other]}]}),
        ("a first input offset", {**plan, "inputs": ["1"]}),
        ("four inputs", {**plan, "inputs": ["0", "1", "3", "1"]}),
        ("an offset outside the table", {**plan, "inputs": ["0", "2"]}),
        ("a variable before it exists", {**plan, "groups": [{"unchecked": False, "steps": [
            {"shift": {**shifted["shift"], "value": {"var": 0}}} if profile["shifts"] else
            {"assign": {**binary["assign"], "left": {"var": 0}}}]}]}),
        ("a literal past the table", {**plan, "groups": [{"unchecked": False, "steps": [
            {"shift": {**shifted["shift"], "value": {"literal": 11}}} if profile["shifts"] else
            {"assign": {**binary["assign"], "right": {"literal": 11}}}]}]}),
        ("an unknown type", {**plan, "value": "uint7"}),
        ("the other plan schema", {**plan, "schema": (ARITHMETIC if profile["shifts"] else SHIFTS)["planSchema"]})]
    if profile["shifts"]:
        broken_plans += [
            ("a helper", {**plan, "helpers": [{"op": "add", "unchecked": False}]}),
            ("run(T)", {**plan, "abi": True}),
            ("no amount", {**plan, "amounts": []}),
            ("a signed amount", {**plan, "amounts": [{"type": "int8", "offset": 0}]}),
            ("an amount offset outside the table", {**plan, "amounts": [{"type": "word", "offset": 2}]}),
            ("an amount past the inputs", {**plan, "groups": [{"unchecked": False, "steps": [
                {"shift": {**shifted["shift"], "amount": {"input": 5}}}]}]})]
    else:
        broken_plans += [
            ("a Word type", {**plan, "value": "word"}),
            ("an amount", {**plan, "amounts": [{"type": "word", "offset": 0}]}),
            ("three helpers", {**plan, "helpers": [{"op": "add", "unchecked": False}] * 3}),
            ("a helper nothing calls", {**plan, "helpers": [{"op": "add", "unchecked": False}],
                                        "groups": [{"unchecked": False, "steps": [binary]}]}),
            ("a negated literal", {**plan, "groups": [{"unchecked": False, "steps": [
                {"assign": {"form": "neg", "operand": {"literal": 0}}}]}]}),
            ("a lambda block inside a block", {**plan, "groups": [{"unchecked": True, "steps": [
                {"assign": {"form": "apply", "op": "add", "unchecked": True, "left": {"input": 0}, "right": {"input": 0}}}]}]}),
            ("a 256-bit T result", {**plan, "value": "uint256", "raw": True}),
            ("three defaulted results", {**plan, "groups": [{"unchecked": False, "steps": [binary] + [
                {"default": {"initial": 0, "test": {"test": "eq", "constant": "0"}, "chosen": 1, "op": "add", "operand": 1}}] * 3}]}),
            ("a test constant outside the table", {**plan, "groups": [{"unchecked": False, "steps": [binary,
                {"default": {"initial": 0, "test": {"test": "eq", "constant": "3"}, "chosen": 1, "op": "add", "operand": 1}}]}]})]
    for label, broken in broken_plans:
        rejects(lambda: check_plan(broken, profile), label)
    path = directory / "negative.json"
    key = profile["planKey"]
    for label, change in (
        ("source", lambda value: value.update(source=value["source"] + "\n")),
        ("a removed group", lambda value: value[key]["groups"].pop(0) if len(value[key]["groups"]) > 1 else
            value[key]["groups"][0]["steps"].append(step)),
        ("original Core", lambda value: value["program"].update(body={"tag": "word", "value": "0x0"})),
        ("input", lambda value: value.update(input="1" if value["input"] != "1" else "2")),
        ("wrapper", lambda value: value["contract"].update(name="SynthesizedRevertData")),
        ("shapes", lambda value: value["provenance"][profile["shapesKey"]].update(contexts=[])),
        ("generator version", lambda value: value["provenance"].update(generatorVersion="core-revert-data-v1")),
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
                 (profile["command"], "1", "255", "8", "1", str(fuel)),
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
    with tempfile.TemporaryDirectory(prefix="integer-corpus-") as name:
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
            require(group["source"] == case["source"], "identical integer plan emitted input-dependent source")
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
            require(group["inputs"] == set(BOUNDARIES), "integer plan lacks a completed boundary input")
            require(len(group["results"]) > 1, "fixed integer plan had one outcome for every boundary input")
        require(seeds == selection(tool, fuel, max(seeds), profile), "the corpus is not every covering seed in order")
        shrinks = sum(checked_shrinks(case, tool, directory, fuel, profile) for case in samples[:2])
        checks = policy_checks(manifest, samples[0], tool, directory, fuel, profile)
    return {"status": "passed", "profile": profile["profile"], "cases": len(entries), "plans": len(groups),
            "seeds": seeds, "outcomes": dict(sorted(outcomes.items())),
            "completedInputs": [str(value) for value in sorted(inputs)],
            "coverage": {"classification": "specified-by-the-plan-and-its-boundary-runs-not-measured",
                         **{dimension: sorted(values) for dimension, values in found.items()}},
            "checkedShrinkCandidates": shrinks, "policyChecks": checks, "evmExecuted": False}


def main(profile=ARITHMETIC):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", "--corpus", dest="manifest", type=Path, default=ROOT / profile["manifest"])
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--fuel", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.manifest.read_text()), args.case_tool.resolve(), args.fuel, profile),
                     sort_keys=True))


if __name__ == "__main__":
    main()
