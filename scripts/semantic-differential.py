#!/usr/bin/env python3
"""Replay one checked pure case through direct Core, imported Hull and local EVM.

This is a single-case runner, not a campaign or shrinker. It starts its own
loopback-only Anvil and never connects to an existing chain. Passing means all
three fresh executions completed and returned the same ABI Word. The source
emitter remains part of the test setup, not a proved compiler pass.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import copy
import hashlib
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
import time
from types import SimpleNamespace
import urllib.error
import urllib.request

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
_bundle_spec = importlib.util.spec_from_file_location("semantic_source_bundle", ROOT / "scripts/semantic-source-bundle.py")
assert _bundle_spec and _bundle_spec.loader
bundle_transport = importlib.util.module_from_spec(_bundle_spec)
_bundle_spec.loader.exec_module(bundle_transport)
CASE_SCHEMA = "solcore-lean.semantic-case.v1"
INPUT_CASE_SCHEMA = "solcore-lean.semantic-input-case.v1"
CALL_GRAPH_CASE_SCHEMA = "solcore-lean.semantic-call-graph-case.v1"
CALL_SHAPES = ("skipped-helper", "multiple-callees", "shared-callee", "nested-call",
               "branch-call", "local-call", "diamond", "predicate-call", "primitive-operand-call")
CALL_GRAPH_VERSIONS = ("profileVersion", "functionVersion", "boundaryVersion", "callShapeVersion")
CALL_GRAPH_LOOP_CASE_SCHEMA = "solcore-lean.semantic-call-graph-loop-case.v1"
CALL_GRAPH_LOOP_VERSIONS = ("profileVersion", "functionVersion", "loopVersion", "stepFunctionVersion",
                            "aggregateVersion", "boundaryVersion", "stepBoundaryVersion", "callShapeVersion")
ASSEMBLY_LOOP_CASE_SCHEMA = "solcore-lean.semantic-assembly-loop-case.v1"
ASSEMBLY_LOOP_FORMS = ("for", "break", "continue", "leave", "pair")
ASSEMBLY_LOOP_VERSIONS = (*CALL_GRAPH_LOOP_VERSIONS, "loopProfileVersion")
AGGREGATE_CALL_GRAPH_CASE_SCHEMA = "solcore-lean.semantic-aggregate-call-graph-case.v1"
AGGREGATE_SHAPES = ("pair-component-call", "sum-payload-call", "projected-call-argument", "case-scrutinee-call",
                    "case-branch-call", "payload-call-argument", "aggregate-let", "aggregate-branch", "nested-case")
AGGREGATE_CALL_GRAPH_VERSIONS = ("profileVersion", "functionVersion", "boundaryVersion", "shapeVersion")
PRIMITIVE_CASE_SCHEMA = "solcore-lean.semantic-primitive-case.v1"
ASSEMBLY_CASE_SCHEMA = "solcore-lean.semantic-assembly-case.v1"
ASSEMBLY_FORMS = ("switch", "if", "operations")
ASSEMBLY_MEMORY_CASE_SCHEMA = "solcore-lean.semantic-assembly-memory-case.v1"
ASSEMBLY_MEMORY_HASH_LENGTHS = (0, 1, 31, 32, 33, 64)
ENUM_CASE_SCHEMA = "solcore-lean.semantic-enum-case.v1"
ENUM_VERSIONS = ("profileVersion", "boundaryVersion")
# The specified shape values of the enum profile, from the plan, never measured.
ENUM_SHAPES = {
    "constructors": ("2", "3", "4"),
    "fields": ("count:0", "count:1", "count:2", "type:applied", "type:enum", "type:param", "type:tuple", "type:word"),
    "declarations": ("argument:enum", "argument:param", "argument:tuple", "argument:word", "generic", "plain", "same-name"),
    "views": ("generic", "pair", "single"),
    "patterns": ("default", "dot", "exhaustive", "nested", "nullary", "qualified", "rebound", "repeated", "same-name",
                 "shadow", "tuple", "variable", "wildcard"),
    "wildcards": ("arm", "column", "component", "deep", "field"),
    "depths": ("1", "2", "3")}
TRAIT_CASE_SCHEMA = "solcore-lean.semantic-trait-case.v1"
TRAIT_VERSIONS = ("profileVersion", "boundaryVersion")
# The specified shape values of the trait profile, from the plan, never measured.
TRAIT_SHAPES = {
    "instances": ("generic:binary", "generic:unary", "plain:binary", "plain:unary", "sum:binary", "sum:unary",
                  "tuple:binary", "tuple:unary", "word:binary", "word:unary"),
    "calls": ("binary:direct", "binary:generic", "binary:lifted", "unary:direct", "unary:generic", "unary:lifted"),
    "depths": ("0", "1", "2", "3"),
    "arguments": ("generic", "plain", "sum", "tuple", "word"),
    "forms": ("enum:columns", "enum:nested", "tuple:columns", "tuple:nested"),
    "shapes": ("sum-of-product",)}
HIERARCHY_CASE_SCHEMA = "solcore-lean.semantic-trait-hierarchy-case.v1"
HIERARCHY_VERSIONS = ("profileVersion", "boundaryVersion")
# The specified shape values of the trait hierarchy profile, from the plan, never measured.
HIERARCHY_SHAPES = {
    "instances": ("generic:binary", "generic:mix", "generic:unary", "plain:binary", "plain:mix", "plain:unary",
                  "sum:binary", "sum:mix", "sum:unary", "tuple:binary", "tuple:mix", "tuple:unary", "word:binary",
                  "word:mix", "word:unary"),
    "calls": ("binary:direct", "binary:function", "binary:sub", "binary:top", "binary:value", "mix:direct", "mix:top",
              "mix:value", "unary:direct", "unary:function", "unary:sub", "unary:top", "unary:value"),
    "depths": ("0", "1", "2", "3"),
    "arguments": ("generic", "plain", "sum", "tuple", "word"),
    "parameters": ("generic", "plain", "sum", "tuple", "word"),
    "forms": ("enum:columns", "enum:nested", "tuple:columns", "tuple:nested"),
    "subclass": ("marker", "mix", "shadow")}
MEMORY_CASE_SCHEMA = "solcore-lean.semantic-memory-value-case.v1"
MEMORY_VERSIONS = ("profileVersion", "boundaryVersion")
# The specified shape values of the memory value profile, from the plan, never measured.
MEMORY_SHAPES = {
    "values": ("alias:array", "alias:bytes", "array:allocated", "array:literal", "bytes", "slice"),
    "parts": ("concat:bytes", "concat:slice", "concat:word", "concat:zeros", "to_bytes:bytes", "to_bytes:slice",
              "to_bytes:word", "to_bytes:zeros"),
    "cuts": ("drop:bytes", "drop:slice", "take:bytes", "take:slice", "window:bytes", "window:slice"),
    "writes": ("array:helper", "array:inline", "bytes:byte:helper", "bytes:byte:inline", "bytes:word:helper",
               "bytes:word:inline", "slice:byte:helper", "slice:byte:inline", "slice:word:helper", "slice:word:inline"),
    "observations": ("byte:bytes", "byte:slice", "element:get", "element:index", "hash:bytes", "hash:slice",
                     "length:bytes", "length:slice", "word:bytes", "word:slice"),
    "indices": tuple(sorted(f"{access}:{kind}" for access in ("byte", "element", "put", "put8", "set", "word")
                            for kind in ("counter", "input", "literal"))),
    "hazards": ("alias", "copy", "helper", "view"),
    "loops": ("nested:counter", "nested:input", "none", "single:1", "single:3", "single:7"),
    "body": ("array", "bytes", "observe", "slice", "write"),
    "hashes": ("0", "1-31", "128", "32", "33-63", "64", "65-95", "96", "97-127")}
MEMORY_CALL_CASE_SCHEMA = "solcore-lean.semantic-memory-call-case.v1"
MEMORY_CALL_VERSIONS = ("profileVersion", "boundaryVersion")
MEMORY_CALL_PARAMETERS = ("bytes", "slice", "generic", "array", "pair", "sum", "enum")
# The specified shape values of the memory call profile, from the plan, never measured.
MEMORY_CALL_SHAPES = {
    "helpers": ("call:array", "call:bytes", "call:enum", "call:generic", "call:pair", "call:slice", "call:sum",
                "copy:bytes", "copy:generic", "copy:slice", "pack:bytes", "read:array", "read:bytes", "read:generic",
                "read:slice", "take:enum", "take:pair", "take:sum", "view:bytes", "view:generic", "view:slice",
                "write:array", "write:bytes", "write:generic", "write:slice"),
    "calls": tuple(sorted(f"{form}:{result}" for form in ("direct", "value")
                          for result in ("array", "bytes", "pair", "slice", "word"))),
    "passes": ("array", "bytes", "pair", "slice"),
    "instances": ("bytes", "several", "slice"),
    "data": ("enum0", "enum1", "inl", "inr", "pair"),
    "closures": ("byte:bytes", "byte:slice", "element:array", "hash:bytes", "hash:slice", "length:bytes",
                 "length:slice", "word:bytes", "word:slice"),
    "observations": tuple(sorted([f"{obs}:{kind}" for obs in ("byte", "hash", "length", "word")
                                  for kind in ("bytes", "enum", "pair", "slice", "sum")] +
                                 ["carried:enum", "carried:sum", "element:array"])),
    "indices": tuple(sorted(f"{access}:{kind}" for access in ("byte", "element", "put", "put8", "set", "word")
                            for kind in ("input", "literal"))),
    "ranges": ("apply", "call"),
    "hazards": ("alias", "closure", "copy", "helper"),
    "steps": ("action:alias", "action:array", "action:bytes", "action:observe", "action:slice", "action:write",
              "apply", "call", "closure", "data")}
REVERT_DATA_CASE_SCHEMA = "solcore-lean.semantic-revert-data-case.v1"
REVERT_DATA_VERSIONS = ("profileVersion", "boundaryVersion")
# The specified shape values of the revert data profile, from the plan, never measured.
REVERT_DATA_SHAPES = {
    "helpers": ("call", "make", "message", "pick", "raise"),
    "forms": ("require", "requireLiteral", "revertEmpty", "revertLit", "revertWithError"),
    "errors": ("empty", "message", "picked", "selector"),
    "contexts": ("call", "closure", "enum", "helper", "loop", "pair", "run", "sum"),
    "carriers": ("captured", "held", "inline", "loop", "passed", "value", "variable"),
    "declarations": ("made", "messaged", "picked", "variable"),
    "data": ("enum0", "enum1", "inl", "inr", "pair"),
    "tests": ("bits", "eq", "gt", "lt", "ne"),
    "words": ("acc", "constant", "counter", "input", "local"),
    "lengths": ("0", "1-31", "32", "33-63", "64"),
    "hazards": ("alias", "allocated", "written"),
    "steps": ("action", "apply", "call", "closure", "data", "error", "loop", "site", "take")}
HALT_CASE_SCHEMA = "solcore-lean.semantic-halt-case.v1"
HALT_VERSIONS = ("profileVersion", "boundaryVersion")
# The specified shape values of the halt profile, from the plan, never measured.
HALT_SHAPES = {
    "halts": ("assert", "inline", "invalid", "yul"),
    "haltContexts": ("call", "closure", "enum", "helper", "loop", "pair", "run", "sum"),
    "haltTests": ("bits", "eq", "gt", "lt", "ne"),
    "haltWords": ("acc", "constant", "counter", "input", "local"),
    "haltOrders": ("revert-after", "revert-before", "write-after", "write-before")}
CHECKED_ARITHMETIC_CASE_SCHEMA = "solcore-lean.semantic-checked-arithmetic-case.v1"
SHIFT_CASE_SCHEMA = "solcore-lean.semantic-shift-case.v1"
INTEGER_VERSIONS = ("profileVersion", "boundaryVersion")
INTEGER_TYPES = ("uint8", "uint16", "uint32", "uint64", "uint128", "uint256",
                 "int8", "int16", "int32", "int64", "int128", "int256")
# The selectors of run(T), keccak256 of each signature; run(uint256) is every pure profile's.
RUN_SELECTORS = {"uint8": "c4e5557a", "uint16": "1f63069c", "uint32": "0f6d710c", "uint64": "8a52d919",
                 "uint128": "edc3b5ad", "uint256": "a444f5e9", "int8": "1778c9c6", "int16": "091ebc26",
                 "int32": "23040ce1", "int64": "ec784157", "int128": "96c07422", "int256": "61a47706"}
# The specified shape values of the checked arithmetic profile, from the plan and the runs its
# plan reaches at the eight boundary inputs, never measured on a compiled path.
CHECKED_ARITHMETIC_SHAPES = {
    "types": tuple(sorted(INTEGER_TYPES)),
    "operators": ("add", "div", "mod", "mul", "neg", "sub"),
    "forms": ("apply", "call", "compound", "default", "inline"),
    "contexts": ("checked", "unchecked"),
    "scopes": ("apply-in-block", "block", "call-in-block", "unchecked-helper", "unchecked-lambda"),
    "operands": ("input", "literal", "offset", "variable"),
    "literals": ("half", "max", "max1", "min", "min1", "minus1", "one", "small", "zero"),
    "parameters": ("abi", "word"),
    "returns": ("raw", "word"),
    "outcomes": ("dirty", "panic-0x11", "panic-0x12", "returned"),
    "panics": ("add", "div-overflow", "div-zero", "mod-zero", "mul", "neg", "sub", "unchecked-div-zero",
               "unchecked-mod-zero"),
    "wraps": ("add", "div", "mul", "neg", "sub"),
    "typeOutcomes": tuple(sorted([f"{name}:{outcome}" for name in INTEGER_TYPES for outcome in ("0x11", "0x12", "wrap")] +
                                 [f"{name}:dirty" for name in INTEGER_TYPES if not name.endswith("256")]))}
# The specified shape values of the shift profile, from the plan and the runs its plan reaches at
# the eight boundary inputs, never measured on a compiled path.
SHIFT_SHAPES = {
    "values": tuple(sorted(("word",) + INTEGER_TYPES)),
    "amounts": tuple(sorted(("literal", "word") + tuple(name for name in INTEGER_TYPES if name.startswith("u")))),
    "operators": ("sar", "shl", "shr"),
    "forms": ("compound", "inline"),
    "contexts": ("checked", "unchecked"),
    "operands": ("input", "literal", "offset", "variable"),
    "ranges": ("beyond", "huge", "inside", "last", "width", "zero"),
    "results": ("minus-one", "zero"),
    "typeRanges": tuple(sorted(f"{name}:width" for name in ("word",) + INTEGER_TYPES))}
INTEGER_PLAN_KEYS = {CHECKED_ARITHMETIC_CASE_SCHEMA: ("checkedArithmeticPlan", "checkedArithmeticShapes",
                                                      CHECKED_ARITHMETIC_SHAPES, "solcore-lean.checked-arithmetic-plan.v1"),
                     SHIFT_CASE_SCHEMA: ("shiftPlan", "shiftShapes", SHIFT_SHAPES, "solcore-lean.shift-plan.v1")}
MEMORY_ARRAY_CASE_SCHEMA = "solcore-lean.semantic-memory-array-case.v1"
ARRAY_ABI_CASE_SCHEMA = "solcore-lean.semantic-array-abi-case.v1"
ARRAY_VERSIONS = ("profileVersion", "boundaryVersion")
# The selectors of run(T[],uint256) and run(T[],T[],uint256), keccak256 of each signature.
ARRAY_SELECTORS = {
    ("uint8", 1): "8bd24abc", ("uint8", 2): "5434d13a", ("uint16", 1): "f9667762", ("uint16", 2): "b80c6e47",
    ("uint32", 1): "6502c8b5", ("uint32", 2): "c85caa6b", ("uint64", 1): "c7b78359", ("uint64", 2): "980d964e",
    ("uint128", 1): "2e2e3fe9", ("uint128", 2): "4317c184", ("uint256", 1): "bb031b59", ("uint256", 2): "f8b1231b",
    ("int8", 1): "57b6bce4", ("int8", 2): "25905c45", ("int16", 1): "0b91d525", ("int16", 2): "83abf9bf",
    ("int32", 1): "14240747", ("int32", 2): "bb1a6908", ("int64", 1): "157e1f25", ("int64", 2): "438c7ad6",
    ("int128", 1): "8018c529", ("int128", 2): "5f653335", ("int256", 1): "4fec41af", ("int256", 2): "0533c749"}
# The specified shape values of the memory array profile, from the plan and the runs its plan
# reaches at the eight boundary inputs, never measured on a compiled path.
MEMORY_ARRAY_SHAPES = {
    "types": tuple(sorted(INTEGER_TYPES)),
    "declarations": tuple(sorted(("new", "literal", "alias", "copy", "helper", "slice-range", "slice-from", "slice-to",
                                  "slice-all", "tail", "grid-new", "grid-arrays", "grid-literal"))),
    "writes": tuple(sorted(("plain", "put", "inc", "fill", "set-row") +
                           tuple(name for op in ("add", "sub", "mul", "div", "mod") for name in (op, "unchecked-" + op)))),
    "targets": ("array", "row", "storage"),
    "members": ("pop", "push", "set-length"),
    "observations": tuple(sorted(("length", "element", "grid-length", "sum", "get", "len"))),
    "collections": ("array", "row", "slice", "storage"),
    "bases": ("array", "row", "slice", "storage"),
    "indices": ("counter", "flagged", "input", "literal"),
    "lengths": ("flagged", "input", "literal"),
    "loops": ("array", "row", "slice", "storage"),
    "sharing": ("alias", "copy", "row", "view"),
    "outcomes": ("panic-0x11", "panic-0x12", "panic-0x31", "panic-0x32", "panic-0x41", "returned"),
    "panics": tuple(sorted(("read", "write", "row", "slice-start", "slice-end", "slice-read", "stale", "pop", "new",
                            "grid-new", "compound-overflow", "compound-zero", "inc", "sum")))}
# The specified shape values of the array ABI profile, from the plan and the runs its plan reaches
# at the eight boundary inputs, never measured on a compiled path.
ARRAY_ABI_SHAPES = {
    "types": tuple(sorted(INTEGER_TYPES)),
    "parameters": ("calldata", "memory", "two"),
    "lengths": ("input", "literal"),
    "elements": ("clean", "raw"),
    "values": ("clean", "raw"),
    "results": ("array", "copy", "parameter", "word"),
    "calldataReads": tuple(sorted(("length", "element", "get", "slice", "copy", "loop"))),
    "parameterWrites": ("compound", "fill", "memref", "plain"),
    "encodings": ("canonical", "normalized"),
    "outcomes": ("dirty", "panic-0x11", "panic-0x12", "panic-0x32", "panic-0x41", "returned"),
    "dirty": ("copy", "memory", "read")}
ARRAY_PLAN_KEYS = {MEMORY_ARRAY_CASE_SCHEMA: ("memoryArrayPlan", "memoryArrayShapes", MEMORY_ARRAY_SHAPES,
                                              "solcore-lean.memory-array-plan.v1"),
                   ARRAY_ABI_CASE_SCHEMA: ("arrayAbiPlan", "arrayAbiShapes", ARRAY_ABI_SHAPES,
                                           "solcore-lean.array-abi-plan.v1")}
CLOSURE_CAPTURES_CASE_SCHEMA = "solcore-lean.semantic-closure-captures-case.v1"
CLOSURE_FACTORIES_CASE_SCHEMA = "solcore-lean.semantic-closure-factories-case.v1"
CLOSURE_VERSIONS = ("profileVersion", "boundaryVersion")
# The specified shape values of the closure capture profile, from the plan and the runs its
# plan reaches at the eight boundary inputs, never measured on a compiled path.
CLOSURE_CAPTURES_SHAPES = {
    "capture": ("arg", "body-value", "closure", "input", "nothing", "value"),
    "field": ("body-read", "body-write", "run-read", "run-write"),
    "write": ("captured-closure", "captured-param", "captured-value", "own-closure", "own-param", "own-value"),
    "outer": ("later-rebind", "later-write"),
    "call": ("apply", "captured", "direct", "in-body", "loop", "repeat", "twice"),
    "closure": ("alias", "lambda", "loop", "nested", "realias", "relambda"),
    "outcome": ("panic-0x11", "panic-0x12", "return"),
    "panicSite": ("body", "run")}
# The closure factory profile's specified shape values, the same way.
CLOSURE_FACTORIES_SHAPES = {
    "capture": ("arg", "body-value", "closure", "input", "nothing", "param", "value"),
    "field": ("body-read", "body-write", "factory-read", "factory-write", "run-read", "run-write"),
    "write": ("captured-closure", "captured-param", "captured-value", "own-closure", "own-param", "own-value"),
    "outer": ("later-rebind", "later-write"),
    "call": ("apply", "captured", "direct", "in-body", "loop", "repeat", "twice"),
    "closure": ("alias", "discard", "lambda", "loop", "make", "nested", "realias", "relambda", "remake"),
    "factory": ("captures-param", "captures-value", "chained", "checked-effect", "closure-result", "free", "in-body",
                "instances", "lambda-result", "later-write", "literal-argument", "method", "runtime-argument"),
    "outcome": ("panic-0x11", "panic-0x12", "return"),
    "panicSite": ("body", "factory", "run")}
CLOSURE_PLAN_KEYS = {CLOSURE_CAPTURES_CASE_SCHEMA: ("closureCapturesPlan", "closureCapturesShapes",
                                                    CLOSURE_CAPTURES_SHAPES, "solcore-lean.closure-captures-plan.v1"),
                     CLOSURE_FACTORIES_CASE_SCHEMA: ("closureFactoriesPlan", "closureFactoriesShapes",
                                                     CLOSURE_FACTORIES_SHAPES, "solcore-lean.closure-factories-plan.v1")}
# Cases whose original Core returns data rather than one Word: an array ABI plan's T[] result,
# or its fold as 32 bytes.
OUTPUT_SCHEMAS = (ARRAY_ABI_CASE_SCHEMA,)
# Cases whose original Core can stop with revert data: std's OutOfBounds() revert at an
# out-of-range access, a revert data or halt plan's site, a checked arithmetic plan's
# Panic or std's DirtyHigherBitsForInteger(), an array plan's Panic or that rejection, or
# a closure plan's checked Panic; three reverts with the same data are a match only for them.
REVERTING_SCHEMAS = (MEMORY_CASE_SCHEMA, MEMORY_CALL_CASE_SCHEMA, REVERT_DATA_CASE_SCHEMA, HALT_CASE_SCHEMA,
                     CHECKED_ARITHMETIC_CASE_SCHEMA, MEMORY_ARRAY_CASE_SCHEMA, ARRAY_ABI_CASE_SCHEMA,
                     CLOSURE_CAPTURES_CASE_SCHEMA, CLOSURE_FACTORIES_CASE_SCHEMA)
# Cases whose original Core can halt with INVALID; three INVALID halts are a match only
# for them.
HALTING_SCHEMAS = (HALT_CASE_SCHEMA,)
FUNCTION_CASE_SCHEMA = "solcore-lean.semantic-function-case.v1"
MUTATION_CASE_SCHEMA = "solcore-lean.semantic-mutation-case.v1"
AGGREGATE_CASE_SCHEMA = "solcore-lean.semantic-aggregate-case.v1"
LOOP_CASE_SCHEMA = "solcore-lean.semantic-loop-case.v1"
NESTED_LOOP_CASE_SCHEMA = "solcore-lean.semantic-nested-loop-case.v1"
NESTED_LOOP_BOUNDS = ("input", "counter", "accumulator")
RECURSION_CASE_SCHEMA = "solcore-lean.semantic-recursion-case.v1"
RECURSION_FORMS = ("tail", "nontail", "mutual")
RECURSIVE_LOOP_CASE_SCHEMA = "solcore-lean.semantic-recursive-loop-case.v1"
LOOP_CLOSURE_CASE_SCHEMA = "solcore-lean.semantic-loop-closure-case.v1"
LOOP_CLOSURE_CAPTURES = ("accumulator", "counter")
GENERIC_CASE_SCHEMA = "solcore-lean.semantic-generic-case.v1"
CLOSURE_CASE_SCHEMA = "solcore-lean.semantic-closure-case.v1"
COMPTIME_CASE_SCHEMA = "solcore-lean.semantic-comptime-case.v1"
MODULE_CASE_SCHEMA = "solcore-lean.semantic-module-case.v1"
CASE_PROFILES = {CASE_SCHEMA: "closed-g0", INPUT_CASE_SCHEMA: "runtime-word",
                 PRIMITIVE_CASE_SCHEMA: "runtime-primitives", ASSEMBLY_CASE_SCHEMA: "runtime-assembly",
                 ASSEMBLY_MEMORY_CASE_SCHEMA: "runtime-assembly-memory",
                 CALL_GRAPH_CASE_SCHEMA: "runtime-call-graphs",
                 CALL_GRAPH_LOOP_CASE_SCHEMA: "runtime-call-graph-loops",
                 ASSEMBLY_LOOP_CASE_SCHEMA: "runtime-assembly-loops",
                 AGGREGATE_CALL_GRAPH_CASE_SCHEMA: "runtime-aggregate-call-graphs",
                 FUNCTION_CASE_SCHEMA: "runtime-functions", MUTATION_CASE_SCHEMA: "runtime-mutation",
                 AGGREGATE_CASE_SCHEMA: "runtime-aggregates", LOOP_CASE_SCHEMA: "runtime-loops",
                 NESTED_LOOP_CASE_SCHEMA: "runtime-nested-loops", RECURSION_CASE_SCHEMA: "runtime-recursion",
                 RECURSIVE_LOOP_CASE_SCHEMA: "runtime-recursive-loops", LOOP_CLOSURE_CASE_SCHEMA: "runtime-loop-closures",
                 GENERIC_CASE_SCHEMA: "runtime-generics", CLOSURE_CASE_SCHEMA: "runtime-closures", COMPTIME_CASE_SCHEMA: "runtime-comptime", MODULE_CASE_SCHEMA: "runtime-modules",
                 ENUM_CASE_SCHEMA: "runtime-enums", TRAIT_CASE_SCHEMA: "runtime-traits",
                 HIERARCHY_CASE_SCHEMA: "runtime-trait-hierarchies", MEMORY_CASE_SCHEMA: "runtime-memory-values",
                 MEMORY_CALL_CASE_SCHEMA: "runtime-memory-calls", REVERT_DATA_CASE_SCHEMA: "runtime-revert-data",
                 HALT_CASE_SCHEMA: "runtime-halts", CHECKED_ARITHMETIC_CASE_SCHEMA: "runtime-checked-arithmetic",
                 SHIFT_CASE_SCHEMA: "runtime-shifts", MEMORY_ARRAY_CASE_SCHEMA: "runtime-memory-arrays",
                 ARRAY_ABI_CASE_SCHEMA: "runtime-array-abi", CLOSURE_CAPTURES_CASE_SCHEMA: "runtime-closure-captures",
                 CLOSURE_FACTORIES_CASE_SCHEMA: "runtime-closure-factories"}
CASE_CONTRACTS = {CASE_SCHEMA: "SynthesizedG0", INPUT_CASE_SCHEMA: "SynthesizedInput",
                  PRIMITIVE_CASE_SCHEMA: "SynthesizedPrimitives", ASSEMBLY_CASE_SCHEMA: "SynthesizedAssembly",
                  ASSEMBLY_MEMORY_CASE_SCHEMA: "SynthesizedAssemblyMemory",
                  CALL_GRAPH_CASE_SCHEMA: "SynthesizedCallGraphs",
                  CALL_GRAPH_LOOP_CASE_SCHEMA: "SynthesizedCallGraphLoops",
                  ASSEMBLY_LOOP_CASE_SCHEMA: "SynthesizedAssemblyLoops",
                  AGGREGATE_CALL_GRAPH_CASE_SCHEMA: "SynthesizedAggregateCallGraphs",
                  FUNCTION_CASE_SCHEMA: "SynthesizedFunctions", MUTATION_CASE_SCHEMA: "SynthesizedMutation",
                  AGGREGATE_CASE_SCHEMA: "SynthesizedAggregates", LOOP_CASE_SCHEMA: "SynthesizedLoops",
                  NESTED_LOOP_CASE_SCHEMA: "SynthesizedNestedLoops", RECURSION_CASE_SCHEMA: "SynthesizedRecursion",
                  RECURSIVE_LOOP_CASE_SCHEMA: "SynthesizedRecursiveLoops", LOOP_CLOSURE_CASE_SCHEMA: "SynthesizedLoopClosures",
                  GENERIC_CASE_SCHEMA: "SynthesizedGenerics", CLOSURE_CASE_SCHEMA: "SynthesizedClosures", COMPTIME_CASE_SCHEMA: "SynthesizedComptime", MODULE_CASE_SCHEMA: "SynthesizedModules",
                  ENUM_CASE_SCHEMA: "SynthesizedEnums", TRAIT_CASE_SCHEMA: "SynthesizedTraits",
                  HIERARCHY_CASE_SCHEMA: "SynthesizedTraitHierarchies", MEMORY_CASE_SCHEMA: "SynthesizedMemoryValues",
                  MEMORY_CALL_CASE_SCHEMA: "SynthesizedMemoryCalls", REVERT_DATA_CASE_SCHEMA: "SynthesizedRevertData",
                  HALT_CASE_SCHEMA: "SynthesizedHalts", CHECKED_ARITHMETIC_CASE_SCHEMA: "SynthesizedCheckedArithmetic",
                  SHIFT_CASE_SCHEMA: "SynthesizedShifts", MEMORY_ARRAY_CASE_SCHEMA: "SynthesizedMemoryArrays",
                  ARRAY_ABI_CASE_SCHEMA: "SynthesizedArrayAbi", CLOSURE_CAPTURES_CASE_SCHEMA: "SynthesizedClosureCaptures",
                  CLOSURE_FACTORIES_CASE_SCHEMA: "SynthesizedClosureFactories"}
REPORT_SCHEMA = "solcore-lean.semantic-differential.v1"
UPSTREAM_COMMIT = "e2eef19409fc8879cd4a9cc342ed60e3152f72c0"
BACKEND_COMMIT = "6bd0ce661ea327c149429b00fee3c8608616040f"
SONATINA_BACKENDS = ("sonatina-o0", "sonatina-o2")
BACKENDS = (*SONATINA_BACKENDS, "yul")
MAX_CASE_BYTES = 4 * 1024 * 1024
GAS_RESOURCE = re.compile(r"out[ _-]?of[ _-]?gas|intrinsic gas.{0,40}(too low|exceed)|"
                          r"gas (required|limit).{0,40}(allowance|exceed)|gas too low", re.I)
RESOURCE = re.compile(GAS_RESOURCE.pattern + r"|out.of.fuel|fuel.{0,40}(exhaust|limit|budget)|"
                      r"(specialization|recursion|export|depth).{0,40}(limit|exhaust)|"
                      r"stack overflow|memory limit", re.I)
COMPLETED = {"returned", "reverted"}
# INVALID's designated halt, an outcome of the profiles in HALTING_SCHEMAS.
HALTED = {"invalid"}
COMPILATION_SCHEMA = "solcore-lean.semantic-compilation.v1"
# Compiler verdicts on the source bytes themselves. A resource or adapter failure
# says nothing about the source, so the next case with that source compiles again.
SHARED_FAILURES = ("source-rejected", "compilation-rejected", "compiler-crash")
COMPILERS = ("debug/solcore-driver", "lean-export-build.json",
             "debug/solcore-code-image-export", "code-image-export-build.json")


class Finding(Exception):
    def __init__(self, category: str, stage: str, detail: str):
        self.category, self.stage, self.detail = category, stage, detail
        super().__init__(detail)


class RpcError(Exception):
    def __init__(self, error):
        self.error = error
        super().__init__(str(error))


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_digest(path: Path) -> str:
    """Hash artifacts without loading a rejected oversized file into memory."""
    result = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(65536), b""):
            result.update(chunk)
    return result.hexdigest()


class DigestCache:
    """Tool digests and version outputs shared by the cases of one campaign.

    A file is hashed again whenever its path, device, inode, size, modification
    or status-change time differs from those it was hashed with. Writing a file
    always moves its status-change time, which cannot be set back, so a reused
    digest is that of the same bytes. A version output is reused with its
    process record, marked as reused, while its tool's file is unchanged.
    """

    def __init__(self):
        self.digests: dict[tuple, str] = {}
        self.versions: dict[tuple, dict] = {}

    @staticmethod
    def key(path: Path) -> tuple:
        status = path.stat()
        return str(path), status.st_dev, status.st_ino, status.st_size, status.st_mtime_ns, status.st_ctime_ns

    def digest(self, path: Path) -> str:
        key = self.key(path)
        if key not in self.digests:
            value = file_digest(path)
            if self.key(path) != key:
                return value  # Changed while it was read: never reused.
            self.digests[key] = value
        return self.digests[key]


def tool_digest(args, path: Path) -> str:
    """A campaign's cached digest of an unchanged tool file, otherwise a fresh one."""
    cache = getattr(args, "digest_cache", None)
    return file_digest(path) if cache is None else cache.digest(path)


def resolve_backend(explicit: str | None, saved_report: dict | None = None) -> str:
    """Only an absent legacy field means O0; replay cannot change compilation."""
    if saved_report is not None and not isinstance(saved_report, dict):
        raise ValueError("saved backend report must be an object")
    saved = saved_report.get("backend", "sonatina-o0") if saved_report is not None else None
    if saved_report is not None and saved not in BACKENDS:
        raise ValueError("unsupported saved backend")
    selected = explicit if explicit is not None else (saved if saved_report is not None else BACKENDS[0])
    if selected not in BACKENDS:
        raise ValueError("unsupported backend")
    if saved_report is not None and selected != saved:
        raise ValueError("exact replay retains the saved backend; use --case for another backend")
    return selected


def optimization_for_backend(backend: str) -> str:
    if backend not in SONATINA_BACKENDS:
        raise ValueError("only Sonatina backends supply Hull code images")
    return {"sonatina-o0": "O0", "sonatina-o2": "O2"}[backend]


def image_backend(backend: str) -> str:
    selected = resolve_backend(backend)
    return "sonatina-o0" if selected == "yul" else selected


def resolve_sonatina_backend(explicit: str | None, saved_report: dict | None = None) -> str:
    selected = resolve_backend(explicit, saved_report)
    if selected not in SONATINA_BACKENDS:
        raise ValueError("stateful comparisons require a Sonatina backend")
    return selected


def path_backends(backend: str) -> dict:
    return {"directCore": "original-core", "importedHull": image_backend(backend), "rustEvm": backend}


_yul_module = None


def yul_transport(operation: str, *args):
    """Load the optional transport lazily; preserve its structured failures.

    Importlib consumers own distinct Finding classes. Translate only this
    trusted helper's class; native caller failures already use our own class.
    """
    global _yul_module
    if _yul_module is None:
        spec = importlib.util.spec_from_file_location("semantic_yul_transport", ROOT / "scripts/semantic-yul.py")
        assert spec and spec.loader
        _yul_module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(_yul_module)
    try:
        return getattr(_yul_module, operation)(*args)
    except _yul_module.common.Finding as error:
        raise Finding(error.category, error.stage, error.detail) from error


def validate_image_backend(images: dict, backend: str) -> None:
    expected = {"name": "sonatina", "revision": BACKEND_COMMIT,
                "optimization": optimization_for_backend(backend)}
    if images.get("backend") != expected:
        raise ValueError("code image backend differs from selected backend")


def verify_archive(directory: Path, report: dict) -> None:
    if not isinstance(report, dict) or report.get("schema") != REPORT_SCHEMA:
        raise ValueError("unsupported saved report schema")
    artifacts = report.get("artifacts")
    if not isinstance(artifacts, dict) or "case.json" not in artifacts:
        raise ValueError("saved artifact inventory is missing its case")
    for name, expected in artifacts.items():
        if (not isinstance(name, str) or not name or name in {".", "..", "report.json"}
                or "/" in name or "\\" in name or Path(name).name != name):
            raise ValueError("saved artifact name must be a plain file name")
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError(f"invalid saved artifact hash: {name}")
        path = directory / name
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"saved artifact is missing or is not a regular file: {name}")
        if file_digest(path) != expected:
            raise ValueError(f"saved artifact hash changed: {name}")
    if artifacts["case.json"] != report.get("caseSha256"):
        raise ValueError("saved case hash differs from the artifact inventory")
    backend = resolve_backend(None, report)
    if "pathBackends" in report and report["pathBackends"] != path_backends(backend):
        raise ValueError("saved execution path backends differ from selected backend")
    if "images.json" in artifacts:
        validate_image_backend(read_json(directory / "images.json", 64 * 1024 * 1024), image_backend(backend))
    provenance = report.get("exportProvenance", {}).get("images")
    if provenance is not None and (provenance.get("backendRevision") != BACKEND_COMMIT or
            provenance.get("optimization") != optimization_for_backend(image_backend(backend))):
        raise ValueError("saved export provenance differs from selected backend")
    if backend == "yul":
        yul_transport("validate_archive", directory, report, 64 * 1024 * 1024)


def json_bytes(value) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2) + "\n").encode()


def read_json(path: Path, limit: int = MAX_CASE_BYTES):
    if path.stat().st_size > limit:
        raise Finding("inconclusive-resource", "input", f"file exceeds {limit} bytes: {path}")
    return json.loads(path.read_text())


def hex_bytes(value, label: str) -> bytes:
    if not isinstance(value, str) or not re.fullmatch(r"0x(?:[0-9a-fA-F]{2})*", value):
        raise ValueError(f"{label} is not a hexadecimal byte string")
    return bytes.fromhex(value[2:])


def word(value, label="word") -> str:
    if not isinstance(value, str) or not re.fullmatch(r"0|[1-9][0-9]*", value):
        raise ValueError(f"{label} must be a canonical decimal string")
    if len(value) > 78 or int(value) >= 2**256:
        raise ValueError(f"{label} exceeds 256 bits")
    return value


def validate_loop_plan(plan) -> dict:
    """Validate the envelope; native replay checks the entire canonical program."""
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.loop-plan.v1":
        raise ValueError("unsupported loop plan schema")
    if type(plan.get("mask")) is not int or plan["mask"] not in (0, 1, 3, 7):
        raise ValueError("loop mask must be zero, one, three or seven")
    if not isinstance(plan.get("stepProgram"), dict):
        raise ValueError("loop plan requires its original step function graph")
    return plan


def validate_nested_loop_plan(plan) -> dict:
    """Validate the envelope; native replay checks the entire canonical program."""
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.nested-loop-plan.v1":
        raise ValueError("unsupported nested loop plan schema")
    for key in ("outerMask", "innerMask"):
        if type(plan.get(key)) is not int or plan[key] not in (0, 1, 3):
            raise ValueError(f"nested loop {key} must be zero, one or three")
    if plan.get("innerBound") not in NESTED_LOOP_BOUNDS:
        raise ValueError("nested loop inner bound must read the input, the counter or the accumulator")
    if not isinstance(plan.get("stepProgram"), dict):
        raise ValueError("nested loop plan requires its original step function graph")
    return plan


def validate_recursion_plan(plan) -> dict:
    """Validate the envelope; native replay checks the entire canonical program."""
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.recursion-plan.v1":
        raise ValueError("unsupported recursion plan schema")
    if type(plan.get("depthMask")) is not int or plan["depthMask"] not in (0, 1, 3, 7):
        raise ValueError("recursion depth mask must be zero, one, three or seven")
    if plan.get("form") not in RECURSION_FORMS:
        raise ValueError("recursion form must be tail, nontail or mutual")
    if not isinstance(plan.get("stepProgram"), dict):
        raise ValueError("recursion plan requires its original step function graph")
    return plan


def validate_recursive_loop_plan(plan) -> dict:
    """Validate the envelope; native replay checks the entire canonical program."""
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.recursive-loop-plan.v1":
        raise ValueError("unsupported recursive-loop plan schema")
    for key in ("depthMask", "innerMask"):
        if type(plan.get(key)) is not int or plan[key] not in (0, 1, 3):
            raise ValueError(f"recursive-loop {key} must be zero, one or three")
    if plan.get("form") not in RECURSION_FORMS:
        raise ValueError("recursive-loop form must be tail, nontail or mutual")
    if not isinstance(plan.get("stepProgram"), dict):
        raise ValueError("recursive-loop plan requires its original step function graph")
    return plan


def validate_loop_closure_plan(plan) -> dict:
    """Validate the envelope; native replay checks the entire canonical program."""
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.loop-closure-plan.v1":
        raise ValueError("unsupported loop-closure plan schema")
    if type(plan.get("mask")) is not int or plan["mask"] not in (0, 1, 3, 7):
        raise ValueError("loop-closure mask must be zero, one, three or seven")
    if plan.get("capture") not in LOOP_CLOSURE_CAPTURES:
        raise ValueError("loop-closure capture must be accumulator or counter")
    if not isinstance(plan.get("stepProgram"), dict):
        raise ValueError("loop-closure plan requires its original step function graph")
    return plan


def validate_assembly_plan(plan) -> dict:
    """Validate the envelope; native replay checks the function and its emission."""
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.assembly-plan.v1":
        raise ValueError("unsupported assembly plan schema")
    if plan.get("form") not in ASSEMBLY_FORMS:
        raise ValueError("assembly form must be switch, if or operations")
    if not isinstance(plan.get("functionProgram"), dict):
        raise ValueError("assembly plan requires its original Word function")
    return plan


def validate_assembly_memory_plan(plan) -> dict:
    """Validate the envelope and the schedule's bounds; native replay checks the
    step, the schedule's seed and the emission."""
    if (not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.assembly-memory-plan.v1"
            or set(plan) != {"schema", "functionProgram", "stages", "finalRead", "hash"}):
        raise ValueError("unsupported assembly memory plan schema")
    if not isinstance(plan["functionProgram"], dict):
        raise ValueError("assembly memory plan requires its original Word function")
    stages = plan["stages"]
    if not isinstance(stages, list) or not 1 <= len(stages) <= 3:
        raise ValueError("assembly memory plan requires one to three stages")
    for stage in stages:
        if (not isinstance(stage, dict) or set(stage) != {"read", "width", "write"}
                or stage["width"] not in ("word", "byte")
                or any(type(stage[key]) is not int for key in ("read", "write"))
                or not 0 <= stage["read"] <= 64
                or not 0 <= stage["write"] <= (64 if stage["width"] == "word" else 95)):
            raise ValueError("assembly memory stages read a Word at 0..64 and write a Word at 0..64 or a byte at 0..95")
    if type(plan["finalRead"]) is not int or not 0 <= plan["finalRead"] <= 64:
        raise ValueError("assembly memory final read must be a Word offset from 0 to 64")
    hash_ = plan["hash"]
    if hash_ is not None and (not isinstance(hash_, dict) or set(hash_) != {"offset", "length"}
            or type(hash_["offset"]) is not int or hash_["length"] not in ASSEMBLY_MEMORY_HASH_LENGTHS
            or type(hash_["length"]) is not int or not 0 <= hash_["offset"] <= 96 - hash_["length"]):
        raise ValueError("assembly memory hash must cover 0, 1, 31, 32, 33 or 64 bytes inside the window")
    return plan


def validate_enum_plan(plan) -> dict:
    """Validate the envelope and the plan's counts; native replay checks every
    type, pattern, arm, body and value, the seed and the emission."""
    if (not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.enum-plan.v1"
            or set(plan) != {"schema", "declarations", "views"}):
        raise ValueError("unsupported enum plan schema")
    declarations, views = plan["declarations"], plan["views"]
    if not isinstance(declarations, list) or not 1 <= len(declarations) <= 3:
        raise ValueError("enum plan requires one to three declarations")
    for declaration in declarations:
        if (not isinstance(declaration, dict) or set(declaration) != {"generic", "sameName", "constructors"}
                or type(declaration["generic"]) is not bool or type(declaration["sameName"]) is not bool
                or not isinstance(declaration["constructors"], list) or not 2 <= len(declaration["constructors"]) <= 4
                or any(not isinstance(fields, list) or len(fields) > 2 for fields in declaration["constructors"])):
            raise ValueError("enum declarations have two to four constructors of at most two fields")
    if not isinstance(views, list) or not 1 <= len(views) <= 3:
        raise ValueError("enum plan requires one to three views")
    for view in views:
        if (not isinstance(view, dict)
                or set(view) != {"kind", "scrutinees", "instances", "arms", "builders", "wordOffset"}
                or view["kind"] not in ("single", "pair", "generic")
                or not isinstance(view["arms"], list) or not 1 <= len(view["arms"]) <= 8
                or not isinstance(view["builders"], list) or not 1 <= len(view["builders"]) <= 2):
            raise ValueError("enum views are single, pair or generic, with one to eight arms and their builders")
        word(view["wordOffset"], "enum view word offset")
    return plan


def validate_enum_shapes(values, label="enumShapes") -> dict:
    """Native replay authenticates the shapes; Python checks their envelope."""
    if not isinstance(values, dict) or set(values) != set(ENUM_SHAPES):
        raise ValueError(f"{label} must name every enum shape dimension")
    for key, allowed in ENUM_SHAPES.items():
        found = values[key]
        if (not isinstance(found, list) or any(not isinstance(v, str) or v not in allowed for v in found)
                or found != sorted(set(found))):
            raise ValueError(f"{label} {key} must be a sorted unique inventory of known shapes")
    return values


def validate_trait_plan(plan) -> dict:
    """Validate the envelope and the plan's counts; native replay checks every
    declaration, impl, helper, use, type and value, the seed and the emission."""
    if (not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.trait-plan.v1"
            or set(plan) != {"schema", "declarations", "methods", "impls", "helpers", "uses"}):
        raise ValueError("unsupported trait plan schema")
    declarations, methods, impls, helpers, uses = (plan[key] for key in ("declarations", "methods", "impls", "helpers", "uses"))
    if not isinstance(declarations, list) or not 1 <= len(declarations) <= 3:
        raise ValueError("trait plan requires one to three declarations")
    if methods not in (["unary"], ["binary"], ["unary", "binary"]):
        raise ValueError("trait plan methods are unary, binary or both, in that order")
    if not isinstance(impls, list) or not 1 <= len(impls) <= 6 or any(
            not isinstance(impl, dict) or set(impl) != {"head", "unary", "binary", "form", "mismatch"}
            or impl["form"] not in ("nested", "columns") for impl in impls):
        raise ValueError("trait impls have a head, per-method steps, a binary match form and mismatch constants")
    if not isinstance(helpers, list) or len(helpers) > 4 or any(
            not isinstance(helper, dict) or set(helper) != {"call", "method", "op", "constant"}
            or helper["call"] not in ("generic", "lifted") or helper["method"] not in ("unary", "binary")
            for helper in helpers):
        raise ValueError("trait helpers are generic or lifted, for one method each")
    if not isinstance(uses, list) or not 1 <= len(uses) <= 6:
        raise ValueError("trait plan requires one to six uses")
    for use in uses:
        if (not isinstance(use, dict) or set(use) != {"method", "call", "type", "shift", "builder"}
                or use["method"] not in ("unary", "binary") or use["call"] not in ("direct", "generic", "lifted")
                or type(use["shift"]) is not int or not 0 <= use["shift"] <= 4):
            raise ValueError("trait uses call one method directly, generically or lifted, with a shift of at most four")
    return plan


def validate_trait_shapes(values, label="traitShapes") -> dict:
    """Native replay authenticates the shapes; Python checks their envelope."""
    if not isinstance(values, dict) or set(values) != set(TRAIT_SHAPES):
        raise ValueError(f"{label} must name every trait shape dimension")
    for key, allowed in TRAIT_SHAPES.items():
        found = values[key]
        if (not isinstance(found, list) or any(not isinstance(v, str) or v not in allowed for v in found)
                or found != sorted(set(found))):
            raise ValueError(f"{label} {key} must be a sorted unique inventory of known shapes")
    return values


def validate_hierarchy_plan(plan) -> dict:
    """Validate the envelope and the plan's counts; native replay checks every
    declaration, impl of the three traits, helper, use, type and value, the seed
    and the emission."""
    keys = {"schema", "declarations", "methods", "impls", "subclass", "subImpls", "tops", "helpers", "uses"}
    if (not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.trait-hierarchy-plan.v1"
            or set(plan) != keys):
        raise ValueError("unsupported trait hierarchy plan schema")
    declarations, methods, impls, subclass, sub_impls, tops, helpers, uses = (plan[key] for key in (
        "declarations", "methods", "impls", "subclass", "subImpls", "tops", "helpers", "uses"))
    if not isinstance(declarations, list) or not 1 <= len(declarations) <= 3:
        raise ValueError("trait hierarchy plan requires one to three declarations")
    if methods not in (["unary"], ["binary"], ["unary", "binary"]):
        raise ValueError("trait hierarchy base methods are unary, binary or both, in that order")
    if not isinstance(impls, list) or not 1 <= len(impls) <= 6 or any(
            not isinstance(impl, dict) or set(impl) != {"head", "unary", "binary", "form", "mismatch"}
            or impl["form"] not in ("nested", "columns") for impl in impls):
        raise ValueError("trait hierarchy base impls have a head, per-method steps, a binary match form and mismatch constants")
    if subclass not in HIERARCHY_SHAPES["subclass"]:
        raise ValueError("trait hierarchy subclass is a marker, mix or shadow")
    if not isinstance(sub_impls, list) or len(sub_impls) > 6 or any(
            not isinstance(impl, dict) or set(impl) != {"head", "steps"} or not isinstance(impl["steps"], list)
            for impl in sub_impls):
        raise ValueError("trait hierarchy subclass impls have a head and steps")
    if not isinstance(tops, list) or len(tops) > 6:
        raise ValueError("trait hierarchy chain impls are at most six heads")
    calls = ("sub", "top", "value", "function")
    if not isinstance(helpers, list) or len(helpers) > 10 or any(
            not isinstance(helper, dict) or set(helper) != {"call", "method", "op", "constant"}
            or helper["call"] not in calls or helper["method"] not in ("unary", "binary", "mix")
            for helper in helpers):
        raise ValueError("trait hierarchy helpers are sub, top, value or function, for one method each")
    if not isinstance(uses, list) or not 1 <= len(uses) <= 6:
        raise ValueError("trait hierarchy plan requires one to six uses")
    for use in uses:
        if (not isinstance(use, dict) or set(use) != {"method", "call", "type", "shift", "builder", "arguments"}
                or use["method"] not in ("unary", "binary", "mix") or use["call"] not in ("direct",) + calls
                or type(use["shift"]) is not int or not 0 <= use["shift"] <= 4
                or not isinstance(use["arguments"], list) or len(use["arguments"]) not in (0, 2)):
            raise ValueError("trait hierarchy uses call one method in one call form, with a shift of at most four "
                             "and none or two arguments")
    return plan


def validate_hierarchy_shapes(values, label="hierarchyShapes") -> dict:
    """Native replay authenticates the shapes; Python checks their envelope."""
    if not isinstance(values, dict) or set(values) != set(HIERARCHY_SHAPES):
        raise ValueError(f"{label} must name every trait hierarchy shape dimension")
    for key, allowed in HIERARCHY_SHAPES.items():
        found = values[key]
        if (not isinstance(found, list) or any(not isinstance(v, str) or v not in allowed for v in found)
                or found != sorted(set(found))):
            raise ValueError(f"{label} {key} must be a sorted unique inventory of known shapes")
    return values


MEMORY_KINDS = ("bytes", "slice", "alias", "array", "write", "observe")


def validate_memory_plan(plan) -> dict:
    """Validate the envelope, the step counts and the action kinds; native replay
    checks every step against its scope, the lengths, indices, loops and the seed."""
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.memory-value-plan.v1" or set(plan) != {"schema", "steps"}:
        raise ValueError("unsupported memory value plan schema")
    steps = plan["steps"]
    if not isinstance(steps, list) or not 1 <= len(steps) <= 10:
        raise ValueError("memory value plan requires one to ten steps")
    loops = 0
    for step in steps:
        if isinstance(step, dict) and set(step) == {"action"}:
            actions = [step["action"]]
        elif isinstance(step, dict) and set(step) == {"loop", "body"} and isinstance(step["body"], list):
            loops += 1
            actions = step["body"]
            if not isinstance(step["loop"], dict) or step["loop"].get("form") not in ("single", "nested") or not 1 <= len(actions) <= 3:
                raise ValueError("a memory value loop is single or nested, of one to three actions")
        else:
            raise ValueError("a memory value step is an action or a loop")
        if any(not isinstance(action, dict) or action.get("kind") not in MEMORY_KINDS for action in actions):
            raise ValueError("memory value actions are bytes, slice, alias, array, write or observe")
    if loops > 1:
        raise ValueError("memory value plan has at most one loop")
    return plan


def validate_memory_shapes(values, label="memoryValueShapes") -> dict:
    """Native replay authenticates the shapes; Python checks their envelope."""
    if not isinstance(values, dict) or set(values) != set(MEMORY_SHAPES):
        raise ValueError(f"{label} must name every memory value shape dimension")
    for key, allowed in MEMORY_SHAPES.items():
        found = values[key]
        if (not isinstance(found, list) or any(not isinstance(v, str) or v not in allowed for v in found)
                or found != sorted(set(found))):
            raise ValueError(f"{label} {key} must be a sorted unique inventory of known shapes")
    return values


MEMORY_CALL_KINDS = ("read", "write", "view", "copy", "call", "pack", "take")
MEMORY_CALL_STEPS = ("action", "call", "data", "closure", "apply")


def validate_memory_call_plan(plan) -> dict:
    """Validate the envelope, the helper and step counts and their kinds; native
    replay checks every helper and step against its scope, the lengths, indices
    and the seed."""
    if (not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.memory-call-plan.v1"
            or set(plan) != {"schema", "helpers", "steps"}):
        raise ValueError("unsupported memory call plan schema")
    helpers, steps = plan["helpers"], plan["steps"]
    if not isinstance(helpers, list) or not 1 <= len(helpers) <= 3:
        raise ValueError("memory call plan requires one to three helpers")
    if any(not isinstance(helper, dict) or helper.get("param") not in MEMORY_CALL_PARAMETERS
           or helper.get("kind") not in MEMORY_CALL_KINDS for helper in helpers):
        raise ValueError("memory call helpers read, write, view, copy, call, pack or take a known parameter")
    if not isinstance(steps, list) or not 1 <= len(steps) <= 12:
        raise ValueError("memory call plan requires one to twelve steps")
    if any(not isinstance(step, dict) or len(step) != 1 or next(iter(step)) not in MEMORY_CALL_STEPS for step in steps):
        raise ValueError("a memory call step is an action, a call, a data value, a closure or an application")
    if not any("call" in step for step in steps):
        raise ValueError("memory call plan has at least one call")
    for step in steps:
        if "action" in step and (not isinstance(step["action"], dict) or step["action"].get("kind") not in MEMORY_KINDS):
            raise ValueError("memory call actions are bytes, slice, alias, array, write or observe")
    return plan


def validate_memory_call_shapes(values, label="memoryCallShapes") -> dict:
    """Native replay authenticates the shapes; Python checks their envelope."""
    if not isinstance(values, dict) or set(values) != set(MEMORY_CALL_SHAPES):
        raise ValueError(f"{label} must name every memory call shape dimension")
    for key, allowed in MEMORY_CALL_SHAPES.items():
        found = values[key]
        if (not isinstance(found, list) or any(not isinstance(v, str) or v not in allowed for v in found)
                or found != sorted(set(found))):
            raise ValueError(f"{label} {key} must be a sorted unique inventory of known shapes")
    return values


REVERT_DATA_HELPERS = ("raise", "make", "message", "pick", "call")
REVERT_DATA_STEPS = ("action", "error", "data", "site", "call", "take", "closure", "apply", "loop")
REVERT_DATA_ACTIONS = ("bytes", "alias", "write", "observe")


def validate_revert_data_plan(plan, schema="solcore-lean.revert-data-plan.v1") -> dict:
    """Validate the envelope, the helper and step counts and their kinds; native
    replay checks every helper and step against its scope, the sites, literals,
    lengths and the seed."""
    if (not isinstance(plan, dict) or plan.get("schema") != schema
            or set(plan) != {"schema", "helpers", "steps"}):
        raise ValueError("unsupported revert data plan schema")
    helpers, steps = plan["helpers"], plan["steps"]
    if not isinstance(helpers, list) or len(helpers) > 3:
        raise ValueError("revert data plan has at most three helpers")
    if any(not isinstance(helper, dict) or helper.get("kind") not in REVERT_DATA_HELPERS for helper in helpers):
        raise ValueError("revert data helpers raise, make, message, pick or call")
    if not isinstance(steps, list) or not 1 <= len(steps) <= 12:
        raise ValueError("revert data plan requires one to twelve steps")
    if any(not isinstance(step, dict) or len(step) != 1 or next(iter(step)) not in REVERT_DATA_STEPS for step in steps):
        raise ValueError("a revert data step is an action, an Error, a data value, a site, a call, a match, "
                         "a closure, an application or a loop")
    if sum("loop" in step for step in steps) > 1:
        raise ValueError("revert data plan has at most one loop")
    for step in steps:
        if "action" in step and (not isinstance(step["action"], dict)
                                 or step["action"].get("kind") not in REVERT_DATA_ACTIONS):
            raise ValueError("revert data actions are bytes, alias, write or observe")
    return plan


def validate_halt_plan(plan) -> dict:
    """A halt plan is a revert data plan under its own schema; native replay
    checks its halt sites and that it reaches one."""
    return validate_revert_data_plan(plan, "solcore-lean.halt-plan.v1")


def validate_revert_data_shapes(values, label="revertDataShapes", dimensions=REVERT_DATA_SHAPES) -> dict:
    """Native replay authenticates the shapes; Python checks their envelope."""
    if not isinstance(values, dict) or set(values) != set(dimensions):
        raise ValueError(f"{label} must name every revert data shape dimension")
    for key, allowed in dimensions.items():
        found = values[key]
        if (not isinstance(found, list) or any(not isinstance(v, str) or v not in allowed for v in found)
                or found != sorted(set(found))):
            raise ValueError(f"{label} {key} must be a sorted unique inventory of known shapes")
    return values


def validate_integer_plan(plan, schema) -> dict:
    """Validate the envelope, the types and the step count; native replay checks every
    input, amount, helper and step against the profile and the seed."""
    if (not isinstance(plan, dict) or plan.get("schema") != INTEGER_PLAN_KEYS[schema][3]
            or set(plan) != {"schema", "value", "abi", "raw", "inputs", "amounts", "helpers", "groups"}):
        raise ValueError("unsupported integer plan schema")
    shifts = schema == SHIFT_CASE_SCHEMA
    if plan["value"] not in INTEGER_TYPES + (("word",) if shifts else ()):
        raise ValueError("integer plan value type is outside the profile's types")
    if type(plan["abi"]) is not bool or type(plan["raw"]) is not bool or (shifts and (plan["abi"] or plan["raw"])):
        raise ValueError("integer plan parameter and result forms are outside the profile")
    groups = plan["groups"]
    if (not isinstance(groups, list) or not groups or any(not isinstance(group, dict) or set(group) != {"unchecked", "steps"}
                                                          or not isinstance(group["steps"], list) for group in groups)):
        raise ValueError("integer plan groups must be a nonempty list of contexts and steps")
    if not 1 <= sum(len(group["steps"]) for group in groups) <= 10:
        raise ValueError("integer plan requires one to ten steps")
    if not isinstance(plan["inputs"], list) or not 1 <= len(plan["inputs"]) <= 3:
        raise ValueError("integer plan requires one to three inputs")
    return plan


def validate_integer_shapes(values, schema) -> dict:
    """Native replay authenticates the shapes; Python checks their envelope."""
    label, dimensions = INTEGER_PLAN_KEYS[schema][1], INTEGER_PLAN_KEYS[schema][2]
    if not isinstance(values, dict) or set(values) != set(dimensions):
        raise ValueError(f"{label} must name every integer shape dimension")
    for key, allowed in dimensions.items():
        found = values[key]
        if (not isinstance(found, list) or any(not isinstance(v, str) or v not in allowed for v in found)
                or found != sorted(set(found))):
            raise ValueError(f"{label} {key} must be a sorted unique inventory of known shapes")
    return values


def integer_signature(case: dict) -> tuple[str, bytes]:
    """The checked arithmetic profile's run(T) when its plan takes the argument as its type."""
    plan = case.get(INTEGER_PLAN_KEYS[case["schema"]][0], {})
    parameter = plan.get("value") if case["schema"] == CHECKED_ARITHMETIC_CASE_SCHEMA and plan.get("abi") else "uint256"
    return f"run({parameter})", bytes.fromhex(RUN_SELECTORS[parameter])


def validate_array_plan(plan, schema) -> dict:
    """Validate the envelope, the element type and the counts; native replay checks every
    value, index, parameter and step against the profile and the seed."""
    if (not isinstance(plan, dict) or plan.get("schema") != ARRAY_PLAN_KEYS[schema][3]
            or set(plan) != {"schema", "element", "values", "indices", "params", "steps", "result"}):
        raise ValueError("unsupported array plan schema")
    if plan["element"] not in INTEGER_TYPES:
        raise ValueError("array plan element type is outside the profile's types")
    if not isinstance(plan["values"], list) or not 1 <= len(plan["values"]) <= 3:
        raise ValueError("array plan requires one to three values")
    if not isinstance(plan["indices"], list) or len(plan["indices"]) > 3:
        raise ValueError("array plan admits at most three indices")
    if not isinstance(plan["steps"], list) or not 1 <= len(plan["steps"]) <= 12:
        raise ValueError("array plan requires one to twelve steps")
    params = plan["params"]
    abi = schema == ARRAY_ABI_CASE_SCHEMA
    if (not isinstance(params, list) or not (1 <= len(params) <= 2 if abi else not params)
            or any(not isinstance(param, dict) or set(param) != {"calldata", "length", "offset", "raw"}
                   or type(param["calldata"]) is not bool or type(param["raw"]) is not bool for param in params)):
        raise ValueError("array plan parameters are outside the profile")
    if not abi and plan["result"] != "word":
        raise ValueError("a memory array plan returns its fold")
    return plan


def validate_array_shapes(values, schema) -> dict:
    """Native replay authenticates the shapes; Python checks their envelope."""
    label, dimensions = ARRAY_PLAN_KEYS[schema][1], ARRAY_PLAN_KEYS[schema][2]
    if not isinstance(values, dict) or set(values) != set(dimensions):
        raise ValueError(f"{label} must name every array shape dimension")
    for key, allowed in dimensions.items():
        found = values[key]
        if (not isinstance(found, list) or any(not isinstance(v, str) or v not in allowed for v in found)
                or found != sorted(set(found))):
            raise ValueError(f"{label} {key} must be a sorted unique inventory of known shapes")
    return values


def validate_closure_plan_envelope(plan, schema) -> dict:
    """Validate the envelope and the counts; native replay checks every statement, scope,
    factory and call against the profile and the seed."""
    if (not isinstance(plan, dict) or plan.get("schema") != CLOSURE_PLAN_KEYS[schema][3]
            or set(plan) != {"schema", "factories", "steps"}):
        raise ValueError("unsupported closure plan schema")
    if not isinstance(plan["steps"], list) or not 1 <= len(plan["steps"]) <= 10:
        raise ValueError("closure plan requires one to ten steps")
    factories = plan["factories"]
    if (not isinstance(factories, list)
            or not (1 <= len(factories) <= 2 if schema == CLOSURE_FACTORIES_CASE_SCHEMA else not factories)
            or any(not isinstance(factory, dict) or set(factory) != {"method", "body", "returns"}
                   or type(factory["method"]) is not bool for factory in factories)):
        raise ValueError("closure plan factories are outside the profile")
    return plan


def validate_closure_shapes(values, schema) -> dict:
    """Native replay authenticates the shapes; Python checks their envelope."""
    label, dimensions = CLOSURE_PLAN_KEYS[schema][1], CLOSURE_PLAN_KEYS[schema][2]
    if not isinstance(values, dict) or set(values) != set(dimensions):
        raise ValueError(f"{label} must name every closure shape dimension")
    for key, allowed in dimensions.items():
        found = values[key]
        if (not isinstance(found, list) or any(not isinstance(v, str) or v not in allowed for v in found)
                or found != sorted(set(found))):
            raise ValueError(f"{label} {key} must be a sorted unique inventory of known shapes")
    return values


def integer_convert(name: str, value: int) -> int:
    """A Word converted to an integer type as the generators convert it: its low bits,
    sign-extended for a signed type."""
    bits = int(name.lstrip("uint"))
    low = value % 2 ** bits
    if name.startswith("int") and low >= 2 ** (bits - 1):
        return (low - 2 ** bits) % 2 ** 256
    return low


def array_calldata(case: dict) -> tuple[str, bytes]:
    """An array plan's signature and calldata, encoded here independently of the case tool:
    run(uint256) and the input, or the ABI encoding of the parameters the input makes."""
    plan = case.get(ARRAY_PLAN_KEYS[case["schema"]][0], {})
    x = int(word(case.get("input"), "input"))
    params = plan.get("params", [])
    if not params:
        return "run(uint256)", bytes.fromhex("a444f5e9") + x.to_bytes(32, "big")
    element = plan["element"]
    lengths = []
    for param in params:
        length = param["length"]
        if set(length) == {"literal"} and type(length["literal"]) is int and 0 <= length["literal"] <= 4:
            lengths.append(length["literal"])
        elif (set(length) == {"shift", "mask"} and length["shift"] in (0, 1, 2, 3, 8, 128, 253)
              and length["mask"] in (1, 3, 7)):
            lengths.append((x >> length["shift"]) & length["mask"])
        else:
            raise ValueError("array parameter length is outside the profile")
    offsets, position, tails = [], 32 * (len(params) + 1), b""
    for param, length in zip(params, lengths):
        offsets.append(position)
        offset = int(word(param["offset"], "parameter offset"))
        items = [(x + offset + k) % 2 ** 256 for k in range(length)]
        items = items if param["raw"] else [integer_convert(element, item) for item in items]
        encoded = length.to_bytes(32, "big") + b"".join(item.to_bytes(32, "big") for item in items)
        tails += encoded
        position += len(encoded)
    signature = "run(" + ",".join([element + "[]"] * len(params) + ["uint256"]) + ")"
    head = b"".join(offset.to_bytes(32, "big") for offset in offsets) + x.to_bytes(32, "big")
    return signature, bytes.fromhex(ARRAY_SELECTORS[(element, len(params))]) + head + tails


def validate_call_graph_loop_plan(plan) -> dict:
    """Validate the envelope; native replay reseals the scalar graph and loop."""
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.call-graph-loop-plan.v1":
        raise ValueError("unsupported call-graph loop plan schema")
    if type(plan.get("mask")) is not int or plan["mask"] not in (0, 1, 3, 7):
        raise ValueError("loop mask must be zero, one, three or seven")
    if not isinstance(plan.get("stepProgram"), dict):
        raise ValueError("call-graph loop plan requires its original scalar step graph")
    return plan


def validate_assembly_loop_plan(plan) -> dict:
    """Validate the envelope; native replay reseals the scalar graph, loop and form."""
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.assembly-loop-plan.v1":
        raise ValueError("unsupported assembly loop plan schema")
    if type(plan.get("mask")) is not int or plan["mask"] not in (0, 1, 3, 7):
        raise ValueError("loop mask must be zero, one, three or seven")
    if plan.get("form") not in ASSEMBLY_LOOP_FORMS:
        raise ValueError("assembly loop form must be for, break, continue, leave or pair")
    if not isinstance(plan.get("stepProgram"), dict):
        raise ValueError("assembly loop plan requires its original scalar step graph")
    return plan


def validate_generic_plan(plan) -> dict:
    """Check the transport envelope; native replay authenticates the full plan."""
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.generic-plan.v1":
        raise ValueError("unsupported generic plan schema")
    if plan.get("variant") not in ("word", "pair", "sum"):
        raise ValueError("generic variant must be word, pair or sum")
    if not isinstance(plan.get("stepProgram"), dict):
        raise ValueError("generic plan requires its original step function graph")
    return plan


def validate_closure_plan(plan) -> dict:
    """Admit the fixed capture recipes; native replay reconstructs all closures."""
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.closure-plan.v1":
        raise ValueError("unsupported closure plan schema")
    if plan.get("variant") not in ("snapshot", "independent"):
        raise ValueError("closure variant must be snapshot or independent")
    if not isinstance(plan.get("stepProgram"), dict):
        raise ValueError("closure plan requires its original step function graph")
    return plan


def validate_comptime_plan(plan) -> dict:
    """Keep both original ASTs; evaluated constants are not reference programs."""
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.comptime-plan.v1":
        raise ValueError("unsupported comptime plan schema")
    if plan.get("variant") not in ("offset", "scale"):
        raise ValueError("comptime variant must be offset or scale")
    if not isinstance(plan.get("stepProgram"), dict) or not isinstance(plan.get("constantProgram"), dict):
        raise ValueError("comptime plan requires its original constant and step programs")
    return plan


def validate_module_plan(plan) -> dict:
    if not isinstance(plan, dict) or plan.get("schema") != "solcore-lean.module-plan.v1":
        raise ValueError("unsupported module plan schema")
    if not isinstance(plan.get("stepProgram"), dict) or not isinstance(plan.get("constantProgram"), dict):
        raise ValueError("module plan requires its original constant and step programs")
    return plan


def validate_call_shapes(values, label="callShapes") -> list[str]:
    """Native replay authenticates these AST labels; Python checks their envelope."""
    if (not isinstance(values, list) or any(not isinstance(v, str) or v not in CALL_SHAPES for v in values)
            or values != [v for v in CALL_SHAPES if v in values]):
        raise ValueError(f"{label} must be a canonical unique call-shape inventory")
    return values


def validate_aggregate_shapes(values, label="aggregateShapes") -> list[str]:
    """Native replay authenticates these AST labels; Python checks their envelope."""
    if (not isinstance(values, list) or any(not isinstance(v, str) or v not in AGGREGATE_SHAPES for v in values)
            or values != [v for v in AGGREGATE_SHAPES if v in values]):
        raise ValueError(f"{label} must be a canonical unique aggregate-shape inventory")
    return values


def validate_case(case: dict) -> None:
    if not isinstance(case, dict) or case.get("schema") not in CASE_PROFILES:
        raise ValueError("unsupported semantic case schema")
    if not isinstance(case.get("program"), dict) or not isinstance(case.get("source"), str):
        raise ValueError("case requires its original Core program and emitted source")
    if case["schema"] == LOOP_CASE_SCHEMA:
        validate_loop_plan(case.get("loopPlan"))
    if case["schema"] == NESTED_LOOP_CASE_SCHEMA:
        validate_nested_loop_plan(case.get("nestedLoopPlan"))
    if case["schema"] == RECURSION_CASE_SCHEMA:
        validate_recursion_plan(case.get("recursionPlan"))
    if case["schema"] == RECURSIVE_LOOP_CASE_SCHEMA:
        validate_recursive_loop_plan(case.get("recursiveLoopPlan"))
    if case["schema"] == LOOP_CLOSURE_CASE_SCHEMA:
        validate_loop_closure_plan(case.get("loopClosurePlan"))
    if case["schema"] == ASSEMBLY_CASE_SCHEMA:
        validate_assembly_plan(case.get("assemblyPlan"))
    if case["schema"] == ASSEMBLY_MEMORY_CASE_SCHEMA:
        validate_assembly_memory_plan(case.get("assemblyMemoryPlan"))
    if case["schema"] == ENUM_CASE_SCHEMA:
        validate_enum_plan(case.get("enumPlan"))
    if case["schema"] == TRAIT_CASE_SCHEMA:
        validate_trait_plan(case.get("traitPlan"))
    if case["schema"] == HIERARCHY_CASE_SCHEMA:
        validate_hierarchy_plan(case.get("hierarchyPlan"))
    if case["schema"] == MEMORY_CASE_SCHEMA:
        validate_memory_plan(case.get("memoryValuePlan"))
    if case["schema"] == MEMORY_CALL_CASE_SCHEMA:
        validate_memory_call_plan(case.get("memoryCallPlan"))
    if case["schema"] == REVERT_DATA_CASE_SCHEMA:
        validate_revert_data_plan(case.get("revertDataPlan"))
    if case["schema"] == HALT_CASE_SCHEMA:
        validate_halt_plan(case.get("haltPlan"))
    if case["schema"] in INTEGER_PLAN_KEYS:
        validate_integer_plan(case.get(INTEGER_PLAN_KEYS[case["schema"]][0]), case["schema"])
    if case["schema"] in ARRAY_PLAN_KEYS:
        validate_array_plan(case.get(ARRAY_PLAN_KEYS[case["schema"]][0]), case["schema"])
    if case["schema"] in CLOSURE_PLAN_KEYS:
        validate_closure_plan_envelope(case.get(CLOSURE_PLAN_KEYS[case["schema"]][0]), case["schema"])
    if case["schema"] == CALL_GRAPH_LOOP_CASE_SCHEMA:
        validate_call_graph_loop_plan(case.get("loopPlan"))
    if case["schema"] == ASSEMBLY_LOOP_CASE_SCHEMA:
        validate_assembly_loop_plan(case.get("assemblyLoopPlan"))
    if case["schema"] == GENERIC_CASE_SCHEMA:
        validate_generic_plan(case.get("genericPlan"))
    if case["schema"] == CLOSURE_CASE_SCHEMA:
        validate_closure_plan(case.get("closurePlan"))
    if case["schema"] == COMPTIME_CASE_SCHEMA:
        validate_comptime_plan(case.get("comptimePlan"))
    if case["schema"] == MODULE_CASE_SCHEMA:
        validate_module_plan(case.get("modulePlan"))
        bundle_transport.validate(case)
    elif "sourceBundle" in case:
        raise ValueError("source bundles are only admitted by the module profile")
    provenance = case.get("provenance")
    if not isinstance(provenance, dict):
        raise ValueError("case provenance is missing")
    for key in ("generatorVersion", "emitterVersion", "wrapperVersion"):
        if not isinstance(provenance.get(key), str) or not provenance[key]:
            raise ValueError(f"missing provenance {key}")
    if case["schema"] in (PRIMITIVE_CASE_SCHEMA, ASSEMBLY_CASE_SCHEMA, ASSEMBLY_MEMORY_CASE_SCHEMA):
        for key in ("profileVersion", "functionVersion", "abstractionVersion",
                    "baseGeneratorVersion", "boundaryVersion",
                    *(("functionProfileVersion",) if case["schema"] != PRIMITIVE_CASE_SCHEMA else ()),
                    *(("memoryVersion",) if case["schema"] == ASSEMBLY_MEMORY_CASE_SCHEMA else ())):
            if not isinstance(provenance.get(key), str) or not provenance[key]:
                raise ValueError(f"missing primitive provenance {key}")
    if case["schema"] in (CALL_GRAPH_CASE_SCHEMA, CALL_GRAPH_LOOP_CASE_SCHEMA, ASSEMBLY_LOOP_CASE_SCHEMA):
        versions = {CALL_GRAPH_CASE_SCHEMA: CALL_GRAPH_VERSIONS, CALL_GRAPH_LOOP_CASE_SCHEMA: CALL_GRAPH_LOOP_VERSIONS,
                    ASSEMBLY_LOOP_CASE_SCHEMA: ASSEMBLY_LOOP_VERSIONS}[case["schema"]]
        for key in versions:
            if not isinstance(provenance.get(key), str) or not provenance[key]:
                raise ValueError(f"missing call-graph provenance {key}")
        if type(provenance.get("helperCount")) is not int or not 1 <= provenance["helperCount"] <= 3:
            raise ValueError("call-graph helperCount must be an integer from one to three")
        validate_call_shapes(provenance.get("callShapes"))
    if case["schema"] == AGGREGATE_CALL_GRAPH_CASE_SCHEMA:
        for key in AGGREGATE_CALL_GRAPH_VERSIONS:
            if not isinstance(provenance.get(key), str) or not provenance[key]:
                raise ValueError(f"missing aggregate call-graph provenance {key}")
        if type(provenance.get("helperCount")) is not int or not 1 <= provenance["helperCount"] <= 3:
            raise ValueError("aggregate call-graph helperCount must be an integer from one to three")
        validate_aggregate_shapes(provenance.get("aggregateShapes"))
    if case["schema"] == ENUM_CASE_SCHEMA:
        for key in ENUM_VERSIONS:
            if not isinstance(provenance.get(key), str) or not provenance[key]:
                raise ValueError(f"missing enum provenance {key}")
        if type(provenance.get("referenceNodes")) is not int or not 1 <= provenance["referenceNodes"] <= 4096:
            raise ValueError("enum referenceNodes must be an integer from 1 to 4,096")
        validate_enum_shapes(provenance.get("enumShapes"))
    if case["schema"] == TRAIT_CASE_SCHEMA:
        for key in TRAIT_VERSIONS:
            if not isinstance(provenance.get(key), str) or not provenance[key]:
                raise ValueError(f"missing trait provenance {key}")
        if type(provenance.get("referenceNodes")) is not int or not 1 <= provenance["referenceNodes"] <= 4096:
            raise ValueError("trait referenceNodes must be an integer from 1 to 4,096")
        validate_trait_shapes(provenance.get("traitShapes"))
    if case["schema"] == HIERARCHY_CASE_SCHEMA:
        for key in HIERARCHY_VERSIONS:
            if not isinstance(provenance.get(key), str) or not provenance[key]:
                raise ValueError(f"missing trait hierarchy provenance {key}")
        if type(provenance.get("referenceNodes")) is not int or not 1 <= provenance["referenceNodes"] <= 4096:
            raise ValueError("trait hierarchy referenceNodes must be an integer from 1 to 4,096")
        validate_hierarchy_shapes(provenance.get("hierarchyShapes"))
    if case["schema"] == MEMORY_CASE_SCHEMA:
        for key in MEMORY_VERSIONS:
            if not isinstance(provenance.get(key), str) or not provenance[key]:
                raise ValueError(f"missing memory value provenance {key}")
        if type(provenance.get("referenceNodes")) is not int or not 1 <= provenance["referenceNodes"] <= 5120:
            raise ValueError("memory value referenceNodes must be an integer from 1 to 5,120")
        validate_memory_shapes(provenance.get("memoryValueShapes"))
    if case["schema"] == MEMORY_CALL_CASE_SCHEMA:
        for key in MEMORY_CALL_VERSIONS:
            if not isinstance(provenance.get(key), str) or not provenance[key]:
                raise ValueError(f"missing memory call provenance {key}")
        if type(provenance.get("referenceNodes")) is not int or not 1 <= provenance["referenceNodes"] <= 5120:
            raise ValueError("memory call referenceNodes must be an integer from 1 to 5,120")
        validate_memory_call_shapes(provenance.get("memoryCallShapes"))
    if case["schema"] == REVERT_DATA_CASE_SCHEMA:
        for key in REVERT_DATA_VERSIONS:
            if not isinstance(provenance.get(key), str) or not provenance[key]:
                raise ValueError(f"missing revert data provenance {key}")
        if type(provenance.get("referenceNodes")) is not int or not 1 <= provenance["referenceNodes"] <= 4096:
            raise ValueError("revert data referenceNodes must be an integer from 1 to 4,096")
        validate_revert_data_shapes(provenance.get("revertDataShapes"))
    if case["schema"] == HALT_CASE_SCHEMA:
        for key in HALT_VERSIONS:
            if not isinstance(provenance.get(key), str) or not provenance[key]:
                raise ValueError(f"missing halt provenance {key}")
        if type(provenance.get("referenceNodes")) is not int or not 1 <= provenance["referenceNodes"] <= 4096:
            raise ValueError("halt referenceNodes must be an integer from 1 to 4,096")
        validate_revert_data_shapes(provenance.get("haltShapes"), "haltShapes", HALT_SHAPES)
    if case["schema"] in INTEGER_PLAN_KEYS:
        for key in INTEGER_VERSIONS:
            if not isinstance(provenance.get(key), str) or not provenance[key]:
                raise ValueError(f"missing integer provenance {key}")
        if type(provenance.get("referenceNodes")) is not int or not 1 <= provenance["referenceNodes"] <= 4096:
            raise ValueError("integer referenceNodes must be an integer from 1 to 4,096")
        validate_integer_shapes(provenance.get(INTEGER_PLAN_KEYS[case["schema"]][1]), case["schema"])
    if case["schema"] in ARRAY_PLAN_KEYS:
        for key in ARRAY_VERSIONS:
            if not isinstance(provenance.get(key), str) or not provenance[key]:
                raise ValueError(f"missing array provenance {key}")
        if type(provenance.get("referenceNodes")) is not int or not 1 <= provenance["referenceNodes"] <= 4096:
            raise ValueError("array referenceNodes must be an integer from 1 to 4,096")
        validate_array_shapes(provenance.get(ARRAY_PLAN_KEYS[case["schema"]][1]), case["schema"])
    if case["schema"] in CLOSURE_PLAN_KEYS:
        for key in CLOSURE_VERSIONS:
            if not isinstance(provenance.get(key), str) or not provenance[key]:
                raise ValueError(f"missing closure provenance {key}")
        if type(provenance.get("referenceNodes")) is not int or not 1 <= provenance["referenceNodes"] <= 4096:
            raise ValueError("closure referenceNodes must be an integer from 1 to 4,096")
        validate_closure_shapes(provenance.get(CLOSURE_PLAN_KEYS[case["schema"]][1]), case["schema"])
    contract = case.get("contract", {})
    if not isinstance(contract, dict):
        raise ValueError("case contract metadata is missing")
    name = CASE_CONTRACTS[case["schema"]]
    if case["schema"] in INTEGER_PLAN_KEYS:
        signature, selector = integer_signature(case)
        calldata = selector + int(word(case.get("input"), "input")).to_bytes(32, "big")
    elif case["schema"] in ARRAY_PLAN_KEYS:
        signature, calldata = array_calldata(case)
    elif case["schema"] != CASE_SCHEMA:
        signature = "run(uint256)"
        calldata = bytes.fromhex("a444f5e9") + int(word(case.get("input"), "input")).to_bytes(32, "big")
    else:
        signature = "run()"
        calldata = bytes.fromhex("c0406226")
    if (contract.get("name"), contract.get("method"), contract.get("signature")) != (name, "run", signature):
        raise Finding("unsupported-scope", "input", "contract wrapper differs from its case profile")
    if contract.get("deployPath") != [name + "Deploy"] or contract.get("runtimePath") != [name + "Deploy", name]:
        raise ValueError("unexpected generated object paths")
    if hex_bytes(contract.get("calldata"), "calldata") != calldata:
        raise ValueError("calldata differs from the profile selector and original Core input")
    if hex_bytes(contract.get("constructorCalldata"), "constructorCalldata"):
        raise Finding("unsupported-scope", "input", "constructor arguments are outside the initial profile")


def validate_replayed_case(case: dict, fresh: dict) -> None:
    """Native replay authenticates source and program; saved output is no oracle."""
    validate_case(fresh)
    for key in ("program", "source", "provenance", "contract", "input", "loopPlan", "nestedLoopPlan", "recursionPlan", "recursiveLoopPlan", "loopClosurePlan", "assemblyPlan", "assemblyMemoryPlan", "assemblyLoopPlan", "enumPlan", "traitPlan", "hierarchyPlan", "memoryValuePlan", "memoryCallPlan", "revertDataPlan", "haltPlan", "checkedArithmeticPlan", "shiftPlan", "memoryArrayPlan", "arrayAbiPlan", "closureCapturesPlan", "closureFactoriesPlan", "genericPlan", "closurePlan", "comptimePlan", "modulePlan", "sourceBundle"):
        if fresh.get(key) != case.get(key):
            raise ValueError(f"case replay changed {key}")


def normalize_observation(row: dict, *, direct: bool = False, outputs: bool = False) -> dict:
    """With `outputs`, for a profile whose original Core returns data, a direct row's return
    data is normalized as the EVM's is."""
    if not isinstance(row, dict) or row.get("stage") != "execution":
        raise ValueError("missing execution observation")
    status = row.get("status")
    if status == "returned":
        if direct and not outputs:
            result = word(row.get("word"))
        else:
            data = hex_bytes(row.get("output"), "return data")
            if len(data) != 32:
                return {"status": status, "output": "0x" + data.hex()}
            result = str(int.from_bytes(data, "big"))
        return {"status": status, "word": result}
    if status == "reverted":
        return {"status": status, "output": "0x" + hex_bytes(row.get("output"), "revert data").hex()}
    if not isinstance(status, str):
        raise ValueError("missing execution status")
    return {"status": status, "detail": row.get("detail", "")}


def compare(observations: dict, *, reverts: bool = False, halts: bool = False) -> dict:
    """Classify only actual completed observations, never missing paths as equal.
    Three returned observations with the same payload match; with `reverts`, for a
    profile whose original Core can revert, so do three reverts with the same data;
    with `halts`, for a profile whose original Core can halt, so do three INVALID
    halts. Resource exhaustion on any path stays inconclusive."""
    names = ("directCore", "importedHull", "rustEvm")
    if set(observations) != set(names):
        return {"category": "adapter-error", "detail": "three observations are required", "pairs": {}}
    rows = [observations[name] for name in names]
    completed = []
    try:
        for row in rows:
            if row.get("status") == "returned":
                if ("word" in row) == ("output" in row):
                    raise ValueError("a returned observation requires exactly one payload")
                data = (int(word(row["word"])).to_bytes(32, "big") if "word" in row
                        else hex_bytes(row["output"], "return data"))
                completed.append(("returned", data))
            elif row.get("status") == "reverted":
                completed.append(("reverted", hex_bytes(row.get("output"), "revert data")))
            elif halts and row.get("status") == "invalid":
                completed.append(("invalid", b""))
            else:
                completed.append(None)
    except (AttributeError, ValueError):
        return {"category": "adapter-error", "detail": "malformed completed observation", "pairs": {}}
    statuses = [row.get("status") for row in rows]
    if any(status in {"out-of-fuel", "out-of-gas", "timeout", "output-limit", "resource-limit"} for status in statuses):
        return {"category": "inconclusive-resource", "pairs": {}}
    if any(status not in COMPLETED | (HALTED if halts else set()) for status in statuses):
        return {"category": "execution-error", "pairs": {}}
    pairs = {f"{names[left]}/{names[right]}": completed[left] == completed[right]
             for left, right in ((0, 2), (0, 1), (1, 2))}
    agreed = (all(status == "returned" for status in statuses) or (reverts and all(status == "reverted" for status in statuses))
              or (halts and all(status == "invalid" for status in statuses)))
    return {"category": "matched" if all(pairs.values()) and agreed else "semantic-mismatch", "pairs": pairs}


def core_rows(stdout: str, exit_code: int) -> list[dict]:
    rows = [json.loads(line) for line in stdout.splitlines() if line.strip()]
    if exit_code not in (0, 1) or not rows or any(not isinstance(row, dict) for row in rows):
        raise ValueError("invalid Core scenario process result")
    if rows[-1].get("stage") == "preparation" and rows[-1].get("status") == "rejected":
        detail = rows[-1].get("detail", "Core preparation rejected")
        raise Finding("inconclusive-resource" if RESOURCE.search(str(detail)) else "compilation-rejected", "core-preparation", detail)
    if rows[0].get("stage") != "deployment":
        raise ValueError("missing Core deployment result")
    if rows[0].get("status") != "returned":
        status = rows[0].get("status")
        category = "inconclusive-resource" if status == "out-of-fuel" else "execution-error"
        raise Finding(category, "core-deployment", json.dumps(rows[0]))
    if len(rows) != 2 or rows[1].get("stage") != "execution" or rows[1].get("index") != 0:
        raise ValueError("expected exactly one ordered Core call after deployment")
    if exit_code != 0 and rows[1].get("status") in {"returned", "reverted", "invalid"}:
        raise ValueError("unexplained Core process failure after completed result")
    return rows


def signal_group(process: subprocess.Popen, signum: int) -> None:
    # macOS can reject killpg with EPERM once the group holds only exited,
    # unreaped members; then signal the leader directly if it still runs.
    try:
        os.killpg(process.pid, signum)
    except PermissionError:
        if process.poll() is None:
            process.send_signal(signum)
    except ProcessLookupError:
        pass


def stop_process(process: subprocess.Popen) -> None:
    # Each process owns a new session. Also stop descendants if its leader has
    # already exited; never signal a shared shell or unrelated Lean process.
    signal_group(process, signal.SIGTERM)
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired:
        pass
    signal_group(process, signal.SIGKILL)
    process.wait(timeout=2)


class Runner:
    def __init__(self, args, report):
        self.args, self.report = args, report
        self.deadline = time.monotonic() + args.total_timeout

    def guard(self) -> None:
        guard = getattr(self.args, "resource_guard", None)
        if guard is not None:
            guard()

    def remaining(self, timeout: float) -> float:
        self.guard()
        left = min(timeout, self.deadline - time.monotonic())
        if left <= 0:
            raise Finding("inconclusive-resource", "runner", "total time budget exhausted")
        return left

    def process(self, stage: str, command: list[str], timeout: float | None = None) -> dict:
        started = time.monotonic()
        budget = self.remaining(timeout or self.args.timeout)
        with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
            process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.DEVNULL,
                                       stdout=stdout, stderr=stderr, start_new_session=True)
            reason = None
            try:
                while process.poll() is None:
                    self.guard()
                    if time.monotonic() - started >= budget:
                        reason = "timeout"
                        break
                    if stdout.tell() + stderr.tell() > self.args.output_limit:
                        reason = "output-limit"
                        break
                    time.sleep(0.05)
            finally:
                stop_process(process)
            if stdout.tell() + stderr.tell() > self.args.output_limit:
                reason = "output-limit"
            stdout.seek(0)
            stderr.seek(0)
            result = {"stage": stage, "command": command, "returncode": process.returncode,
                      "elapsedSeconds": round(time.monotonic() - started, 3),
                      "stdout": stdout.read(self.args.output_limit).decode(errors="replace"),
                      "stderr": stderr.read(self.args.output_limit).decode(errors="replace")}
        if reason:
            result["resourceFailure"] = reason
        self.report["processes"].append(result)
        self.guard()
        if reason:
            raise Finding("inconclusive-resource", stage, reason)
        return result

    def identity(self, path: Path, version=False) -> dict:
        path = path.resolve(strict=True)
        self.guard()
        result = {"path": str(path), "sha256": tool_digest(self.args, path)}
        self.guard()
        if version:
            cache = getattr(self.args, "digest_cache", None)
            key = None if cache is None else cache.key(path)
            outcome = None if cache is None else cache.versions.get(key)
            if outcome is not None:
                self.report["processes"].append({**outcome, "reused": True})
            else:
                outcome = self.process("tool-version", [str(path), "--version"], 10)
                if cache is not None and not outcome["returncode"] and cache.key(path) == key:
                    cache.versions[key] = outcome
            if outcome["returncode"]:
                raise Finding("adapter-error", "tool-version", str(path))
            result["version"] = outcome["stdout"].strip()
        return result


class Rpc:
    def __init__(self, url: str, runner: Runner):
        self.url, self.runner, self.counter = url, runner, 0
        # A local chain must not be routed through HTTP_PROXY/HTTPS_PROXY.
        self.opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))

    def call(self, method: str, params):
        self.runner.guard()
        self.counter += 1
        payload = {"jsonrpc": "2.0", "id": self.counter, "method": method, "params": params}
        request = urllib.request.Request(self.url, json_bytes(payload), {"Content-Type": "application/json"})
        with self.opener.open(request, timeout=self.runner.remaining(10)) as response:
            content = response.read(self.runner.args.output_limit + 1)
        self.runner.guard()
        if len(content) > self.runner.args.output_limit:
            raise Finding("inconclusive-resource", "evm-rpc", "RPC output limit")
        result = json.loads(content)
        if result.get("id") != self.counter or result.get("jsonrpc") != "2.0":
            raise ValueError("invalid JSON-RPC response")
        if "error" in result:
            raise RpcError(result["error"])
        if "result" not in result:
            raise ValueError("missing JSON-RPC result")
        return result["result"]


@contextmanager
def anvil(runner: Runner, binary: Path, *, steps_tracing: bool = False):
    command = [str(binary), "--host", "127.0.0.1", "--port", "0", "--hardfork", "osaka",
               "--chain-id", "31337", "--timestamp", "1700000000", "--gas-limit", str(max(30000000, runner.args.gas))]
    if steps_tracing:
        command.append("--steps-tracing")
    budget = runner.remaining(runner.args.startup_timeout)
    with tempfile.TemporaryFile() as log:
        process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.DEVNULL, stdout=log,
                                   stderr=log, start_new_session=True)
        start = time.monotonic()
        try:
            while True:
                runner.guard()
                contents = os.pread(log.fileno(), runner.args.output_limit + 1, 0)
                if len(contents) > runner.args.output_limit:
                    raise Finding("inconclusive-resource", "anvil-startup", "output limit")
                matched = re.search(rb"Listening on (127\.0\.0\.1:\d+)", contents)
                if matched:
                    rpc = Rpc("http://" + matched[1].decode(), runner)
                    runner.report["evmConfiguration"] = {
                        "command": command, "url": rpc.url, "hardfork": "osaka", "chainId": "31337",
                        "timestamp": 1700000000, "gas": runner.args.gas,
                        "clientVersion": rpc.call("web3_clientVersion", [])}
                    yield rpc
                    break
                if process.poll() is not None:
                    raise Finding("adapter-error", "anvil-startup", contents.decode(errors="replace"))
                if time.monotonic() - start >= budget:
                    raise Finding("inconclusive-resource", "anvil-startup", "startup timeout")
                time.sleep(0.05)
        finally:
            stop_process(process)
            runner.report["anvilLog"] = os.pread(log.fileno(), runner.args.output_limit, 0).decode(errors="replace")


def evm_failure(error: RpcError) -> dict:
    message = str(error.error.get("message", "")) if isinstance(error.error, dict) else str(error.error)
    if GAS_RESOURCE.search(message):
        return {"stage": "execution", "status": "out-of-gas", "detail": message}
    if RESOURCE.search(message):
        return {"stage": "execution", "status": "resource-limit", "detail": message}
    data = error.error.get("data") if isinstance(error.error, dict) else None
    if "revert" in message.lower() and isinstance(data, str):
        return {"stage": "execution", "status": "reverted", "output": "0x" + hex_bytes(data, "RPC revert data").hex()}
    return {"stage": "execution", "status": "evm-exceptional", "detail": message, "rpcError": error.error}


# Anvil names an exceptional halt after revm's instruction result: INVALID (0xFE) is
# `InvalidFEOpcode`, an undefined opcode `OpcodeNotFound`, and gas exhaustion
# `OutOfGas` or a name ending in `OOG`, such as `InvalidOperandOOG` for a memory
# offset past any gas.
EVM_HALT = re.compile(r"EVM error (\w+)")


def evm_halt(observation: dict) -> dict:
    """An exceptional EVM observation classified by its halt, for a profile that
    compares halts: INVALID is `invalid`, any gas exhaustion `out-of-gas`, and
    every other halt stays `evm-exceptional`."""
    halt = EVM_HALT.fullmatch(observation.get("detail", "")) if observation.get("status") == "evm-exceptional" else None
    if halt is None:
        return observation
    if halt[1] == "InvalidFEOpcode":
        return {**observation, "status": "invalid"}
    if halt[1] == "OutOfGas" or halt[1].endswith("OOG"):
        return {**observation, "status": "out-of-gas"}
    return observation


def deployment_failure(error: RpcError) -> Finding:
    failure = evm_failure(error)
    if failure["status"] in {"out-of-gas", "resource-limit"}:
        category = "inconclusive-resource"
    elif isinstance(error.error, dict) and error.error.get("code") in {-32700, -32600, -32601, -32602}:
        category = "adapter-error"
    else:
        category = "execution-error"
    return Finding(category, "evm-deployment", str(error))


def image_bytes(images: dict, path: list[str]) -> bytes:
    if images.get("schema") != "solcore-rs.code-images.v1" or images.get("upstreamCommit") != UPSTREAM_COMMIT:
        raise ValueError("code image schema/revision differs from pinned reference")
    found = [item for item in images.get("images", []) if item.get("path") == path]
    if len(found) != 1:
        raise ValueError(f"expected one exact code image: {path}")
    return hex_bytes(found[0].get("bytes"), "code image")


def validate_export(hull_path: Path, image_path: Path, source: Path, limit: int,
                    backend: str = "sonatina-o0", compiled: Path | None = None) -> dict:
    """`compiled` is where a shared compilation read `source`'s exact bytes."""
    hull = read_json(hull_path, limit)
    images = read_json(image_path, limit)
    validate_image_backend(images, backend)
    hp = read_json(hull_path.with_suffix(".json.provenance.json"), limit)
    ip = read_json(image_path.with_suffix(".json.provenance.json"), limit)
    if hull.get("schema") != "solcore-rs.hull.v1" or hull.get("upstreamCommit") != UPSTREAM_COMMIT:
        raise ValueError("Hull schema/revision differs from pinned reference")
    if hp.get("outputSha256") != file_digest(hull_path) or ip.get("outputSha256") != file_digest(image_path):
        raise ValueError("export artifact hash mismatch")
    if ip.get("hullProvenance") != hp or ip.get("sources") != hp.get("sources"):
        raise ValueError("Hull/image provenance differs")
    if ip.get("backendRevision") != BACKEND_COMMIT or ip.get("optimization") != optimization_for_backend(backend):
        raise ValueError("backend revision/optimization differs")
    if hp.get("sources", {}).get((compiled or source).as_uri()) != file_digest(source):
        raise ValueError("source hash differs from exported artifact")
    return {"hull": hp, "images": ip}


def checked_process(runner: Runner, stage: str, command: list[str], timeout=None) -> dict:
    result = runner.process(stage, command, timeout)
    if result["returncode"]:
        detail = result["stderr"] + result["stdout"]
        if RESOURCE.search(detail):
            category = "inconclusive-resource"
        elif result["returncode"] < 0 or re.search(r"panicked at|internal compiler error|backtrace:", detail, re.I):
            category = "compiler-crash" if stage.startswith("rust-") else "adapter-error"
        elif stage == "direct-core-replay":
            category = "unsupported-scope" if "unsupported" in detail.lower() else "adapter-error"
        elif (stage == "rust-checked-source" and detail.startswith("export-rust-hull:")) or any(
                text in detail for text in ("receipt is stale", "receipt;", "rebuild with", "unexpected code image schema", "source files changed")):
            category = "adapter-error"
        else:
            category = "source-rejected" if stage == "rust-checked-source" else "compilation-rejected"
        raise Finding(category, stage, detail)
    return result


def export_sources(args, runner: Runner, directory: Path, source: Path, linked_backend: str, audit) -> None:
    """Export checked Hull and linked code images for the sources in `directory`."""
    hull_path, image_path = directory / "hull.json", directory / "images.json"
    common = [str(source), "--root", str(directory), "--upstream", str(args.upstream), "--target-dir", str(args.target_dir)]
    audit()
    checked_process(runner, "rust-checked-source", [sys.executable, str(ROOT / "scripts/export-rust-hull.py"), *common, "--output", str(hull_path)])
    audit()
    checked_process(runner, "rust-code-images", [sys.executable, str(ROOT / "scripts/export-rust-code-image.py"), *common,
        "--output", str(image_path), "--hull-output", str(hull_path), "--timeout", str(args.timeout),
        "--optimization", optimization_for_backend(linked_backend)], args.timeout * 3)
    audit()


def compile_identity(args, report: dict, backend: str, names: tuple[str, ...]) -> dict:
    """Everything a compilation reads, by digest: the case's own source files, the
    backend, the library, the exporters and both compiler builds."""
    target, library = Path(args.target_dir), Path(args.upstream) / "std"
    identity = {"schema": COMPILATION_SCHEMA, "backend": backend,
        "imageOptimization": optimization_for_backend(image_backend(backend)),
        "sources": {name: file_digest(args.output / name) for name in names},
        "library": {path.relative_to(library).as_posix(): tool_digest(args, path) for path in sorted(library.rglob("*.sol"))},
        "upstream": str(args.upstream), "targetDir": str(args.target_dir), "python": sys.executable,
        "runnerSha256": report["tools"]["runnerSha256"], "exporters": report["tools"]["exporters"],
        "compilers": {name: tool_digest(args, target / name) for name in COMPILERS}}
    if "bundleTransportSha256" in report["tools"]:
        identity["bundleTransportSha256"] = report["tools"]["bundleTransportSha256"]
    if backend == "yul":
        identity["yul"] = {key: report["tools"][key] for key in ("solc", "yulExporterSha256", "yulTransportSha256")}
    return identity


def accept_yul(args, case: dict, report: dict, expected: dict) -> tuple[bytes, bytes]:
    """Check a copied shared Yul export as this case's own evidence."""
    record = yul_transport("validate_export", args.output, case["contract"]["name"],
                           report["exportProvenance"]["hull"], args.artifact_limit)
    yul_transport("validate_tool_record", record, report["tools"])
    if record != expected:
        raise ValueError("copied Yul export differs from its shared compilation")
    report["yulExportProvenance"] = record
    artifact = read_json(args.output / "yul.json", args.artifact_limit)
    return hex_bytes(artifact["initCode"], "Yul init code"), hex_bytes(artifact["runtimeCode"], "Yul runtime code")


def shared_compilations(args):
    """A campaign's shared compilations; exact replay always compiles its own case."""
    return None if args.replay else getattr(args, "compile_cache", None)


class CompileCache:
    """Compilations shared within one campaign by cases whose source bytes,
    backend and compiler tools are identical by digest.

    A compilation runs once, in a directory named by the digest of that
    identity, so every case reusing it saw the same paths. Each case copies all
    of its outputs into its own run directory, keeping its archive
    self-contained, and records the shared compiler processes. A rejection or
    crash is shared the same way; a resource or adapter failure is not kept, so
    the next case compiles again. Exact replay never uses a cache. The least
    recently used compilations beyond `capacity` are deleted.
    """

    def __init__(self, directory: Path, capacity: int = 8):
        self.directory, self.capacity = directory, capacity
        self.entries: dict[str, dict] = {}

    def compile(self, args, runner: Runner, case: dict, report: dict, backend: str, receipt: dict | None, audit) -> dict:
        names = bundle_transport.FILES if receipt is not None else ("case.sol",)
        identity = compile_identity(args, report, backend, names)
        key = digest(json_bytes(identity))
        entry = self.entries.pop(key, None)
        reused = entry is not None
        if entry is None:
            entry = self.build(key, args, runner, case, report, backend, receipt, names, audit)
        self.entries[key] = entry
        while len(self.entries) > self.capacity:
            shutil.rmtree(self.entries.pop(next(iter(self.entries)))["directory"], ignore_errors=True)
        report["compilation"] = {"schema": COMPILATION_SCHEMA, "key": key, "identity": identity,
            "directory": str(entry["directory"]), "reused": reused, "outputs": dict(entry["outputs"])}
        if reused:
            report["processes"].extend({**process, "reused": True} for process in entry["processes"])
        for name, expected in entry["outputs"].items():
            shutil.copyfile(entry["directory"] / name, args.output / name)
            if file_digest(args.output / name) != expected:
                raise ValueError("shared compilation output changed: " + name)
        if entry["failure"] is not None:
            report["compilation"]["failure"] = {field: entry["failure"][field] for field in ("category", "stage")}
        return entry

    @staticmethod
    def fail(entry: dict, yul: bool = False) -> None:
        """Raise a shared failure where its stage would have raised it: a Yul
        export failure after the copied Sonatina exports are checked, others at once."""
        failure = entry["failure"]
        if failure is not None and (failure["stage"] == "rust-yul-evm") == yul:
            raise Finding(**failure)

    def build(self, key: str, args, runner: Runner, case: dict, report: dict, backend: str,
              receipt: dict | None, names: tuple[str, ...], audit) -> dict:
        directory = self.directory / key
        shutil.rmtree(directory, ignore_errors=True)
        directory.mkdir(parents=True)
        source, linked_backend = directory / "case.sol", image_backend(backend)
        if receipt is not None:
            receipt = {**bundle_transport.write(directory, case), "libraries": receipt["libraries"]}
        else:
            source.write_text(case["source"])
        first, failure, yul = len(report["processes"]), None, None
        try:
            export_sources(args, runner, directory, source, linked_backend, lambda: audit(directory))
            if backend == "yul":
                hull = directory / "hull.json"
                shared = {"backend": backend, "pathBackends": report["pathBackends"], "tools": report["tools"],
                          "exportProvenance": validate_export(hull, directory / "images.json", source,
                                                              args.artifact_limit, linked_backend)}
                audit(directory)
                yul_transport("execute", SimpleNamespace(**{**vars(args), "output": directory}),
                              runner, case, source, hull, shared)
                audit(directory)
                yul = shared["yulExportProvenance"]
        except Finding as error:
            if error.category not in SHARED_FAILURES:
                shutil.rmtree(directory, ignore_errors=True)
                raise
            failure = {"category": error.category, "stage": error.stage, "detail": error.detail}
        except BaseException:
            shutil.rmtree(directory, ignore_errors=True)
            raise
        outputs = {path.name: file_digest(path) for path in sorted(directory.iterdir())
                   if path.is_file() and path.name not in names}
        return {"directory": directory, "source": source, "receipt": receipt, "outputs": outputs, "yul": yul,
                "failure": failure, "processes": copy.deepcopy(report["processes"][first:])}


def execute(args, report: dict) -> None:
    runner = Runner(args, report)
    original = args.case
    previous = None
    if args.replay:
        previous = read_json(args.replay / "report.json", args.artifact_limit)
        verify_archive(args.replay, previous)
        original = args.replay / "case.json"
    backend = resolve_backend(getattr(args, "backend", None), previous)
    report["backend"] = backend
    report["pathBackends"] = path_backends(backend)
    linked_backend = image_backend(backend)
    case = read_json(original)
    validate_case(case)
    if args.replay and case["schema"] == MODULE_CASE_SCHEMA:
        bundle_transport.verify_archive(args.replay, case, previous)
    report["scope"] = {
        CASE_SCHEMA: "closed G0 Word/Bool, gas-independent, Sonatina O0, pure run() ABI Word",
        INPUT_CASE_SCHEMA: "runtime Word input, pure scalar function, Sonatina O0, run(uint256) ABI Word",
        PRIMITIVE_CASE_SCHEMA: "runtime Word input, checked scalar primitive operations, Sonatina O0, run(uint256) ABI Word",
        ASSEMBLY_CASE_SCHEMA: "runtime Word input, checked scalar primitive operations as inline Yul in whole-body or per-operation assembly blocks, Sonatina O0, run(uint256) ABI Word",
        ASSEMBLY_MEMORY_CASE_SCHEMA: "runtime Word input, a checked scalar primitive step as a Yul function over inline Yul memory above the free-memory pointer, with Word and byte writes, overlapping reads and keccak256 versus Core shifts, masks and the Keccak builders, Sonatina O0, run(uint256) ABI Word",
        CALL_GRAPH_CASE_SCHEMA: "runtime Word input, directly generated acyclic Word helper graphs, Sonatina O0, run(uint256) ABI Word",
        CALL_GRAPH_LOOP_CASE_SCHEMA: "runtime Word input, bounded source while versus finite Core guards, directly generated acyclic Word helper step graph, Sonatina O0, run(uint256) ABI Word",
        ASSEMBLY_LOOP_CASE_SCHEMA: "runtime Word input, an inline Yul for loop with break, continue, leave or a two-result step function versus finite Core guards, directly generated acyclic Word helper step graph as Yul functions, Sonatina O0, run(uint256) ABI Word",
        AGGREGATE_CALL_GRAPH_CASE_SCHEMA: "runtime Word input, directly generated internal Word pairs/sums, projections and case payload scopes with acyclic Word helper calls, Sonatina O0, run(uint256) ABI Word",
        ENUM_CASE_SCHEMA: "runtime Word input, user-defined plain and generic enums built from the input and matched with nested constructor and tuple patterns, wildcards and nested matches versus Core sums, products and caseE, Sonatina O0, run(uint256) ABI Word",
        TRAIT_CASE_SCHEMA: "runtime Word input, one trait with a unary and a binary method and impls at Words, tuples, std sums and user-defined enums, called directly and through constrained generic functions at values built from the input, versus one Core closure per reached instance and method, Sonatina O0, run(uint256) ABI Word",
        HIERARCHY_CASE_SCHEMA: "runtime Word input, a subclass of the trait profile's trait with its own method-level generic or none and a chain of two bounds, called directly, through subclass-bounded helpers, method values and generic function values at values built from the input, versus one Core closure per reached instance, method and argument type, Sonatina O0, run(uint256) ABI Word",
        MEMORY_CASE_SCHEMA: "runtime Word input, std's memory<bytes>, memory_ref and memory<DynArray<uint256>> values built from the input, with lengths, Word and byte reads and writes through std's range checks, concatenation, slices, copies, keccak256_, second variables and helpers that write, in straight-line code and bounded while loops, versus a Core reference over byte lists, std's OutOfBounds() revert data compared exactly, Sonatina O0, run(uint256) ABI Word",
        MEMORY_CALL_CASE_SCHEMA: "runtime Word input, std's memory<bytes>, memory_ref and memory<DynArray<uint256>> values passed to and returned by helpers, generic helpers over std's memory traits, function values, tuples, std sums and a user enum holding a value and closures capturing one, in straight-line code, versus a Core reference over byte lists with every call inlined, std's OutOfBounds() revert data compared exactly, Sonatina O0, run(uint256) ABI Word",
        REVERT_DATA_CASE_SCHEMA: "runtime Word input, std Error values made from the input, held by variables, pairs, std sums and a user enum, made, chosen and raised by helpers, closures, match arms and a bounded while loop, through revertWithError, require with an Error or a string literal, revertLit and revertEmpty, beside std's memory<bytes> values that messages view, versus a Core reference over byte lists whose right injection is the revert data, compared exactly, Sonatina O0, run(uint256) ABI Word",
        HALT_CASE_SCHEMA: "runtime Word input, the revert data profile's sites beside halts with INVALID through std's assert, std.opcodes' invalid() and inline Yul invalid() under a Solcore or a Yul if, in run, helpers, closures, match arms and a bounded while loop, versus the revert data profile's Core reference, whose right injection with a length no revert data has is the halt, an INVALID halt matching only three INVALID halts and revert data compared exactly, Sonatina O0, run(uint256) ABI Word",
        CHECKED_ARITHMETIC_CASE_SCHEMA: "runtime Word input or a run(T) argument, std's uint8 to uint256 and int8 to int256 converted from the input with offsets, checked + - * / % and unary - with std's Panic(0x11) and Panic(0x12), the same inside unchecked blocks, through helpers and lambda bodies whose own scope decides, compound assignments, typed literals at the extremes and uint256 literals typed by defaulting, std's DirtyHigherBitsForInteger() for a run(T) argument and a T result std masks or sign-extends, versus an exact integer Core reference whose right injection is the revert data, compared exactly, Sonatina O0, run(uint256) or run(T) ABI Word",
        SHIFT_CASE_SCHEMA: "runtime Word input, << >> <<= >>= of Words and std's uint8 to uint256 and int8 to int256 by amounts of a Word or an unsigned type converted from the input with offsets or literal amounts, arithmetic >> for signed types, amounts of at least the width, inside and outside unchecked blocks, versus an exact integer Core reference, Sonatina O0, run(uint256) ABI Word",
        MEMORY_ARRAY_CASE_SCHEMA: "runtime Word input, T[] memory arrays of std's integer types made with new T[](n), literals, aliases, toArray copies and helper results, element reads and checked, unchecked and memref writes, the four read-only slice forms over arrays, slices, grid rows and a storage array, T[][] grids, the storage array's push, pop and setLength and a loop over a length, versus a Core reference over length and element cells whose right injection is Panic(0x11), Panic(0x12), Panic(0x31), Panic(0x32) or Panic(0x41), compared exactly, Sonatina O0, run(uint256) ABI Word",
        ARRAY_ABI_CASE_SCHEMA: "runtime Word input encoded with one or two T[] or calldata<T[]> parameters of std's integer types whose lengths and elements the input makes, memory arrays, slices and grids over them, std's DirtyHigherBitsForInteger() for a narrow element its decoder rejects, eagerly or when read, and a T[] result std's encoder masks or sign-extends, versus the memory array Core reference with the return data, compared exactly, Sonatina O0, run(T[],[T[],]uint256) ABI",
        CLOSURE_CAPTURES_CASE_SCHEMA: "runtime Word input, Word locals and closures of one run body captured by value, writes through captures to per-call copies, repeated calls, rebinding to lambdas over old values, aliases and nested lambdas, direct calls and generic sc_apply and sc_twice, a bounded while loop and a contract field read and written at call time, with checked uint256 + and / as Panic(0x11) and Panic(0x12), versus checked Core snapshot cells copied at every call, Sonatina O0, run(uint256) ABI Word",
        CLOSURE_FACTORIES_CASE_SCHEMA: "runtime Word input, one or two free or method factories returning closures over their parameter and locals, run's names reused in factories, factory effects on the field and checked operations, factories called from run and lambda bodies, made, discarded and remade, with the closure capture profile's forms, versus checked Core snapshot cells with every factory run where it is called, Sonatina O0, run(uint256) ABI Word",
        FUNCTION_CASE_SCHEMA: "runtime Word input, acyclic named Word functions, Sonatina O0, run(uint256) ABI Word",
        MUTATION_CASE_SCHEMA: "runtime Word input, local Word mutation and acyclic named functions, Sonatina O0, run(uint256) ABI Word",
        AGGREGATE_CASE_SCHEMA: "runtime Word input, internal Word pairs/sums, matches, private cells and acyclic named functions, Sonatina O0, run(uint256) ABI Word",
        LOOP_CASE_SCHEMA: "runtime Word input, bounded source while versus finite Core guards, aggregate step graph, Sonatina O0, run(uint256) ABI Word",
        NESTED_LOOP_CASE_SCHEMA: "runtime Word input, bounded source while nested in a bounded while versus finite Core guards, aggregate step graph, Sonatina O0, run(uint256) ABI Word",
        RECURSION_CASE_SCHEMA: "runtime Word input, bounded self or mutual source recursion versus finite Core guards, aggregate step graph, Sonatina O0, run(uint256) ABI Word",
        RECURSIVE_LOOP_CASE_SCHEMA: "runtime Word input, bounded source while loops inside bounded self or mutual recursion versus finite Core guards, aggregate step graph, Sonatina O0, run(uint256) ABI Word",
        LOOP_CLOSURE_CASE_SCHEMA: "runtime Word input, closures created in bounded source while bodies over loop-carried Word captures versus finite Core guards and snapshot lambdas, aggregate step graph, Sonatina O0, run(uint256) ABI Word",
        GENERIC_CASE_SCHEMA: "runtime Word input, generic Word/pair/sum selection versus checked monomorphic Core, aggregate step graph, Sonatina O0, run(uint256) ABI Word",
        CLOSURE_CASE_SCHEMA: "runtime Word capture, repeated or independent snapshot closures and outer mutation, checked Core lambdas, Sonatina O0, run(uint256) ABI Word",
        COMPTIME_CASE_SCHEMA: "original closed G0 expression evaluated by source comptime versus Core, runtime aggregate step and Word input, Sonatina O0, run(uint256) ABI Word",
        MODULE_CASE_SCHEMA: "four canonical source modules combining generic selection, snapshot closures and comptime with original Core ASTs, Sonatina O0, run(uint256) ABI Word"
    }[case["schema"]].replace("Sonatina O0", "Yul EVM and Sonatina O0-linked Hull" if backend == "yul"
                             else "Sonatina " + optimization_for_backend(backend))
    case_path, source = args.output / "case.json", args.output / "case.sol"
    case_path.write_bytes(json_bytes(case))
    bundle_receipt = None
    library_paths = []
    if case["schema"] == MODULE_CASE_SCHEMA:
        bundle_receipt = bundle_transport.write(args.output, case)
        revision = runner.process("pinned-library-revision", ["git", "-C", str(args.upstream), "rev-parse", "HEAD"], 10)
        dirty = runner.process("pinned-library-clean", ["git", "-C", str(args.upstream), "diff", "--quiet", "HEAD", "--", "std"], 10)
        tracked = runner.process("pinned-library-inventory", ["git", "-C", str(args.upstream), "ls-files", "-z", "--", "std"], 10)
        if revision["returncode"] or revision["stdout"].strip() != UPSTREAM_COMMIT or dirty["returncode"] or tracked["returncode"]:
            raise ValueError("module profile requires the pinned unmodified standard library")
        library_paths = [name for name in tracked["stdout"].split("\0") if name.endswith(".sol")]
        bundle_receipt["libraries"] = bundle_transport.library_files(args.upstream, library_paths)
        report["sourceBundleReceipt"] = bundle_receipt
        if args.replay and bundle_receipt["libraries"] != previous["sourceBundleReceipt"]["libraries"]:
            raise Finding("adapter-error", "replay", "pinned standard-library inventory or hashes changed")
    else:
        source.write_text(case["source"])

    def audit_bundle(directory=None):
        if bundle_receipt is not None:
            bundle_transport.audit_files(directory or args.output, bundle_receipt["files"])
            if bundle_transport.library_files(args.upstream, library_paths) != bundle_receipt["libraries"]:
                raise ValueError("standard-library sources changed during export")
    report.update(caseSha256=file_digest(case_path), sourceSha256=file_digest(source),
                  programSha256=digest(json_bytes(case["program"])), provenance=case["provenance"],
                  replayOf=str(args.replay.resolve()) if args.replay else None)
    report["tools"] = {
        "caseTool": runner.identity(args.case_tool), "coreRunner": runner.identity(args.core_runner),
        "anvil": runner.identity(args.anvil, version=True),
        "python": {"path": sys.executable, "version": sys.version},
        "runnerSha256": file_digest(Path(__file__)),
        "leanToolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "exporters": {name: file_digest(ROOT / "scripts" / name) for name in
                      ("export-rust-hull.py", "export-rust-code-image.py", "rust-hull-export.rs", "rust-code-image-export.rs")}}
    if bundle_receipt is not None:
        report["tools"]["bundleTransportSha256"] = file_digest(ROOT / "scripts/semantic-source-bundle.py")
    if backend == "yul":
        report["tools"].update(solc=runner.identity(args.solc, version=True),
            yulExporterSha256=file_digest(ROOT / "scripts/export-rust-yul.py"),
            yulTransportSha256=file_digest(ROOT / "scripts/semantic-yul.py"))
    revision = runner.process("repository-revision", ["git", "rev-parse", "HEAD"], 10)
    dirty = runner.process("repository-diff", ["git", "diff", "--binary", "HEAD"], 10)
    if revision["returncode"] or dirty["returncode"]:
        raise ValueError("cannot identify repository revision")
    report["repository"] = {"revision": revision["stdout"].strip(), "trackedDiffSha256": digest(dirty["stdout"].encode())}
    if args.replay:
        # Tool drift is an explicit finding, never silently a reproducible replay.
        for key in ("runnerSha256", "exporters", "leanToolchain") + (("bundleTransportSha256",) if bundle_receipt is not None else ()):
            if report["tools"][key] != previous.get("tools", {}).get(key):
                raise Finding("adapter-error", "replay", f"{key} changed since saved run")
        for key in ("caseTool", "coreRunner", "anvil"):
            if report["tools"][key]["sha256"] != previous.get("tools", {}).get(key, {}).get("sha256"):
                raise Finding("adapter-error", "replay", f"{key} binary changed since saved run")
        if backend == "yul":
            for key in ("yulExporterSha256", "yulTransportSha256"):
                if report["tools"][key] != previous.get("tools", {}).get(key):
                    raise Finding("adapter-error", "replay", f"{key} changed since saved run")
            for key in ("sha256", "version"):
                if report["tools"]["solc"][key] != previous.get("tools", {}).get("solc", {}).get(key):
                    raise Finding("adapter-error", "replay", f"solc {key} changed since saved run")
    refreshed = checked_process(runner, "direct-core-replay",
        [str(args.case_tool), "replay", str(case_path), str(args.direct_fuel)])
    fresh = json.loads(refreshed["stdout"])
    validate_replayed_case(case, fresh)
    (args.output / "replayed-case.json").write_bytes(json_bytes(fresh))
    report["rawObservations"]["directCore"] = fresh.get("directCore")
    report["observations"]["directCore"] = normalize_observation(fresh.get("directCore"), direct=True,
                                                                 outputs=case["schema"] in OUTPUT_SCHEMAS)
    halting = case["schema"] in HALTING_SCHEMAS
    if report["observations"]["directCore"]["status"] not in COMPLETED | (HALTED if halting else set()):
        report["comparison"] = {"category": "inconclusive-resource" if report["observations"]["directCore"]["status"] == "out-of-fuel" else "execution-error", "pairs": {}}
        return
    hull_path, image_path = args.output / "hull.json", args.output / "images.json"
    cache = shared_compilations(args)
    compiled, shared = source, None
    if cache is None:
        export_sources(args, runner, args.output, source, linked_backend, audit_bundle)
    else:
        shared = cache.compile(args, runner, case, report, backend, bundle_receipt, audit_bundle)
        compiled = shared["source"]
        if bundle_receipt is not None:
            # Hull provenance names the shared directory's files; this case's
            # own copies have the same digests.
            bundle_receipt = report["sourceBundleReceipt"] = copy.deepcopy(shared["receipt"])
        audit_bundle()
        cache.fail(shared)
    report["exportProvenance"] = validate_export(hull_path, image_path, source, args.artifact_limit, linked_backend, compiled)
    if bundle_receipt is not None:
        bundle_transport.normalized_sources(report["exportProvenance"]["hull"].get("sources"), bundle_receipt, case)
    if args.replay and "exportProvenance" in previous:
        old = previous["exportProvenance"]
        new = report["exportProvenance"]
        if old["images"].get("toolBuild") != new["images"].get("toolBuild") or old["hull"].get("patches") != new["hull"].get("patches") or old["hull"].get("binarySha256") != new["hull"].get("binarySha256"):
            raise Finding("adapter-error", "replay", "Rust compiler/exporter build changed")
        # The saved .sol path changes in a copied run; the pinned library hashes
        # must still agree. The emitted source is independently rechecked above.
        if bundle_receipt is not None:
            old_sources = bundle_transport.normalized_sources(old["hull"].get("sources"), previous["sourceBundleReceipt"], case)
            new_sources = bundle_transport.normalized_sources(new["hull"].get("sources"), bundle_receipt, case)
        else:
            old_sources = {key: value for key, value in old["hull"].get("sources", {}).items() if not key.endswith("/case.sol")}
            new_sources = {key: value for key, value in new["hull"].get("sources", {}).items() if not key.endswith("/case.sol")}
        if old_sources != new_sources:
            raise Finding("adapter-error", "replay", "imported source/library hashes changed")
    images = read_json(image_path, args.artifact_limit)
    init = image_bytes(images, case["contract"]["deployPath"])
    runtime = image_bytes(images, case["contract"]["runtimePath"])
    if backend == "yul":
        audit_bundle()
        if shared is None:
            init, runtime = yul_transport("execute", args, runner, case, source, hull_path, report, previous)
        else:
            cache.fail(shared, yul=True)
            init, runtime = accept_yul(args, case, report, shared["yul"])
        audit_bundle()
    with anvil(runner, args.anvil) as rpc:
        accounts = rpc.call("eth_accounts", [])
        if not accounts or not re.fullmatch(r"0x[0-9a-fA-F]{40}", accounts[0]):
            raise ValueError("Anvil supplied no valid local sender")
        sender = accounts[0]
        gas = hex(args.gas)
        transaction = {"from": sender, "data": "0x" + init.hex(), "value": "0x0", "gas": gas}
        try:
            tx_hash = rpc.call("eth_sendTransaction", [transaction])
        except RpcError as error:
            report["evmDeployment"] = {"rpcError": error.error}
            raise deployment_failure(error) from error
        deadline = time.monotonic() + runner.remaining(args.startup_timeout)
        while True:
            deployed = rpc.call("eth_getTransactionReceipt", [tx_hash])
            if deployed is not None:
                break
            if time.monotonic() >= deadline:
                raise Finding("inconclusive-resource", "evm-deployment", "receipt timeout")
            time.sleep(0.05)
        report["evmDeployment"] = deployed
        if deployed.get("status") != "0x1":
            trace = rpc.call("debug_traceTransaction", [tx_hash, {"disableStorage": True, "disableStack": True, "enableMemory": False}])
            reason = str(trace.get("error", "deployment failed"))
            raise Finding("inconclusive-resource" if RESOURCE.search(reason) else "execution-error", "evm-deployment", reason)
        address = deployed.get("contractAddress")
        if not isinstance(address, str) or not re.fullmatch(r"0x[0-9a-fA-F]{40}", address):
            raise ValueError("invalid deployed contract address")
        installed = hex_bytes(rpc.call("eth_getCode", [address, "latest"]), "installed runtime")
        if installed != runtime:
            raise Finding("adapter-error", "evm-deployment", "deployed bytes differ from exported runtime image")
        call = {"from": sender, "to": address, "data": case["contract"]["calldata"], "value": "0x0", "gas": gas}
        try:
            returned = rpc.call("eth_call", [call, "latest"])
            evm = {"stage": "execution", "status": "returned", "output": returned}
        except RpcError as error:
            evm = evm_failure(error)
            if halting:
                evm = evm_halt(evm)
        report["rawObservations"]["rustEvm"] = evm
        report["observations"]["rustEvm"] = normalize_observation(evm)
        report["executionContext"] = {"sender": sender, "address": address, "calldata": case["contract"]["calldata"], "value": "0", "persist": False, "gas": args.gas}
        base = {"caller": str(int(sender, 16)), "address": str(int(address, 16)), "value": "0", "availableGas": str(args.gas)}
        scenario = {"schema": "solcore-lean.contract-scenario.v1", "hull": str(hull_path), "images": str(image_path),
            "deployPath": case["contract"]["deployPath"], "runtimePath": case["contract"]["runtimePath"],
            "fuel": args.core_fuel, "constructor": {**base, "calldata": "0x"},
            "calls": [{**base, "calldata": case["contract"]["calldata"], "persist": False}]}
        scenario_path = args.output / "scenario.json"
        scenario_path.write_bytes(json_bytes(scenario))
        result = runner.process("imported-hull", [str(args.core_runner), str(scenario_path)])
        rows = core_rows(result["stdout"], result["returncode"])
        report["coreDeployment"] = rows[0]
        report["rawObservations"]["importedHull"] = rows[1]
        report["observations"]["importedHull"] = normalize_observation(rows[1])
    report["comparison"] = compare(report["observations"], reverts=case["schema"] in REVERTING_SCHEMAS, halts=halting)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--case", type=Path)
    selection.add_argument("--replay", type=Path, help="saved run directory; recompile and execute its immutable case")
    parser.add_argument("--output", type=Path, required=True, help="new run directory; never overwritten")
    parser.add_argument("--case-tool", type=Path, default=ROOT / ".lake/build/bin/semantic-case-tool")
    parser.add_argument("--core-runner", type=Path, default=ROOT / ".lake/build/bin/rust-hull-scenario")
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261102")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--backend", choices=BACKENDS, help="default Sonatina O0; exact replay inherits its saved backend")
    parser.add_argument("--solc", type=Path, default=Path(shutil.which("solc") or "solc"), help="pinned solc, used only for --backend yul")
    defaults = {"direct_fuel": 1000000, "core_fuel": 10000000, "gas": 10000000,
                "timeout": 300, "startup_timeout": 30, "total_timeout": 900,
                "output_limit": 2 * 1024 * 1024, "artifact_limit": 64 * 1024 * 1024}
    for key in defaults:
        parser.add_argument("--" + key.replace("_", "-"), type=float if "timeout" in key else int)
    args = parser.parse_args()
    saved_budgets = {}
    saved_report = None
    if args.replay:
        saved_report = read_json(args.replay / "report.json", defaults["artifact_limit"])
        if not isinstance(saved_report, dict):
            parser.error("saved report must be an object")
        saved_budgets = saved_report.get("budgets", {})
        if not isinstance(saved_budgets, dict):
            parser.error("saved budgets must be an object")
    try:
        args.backend = resolve_backend(args.backend, saved_report)
    except ValueError as error:
        parser.error(str(error))
    for key, default in defaults.items():
        explicit = getattr(args, key)
        value = saved_budgets.get(key, default) if explicit is None else explicit
        if isinstance(value, bool) or not isinstance(value, (int, float)) or ("timeout" not in key and not isinstance(value, int)) or not math.isfinite(value) or value <= 0 or value > 10**9:
            parser.error(f"{key} must be finite, positive and at most 1000000000")
        if args.replay and explicit is not None and value != saved_budgets.get(key):
            parser.error(f"replay must retain the saved {key}; use --case for changed budgets")
        setattr(args, key, value)
    for key in ("case", "replay", "output", "case_tool", "core_runner", "anvil", "upstream", "target_dir", "solc"):
        if getattr(args, key) is not None:
            setattr(args, key, getattr(args, key).resolve())
    args.output.mkdir(parents=True, exist_ok=False)
    report = {"schema": REPORT_SCHEMA, "backend": args.backend, "pathBackends": path_backends(args.backend), "processes": [], "observations": {}, "rawObservations": {},
              "budgets": {key: getattr(args, key) for key in ("direct_fuel", "core_fuel", "gas", "timeout", "startup_timeout", "total_timeout", "output_limit", "artifact_limit")},
              "scope": "pure Word ABI; selected backend " + args.backend}
    previous_term = signal.getsignal(signal.SIGTERM)

    def interrupted(_signal, _frame):
        # A second termination request must not interrupt owned-process cleanup.
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupted)
    try:
        execute(args, report)
    except KeyboardInterrupt:
        report["comparison"] = {"category": "inconclusive-resource", "stage": "runner", "detail": "interrupted", "pairs": {}}
    except Finding as error:
        report["comparison"] = {"category": error.category, "stage": error.stage, "detail": error.detail, "pairs": {}}
    except (ValueError, OSError, KeyError, TypeError, RpcError, subprocess.SubprocessError) as error:
        report["comparison"] = {"category": "adapter-error", "stage": "runner", "detail": str(error), "pairs": {}}
    finally:
        try:
            report["artifacts"] = {path.name: file_digest(path) for path in args.output.iterdir() if path.is_file()}
            (args.output / "report.json").write_bytes(json_bytes(report))
        finally:
            signal.signal(signal.SIGTERM, previous_term)
    category = report["comparison"]["category"]
    print(json.dumps({"category": category, "report": str(args.output / "report.json")}))
    return 0 if category == "matched" else 1


if __name__ == "__main__":
    raise SystemExit(main())
