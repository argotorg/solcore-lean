#!/usr/bin/env python3
"""Focused protocol/classification tests; these do not simulate EVM execution.

The process tests execute real bounded Python subprocesses. End-to-end compiler,
Core and Anvil validation is performed with semantic-differential.py itself.
"""
import importlib.util
import copy
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("semantic_differential", ROOT / "scripts/semantic-differential.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def call(value=7):
    return {"stage": "execution", "index": 0, "status": "returned", "output": "0x" + f"{value:064x}"}


def observations(value=7):
    return {name: {"status": "returned", "word": str(value)}
            for name in ("directCore", "importedHull", "rustEvm")}


class ProcessGroupSignalTests(unittest.TestCase):
    """macOS can reject killpg with EPERM when a group holds only unreaped exits."""

    def test_permission_error_from_an_exited_group_does_not_escape_cleanup(self):
        process = subprocess.Popen([sys.executable, '-c', 'pass'], start_new_session=True)
        process.wait(timeout=10)
        with patch.object(runner.os, 'killpg', side_effect=PermissionError(1, 'Operation not permitted')) as killpg:
            runner.stop_process(process)
        self.assertEqual(killpg.call_count, 2)
        self.assertEqual(process.returncode, 0)

    def test_permission_error_still_stops_a_running_leader(self):
        process = subprocess.Popen([sys.executable, '-c', 'import time;time.sleep(30)'], start_new_session=True)
        try:
            started = time.monotonic()
            with patch.object(runner.os, 'killpg', side_effect=PermissionError(1, 'Operation not permitted')):
                runner.stop_process(process)
            self.assertEqual(process.returncode, -signal.SIGTERM)
            self.assertLess(time.monotonic() - started, 5)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait(timeout=10)

    def test_missing_group_is_still_ignored(self):
        process = subprocess.Popen([sys.executable, '-c', 'pass'], start_new_session=True)
        process.wait(timeout=10)
        with patch.object(runner.os, 'killpg', side_effect=ProcessLookupError()) as killpg:
            runner.stop_process(process)
        self.assertEqual(killpg.call_count, 2)


class CaseProfileTests(unittest.TestCase):
    def input_case(self, value):
        # Envelope validation only; the native tool separately checks the Core program.
        return {"schema": runner.INPUT_CASE_SCHEMA, "input": str(value), "program": {},
            "source": "profile test", "provenance": {
                key: "profile-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
            "contract": {"name": "SynthesizedInput", "method": "run", "signature": "run(uint256)",
                "deployPath": ["SynthesizedInputDeploy"],
                "runtimePath": ["SynthesizedInputDeploy", "SynthesizedInput"],
                "calldata": "0xa444f5e9" + f"{value:064x}", "constructorCalldata": "0x"}}

    def test_runtime_boundary_inputs_have_exact_abi(self):
        for value in (0, 1, 2**255, 2**256 - 1):
            with self.subTest(value=value):
                runner.validate_case(self.input_case(value))

    def test_input_and_calldata_cannot_disagree(self):
        case = self.input_case(1)
        for value in (0, 2, 2**255):
            with self.assertRaisesRegex(ValueError, "calldata differs"):
                runner.validate_case({**case, "input": str(value)})
        for value in (1, "01", "-1", str(2**256)):
            with self.assertRaises(ValueError):
                runner.validate_case({**case, "input": value})
        for calldata in ("0xa444f5e9", case["contract"]["calldata"] + "00", "0xc0406226" + "00" * 32):
            with self.assertRaisesRegex(ValueError, "calldata differs"):
                runner.validate_case({**case, "contract": {**case["contract"], "calldata": calldata}})

    def test_profile_and_wrapper_cannot_be_mixed(self):
        case = self.input_case(1)
        with self.assertRaises(runner.Finding):
            runner.validate_case({**case, "schema": runner.CASE_SCHEMA})
        with self.assertRaises(ValueError):
            runner.validate_case({**case, "contract": []})

    def test_named_function_profile_retains_the_runtime_argument(self):
        for schema in (runner.FUNCTION_CASE_SCHEMA, runner.MUTATION_CASE_SCHEMA,
                       runner.AGGREGATE_CASE_SCHEMA, runner.LOOP_CASE_SCHEMA, runner.GENERIC_CASE_SCHEMA, runner.CLOSURE_CASE_SCHEMA, runner.COMPTIME_CASE_SCHEMA, runner.MODULE_CASE_SCHEMA):
            name = runner.CASE_CONTRACTS[schema]
            for value in (0, 1, 2**255, 2**256 - 1):
                case = self.input_case(value)
                case["schema"] = schema
                if schema == runner.LOOP_CASE_SCHEMA:
                    case["loopPlan"] = {"schema": "solcore-lean.loop-plan.v1", "mask": 7, "stepProgram": {}}
                if schema == runner.GENERIC_CASE_SCHEMA:
                    case["genericPlan"] = {"schema": "solcore-lean.generic-plan.v1", "variant": "sum", "stepProgram": {}}
                if schema == runner.CLOSURE_CASE_SCHEMA:
                    case["closurePlan"] = {"schema": "solcore-lean.closure-plan.v1", "variant": "independent", "stepProgram": {}}
                if schema == runner.COMPTIME_CASE_SCHEMA:
                    case["comptimePlan"] = {"schema": "solcore-lean.comptime-plan.v1", "variant": "offset", "stepProgram": {}, "constantProgram": {}}
                if schema == runner.MODULE_CASE_SCHEMA:
                    case["modulePlan"] = {"schema": "solcore-lean.module-plan.v1", "stepProgram": {}, "constantProgram": {}}
                    case["sourceBundle"] = {"schema": runner.bundle_transport.SCHEMA, "entry": "case.sol",
                        "files": [{"path": name, "source": case["source"] if name == "case.sol" else "// provider"}
                                  for name in runner.bundle_transport.FILES]}
                case["contract"].update(name=name,
                    deployPath=[name + "Deploy"], runtimePath=[name + "Deploy", name])
                runner.validate_case(case)
                with self.assertRaises(ValueError if schema == runner.MODULE_CASE_SCHEMA else runner.Finding):
                    runner.validate_case({**case, "schema": runner.INPUT_CASE_SCHEMA})
                with self.assertRaisesRegex(ValueError, "calldata differs"):
                    runner.validate_case({**case, "input": str(value ^ 1)})

    def test_loop_plan_requires_a_bounded_mask_and_original_step_program(self):
        plan = {"schema": "solcore-lean.loop-plan.v1", "mask": 7, "stepProgram": {}}
        for mask in (0, 1, 3, 7):
            runner.validate_loop_plan({**plan, "mask": mask})
        for mask in (True, -1, 2, 8, '7', 7.0):
            with self.assertRaises(ValueError):
                runner.validate_loop_plan({**plan, "mask": mask})
        for invalid in (None, {}, {**plan, "schema": "unknown"}, {**plan, "stepProgram": None}):
            with self.assertRaises(ValueError):
                runner.validate_loop_plan(invalid)

    def test_nested_loop_plan_requires_bounded_masks_a_bound_form_and_original_step_program(self):
        plan = {"schema": "solcore-lean.nested-loop-plan.v1", "outerMask": 3, "innerMask": 3,
                "innerBound": "accumulator", "stepProgram": {}}
        for outer in (0, 1, 3):
            for inner in (0, 1, 3):
                for bound in ("input", "counter", "accumulator"):
                    runner.validate_nested_loop_plan({**plan, "outerMask": outer, "innerMask": inner, "innerBound": bound})
        for key in ("outerMask", "innerMask"):
            for mask in (True, -1, 2, 7, '3', 3.0):
                with self.assertRaises(ValueError):
                    runner.validate_nested_loop_plan({**plan, key: mask})
        for invalid in (None, {}, {**plan, "schema": "solcore-lean.loop-plan.v1"}, {**plan, "stepProgram": None},
                        {**plan, "innerBound": "step"}, {**plan, "innerBound": None}):
            with self.assertRaises(ValueError):
                runner.validate_nested_loop_plan(invalid)
        self.assertEqual(runner.CASE_PROFILES[runner.NESTED_LOOP_CASE_SCHEMA], "runtime-nested-loops")
        self.assertEqual(runner.CASE_CONTRACTS[runner.NESTED_LOOP_CASE_SCHEMA], "SynthesizedNestedLoops")

    def test_recursion_plan_requires_a_bounded_depth_mask_a_form_and_original_step_program(self):
        plan = {"schema": "solcore-lean.recursion-plan.v1", "depthMask": 7, "form": "mutual", "stepProgram": {}}
        for mask in (0, 1, 3, 7):
            for form in ("tail", "nontail", "mutual"):
                runner.validate_recursion_plan({**plan, "depthMask": mask, "form": form})
        for mask in (True, -1, 2, 5, 8, '7', 7.0):
            with self.assertRaises(ValueError):
                runner.validate_recursion_plan({**plan, "depthMask": mask})
        for invalid in (None, {}, {**plan, "schema": "solcore-lean.loop-plan.v1"}, {**plan, "stepProgram": None},
                        {**plan, "form": "loop"}, {**plan, "form": None}):
            with self.assertRaises(ValueError):
                runner.validate_recursion_plan(invalid)
        self.assertEqual(runner.CASE_PROFILES[runner.RECURSION_CASE_SCHEMA], "runtime-recursion")
        self.assertEqual(runner.CASE_CONTRACTS[runner.RECURSION_CASE_SCHEMA], "SynthesizedRecursion")

    def test_recursive_loop_plan_requires_bounded_masks_a_form_and_original_step_program(self):
        plan = {"schema": "solcore-lean.recursive-loop-plan.v1", "depthMask": 3, "innerMask": 3, "form": "mutual",
                "stepProgram": {}}
        for depth in (0, 1, 3):
            for inner in (0, 1, 3):
                for form in ("tail", "nontail", "mutual"):
                    runner.validate_recursive_loop_plan({**plan, "depthMask": depth, "innerMask": inner, "form": form})
        for key in ("depthMask", "innerMask"):
            for mask in (True, -1, 2, 7, '3', 3.0):
                with self.assertRaises(ValueError):
                    runner.validate_recursive_loop_plan({**plan, key: mask})
        for invalid in (None, {}, {**plan, "schema": "solcore-lean.recursion-plan.v1"}, {**plan, "stepProgram": None},
                        {**plan, "form": "loop"}):
            with self.assertRaises(ValueError):
                runner.validate_recursive_loop_plan(invalid)
        self.assertEqual(runner.CASE_PROFILES[runner.RECURSIVE_LOOP_CASE_SCHEMA], "runtime-recursive-loops")
        self.assertEqual(runner.CASE_CONTRACTS[runner.RECURSIVE_LOOP_CASE_SCHEMA], "SynthesizedRecursiveLoops")

    def test_loop_closure_plan_requires_a_bounded_mask_a_capture_and_original_step_program(self):
        plan = {"schema": "solcore-lean.loop-closure-plan.v1", "mask": 7, "capture": "counter", "stepProgram": {}}
        for mask in (0, 1, 3, 7):
            for capture in ("accumulator", "counter"):
                runner.validate_loop_closure_plan({**plan, "mask": mask, "capture": capture})
        for mask in (True, -1, 2, 5, 8, '7', 7.0):
            with self.assertRaises(ValueError):
                runner.validate_loop_closure_plan({**plan, "mask": mask})
        for invalid in (None, {}, {**plan, "schema": "solcore-lean.loop-plan.v1"}, {**plan, "stepProgram": None},
                        {**plan, "capture": "reference"}, {**plan, "capture": None}):
            with self.assertRaises(ValueError):
                runner.validate_loop_closure_plan(invalid)
        self.assertEqual(runner.CASE_PROFILES[runner.LOOP_CLOSURE_CASE_SCHEMA], "runtime-loop-closures")
        self.assertEqual(runner.CASE_CONTRACTS[runner.LOOP_CLOSURE_CASE_SCHEMA], "SynthesizedLoopClosures")

    def test_assembly_plan_requires_a_form_and_the_original_function(self):
        plan = {"schema": "solcore-lean.assembly-plan.v1", "functionProgram": {}, "form": "switch"}
        for form in ("switch", "if", "operations"):
            runner.validate_assembly_plan({**plan, "form": form})
        for invalid in (None, {}, {**plan, "schema": "solcore-lean.recursion-plan.v1"}, {**plan, "functionProgram": None},
                        {**plan, "form": "branches"}, {**plan, "form": None}):
            with self.assertRaises(ValueError):
                runner.validate_assembly_plan(invalid)
        self.assertEqual(runner.CASE_PROFILES[runner.ASSEMBLY_CASE_SCHEMA], "runtime-assembly")
        self.assertEqual(runner.CASE_CONTRACTS[runner.ASSEMBLY_CASE_SCHEMA], "SynthesizedAssembly")

    def test_assembly_loop_plan_requires_a_bounded_mask_a_form_and_the_original_step_graph(self):
        plan = {"schema": "solcore-lean.assembly-loop-plan.v1", "stepProgram": {}, "mask": 7, "form": "for"}
        self.assertEqual(runner.ASSEMBLY_LOOP_FORMS, ("for", "break", "continue", "leave", "pair"))
        for mask in (0, 1, 3, 7):
            for form in runner.ASSEMBLY_LOOP_FORMS:
                runner.validate_assembly_loop_plan({**plan, "mask": mask, "form": form})
        for mask in (True, -1, 2, 5, 8, '7', 7.0):
            with self.assertRaises(ValueError):
                runner.validate_assembly_loop_plan({**plan, "mask": mask})
        for invalid in (None, {}, {**plan, "schema": "solcore-lean.call-graph-loop-plan.v1"},
                        {**plan, "stepProgram": None}, {**plan, "form": "while"}, {**plan, "form": None}):
            with self.assertRaises(ValueError):
                runner.validate_assembly_loop_plan(invalid)
        self.assertEqual(runner.CASE_PROFILES[runner.ASSEMBLY_LOOP_CASE_SCHEMA], "runtime-assembly-loops")
        self.assertEqual(runner.CASE_CONTRACTS[runner.ASSEMBLY_LOOP_CASE_SCHEMA], "SynthesizedAssemblyLoops")
        self.assertEqual(runner.ASSEMBLY_LOOP_VERSIONS, (*runner.CALL_GRAPH_LOOP_VERSIONS, "loopProfileVersion"))

    def test_assembly_memory_plan_keeps_every_access_and_the_hash_inside_the_window(self):
        stage = {"read": 64, "width": "word", "write": 64}
        plan = {"schema": "solcore-lean.assembly-memory-plan.v1", "functionProgram": {}, "stages": [stage],
                "finalRead": 64, "hash": None}
        self.assertEqual(runner.ASSEMBLY_MEMORY_HASH_LENGTHS, (0, 1, 31, 32, 33, 64))
        for length in runner.ASSEMBLY_MEMORY_HASH_LENGTHS:
            runner.validate_assembly_memory_plan({**plan, "hash": {"offset": 96 - length, "length": length}})
        runner.validate_assembly_memory_plan({**plan, "stages": [stage, {**stage, "width": "byte", "write": 95}, stage]})
        for invalid in (None, {}, {**plan, "schema": "solcore-lean.assembly-plan.v1"}, {**plan, "functionProgram": None},
                        {**plan, "stages": []}, {**plan, "stages": [stage] * 4}, {**plan, "stages": [{**stage, "read": 65}]},
                        {**plan, "stages": [{**stage, "write": 65}]}, {**plan, "stages": [{**stage, "width": "byte", "write": 96}]},
                        {**plan, "stages": [{**stage, "width": "half"}]}, {**plan, "stages": [{**stage, "read": True}]},
                        {**plan, "stages": [{**stage, "extra": 0}]}, {**plan, "finalRead": 65}, {**plan, "finalRead": -1},
                        {**plan, "hash": {"offset": 64, "length": 33}}, {**plan, "hash": {"offset": 0, "length": 2}},
                        {**plan, "hash": {"offset": 0, "length": True}}, {**plan, "hash": {"offset": 0}},
                        {**plan, "extra": 0}):
            with self.assertRaises(ValueError):
                runner.validate_assembly_memory_plan(invalid)
        self.assertEqual(runner.CASE_PROFILES[runner.ASSEMBLY_MEMORY_CASE_SCHEMA], "runtime-assembly-memory")
        self.assertEqual(runner.CASE_CONTRACTS[runner.ASSEMBLY_MEMORY_CASE_SCHEMA], "SynthesizedAssemblyMemory")

    def test_enum_plan_envelope_and_shape_inventory(self):
        declaration = {"generic": True, "sameName": True, "constructors": [["param", "word"], [], [{"enum": 0}]]}
        view = {"kind": "generic", "scrutinees": [{"enum": 0, "argument": "param"}], "instances": ["word", {"tuple": ["word", "word"]}],
                "arms": [{"patterns": ["_"], "return": {"terms": [{"name": "sc_w"}], "operations": [], "constant": "1"}}],
                "builders": [{"offset": 0, "values": []}, {"offset": 1, "values": []}], "wordOffset": "7"}
        plan = {"schema": "solcore-lean.enum-plan.v1", "declarations": [declaration] * 3, "views": [view] * 3}
        runner.validate_enum_plan(plan)
        runner.validate_enum_plan({**plan, "declarations": [{**declaration, "constructors": [[]] * 4}]})
        for invalid in (None, {}, {**plan, "schema": "solcore-lean.assembly-plan.v1"}, {**plan, "extra": 0},
                        {**plan, "declarations": []}, {**plan, "declarations": [declaration] * 4},
                        {**plan, "declarations": [{**declaration, "constructors": [[]]}]},
                        {**plan, "declarations": [{**declaration, "constructors": [[]] * 5}]},
                        {**plan, "declarations": [{**declaration, "constructors": [["word"] * 3, []]}]},
                        {**plan, "declarations": [{**declaration, "generic": 0}]},
                        {**plan, "declarations": [{**declaration, "extra": 0}]},
                        {**plan, "views": []}, {**plan, "views": [view] * 4}, {**plan, "views": [{**view, "kind": "triple"}]},
                        {**plan, "views": [{**view, "arms": []}]}, {**plan, "views": [{**view, "arms": [view["arms"][0]] * 9}]},
                        {**plan, "views": [{**view, "builders": []}]}, {**plan, "views": [{**view, "wordOffset": 7}]},
                        {**plan, "views": [{**view, "wordOffset": "07"}]}, {**plan, "views": [{**view, "extra": 0}]}):
            with self.assertRaises(ValueError):
                runner.validate_enum_plan(invalid)
        shapes = {key: list(values) for key, values in runner.ENUM_SHAPES.items()}
        runner.validate_enum_shapes(shapes)
        for invalid in (None, {}, {**shapes, "extra": []}, {**shapes, "views": ["single", "generic"]},
                        {**shapes, "views": ["single", "single"]}, {**shapes, "depths": ["4"]}, {**shapes, "depths": [1]}):
            with self.assertRaises(ValueError):
                runner.validate_enum_shapes(invalid)
        self.assertEqual(runner.CASE_PROFILES[runner.ENUM_CASE_SCHEMA], "runtime-enums")
        self.assertEqual(runner.CASE_CONTRACTS[runner.ENUM_CASE_SCHEMA], "SynthesizedEnums")
        self.assertEqual(runner.ENUM_VERSIONS, ("profileVersion", "boundaryVersion"))

    def test_trait_plan_envelope_and_shape_inventory(self):
        declaration = {"generic": True, "sameName": False, "constructors": [["param"], []]}
        impl = {"head": "sum", "unary": [], "binary": [], "form": "nested", "mismatch": ["1", "2"]}
        helper = {"call": "lifted", "method": "binary", "op": "sub", "constant": "9"}
        use = {"method": "binary", "call": "lifted", "type": {"sum": ["word", "word"]}, "shift": 4,
               "builder": {"offset": 0, "values": []}}
        plan = {"schema": "solcore-lean.trait-plan.v1", "declarations": [declaration] * 3, "methods": ["binary"],
                "impls": [impl] * 6, "helpers": [helper] * 4, "uses": [use] * 6}
        runner.validate_trait_plan(plan)
        for methods in (["unary"], ["unary", "binary"]):
            runner.validate_trait_plan({**plan, "methods": methods})
        runner.validate_trait_plan({**plan, "helpers": [], "uses": [{**use, "call": "direct", "shift": 0}]})
        for invalid in (None, {}, {**plan, "schema": "solcore-lean.enum-plan.v1"}, {**plan, "extra": 0},
                        {**plan, "declarations": []}, {**plan, "declarations": [declaration] * 4},
                        {**plan, "methods": []}, {**plan, "methods": ["binary", "unary"]}, {**plan, "methods": ["unary"] * 2},
                        {**plan, "impls": []}, {**plan, "impls": [impl] * 7}, {**plan, "impls": [{**impl, "form": "flat"}]},
                        {**plan, "impls": [{**impl, "extra": 0}]}, {**plan, "helpers": [helper] * 5},
                        {**plan, "helpers": [{**helper, "call": "direct"}]}, {**plan, "helpers": [{**helper, "method": "ternary"}]},
                        {**plan, "uses": []}, {**plan, "uses": [use] * 7}, {**plan, "uses": [{**use, "call": "inline"}]},
                        {**plan, "uses": [{**use, "method": "nullary"}]}, {**plan, "uses": [{**use, "shift": 5}]},
                        {**plan, "uses": [{**use, "shift": "4"}]}, {**plan, "uses": [{**use, "extra": 0}]}):
            with self.assertRaises(ValueError):
                runner.validate_trait_plan(invalid)
        shapes = {key: list(values) for key, values in runner.TRAIT_SHAPES.items()}
        runner.validate_trait_shapes(shapes)
        for invalid in (None, {}, {**shapes, "extra": []}, {**shapes, "calls": ["unary:direct", "binary:direct"]},
                        {**shapes, "depths": ["0", "0"]}, {**shapes, "depths": ["4"]}, {**shapes, "depths": [0]},
                        {**shapes, "shapes": ["product-of-sum"]}):
            with self.assertRaises(ValueError):
                runner.validate_trait_shapes(invalid)
        self.assertEqual({key: len(values) for key, values in runner.TRAIT_SHAPES.items()},
                         {"instances": 10, "calls": 6, "depths": 4, "arguments": 5, "forms": 4, "shapes": 1})
        self.assertEqual(runner.CASE_PROFILES[runner.TRAIT_CASE_SCHEMA], "runtime-traits")
        self.assertEqual(runner.CASE_CONTRACTS[runner.TRAIT_CASE_SCHEMA], "SynthesizedTraits")
        self.assertEqual(runner.TRAIT_VERSIONS, ("profileVersion", "boundaryVersion"))

    def test_memory_plan_envelope_and_shape_inventory(self):
        action = {"kind": "observe", "fold": "add", "constant": 3, "value": "sc_b0", "access": {"access": "length"}}
        build = {"kind": "bytes", "build": "to_bytes", "parts": [{"part": "word", "operand": {"operand": "input"}}]}
        loop = {"loop": {"form": "nested", "outer": 3, "bound": "counter", "inner": 1}, "body": [action] * 3}
        plan = {"schema": "solcore-lean.memory-value-plan.v1",
                "steps": [{"action": build}] + [{"action": action}] * 8 + [loop]}
        runner.validate_memory_plan(plan)
        for kind in ("slice", "alias", "array", "write"):
            runner.validate_memory_plan({**plan, "steps": [{"action": {**build, "kind": kind}}]})
        for invalid in (None, {}, {**plan, "schema": "solcore-lean.trait-plan.v1"}, {**plan, "extra": 0},
                        {**plan, "steps": []}, {**plan, "steps": plan["steps"] + [{"action": action}]},
                        {**plan, "steps": [{"action": {**action, "kind": "free"}}]}, {**plan, "steps": [action]},
                        {**plan, "steps": [{"action": action, "body": []}]}, {**plan, "steps": [loop, loop]},
                        {**plan, "steps": [{**loop, "body": []}]}, {**plan, "steps": [{**loop, "body": [action] * 4}]},
                        {**plan, "steps": [{**loop, "loop": {"form": "triple"}}]},
                        {**plan, "steps": [{**loop, "body": [{**action, "kind": None}]}]}):
            with self.assertRaises(ValueError):
                runner.validate_memory_plan(invalid)
        shapes = {key: list(values) for key, values in runner.MEMORY_SHAPES.items()}
        runner.validate_memory_shapes(shapes)
        for invalid in (None, {}, {**shapes, "extra": []}, {**shapes, "values": ["slice", "bytes"]},
                        {**shapes, "hashes": ["0", "0"]}, {**shapes, "hashes": ["129"]}, {**shapes, "loops": ["single:5"]},
                        {**shapes, "indices": ["word:register"]}, {key: values for key, values in shapes.items() if key != "body"}):
            with self.assertRaises(ValueError):
                runner.validate_memory_shapes(invalid)
        self.assertEqual({key: len(values) for key, values in runner.MEMORY_SHAPES.items()},
                         {"values": 6, "parts": 8, "cuts": 6, "writes": 10, "observations": 10, "indices": 18,
                          "hazards": 4, "loops": 6, "body": 5, "hashes": 9})
        self.assertEqual(runner.CASE_PROFILES[runner.MEMORY_CASE_SCHEMA], "runtime-memory-values")
        self.assertEqual(runner.CASE_CONTRACTS[runner.MEMORY_CASE_SCHEMA], "SynthesizedMemoryValues")
        self.assertEqual(runner.MEMORY_VERSIONS, ("profileVersion", "boundaryVersion"))
        self.assertEqual(runner.REVERTING_SCHEMAS, (runner.MEMORY_CASE_SCHEMA, runner.MEMORY_CALL_CASE_SCHEMA))

    def test_memory_call_plan_envelope_and_shape_inventory(self):
        build = {"kind": "bytes", "build": "to_bytes", "parts": [{"part": "word", "operand": {"operand": "input"}}]}
        call = {"helper": 0, "arg": "sc_b0", "index": {"index": "literal", "value": 0}, "word": {"operand": "input"},
                "form": "direct", "fold": "add", "constant": 3}
        helper = {"param": "bytes", "kind": "read", "obs": "length", "fold": "add"}
        plan = {"schema": "solcore-lean.memory-call-plan.v1", "helpers": [helper] * 3,
                "steps": [{"action": build}, {"call": call}, {"data": {"datum": "inr", "word": {"operand": "input"}}},
                          {"closure": {"value": "sc_b0", "obs": "length"}},
                          {"apply": {"closure": 0, "index": {"index": "literal", "value": 0}, "fold": "add",
                                     "constant": 3}}] + [{"call": call}] * 7}
        runner.validate_memory_call_plan(plan)
        for param in ("slice", "generic", "array", "pair", "sum", "enum"):
            for kind in ("write", "view", "copy", "call", "pack", "take"):
                runner.validate_memory_call_plan({**plan, "helpers": [{**helper, "param": param, "kind": kind}]})
        for invalid in (None, {}, {**plan, "schema": "solcore-lean.memory-value-plan.v1"}, {**plan, "extra": 0},
                        {**plan, "helpers": []}, {**plan, "helpers": [helper] * 4}, {**plan, "steps": []},
                        {**plan, "steps": plan["steps"] + [{"call": call}]},
                        {**plan, "helpers": [{**helper, "param": "word"}]}, {**plan, "helpers": [{**helper, "kind": "free"}]},
                        {**plan, "steps": [{"action": build}]}, {**plan, "steps": [{"loop": {}, "body": []}, {"call": call}]},
                        {**plan, "steps": [{"action": build, "call": call}]}, {**plan, "steps": [call]},
                        {**plan, "steps": [{"action": {**build, "kind": "free"}}, {"call": call}]}):
            with self.assertRaises(ValueError):
                runner.validate_memory_call_plan(invalid)
        shapes = {key: list(values) for key, values in runner.MEMORY_CALL_SHAPES.items()}
        runner.validate_memory_call_shapes(shapes)
        for invalid in (None, {}, {**shapes, "extra": []}, {**shapes, "passes": ["slice", "bytes"]},
                        {**shapes, "data": ["pair", "pair"]}, {**shapes, "hazards": ["view"]},
                        {**shapes, "indices": ["word:counter"]}, {key: values for key, values in shapes.items() if key != "steps"}):
            with self.assertRaises(ValueError):
                runner.validate_memory_call_shapes(invalid)
        self.assertEqual({key: len(values) for key, values in runner.MEMORY_CALL_SHAPES.items()},
                         {"helpers": 25, "calls": 10, "passes": 4, "instances": 3, "data": 5, "closures": 9,
                          "observations": 23, "indices": 12, "ranges": 2, "hazards": 4, "steps": 10})
        self.assertEqual(runner.CASE_PROFILES[runner.MEMORY_CALL_CASE_SCHEMA], "runtime-memory-calls")
        self.assertEqual(runner.CASE_CONTRACTS[runner.MEMORY_CALL_CASE_SCHEMA], "SynthesizedMemoryCalls")
        self.assertEqual(runner.MEMORY_CALL_VERSIONS, ("profileVersion", "boundaryVersion"))

    def test_hierarchy_plan_envelope_and_shape_inventory(self):
        declaration = {"generic": True, "sameName": False, "constructors": [["param"], []]}
        impl = {"head": "sum", "unary": [], "binary": [], "form": "nested", "mismatch": ["1", "2"]}
        sub = {"head": "sum", "steps": []}
        helper = {"call": "top", "method": "mix", "op": "sub", "constant": "9"}
        argument = {"type": "word", "builder": {"offset": 0, "values": []}}
        use = {"method": "mix", "call": "top", "type": {"sum": ["word", "word"]}, "shift": 0,
               "builder": {"offset": 0, "values": []}, "arguments": [argument, argument]}
        plan = {"schema": "solcore-lean.trait-hierarchy-plan.v1", "declarations": [declaration] * 3,
                "methods": ["unary", "binary"], "impls": [impl] * 6, "subclass": "mix", "subImpls": [sub] * 6,
                "tops": ["sum"] * 6, "helpers": [helper] * 10, "uses": [use] * 6}
        runner.validate_hierarchy_plan(plan)
        for subclass in ("marker", "shadow"):
            runner.validate_hierarchy_plan({**plan, "subclass": subclass})
        for call in ("direct", "sub", "value", "function"):
            runner.validate_hierarchy_plan({**plan, "helpers": [],
                                            "uses": [{**use, "method": "binary", "call": call, "shift": 4, "arguments": []}]})
        for invalid in (None, {}, {**plan, "schema": "solcore-lean.trait-plan.v1"}, {**plan, "extra": 0},
                        {**plan, "declarations": []}, {**plan, "declarations": [declaration] * 4},
                        {**plan, "methods": []}, {**plan, "methods": ["binary", "unary"]},
                        {**plan, "impls": []}, {**plan, "impls": [impl] * 7}, {**plan, "impls": [{**impl, "form": "flat"}]},
                        {**plan, "subclass": "deep"}, {**plan, "subImpls": [sub] * 7},
                        {**plan, "subImpls": [{**sub, "extra": 0}]}, {**plan, "subImpls": [{**sub, "steps": None}]},
                        {**plan, "tops": ["sum"] * 7}, {**plan, "helpers": [helper] * 11},
                        {**plan, "helpers": [{**helper, "call": "direct"}]}, {**plan, "helpers": [{**helper, "call": "lifted"}]},
                        {**plan, "helpers": [{**helper, "method": "ternary"}]},
                        {**plan, "uses": []}, {**plan, "uses": [use] * 7}, {**plan, "uses": [{**use, "call": "generic"}]},
                        {**plan, "uses": [{**use, "method": "nullary"}]}, {**plan, "uses": [{**use, "shift": 5}]},
                        {**plan, "uses": [{**use, "arguments": [argument]}]},
                        {**plan, "uses": [{**use, "arguments": [argument] * 3}]},
                        {**plan, "uses": [{key: value for key, value in use.items() if key != "arguments"}]},
                        {**plan, "uses": [{**use, "extra": 0}]}):
            with self.assertRaises(ValueError):
                runner.validate_hierarchy_plan(invalid)
        shapes = {key: list(values) for key, values in runner.HIERARCHY_SHAPES.items()}
        runner.validate_hierarchy_shapes(shapes)
        for invalid in (None, {}, {**shapes, "extra": []}, {**shapes, "calls": ["unary:direct", "binary:direct"]},
                        {**shapes, "depths": ["0", "0"]}, {**shapes, "depths": ["4"]}, {**shapes, "parameters": ["param"]},
                        {**shapes, "subclass": ["deep"]}, {key: values for key, values in shapes.items() if key != "subclass"}):
            with self.assertRaises(ValueError):
                runner.validate_hierarchy_shapes(invalid)
        self.assertEqual({key: len(values) for key, values in runner.HIERARCHY_SHAPES.items()},
                         {"instances": 15, "calls": 13, "depths": 4, "arguments": 5, "parameters": 5, "forms": 4,
                          "subclass": 3})
        self.assertEqual(runner.CASE_PROFILES[runner.HIERARCHY_CASE_SCHEMA], "runtime-trait-hierarchies")
        self.assertEqual(runner.CASE_CONTRACTS[runner.HIERARCHY_CASE_SCHEMA], "SynthesizedTraitHierarchies")
        self.assertEqual(runner.HIERARCHY_VERSIONS, ("profileVersion", "boundaryVersion"))

    def test_generic_plan_requires_an_admitted_type_and_original_step(self):
        plan = {"schema": "solcore-lean.generic-plan.v1", "variant": "word", "stepProgram": {}}
        for variant in ("word", "pair", "sum"):
            runner.validate_generic_plan({**plan, "variant": variant})
        for variant in (True, 0, None, [], {}, "closure", "Word", "word "):
            with self.assertRaises(ValueError):
                runner.validate_generic_plan({**plan, "variant": variant})
        for invalid in (None, {}, {**plan, "schema": "unknown"}, {**plan, "stepProgram": None}):
            with self.assertRaises(ValueError):
                runner.validate_generic_plan(invalid)

    def test_closure_plan_rejects_unknown_capture_recipes_and_missing_step(self):
        plan = {"schema": "solcore-lean.closure-plan.v1", "variant": "snapshot", "stepProgram": {}}
        for variant in ("snapshot", "independent"):
            runner.validate_closure_plan({**plan, "variant": variant})
        for variant in (True, 0, None, [], {}, "reference", "escaping", "snapshot "):
            with self.assertRaises(ValueError):
                runner.validate_closure_plan({**plan, "variant": variant})
        for invalid in (None, {}, {**plan, "schema": "unknown"}, {**plan, "stepProgram": None}):
            with self.assertRaises(ValueError):
                runner.validate_closure_plan(invalid)

    def test_comptime_plan_requires_original_constant_ast_not_an_evaluated_word(self):
        plan = {"schema": "solcore-lean.comptime-plan.v1", "variant": "offset", "stepProgram": {}, "constantProgram": {}}
        for variant in ("offset", "scale"):
            runner.validate_comptime_plan({**plan, "variant": variant})
        for variant in (True, 0, None, [], {}, "runtime", "offset "):
            with self.assertRaises(ValueError):
                runner.validate_comptime_plan({**plan, "variant": variant})
        for invalid in (None, {}, {**plan, "schema": "unknown"}, {**plan, "stepProgram": None},
                {**plan, "constantProgram": "15"}, {**plan, "constantProgram": None}):
            with self.assertRaises(ValueError):
                runner.validate_comptime_plan(invalid)

    def test_module_plan_requires_both_original_programs(self):
        plan = {"schema": "solcore-lean.module-plan.v1", "stepProgram": {}, "constantProgram": {}}
        runner.validate_module_plan(plan)
        for invalid in (None, {}, {**plan, "schema": "unknown"}, {**plan, "stepProgram": None},
                {**plan, "constantProgram": "15"}):
            with self.assertRaises(ValueError):
                runner.validate_module_plan(invalid)
        case = self.input_case(0)
        case['sourceBundle'] = {}
        with self.assertRaisesRegex(ValueError, 'only admitted by the module profile'):
            runner.validate_case(case)


class PrimitiveProfileTests(unittest.TestCase):
    def case(self, value=1):
        case = CaseProfileTests().input_case(value)
        case['schema'] = runner.PRIMITIVE_CASE_SCHEMA
        case['source'] = 'import { div as sc_div } from std.opcodes; // envelope fixture only'
        case['provenance'].update({key: 'primitive-policy-test' for key in
            ('profileVersion', 'functionVersion', 'abstractionVersion', 'baseGeneratorVersion', 'boundaryVersion')})
        case['contract'].update(name='SynthesizedPrimitives', deployPath=['SynthesizedPrimitivesDeploy'],
            runtimePath=['SynthesizedPrimitivesDeploy', 'SynthesizedPrimitives'])
        return case

    def test_all_eight_primitive_inputs_have_exact_abi_and_a_distinct_wrapper(self):
        for value in (0, 1, 2, 255, 256, 2**256 - 1, 2**255, 2**255 - 1):
            case = self.case(value)
            runner.validate_case(case)
            self.assertEqual(runner.CASE_PROFILES[case['schema']], 'runtime-primitives')
            with self.assertRaisesRegex(ValueError, 'calldata differs'):
                runner.validate_case({**case, 'input': str(value ^ 1)})
            with self.assertRaises(runner.Finding):
                runner.validate_case({**case, 'schema': runner.INPUT_CASE_SCHEMA})

    def test_primitive_version_receipts_are_not_optional(self):
        for key in ('profileVersion', 'functionVersion', 'abstractionVersion', 'baseGeneratorVersion', 'boundaryVersion'):
            for value in (None, '', 1):
                case = self.case()
                case['provenance'][key] = value
                with self.assertRaisesRegex(ValueError, key):
                    runner.validate_case(case)

    def test_native_replay_source_alias_program_and_provenance_cannot_change(self):
        case = self.case()
        # No Rust/Core execution is simulated: exercise the post-native equality gate.
        runner.validate_replayed_case(case, copy.deepcopy(case))
        for key, value in [('source', case['source'].replace('div as', 'sdiv as')),
                ('program', {'unsealed': True}),
                ('provenance', {**case['provenance'], 'boundaryVersion': 'forged-bank'})]:
            with self.assertRaisesRegex(ValueError, 'case replay changed ' + key):
                runner.validate_replayed_case(case, {**case, key: value})
        saved = {**case, 'directCore': {'stage': 'execution', 'status': 'returned', 'word': '999'}}
        fresh = {**case, 'directCore': {'stage': 'execution', 'status': 'returned', 'word': '2'}}
        runner.validate_replayed_case(saved, fresh)
        self.assertEqual(runner.normalize_observation(fresh['directCore'], direct=True)['word'], '2')

    def test_primitive_backend_replay_keeps_yul_hull_images_explicit(self):
        case = self.case()
        runner.validate_case(case)
        for backend in runner.BACKENDS:
            self.assertEqual(runner.resolve_backend(None, {'backend': backend}), backend)
            expected_images = 'sonatina-o0' if backend == 'yul' else backend
            self.assertEqual(runner.path_backends(backend),
                {'directCore': 'original-core', 'importedHull': expected_images, 'rustEvm': backend})
            other = 'sonatina-o2' if backend != 'sonatina-o2' else 'yul'
            with self.assertRaises(ValueError):
                runner.resolve_backend(other, {'backend': backend})


class CallGraphProfileTests(unittest.TestCase):
    def case(self, value=2):
        case = CaseProfileTests().input_case(value)
        case['schema'] = runner.CALL_GRAPH_CASE_SCHEMA
        case['source'] = '// call graph admission fixture; no simulated execution'
        case['provenance'].update({key: 'policy' for key in runner.CALL_GRAPH_VERSIONS})
        case['provenance'].update(helperCount=2, callShapes=['nested-call', 'predicate-call'])
        case['contract'].update(name='SynthesizedCallGraphs', deployPath=['SynthesizedCallGraphsDeploy'],
            runtimePath=['SynthesizedCallGraphsDeploy', 'SynthesizedCallGraphs'])
        return case

    def test_call_graph_abi_versions_and_helper_count_are_required(self):
        for value in (0, 1, 2, 255, 256, 2**256 - 1, 2**255, 2**255 - 1):
            runner.validate_case(self.case(value))
        for key in runner.CALL_GRAPH_VERSIONS:
            case = self.case(); del case['provenance'][key]
            with self.assertRaisesRegex(ValueError, key): runner.validate_case(case)
        for value in (None, True, 0, 4, '2'):
            case = self.case(); case['provenance']['helperCount'] = value
            with self.assertRaisesRegex(ValueError, 'helperCount'): runner.validate_case(case)
        with self.assertRaisesRegex(ValueError, 'calldata differs'):
            runner.validate_case({**self.case(), 'input': '1'})

    def test_shapes_have_one_canonical_order_and_no_unknown_or_duplicate_items(self):
        self.assertEqual(runner.CALL_SHAPES, ('skipped-helper', 'multiple-callees', 'shared-callee',
            'nested-call', 'branch-call', 'local-call', 'diamond', 'predicate-call', 'primitive-operand-call'))
        for values in ([], ['diamond'], list(runner.CALL_SHAPES)):
            self.assertEqual(runner.validate_call_shapes(values), values)
        for values in (None, {}, 'diamond', [1], ['recursive'], ['diamond', 'diamond'],
                       ['predicate-call', 'nested-call']):
            case = self.case(); case['provenance']['callShapes'] = values
            with self.assertRaisesRegex(ValueError, 'canonical'): runner.validate_case(case)

    def test_native_replay_must_authenticate_call_shape_claims_and_source(self):
        case = self.case()
        for key, value in [('source', case['source'] + 'changed'),
            ('provenance', {**case['provenance'], 'callShapes': ['diamond']}),
            ('provenance', {**case['provenance'], 'helperCount': 1})]:
            with self.assertRaisesRegex(ValueError, 'case replay changed'):
                runner.validate_replayed_case(case, {**case, key: value})
        runner.validate_replayed_case({**case, 'directCore': {'word': 'fake'}}, case)

    def test_call_graph_backend_receipts_keep_yul_and_linked_hull_distinct(self):
        self.assertEqual(runner.CASE_CONTRACTS[runner.CALL_GRAPH_CASE_SCHEMA], 'SynthesizedCallGraphs')
        for backend in runner.BACKENDS:
            self.assertEqual(runner.resolve_backend(None, {'backend': backend}), backend)
            self.assertEqual(runner.path_backends(backend)['importedHull'],
                'sonatina-o0' if backend == 'yul' else backend)


class CallGraphLoopProfileTests(unittest.TestCase):
    NAME = 'SynthesizedCallGraphLoops'
    SHAPES = ['nested-call', 'predicate-call']

    def plan(self, mask=7):
        # Envelope only; the native tool separately reseals the scalar graph and the loop.
        return {'schema': 'solcore-lean.call-graph-loop-plan.v1', 'mask': mask, 'stepProgram': {}}

    def case(self, value=7, mask=7):
        case = CaseProfileTests().input_case(value)
        case['schema'] = runner.CALL_GRAPH_LOOP_CASE_SCHEMA
        case['source'] = '// call-graph loop admission fixture; no simulated execution'
        case['loopPlan'] = self.plan(mask)
        case['provenance'].update({key: 'policy' for key in runner.CALL_GRAPH_LOOP_VERSIONS})
        case['provenance'].update(helperCount=2, callShapes=list(self.SHAPES))
        case['contract'].update(name=self.NAME, deployPath=[self.NAME + 'Deploy'],
            runtimePath=[self.NAME + 'Deploy', self.NAME])
        return case

    def test_schema_registers_a_distinct_profile_contract_and_version_inventory(self):
        schema = runner.CALL_GRAPH_LOOP_CASE_SCHEMA
        self.assertEqual(schema, 'solcore-lean.semantic-call-graph-loop-case.v1')
        self.assertEqual(runner.CASE_PROFILES[schema], 'runtime-call-graph-loops')
        self.assertEqual(runner.CASE_CONTRACTS[schema], self.NAME)
        others = (runner.CALL_GRAPH_CASE_SCHEMA, runner.LOOP_CASE_SCHEMA)
        self.assertNotIn(schema, others)
        self.assertEqual(len({runner.CASE_CONTRACTS[s] for s in (schema, *others)}), 3)
        self.assertEqual(len(set(runner.CASE_PROFILES.values())), len(runner.CASE_PROFILES))
        self.assertEqual(len(set(runner.CASE_CONTRACTS.values())), len(runner.CASE_CONTRACTS))
        self.assertEqual(runner.CALL_GRAPH_LOOP_VERSIONS, ('profileVersion', 'functionVersion', 'loopVersion',
            'stepFunctionVersion', 'aggregateVersion', 'boundaryVersion', 'stepBoundaryVersion', 'callShapeVersion'))
        self.assertTrue(set(runner.CALL_GRAPH_VERSIONS) < set(runner.CALL_GRAPH_LOOP_VERSIONS))

    def test_all_six_loop_inputs_and_masks_have_exact_abi_and_a_distinct_wrapper(self):
        for value in (0, 1, 3, 7, 2**256 - 1, 2**255):
            for mask in (0, 1, 3, 7):
                case = self.case(value, mask)
                runner.validate_case(case)
                self.assertEqual(runner.CASE_PROFILES[case['schema']], 'runtime-call-graph-loops')
            with self.assertRaisesRegex(ValueError, 'calldata differs'):
                runner.validate_case({**case, 'input': str(value ^ 1)})
            with self.assertRaises(runner.Finding):
                runner.validate_case({**case, 'schema': runner.CALL_GRAPH_CASE_SCHEMA})
            with self.assertRaises(runner.Finding):
                runner.validate_case({**case, 'schema': runner.INPUT_CASE_SCHEMA})

    def test_plan_envelope_requires_its_own_schema_a_bounded_mask_and_the_original_step_graph(self):
        for mask in (0, 1, 3, 7):
            runner.validate_call_graph_loop_plan(self.plan(mask))
        for mask in (True, False, -1, 2, 4, 8, '7', 7.0, None):
            with self.assertRaisesRegex(ValueError, 'mask'):
                runner.validate_call_graph_loop_plan(self.plan(mask))
        plan = self.plan()
        for invalid in (None, [], 'plan', {}, {**plan, 'schema': 'unknown'},
                        {**plan, 'schema': 'solcore-lean.loop-plan.v1'}):
            with self.assertRaisesRegex(ValueError, 'schema'):
                runner.validate_call_graph_loop_plan(invalid)
        for key in ('mask', 'stepProgram'):
            missing = dict(plan); del missing[key]
            with self.assertRaises(ValueError): runner.validate_call_graph_loop_plan(missing)
        for step in (None, [], 'program', 0):
            with self.assertRaisesRegex(ValueError, 'scalar step graph'):
                runner.validate_call_graph_loop_plan({**plan, 'stepProgram': step})
        # The ordinary loop plan and this plan are separate envelopes.
        with self.assertRaises(ValueError):
            runner.validate_loop_plan(plan)
        with self.assertRaises(ValueError):
            runner.validate_call_graph_loop_plan({**plan, 'schema': 'solcore-lean.loop-plan.v1'})

    def test_case_requires_a_valid_loop_plan(self):
        case = self.case()
        missing = dict(case); del missing['loopPlan']
        invalid = [missing, {**case, 'loopPlan': None}, {**case, 'loopPlan': {}},
                   {**case, 'loopPlan': {**self.plan(), 'schema': 'solcore-lean.loop-plan.v1'}},
                   {**case, 'loopPlan': {**self.plan(), 'schema': 'unknown'}}]
        invalid += [{**case, 'loopPlan': self.plan(mask)} for mask in (2, 8, True, '7')]
        for key in ('mask', 'stepProgram'):
            plan = self.plan(); del plan[key]
            invalid.append({**case, 'loopPlan': plan})
        invalid.append({**case, 'loopPlan': {**self.plan(), 'stepProgram': None}})
        for value in invalid:
            with self.assertRaises(ValueError):
                runner.validate_case(value)
        # A loop plan supplies no substitute for the plain call-graph or loop profiles' own envelopes.
        plain = self.case(); plain['schema'] = runner.LOOP_CASE_SCHEMA
        with self.assertRaises(ValueError):
            runner.validate_case(plain)
        runner.validate_case(case)

    def test_every_call_graph_loop_version_receipt_is_required(self):
        for key in runner.CALL_GRAPH_LOOP_VERSIONS:
            case = self.case(); del case['provenance'][key]
            with self.assertRaisesRegex(ValueError, key): runner.validate_case(case)
            for value in (None, '', 1, True, []):
                case = self.case(); case['provenance'][key] = value
                with self.assertRaisesRegex(ValueError, key): runner.validate_case(case)
        for key in ('loopVersion', 'stepFunctionVersion', 'aggregateVersion', 'stepBoundaryVersion'):
            # These loop-specific receipts are not part of the plain call-graph inventory.
            self.assertNotIn(key, runner.CALL_GRAPH_VERSIONS)
        for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion'):
            case = self.case(); del case['provenance'][key]
            with self.assertRaisesRegex(ValueError, key): runner.validate_case(case)
        case = self.case(); case['provenance'] = {key: 'policy' for key in runner.CALL_GRAPH_VERSIONS}
        case['provenance'].update(helperCount=2, callShapes=list(self.SHAPES),
            **{key: 'policy' for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion')})
        with self.assertRaisesRegex(ValueError, 'loopVersion'): runner.validate_case(case)

    def test_helper_count_is_one_to_three(self):
        for value in (1, 2, 3):
            case = self.case(); case['provenance']['helperCount'] = value
            runner.validate_case(case)
        for value in (None, True, False, 0, 4, -1, 2.0, '2'):
            case = self.case(); case['provenance']['helperCount'] = value
            with self.assertRaisesRegex(ValueError, 'helperCount'): runner.validate_case(case)
        case = self.case(); del case['provenance']['helperCount']
        with self.assertRaisesRegex(ValueError, 'helperCount'): runner.validate_case(case)

    def test_call_shapes_keep_one_canonical_order_and_no_unknown_or_duplicate_items(self):
        for values in ([], ['diamond'], list(runner.CALL_SHAPES)):
            case = self.case(); case['provenance']['callShapes'] = values
            runner.validate_case(case)
        for values in (None, {}, 'diamond', [1], ['recursive'], ['diamond', 'diamond'],
                       ['predicate-call', 'nested-call'], list(reversed(runner.CALL_SHAPES))):
            case = self.case(); case['provenance']['callShapes'] = values
            with self.assertRaisesRegex(ValueError, 'canonical'): runner.validate_case(case)
        case = self.case(); del case['provenance']['callShapes']
        with self.assertRaisesRegex(ValueError, 'canonical'): runner.validate_case(case)

    def test_wrapper_name_object_paths_and_calldata_cannot_change(self):
        case = self.case()
        for name in ('SynthesizedLoops', 'SynthesizedCallGraphs', 'SynthesizedInput', 'SynthesizedG0'):
            with self.assertRaises(runner.Finding):
                runner.validate_case({**case, 'contract': {**case['contract'], 'name': name}})
        for key, value in (('method', 'other'), ('signature', 'run()')):
            with self.assertRaises(runner.Finding):
                runner.validate_case({**case, 'contract': {**case['contract'], key: value}})
        for deploy, runtime in ((['SynthesizedLoopsDeploy'], ['SynthesizedLoopsDeploy', 'SynthesizedLoops']),
                                (['SynthesizedCallGraphsDeploy'], ['SynthesizedCallGraphsDeploy', 'SynthesizedCallGraphs']),
                                ([self.NAME], [self.NAME + 'Deploy', self.NAME]),
                                ([self.NAME + 'Deploy'], [self.NAME + 'Deploy']),
                                ([self.NAME + 'Deploy'], [self.NAME, self.NAME + 'Deploy'])):
            with self.assertRaisesRegex(ValueError, 'object paths'):
                runner.validate_case({**case, 'contract': {**case['contract'], 'deployPath': deploy, 'runtimePath': runtime}})
        for calldata in ('0xa444f5e9', case['contract']['calldata'] + '00', '0xc0406226' + '00' * 32):
            with self.assertRaisesRegex(ValueError, 'calldata differs'):
                runner.validate_case({**case, 'contract': {**case['contract'], 'calldata': calldata}})
        with self.assertRaises(runner.Finding):
            runner.validate_case({**case, 'contract': {**case['contract'], 'constructorCalldata': '0x00'}})
        with self.assertRaisesRegex(ValueError, 'only admitted by the module profile'):
            runner.validate_case({**case, 'sourceBundle': {}})

    def test_native_replay_must_authenticate_the_loop_plan_call_shapes_and_helper_count(self):
        case = self.case()
        runner.validate_replayed_case(case, copy.deepcopy(case))
        runner.validate_replayed_case({**case, 'directCore': {'word': 'fake'}}, case)
        for key, value in [('loopPlan', self.plan(3)),
                ('loopPlan', {**self.plan(), 'stepProgram': {'unsealed': True}}),
                ('source', case['source'] + 'changed'),
                ('provenance', {**case['provenance'], 'callShapes': ['diamond']}),
                ('provenance', {**case['provenance'], 'helperCount': 1}),
                ('provenance', {**case['provenance'], 'stepBoundaryVersion': 'forged'})]:
            with self.assertRaisesRegex(ValueError, 'case replay changed'):
                runner.validate_replayed_case(case, {**case, key: value})
        with self.assertRaisesRegex(ValueError, 'case replay changed'):
            runner.validate_replayed_case(case, self.case(3))

    def test_backend_receipts_keep_yul_and_linked_hull_distinct(self):
        self.assertEqual(runner.CASE_CONTRACTS[runner.CALL_GRAPH_LOOP_CASE_SCHEMA], self.NAME)
        for backend in runner.BACKENDS:
            self.assertEqual(runner.resolve_backend(None, {'backend': backend}), backend)
            self.assertEqual(runner.path_backends(backend)['importedHull'],
                'sonatina-o0' if backend == 'yul' else backend)
            other = 'sonatina-o2' if backend != 'sonatina-o2' else 'yul'
            with self.assertRaises(ValueError):
                runner.resolve_backend(other, {'backend': backend})


class AggregateCallGraphProfileTests(unittest.TestCase):
    NAME = 'SynthesizedAggregateCallGraphs'
    SHAPES = ['pair-component-call', 'case-branch-call']
    INPUTS = (0, 1, 2, 255, 256, 2**256 - 1, 2**255, 2**255 - 1)

    def case(self, value=2):
        # Envelope only; the native tool separately reseals the Core graph, its shapes and the source.
        case = CaseProfileTests().input_case(value)
        case['schema'] = runner.AGGREGATE_CALL_GRAPH_CASE_SCHEMA
        case['source'] = '// aggregate call-graph admission fixture; no simulated execution'
        case['provenance'].update({key: 'policy' for key in runner.AGGREGATE_CALL_GRAPH_VERSIONS})
        case['provenance'].update(helperCount=2, aggregateShapes=list(self.SHAPES))
        case['contract'].update(name=self.NAME, deployPath=[self.NAME + 'Deploy'],
            runtimePath=[self.NAME + 'Deploy', self.NAME])
        return case

    def test_schema_registers_a_distinct_profile_contract_and_version_inventory(self):
        schema = runner.AGGREGATE_CALL_GRAPH_CASE_SCHEMA
        self.assertEqual(schema, 'solcore-lean.semantic-aggregate-call-graph-case.v1')
        self.assertEqual(runner.CASE_PROFILES[schema], 'runtime-aggregate-call-graphs')
        self.assertEqual(runner.CASE_CONTRACTS[schema], self.NAME)
        others = (runner.CALL_GRAPH_CASE_SCHEMA, runner.CALL_GRAPH_LOOP_CASE_SCHEMA, runner.AGGREGATE_CASE_SCHEMA)
        self.assertNotIn(schema, others)
        self.assertEqual(len({runner.CASE_CONTRACTS[s] for s in (schema, *others)}), 4)
        self.assertEqual(len({runner.CASE_PROFILES[s] for s in (schema, *others)}), 4)
        self.assertEqual(len(runner.CASE_PROFILES), 26)
        self.assertEqual(set(runner.CASE_PROFILES), set(runner.CASE_CONTRACTS))
        self.assertEqual(len(set(runner.CASE_PROFILES.values())), len(runner.CASE_PROFILES))
        self.assertEqual(len(set(runner.CASE_CONTRACTS.values())), len(runner.CASE_CONTRACTS))
        self.assertEqual(runner.AGGREGATE_CALL_GRAPH_VERSIONS,
            ('profileVersion', 'functionVersion', 'boundaryVersion', 'shapeVersion'))
        # The scalar profile names its shape receipt differently, so neither inventory can stand in for the other.
        self.assertEqual(set(runner.CALL_GRAPH_VERSIONS) ^ set(runner.AGGREGATE_CALL_GRAPH_VERSIONS),
            {'callShapeVersion', 'shapeVersion'})

    def test_shape_inventory_is_nine_ordered_names_disjoint_from_the_scalar_call_shapes(self):
        self.assertEqual(runner.AGGREGATE_SHAPES, ('pair-component-call', 'sum-payload-call', 'projected-call-argument',
            'case-scrutinee-call', 'case-branch-call', 'payload-call-argument', 'aggregate-let', 'aggregate-branch',
            'nested-case'))
        self.assertEqual(len(set(runner.AGGREGATE_SHAPES)), 9)
        self.assertFalse(set(runner.AGGREGATE_SHAPES) & set(runner.CALL_SHAPES))

    def test_all_eight_primitive_inputs_have_exact_abi_and_a_distinct_wrapper(self):
        for value in self.INPUTS:
            with self.subTest(value=value):
                case = self.case(value)
                runner.validate_case(case)
                self.assertEqual(runner.CASE_PROFILES[case['schema']], 'runtime-aggregate-call-graphs')
                with self.assertRaisesRegex(ValueError, 'calldata differs'):
                    runner.validate_case({**case, 'input': str(value ^ 1)})
                # The wrapper name selects the profile: other schemas do not admit this envelope.
                for schema in (runner.INPUT_CASE_SCHEMA, runner.AGGREGATE_CASE_SCHEMA, runner.FUNCTION_CASE_SCHEMA,
                               runner.CASE_SCHEMA):
                    with self.assertRaises(runner.Finding):
                        runner.validate_case({**case, 'schema': schema})
                for schema in (runner.CALL_GRAPH_CASE_SCHEMA, runner.CALL_GRAPH_LOOP_CASE_SCHEMA,
                               runner.PRIMITIVE_CASE_SCHEMA, 'unknown', None,
                               runner.AGGREGATE_CALL_GRAPH_CASE_SCHEMA.replace('.v1', '.v2')):
                    with self.assertRaises(ValueError):
                        runner.validate_case({**case, 'schema': schema})
        for value in (1, '01', '-1', str(2**256), None):
            with self.assertRaises(ValueError):
                runner.validate_case({**self.case(), 'input': value})

    def test_case_requires_its_original_core_program_and_emitted_source(self):
        case = self.case()
        for key, value in (('program', None), ('program', []), ('program', 'core'),
                           ('source', None), ('source', 7), ('source', [])):
            with self.assertRaisesRegex(ValueError, 'original Core program and emitted source'):
                runner.validate_case({**case, key: value})
        for key in ('program', 'source', 'provenance', 'contract', 'input'):
            missing = dict(case); del missing[key]
            with self.assertRaises((ValueError, runner.Finding)):
                runner.validate_case(missing)
        for provenance in (None, [], 'policy'):
            with self.assertRaisesRegex(ValueError, 'provenance'):
                runner.validate_case({**case, 'provenance': provenance})

    def test_every_aggregate_call_graph_version_receipt_is_required(self):
        for key in runner.AGGREGATE_CALL_GRAPH_VERSIONS:
            case = self.case(); del case['provenance'][key]
            with self.assertRaisesRegex(ValueError, key): runner.validate_case(case)
            for value in (None, '', 1, True, []):
                case = self.case(); case['provenance'][key] = value
                with self.assertRaisesRegex(ValueError, key): runner.validate_case(case)
        for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion'):
            case = self.case(); del case['provenance'][key]
            with self.assertRaisesRegex(ValueError, key): runner.validate_case(case)
        # The scalar call-graph shape receipt is a different field and cannot replace this profile's.
        case = self.case(); del case['provenance']['shapeVersion']; case['provenance']['callShapeVersion'] = 'policy'
        with self.assertRaisesRegex(ValueError, 'shapeVersion'): runner.validate_case(case)
        # The aggregate receipts are not part of the scalar call-graph inventory either.
        scalar = CallGraphProfileTests().case()
        scalar['provenance'].update({key: 'policy' for key in runner.AGGREGATE_CALL_GRAPH_VERSIONS})
        runner.validate_case(scalar)
        del scalar['provenance']['callShapeVersion']
        with self.assertRaisesRegex(ValueError, 'callShapeVersion'): runner.validate_case(scalar)

    def test_helper_count_is_one_to_three(self):
        for value in (1, 2, 3):
            case = self.case(); case['provenance']['helperCount'] = value
            runner.validate_case(case)
        for value in (None, True, False, 0, 4, -1, 2.0, '2'):
            case = self.case(); case['provenance']['helperCount'] = value
            with self.assertRaisesRegex(ValueError, 'helperCount'): runner.validate_case(case)
        case = self.case(); del case['provenance']['helperCount']
        with self.assertRaisesRegex(ValueError, 'helperCount'): runner.validate_case(case)

    def test_aggregate_shapes_keep_one_canonical_order_and_no_unknown_or_duplicate_items(self):
        valid = [[], ['nested-case'], ['pair-component-call', 'aggregate-let'], list(runner.AGGREGATE_SHAPES)]
        valid += [[shape] for shape in runner.AGGREGATE_SHAPES]
        for values in valid:
            self.assertEqual(runner.validate_aggregate_shapes(values), values)
            case = self.case(); case['provenance']['aggregateShapes'] = values
            runner.validate_case(case)
        invalid = [None, {}, 'nested-case', 7, [1], [None], ['recursive'], ['Nested-Case'], ['nested-case '],
                   ['nested-case', 'nested-case'], ['nested-case', 'aggregate-let'],
                   ['case-branch-call', 'pair-component-call'], list(reversed(runner.AGGREGATE_SHAPES)),
                   tuple(runner.AGGREGATE_SHAPES), ['diamond'], list(runner.CALL_SHAPES)]
        for values in invalid:
            with self.subTest(values=values):
                case = self.case(); case['provenance']['aggregateShapes'] = values
                with self.assertRaisesRegex(ValueError, 'canonical'): runner.validate_case(case)
                with self.assertRaisesRegex(ValueError, 'canonical'): runner.validate_aggregate_shapes(values)
        case = self.case(); del case['provenance']['aggregateShapes']
        with self.assertRaisesRegex(ValueError, 'canonical'): runner.validate_case(case)
        with self.assertRaisesRegex(ValueError, 'expectedAggregateShapes'):
            runner.validate_aggregate_shapes(None, 'expectedAggregateShapes')
        # Neither profile accepts the other's shape vocabulary.
        scalar = CallGraphProfileTests().case()
        scalar['provenance']['callShapes'] = ['nested-case']
        with self.assertRaisesRegex(ValueError, 'canonical'): runner.validate_case(scalar)
        with self.assertRaisesRegex(ValueError, 'canonical'): runner.validate_call_shapes(['pair-component-call'])

    def test_wrapper_name_object_paths_and_calldata_cannot_change(self):
        case = self.case()
        for name in ('SynthesizedCallGraphs', 'SynthesizedCallGraphLoops', 'SynthesizedAggregates', 'SynthesizedInput',
                     'SynthesizedG0', self.NAME + 'Deploy', ''):
            with self.assertRaises(runner.Finding):
                runner.validate_case({**case, 'contract': {**case['contract'], 'name': name}})
        for key, value in (('method', 'other'), ('signature', 'run()'), ('signature', 'run(uint256) ')):
            with self.assertRaises(runner.Finding):
                runner.validate_case({**case, 'contract': {**case['contract'], key: value}})
        missing = dict(case); del missing['contract']
        with self.assertRaises(runner.Finding): runner.validate_case(missing)
        for deploy, runtime in ((['SynthesizedAggregatesDeploy'], ['SynthesizedAggregatesDeploy', 'SynthesizedAggregates']),
                                (['SynthesizedCallGraphsDeploy'], ['SynthesizedCallGraphsDeploy', 'SynthesizedCallGraphs']),
                                ([self.NAME], [self.NAME + 'Deploy', self.NAME]),
                                ([self.NAME + 'Deploy'], [self.NAME + 'Deploy']),
                                ([self.NAME + 'Deploy'], [self.NAME, self.NAME + 'Deploy']),
                                ([self.NAME + 'Deploy', 'extra'], [self.NAME + 'Deploy', self.NAME])):
            with self.assertRaisesRegex(ValueError, 'object paths'):
                runner.validate_case({**case, 'contract': {**case['contract'], 'deployPath': deploy, 'runtimePath': runtime}})
        for calldata in ('0xa444f5e9', case['contract']['calldata'] + '00', '0xc0406226' + '00' * 32):
            with self.assertRaisesRegex(ValueError, 'calldata differs'):
                runner.validate_case({**case, 'contract': {**case['contract'], 'calldata': calldata}})
        with self.assertRaises(runner.Finding):
            runner.validate_case({**case, 'contract': {**case['contract'], 'constructorCalldata': '0x00'}})
        with self.assertRaises(ValueError):
            runner.validate_case({**case, 'contract': []})

    def test_source_bundles_are_only_admitted_by_the_module_profile(self):
        case = self.case()
        well_formed = {'schema': runner.bundle_transport.SCHEMA, 'entry': 'case.sol',
            'files': [{'path': name, 'source': case['source'] if name == 'case.sol' else '// provider'}
                      for name in runner.bundle_transport.FILES]}
        for bundle in ({}, None, [], well_formed):
            with self.assertRaisesRegex(ValueError, 'only admitted by the module profile'):
                runner.validate_case({**case, 'sourceBundle': bundle})

    def test_native_replay_must_authenticate_program_source_shapes_helper_count_versions_and_input(self):
        case = self.case()
        runner.validate_replayed_case(case, copy.deepcopy(case))
        # A saved observation is no oracle for the replayed case.
        runner.validate_replayed_case({**case, 'directCore': {'word': 'fake'}}, case)
        runner.validate_replayed_case(case, {**case, 'directCore': {'word': 'other'}})
        provenance = case['provenance']
        changes = [('source', case['source'] + 'changed'), ('program', {'unsealed': True}),
            ('contract', {**case['contract'], 'note': 'unsealed'}),
            ('provenance', {**provenance, 'aggregateShapes': ['nested-case']}),
            ('provenance', {**provenance, 'aggregateShapes': []}),
            ('provenance', {**provenance, 'helperCount': 1}), ('provenance', {**provenance, 'helperCount': 3}),
            ('provenance', {**provenance, 'features': ['forged']}),
            ('provenance', {**provenance, 'origin': {'kind': 'forged'}})]
        changes += [('provenance', {**provenance, key: 'forged'}) for key in
                    (*runner.AGGREGATE_CALL_GRAPH_VERSIONS, 'generatorVersion', 'emitterVersion', 'wrapperVersion')]
        # A plan envelope belongs to other profiles: native replay may neither add nor drop one.
        changes += [(key, {'schema': 'solcore-lean.loop-plan.v1', 'stepProgram': {}}) for key in
                    ('loopPlan', 'genericPlan', 'closurePlan', 'comptimePlan', 'modulePlan')]
        for key, value in changes:
            with self.subTest(key=key, value=value):
                with self.assertRaisesRegex(ValueError, 'case replay changed ' + key):
                    runner.validate_replayed_case(case, {**case, key: value})
                with self.assertRaisesRegex(ValueError, 'case replay changed ' + key):
                    runner.validate_replayed_case({**case, key: value}, case)
        with self.assertRaisesRegex(ValueError, 'case replay changed input'):
            runner.validate_replayed_case({**case, 'input': '3'}, case)
        with self.assertRaisesRegex(ValueError, 'case replay changed'):
            runner.validate_replayed_case(case, self.case(3))
        # The replayed case must itself be a valid envelope before it is compared.
        fresh_provenance = {**provenance, 'aggregateShapes': ['nested-case', 'aggregate-let']}
        with self.assertRaisesRegex(ValueError, 'canonical'):
            runner.validate_replayed_case({**case, 'provenance': fresh_provenance}, {**case, 'provenance': fresh_provenance})
        fresh_provenance = {**provenance, 'helperCount': 4}
        with self.assertRaisesRegex(ValueError, 'helperCount'):
            runner.validate_replayed_case({**case, 'provenance': fresh_provenance}, {**case, 'provenance': fresh_provenance})
        with self.assertRaisesRegex(ValueError, 'only admitted by the module profile'):
            runner.validate_replayed_case(case, {**case, 'sourceBundle': {}})

    def test_backend_receipts_keep_yul_and_linked_hull_distinct(self):
        self.assertEqual(runner.CASE_CONTRACTS[runner.AGGREGATE_CALL_GRAPH_CASE_SCHEMA], self.NAME)
        for backend in runner.BACKENDS:
            self.assertEqual(runner.resolve_backend(None, {'backend': backend}), backend)
            self.assertEqual(runner.path_backends(backend)['importedHull'],
                'sonatina-o0' if backend == 'yul' else backend)
            other = 'sonatina-o2' if backend != 'sonatina-o2' else 'yul'
            with self.assertRaises(ValueError):
                runner.resolve_backend(other, {'backend': backend})

    def test_execution_scope_is_registered_for_every_backend_before_any_tool_runs(self):
        class Stop(Exception):
            pass

        class StoppingRunner:
            """Stops at the first tool identity: no process, compiler or EVM is started."""
            def __init__(self, args, report):
                pass

            def identity(self, *_args, **_kwargs):
                raise Stop

        for backend in runner.BACKENDS:
            with self.subTest(backend=backend), tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)
                (folder / 'input.json').write_text(json.dumps(self.case()))
                (folder / 'out').mkdir()
                args = SimpleNamespace(case=folder / 'input.json', replay=None, backend=backend, output=folder / 'out',
                    case_tool=Path('/unused/case-tool'), total_timeout=5)
                report = {'processes': [], 'observations': {}, 'rawObservations': {}}
                with patch.object(runner, 'Runner', StoppingRunner), self.assertRaises(Stop):
                    runner.execute(args, report)
                self.assertIn('directly generated internal Word pairs/sums, projections and case payload scopes with '
                              'acyclic Word helper calls', report['scope'])
                self.assertIn('Yul EVM and Sonatina O0-linked Hull' if backend == 'yul'
                              else 'Sonatina ' + runner.optimization_for_backend(backend), report['scope'])
                self.assertEqual((report['backend'], report['pathBackends']), (backend, runner.path_backends(backend)))
                self.assertEqual(report['provenance'], self.case()['provenance'])
                self.assertEqual(json.loads((folder / 'out/case.json').read_text()), self.case())


class ClassificationTests(unittest.TestCase):
    def test_three_completed_paths_required(self):
        actual = observations()
        self.assertEqual(runner.compare(actual)["category"], "matched")
        del actual["importedHull"]
        self.assertEqual(runner.compare(actual)["category"], "adapter-error")

    def test_missing_completed_payload_cannot_pass(self):
        actual = {name: {"status": "returned"} for name in observations()}
        self.assertEqual(runner.compare(actual)["category"], "adapter-error")

    def test_perturbed_observation_cannot_pass(self):
        actual = observations()
        actual["rustEvm"]["word"] = "8"
        result = runner.compare(actual)
        self.assertEqual(result["category"], "semantic-mismatch")
        self.assertEqual(result["pairs"], {"directCore/rustEvm": False,
            "directCore/importedHull": True, "importedHull/rustEvm": False})

    def test_hull_disagreement_cannot_be_hidden_by_the_primary_pair(self):
        actual = observations()
        actual["importedHull"]["word"] = "8"
        result = runner.compare(actual)
        self.assertEqual(result["category"], "semantic-mismatch")
        self.assertEqual(result["pairs"], {"directCore/rustEvm": True,
            "directCore/importedHull": False, "importedHull/rustEvm": False})

    def test_identical_resource_or_fault_rows_are_not_agreement(self):
        for status, category in [("out-of-fuel", "inconclusive-resource"),
                ("out-of-gas", "inconclusive-resource"), ("timeout", "inconclusive-resource"),
                ("core-fault", "execution-error"), ("not-executed", "execution-error"),
                ("evm-exceptional", "execution-error")]:
            actual = {name: {"status": status} for name in observations()}
            self.assertEqual(runner.compare(actual)["category"], category)

    def test_equal_reverts_match_only_for_a_reverting_profile(self):
        reverted = {"status": "reverted", "output": "0xb4120f14"}
        actual = {name: dict(reverted) for name in observations()}
        self.assertEqual(runner.compare(actual)["category"], "semantic-mismatch")
        result = runner.compare(actual, reverts=True)
        self.assertEqual(result["category"], "matched")
        self.assertEqual(result["pairs"], {"directCore/rustEvm": True, "directCore/importedHull": True,
                                           "importedHull/rustEvm": True})
        actual["rustEvm"] = {"status": "reverted", "output": "0xb4120f15"}
        self.assertEqual(runner.compare(actual, reverts=True)["category"], "semantic-mismatch")
        actual["rustEvm"] = {"status": "returned", "word": "7"}
        self.assertEqual(runner.compare(actual, reverts=True)["category"], "semantic-mismatch")
        self.assertEqual(runner.compare(observations(), reverts=True)["category"], "matched")
        for status, category in (("out-of-gas", "inconclusive-resource"), ("evm-exceptional", "execution-error")):
            actual = {name: dict(reverted) for name in observations()}
            actual["rustEvm"] = {"status": status}
            self.assertEqual(runner.compare(actual, reverts=True)["category"], category)

    def test_revert_difference_preserves_bytes(self):
        row = runner.normalize_observation({"stage": "execution", "status": "reverted", "output": "0xAB00"})
        self.assertEqual(row, {"status": "reverted", "output": "0xab00"})
        actual = observations()
        actual["rustEvm"] = row
        self.assertEqual(runner.compare(actual)["category"], "semantic-mismatch")

    def test_exact_abi_word(self):
        self.assertEqual(runner.normalize_observation(call(2**256 - 1))["word"], str(2**256 - 1))
        for output in (None, "0x0", "garbage", "0xzz"):
            with self.assertRaises(ValueError):
                runner.normalize_observation({**call(), "output": output})
        for value in (7, "-1", "07", str(2**256)):
            with self.assertRaises(ValueError):
                runner.normalize_observation({"stage": "execution", "status": "returned", "word": value}, direct=True)

    def test_wrong_abi_length_remains_an_observed_mismatch(self):
        for output in ("0x", "0x" + "00" * 31, "0x" + "00" * 33):
            actual = observations()
            actual["rustEvm"] = runner.normalize_observation({**call(), "output": output})
            self.assertEqual(actual["rustEvm"], {"status": "returned", "output": output})
            result = runner.compare(actual)
            self.assertEqual(result["category"], "semantic-mismatch")
            self.assertEqual(result["pairs"], {"directCore/rustEvm": False,
                "directCore/importedHull": True, "importedHull/rustEvm": False})

    def test_completed_payloads_are_compared_as_bytes(self):
        actual = observations()
        actual["rustEvm"] = {"status": "returned", "output": call()["output"]}
        self.assertEqual(runner.compare(actual)["category"], "matched")
        actual["rustEvm"]["word"] = "7"
        self.assertEqual(runner.compare(actual)["category"], "adapter-error")

    def test_rpc_error_is_not_unconditionally_a_revert(self):
        error = runner.evm_failure(runner.RpcError({"message": "out of gas", "data": "0x"}))
        self.assertEqual(error["status"], "out-of-gas")
        error = runner.evm_failure(runner.RpcError({"message": "execution reverted", "data": "0x1234"}))
        self.assertEqual(error["output"], "0x1234")
        for body in ({"message": "execution reverted"}, {"message": "invalid opcode", "data": "0x"}):
            self.assertEqual(runner.evm_failure(runner.RpcError(body))["status"], "evm-exceptional")

    def test_deployment_rpc_gas_failures_are_resources(self):
        for message in ("intrinsic gas too low", "OutOfGas", "gas required exceeds allowance (100)"):
            error = runner.RpcError({"code": -32000, "message": message})
            self.assertEqual(runner.evm_failure(error)["status"], "out-of-gas")
            finding = runner.deployment_failure(error)
            self.assertEqual((finding.category, finding.stage), ("inconclusive-resource", "evm-deployment"))
        self.assertEqual(runner.deployment_failure(runner.RpcError({
            "code": -32000, "message": "invalid opcode"})).category, "execution-error")
        self.assertEqual(runner.deployment_failure(runner.RpcError({
            "code": -32602, "message": "invalid transaction arguments"})).category, "adapter-error")
        self.assertEqual(runner.evm_failure(runner.RpcError({"message": "stack overflow"}))["status"], "resource-limit")


class CoreProtocolTests(unittest.TestCase):
    deployment = {"stage": "deployment", "status": "returned", "output": "0x6000"}

    def rows(self, *rows):
        return "\n".join(json.dumps(row) for row in rows)

    def test_only_exact_deployment_and_call(self):
        self.assertEqual(len(runner.core_rows(self.rows(self.deployment, call()), 0)), 2)
        for values in ((call(),), (self.deployment,), (self.deployment, call(), call()),
                       (self.deployment, {**call(), "index": 1})):
            with self.assertRaises(ValueError):
                runner.core_rows(self.rows(*values), 0)
        with self.assertRaises(ValueError):
            runner.core_rows(self.rows(self.deployment, call()), 1)

    def test_resource_and_preparation_have_distinct_classes(self):
        with self.assertRaises(runner.Finding) as caught:
            runner.core_rows(self.rows({"stage": "deployment", "status": "out-of-fuel"}), 1)
        self.assertEqual(caught.exception.category, "inconclusive-resource")
        with self.assertRaises(runner.Finding) as caught:
            runner.core_rows(self.rows(self.deployment, {"stage": "preparation", "status": "rejected", "detail": "bad type"}), 1)
        self.assertEqual(caught.exception.category, "compilation-rejected")
        with self.assertRaises(runner.Finding) as caught:
            runner.core_rows(self.rows({"stage": "preparation", "status": "rejected", "detail": "specialization budget exhausted"}), 1)
        self.assertEqual(caught.exception.category, "inconclusive-resource")


class ProcessTests(unittest.TestCase):
    def make_runner(self, timeout=2, limit=65536):
        args = SimpleNamespace(total_timeout=5, timeout=timeout, output_limit=limit)
        return runner.Runner(args, {"processes": []})

    def test_real_process_output_and_receipt(self):
        instance = self.make_runner()
        result = instance.process("unit-process", [sys.executable, "-c", "print('executed')"])
        self.assertEqual(result["returncode"], 0)
        self.assertEqual(result["stdout"], "executed\n")
        self.assertEqual(instance.report["processes"], [result])

    def test_real_process_timeout(self):
        instance = self.make_runner(timeout=0.1)
        with self.assertRaises(runner.Finding) as caught:
            instance.process("unit-timeout", [sys.executable, "-c", "import time; time.sleep(10)"])
        self.assertEqual(caught.exception.category, "inconclusive-resource")
        self.assertEqual(instance.report["processes"][0]["resourceFailure"], "timeout")
        self.assertIsNotNone(instance.report["processes"][0]["returncode"])

    def test_real_process_output_limit(self):
        instance = self.make_runner(limit=64)
        with self.assertRaises(runner.Finding) as caught:
            instance.process("unit-output", [sys.executable, "-c", "print('x' * 10000)"])
        self.assertEqual(caught.exception.category, "inconclusive-resource")
        self.assertLessEqual(len(instance.report["processes"][0]["stdout"]), 64)

    def test_guard_stops_a_running_process(self):
        instance = self.make_runner()
        checks = 0

        def guard():
            nonlocal checks
            checks += 1
            if checks == 3:
                raise runner.Finding("inconclusive-resource", "campaign-disk", "budget exhausted")

        instance.args.resource_guard = guard
        with self.assertRaises(runner.Finding) as caught:
            instance.process("unit-guard", [sys.executable, "-c", "import time; time.sleep(10)"])
        self.assertEqual(caught.exception.stage, "campaign-disk")
        self.assertEqual(checks, 3)


class CancellationTests(unittest.TestCase):
    def test_sigterm_stops_owned_process_and_saves_report(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            marker = folder / "started"
            helper = folder / "case-tool"
            helper.write_text("#!" + sys.executable + "\nimport os, sys, time\nfrom pathlib import Path\n"
                "if sys.argv[1:] == ['--version']:\n    print('lifecycle-test 1')\nelse:\n"
                "    Path(" + repr(str(marker)) + ").write_text(str(os.getpid()))\n    time.sleep(20)\n")
            helper.chmod(0o700)
            case = folder / "case.json"
            # This envelope reaches the sleeping process; it is not a semantic result.
            case.write_text(json.dumps({"schema": runner.CASE_SCHEMA, "program": {},
                "source": "lifecycle test only", "provenance": {
                    key: "lifecycle-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
                "contract": {"name": "SynthesizedG0", "method": "run", "signature": "run()",
                    "deployPath": ["SynthesizedG0Deploy"], "runtimePath": ["SynthesizedG0Deploy", "SynthesizedG0"],
                    "calldata": "0xc0406226", "constructorCalldata": "0x"}}))
            output = folder / "run"
            process = subprocess.Popen([sys.executable, str(ROOT / "scripts/semantic-differential.py"),
                "--case", str(case), "--output", str(output), "--case-tool", str(helper),
                "--core-runner", str(helper), "--anvil", str(helper), "--timeout", "30",
                "--total-timeout", "60"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            child_pid = None
            try:
                deadline = time.monotonic() + 10
                while process.poll() is None and time.monotonic() < deadline:
                    if marker.exists() and marker.read_text():
                        child_pid = int(marker.read_text())
                        break
                    time.sleep(0.02)
                self.assertIsNotNone(child_pid)
                process.send_signal(signal.SIGTERM)
                stdout, stderr = process.communicate(timeout=10)
                self.assertEqual(process.returncode, 1, stderr + stdout)
                report = json.loads((output / "report.json").read_text())
                self.assertEqual(report["comparison"]["category"], "inconclusive-resource")
                self.assertEqual(report["comparison"]["detail"], "interrupted")
                with self.assertRaises(ProcessLookupError):
                    os.kill(child_pid, 0)
            finally:
                if process.poll() is None:
                    process.kill()
                process.communicate(timeout=5)
                if child_pid is None and marker.exists() and marker.read_text():
                    child_pid = int(marker.read_text())
                if child_pid is not None:
                    try:
                        os.killpg(child_pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass

    def test_original_sigterm_handler_is_restored(self):
        previous = signal.getsignal(signal.SIGTERM)

        def original_handler(_signal, _frame):
            self.fail("original handler must be replaced while the CLI runs")

        signal.signal(signal.SIGTERM, original_handler)
        try:
            with tempfile.TemporaryDirectory() as temporary:
                for interrupt in (False, True):
                    with self.subTest(interrupt=interrupt):
                        output = Path(temporary) / str(interrupt)

                        def execute(_args, report):
                            if interrupt:
                                os.kill(os.getpid(), signal.SIGTERM)
                            report["comparison"] = {"category": "matched", "pairs": {}}

                        with patch.object(sys, "argv", ["semantic-differential", "--case", "unused.json",
                                "--output", str(output)]), patch.object(runner, "execute", side_effect=execute), \
                                redirect_stdout(io.StringIO()):
                            self.assertEqual(runner.main(), int(interrupt))
                        self.assertIs(signal.getsignal(signal.SIGTERM), original_handler)
                        report = json.loads((output / "report.json").read_text())
                        self.assertEqual(report["comparison"]["category"],
                            "inconclusive-resource" if interrupt else "matched")
        finally:
            signal.signal(signal.SIGTERM, previous)


class ArtifactTests(unittest.TestCase):
    def archive(self, directory):
        case = directory / "case.json"
        case.write_text('{"case": 1}')
        image = directory / "images.json"
        image.write_text(json.dumps({"backend": {"name": "sonatina",
            "revision": runner.BACKEND_COMMIT, "optimization": "O0"}}))
        hashes = {path.name: runner.file_digest(path) for path in (case, image)}
        return {"schema": runner.REPORT_SCHEMA, "caseSha256": hashes["case.json"], "artifacts": hashes}

    def test_all_archived_members_must_retain_their_hashes(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            report = self.archive(directory)
            runner.verify_archive(directory, report)
            image = directory / "images.json"
            image.write_text('{"image": 2}')
            with self.assertRaisesRegex(ValueError, "hash changed: images.json"):
                runner.verify_archive(directory, report)
            image.unlink()
            with self.assertRaisesRegex(ValueError, "missing or is not a regular file: images.json"):
                runner.verify_archive(directory, report)

    def test_archive_rejects_path_escape_symlink_and_invalid_inventory(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            report = self.archive(directory)
            for name in ("../outside", "/absolute", "nested/file", "nested\\file", ".", "..", "report.json"):
                malformed = {**report, "artifacts": {**report["artifacts"], name: "0" * 64}}
                with self.assertRaisesRegex(ValueError, "plain file name"):
                    runner.verify_archive(directory, malformed)
            (directory / "alias").symlink_to(directory / "case.json")
            malformed = {**report, "artifacts": {**report["artifacts"], "alias": report["caseSha256"]}}
            with self.assertRaisesRegex(ValueError, "not a regular file"):
                runner.verify_archive(directory, malformed)
            for malformed in ({**report, "schema": "unknown"}, {**report, "artifacts": {}},
                              {**report, "caseSha256": "0" * 64}):
                with self.assertRaises(ValueError):
                    runner.verify_archive(directory, malformed)

    def test_file_hash_uses_streaming_reads(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "large-artifact"
            chunk = b"x" * 65536
            with path.open("wb") as output:
                for _ in range(32):
                    output.write(chunk)
            expected = runner.digest(chunk * 32)
            with patch.object(Path, "read_bytes", side_effect=AssertionError("unbounded read")):
                self.assertEqual(runner.file_digest(path), expected)

    def test_exact_path_selection_and_unique_images(self):
        image = {"path": ["C"], "bytes": "0x6000"}
        envelope = {"schema": "solcore-rs.code-images.v1", "upstreamCommit": runner.UPSTREAM_COMMIT, "images": [image]}
        self.assertEqual(runner.image_bytes(envelope, ["C"]), b"\x60\x00")
        for images in ([], [image, image]):
            with self.assertRaises(ValueError):
                runner.image_bytes({**envelope, "images": images}, ["C"])

    def test_file_budget_is_enforced(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "case.json"
            path.write_text('{"x":"123456789"}')
            with self.assertRaises(runner.Finding):
                runner.read_json(path, 4)


class SharedCompilationTests(unittest.TestCase):
    """Sharing policy with a stand-in exporter; campaigns check real compilations."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.target, self.upstream = self.root / "target", self.root / "upstream"
        for name in runner.COMPILERS:
            (self.target / name).parent.mkdir(parents=True, exist_ok=True)
            (self.target / name).write_text("build of " + name)
        (self.upstream / "std").mkdir(parents=True)
        (self.upstream / "std/prelude.sol").write_text("library")
        self.cache = runner.CompileCache(self.root / "compilations")
        self.exports, self.counter = [], 0

    def tearDown(self):
        self.temporary.cleanup()

    def case(self, source="contract A {}", backend="sonatina-o0"):
        self.counter += 1
        output = self.root / f"run-{self.counter}"
        output.mkdir()
        (output / "case.sol").write_text(source)
        args = SimpleNamespace(output=output, upstream=self.upstream, target_dir=self.target, timeout=10,
                               artifact_limit=1024 * 1024, replay=None, compile_cache=self.cache)
        report = {"processes": [], "pathBackends": runner.path_backends(backend),
                  "tools": {"runnerSha256": "runner", "exporters": {"export-rust-hull.py": "exporter"}}}
        return args, report, {"source": source, "contract": {"name": "SynthesizedInput"}}

    def stages(self, failure=None):
        """Both export stages: hull.json, a process record, then images.json or a failure."""
        def export(args, process_runner, directory, source, linked_backend, audit):
            self.exports.append((directory, linked_backend))
            audit()
            (directory / "hull.json").write_text("hull of " + source.read_text())
            process_runner.report["processes"].append({"stage": "rust-checked-source", "returncode": 0})
            if failure:
                raise runner.Finding(*failure)
            (directory / "images.json").write_text("images of " + source.read_text())
        return patch.object(runner, "export_sources", side_effect=export)

    def compile(self, args, report, case, backend="sonatina-o0", receipt=None, audited=None):
        """Compile or reuse, then raise a shared Sonatina failure as the runner does."""
        audit = (lambda directory=None: audited.append(directory)) if audited is not None else (lambda directory=None: None)
        entry = self.cache.compile(args, SimpleNamespace(report=report), case, report, backend, receipt, audit)
        runner.CompileCache.fail(entry)
        return entry

    def test_identical_sources_share_one_compilation_and_keep_their_own_copies(self):
        with self.stages():
            first_args, first, case = self.case()
            entry = self.compile(first_args, first, case)
            second_args, second, case = self.case()
            self.assertIs(self.compile(second_args, second, case), entry)
        self.assertEqual(len(self.exports), 1)
        shared = entry["directory"]
        identity = first["compilation"]["identity"]
        self.assertEqual(shared, self.cache.directory / first["compilation"]["key"])
        self.assertEqual(first["compilation"]["key"], runner.digest(runner.json_bytes(identity)))
        self.assertEqual(second["compilation"]["identity"], identity)
        self.assertEqual(identity["sources"], {"case.sol": runner.file_digest(first_args.output / "case.sol")})
        self.assertEqual(identity["library"], {"prelude.sol": runner.file_digest(self.upstream / "std/prelude.sol")})
        self.assertEqual(identity["compilers"], {name: runner.file_digest(self.target / name) for name in runner.COMPILERS})
        self.assertEqual((first["compilation"]["reused"], second["compilation"]["reused"]), (False, True))
        self.assertEqual(entry["source"], shared / "case.sol")
        self.assertEqual(first["compilation"]["outputs"],
                         {name: runner.file_digest(shared / name) for name in ("hull.json", "images.json")})
        for args in (first_args, second_args):
            for name in ("hull.json", "images.json"):
                self.assertEqual((args.output / name).read_bytes(), (shared / name).read_bytes())
        # The compiling case ran the stage itself; the other case records it as shared.
        self.assertEqual(second["processes"], [{**first["processes"][0], "reused": True}])
        self.assertNotIn("reused", first["processes"][0])

    def test_a_different_source_backend_tool_or_library_compiles_again(self):
        changes = [lambda report: None, lambda report: None,
                   lambda report: (self.target / "debug/solcore-driver").write_text("rebuilt driver"),
                   lambda report: report["tools"]["exporters"].update({"export-rust-hull.py": "changed"}),
                   lambda report: (self.upstream / "std/prelude.sol").write_text("changed library")]
        keys = []
        with self.stages():
            for index, change in enumerate(changes):
                backend = "sonatina-o2" if index == 1 else "sonatina-o0"
                args, report, case = self.case("contract B {}" if index == 0 else "contract A {}", backend)
                change(report)
                self.compile(args, report, case, backend)
                self.assertFalse(report["compilation"]["reused"])
                keys.append(report["compilation"]["key"])
        self.assertEqual(len(set(keys)), len(changes))
        self.assertEqual([backend for _, backend in self.exports],
                         ["sonatina-o0", "sonatina-o2", "sonatina-o0", "sonatina-o0", "sonatina-o0"])

    def test_rejections_and_crashes_are_shared_without_compiling_again(self):
        for category in runner.SHARED_FAILURES:
            with self.subTest(category=category):
                self.cache, self.exports = runner.CompileCache(self.root / ("compilations-" + category)), []
                failure = (category, "rust-code-images", "rejected: " + category)
                outcomes = []
                with self.stages(failure):
                    for _ in range(3):
                        args, report, case = self.case()
                        with self.assertRaises(runner.Finding) as caught:
                            self.compile(args, report, case)
                        outcomes.append((args, report, caught.exception))
                self.assertEqual(len(self.exports), 1)
                for args, report, error in outcomes:
                    self.assertEqual((error.category, error.stage, error.detail), failure)
                    self.assertEqual(report["compilation"]["failure"], {"category": category, "stage": "rust-code-images"})
                    # Partial outputs stay in every affected case's own archive.
                    self.assertTrue((args.output / "hull.json").is_file())
                    self.assertFalse((args.output / "images.json").exists())
                compiled = outcomes[0][1]["processes"]
                self.assertEqual([report["processes"] for _, report, _ in outcomes[1:]],
                                 [[{**compiled[0], "reused": True}]] * 2)

    def test_a_shared_failure_is_raised_where_its_own_stage_would_raise_it(self):
        yul = {"failure": {"category": "compilation-rejected", "stage": "rust-yul-evm", "detail": "solc rejected"}}
        images = {"failure": {"category": "compiler-crash", "stage": "rust-code-images", "detail": "panicked at"}}
        # A Yul failure waits until the copied Sonatina exports are checked.
        runner.CompileCache.fail(yul)
        runner.CompileCache.fail(images, yul=True)
        for entry, yul_stage in ((yul, True), (images, False)):
            with self.assertRaises(runner.Finding) as caught:
                runner.CompileCache.fail(entry, yul=yul_stage)
            self.assertEqual((caught.exception.category, caught.exception.stage, caught.exception.detail),
                             tuple(entry["failure"].values()))
        for yul_stage in (False, True):
            runner.CompileCache.fail({"failure": None}, yul=yul_stage)

    def test_resource_adapter_and_interrupted_compilations_are_not_kept(self):
        for failure in (("inconclusive-resource", "rust-code-images", "timeout"),
                        ("adapter-error", "rust-checked-source", "export-rust-hull: receipt is stale")):
            with self.subTest(category=failure[0]):
                self.exports = []
                with self.stages(failure):
                    for _ in range(2):
                        args, report, case = self.case()
                        with self.assertRaises(runner.Finding):
                            self.compile(args, report, case)
                        self.assertNotIn("compilation", report)
                        self.assertEqual(list(self.cache.directory.iterdir()), [])
                self.assertEqual(len(self.exports), 2)
        with patch.object(runner, "export_sources", side_effect=KeyboardInterrupt):
            args, report, case = self.case()
            with self.assertRaises(KeyboardInterrupt):
                self.compile(args, report, case)
        self.assertEqual((self.cache.entries, list(self.cache.directory.iterdir())), ({}, []))

    def test_a_changed_shared_output_is_rejected_rather_than_copied(self):
        with self.stages():
            args, report, case = self.case()
            entry = self.compile(args, report, case)
            (entry["directory"] / "images.json").write_text("changed images")
            args, report, case = self.case()
            with self.assertRaisesRegex(ValueError, "shared compilation output changed: images.json"):
                self.compile(args, report, case)

    def test_least_recently_used_compilations_are_deleted(self):
        self.cache.capacity = 2
        with self.stages():
            directories = []
            for source in ("contract A {}", "contract B {}", "contract A {}", "contract C {}"):
                args, report, case = self.case(source)
                directories.append(self.compile(args, report, case)["directory"])
            # A was used again after B, so C evicts B.
            self.assertEqual([path.exists() for path in directories], [True, False, True, True])
            args, report, case = self.case("contract B {}")
            self.compile(args, report, case)
            self.assertFalse(report["compilation"]["reused"])
        self.assertEqual(len(self.exports), 4)
        self.assertEqual(len(list(self.cache.directory.iterdir())), 2)

    def test_bundle_provenance_names_the_shared_files_with_the_cases_own_digests(self):
        bundle = runner.bundle_transport
        case = {"source": "import common;", "contract": {"name": "SynthesizedModules"},
                "sourceBundle": {"schema": bundle.SCHEMA, "entry": "case.sol", "files": [
                    {"path": name, "source": "import common;" if name == "case.sol" else "module " + name}
                    for name in bundle.FILES]}}
        receipts, audited = [], []
        with self.stages():
            for _ in range(2):
                args, report, _ = self.case()
                (args.output / "case.sol").unlink()
                receipt = {**bundle.write(args.output, case), "libraries": {(self.upstream / "std/prelude.sol").as_uri(): "0" * 64}}
                entry = self.compile(args, report, case, receipt=receipt, audited=audited)
                receipts.append(receipt)
        self.assertEqual(len(self.exports), 1)
        shared = entry["receipt"]
        self.assertEqual(shared["generatedUris"], {(entry["directory"] / name).resolve().as_uri(): name for name in bundle.FILES})
        self.assertEqual((shared["files"], shared["libraries"]), (receipts[0]["files"], receipts[0]["libraries"]))
        self.assertEqual(set(report["compilation"]["identity"]["sources"]), set(bundle.FILES))
        self.assertIn(entry["directory"], audited)
        bundle.audit_files(entry["directory"], shared["files"])

    def test_yul_compilations_share_their_yul_export(self):
        calls = []

        def transport(operation, args, process_runner, case, source, hull, report):
            calls.append((operation, args.output, source, hull, report["exportProvenance"]))
            (args.output / "yul.json").write_text("yul of " + source.read_text())
            report["yulExportProvenance"] = {"record": "yul"}

        exported = {"hull": {"sources": {}}, "images": {}}
        with self.stages(), patch.object(runner, "validate_export", return_value=exported), \
                patch.object(runner, "yul_transport", side_effect=transport):
            for _ in range(2):
                args, report, case = self.case(backend="yul")
                report["tools"].update(solc={"sha256": "solc", "version": "0.8.35"},
                                       yulExporterSha256="exporter", yulTransportSha256="transport")
                entry = self.compile(args, report, case, "yul")
                self.assertEqual((args.output / "yul.json").read_text(), "yul of contract A {}")
        directory = entry["directory"]
        self.assertEqual(calls, [("execute", directory, directory / "case.sol", directory / "hull.json", exported)])
        self.assertEqual(entry["yul"], {"record": "yul"})
        # The imported Hull path of a Yul run executes Sonatina O0 images.
        self.assertEqual(self.exports, [(directory, "sonatina-o0")])
        self.assertEqual(report["compilation"]["identity"]["yul"]["solc"], {"sha256": "solc", "version": "0.8.35"})

    def test_a_copied_yul_export_must_equal_its_shared_record(self):
        args, report, case = self.case(backend="yul")
        (args.output / "yul.json").write_text(json.dumps({"initCode": "0x6001", "runtimeCode": "0x00"}))
        report["exportProvenance"] = {"hull": {}}
        validated = lambda operation, *_: {"record": "copied"} if operation == "validate_export" else None
        with patch.object(runner, "yul_transport", side_effect=validated):
            self.assertEqual(runner.accept_yul(args, case, report, {"record": "copied"}), (b"\x60\x01", b"\x00"))
            self.assertEqual(report["yulExportProvenance"], {"record": "copied"})
            with self.assertRaisesRegex(ValueError, "differs from its shared compilation"):
                runner.accept_yul(args, case, report, {"record": "shared"})

    def test_exact_replay_never_shares_a_compilation(self):
        self.assertIs(runner.shared_compilations(SimpleNamespace(replay=None, compile_cache=self.cache)), self.cache)
        self.assertIsNone(runner.shared_compilations(SimpleNamespace(replay=self.root, compile_cache=self.cache)))
        self.assertIsNone(runner.shared_compilations(SimpleNamespace(replay=None)))


class BackendTests(unittest.TestCase):
    def test_default_legacy_and_exact_replay_selection(self):
        self.assertEqual(runner.resolve_backend(None), "sonatina-o0")
        self.assertEqual(runner.resolve_backend(None, {}), "sonatina-o0")
        for backend in runner.BACKENDS:
            self.assertEqual(runner.resolve_backend(backend), backend)
            self.assertEqual(runner.resolve_backend(None, {"backend": backend}), backend)
            self.assertEqual(runner.resolve_backend(backend, {"backend": backend}), backend)
            for other in set(runner.BACKENDS) - {backend}:
                with self.assertRaisesRegex(ValueError, "retains the saved backend"):
                    runner.resolve_backend(other, {"backend": backend})
        for invalid in (None, [], {}, True, "O2", "sonatina-o1", "yul-o0"):
            with self.assertRaisesRegex(ValueError, "unsupported saved backend"):
                runner.resolve_backend(None, {"backend": invalid})

    def test_actual_image_configuration_must_match_selection(self):
        for backend, level in (("sonatina-o0", "O0"), ("sonatina-o2", "O2")):
            image = {"backend": {"name": "sonatina", "revision": runner.BACKEND_COMMIT,
                                 "optimization": level}}
            runner.validate_image_backend(image, backend)
            for key, bad in (("name", "yul"), ("revision", "0" * 40),
                             ("optimization", "O0" if level == "O2" else "O2")):
                with self.assertRaisesRegex(ValueError, "code image backend differs"):
                    runner.validate_image_backend({"backend": {**image["backend"], key: bad}}, backend)
        with self.assertRaisesRegex(ValueError, "code image backend differs"):
            runner.validate_image_backend({}, "sonatina-o0")

    def test_saved_report_cannot_relabel_its_artifact(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            report = ArtifactTests().archive(directory)
            with self.assertRaisesRegex(ValueError, "code image backend differs"):
                runner.verify_archive(directory, {**report, "backend": "sonatina-o2"})
            report["exportProvenance"] = {"images": {"backendRevision": runner.BACKEND_COMMIT,
                                                        "optimization": "O2"}}
            with self.assertRaisesRegex(ValueError, "saved export provenance differs"):
                runner.verify_archive(directory, report)

    def test_export_provenance_and_artifact_both_match_backend(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            source, hull, image = (directory / name for name in ("case.sol", "hull.json", "images.json"))
            source.write_text("// protocol fixture only")
            hull.write_text(json.dumps({"schema": "solcore-rs.hull.v1", "upstreamCommit": runner.UPSTREAM_COMMIT}))
            hp = {"sources": {source.as_uri(): runner.file_digest(source)}, "outputSha256": runner.file_digest(hull)}
            hull.with_suffix(".json.provenance.json").write_text(json.dumps(hp))
            for backend, level in (("sonatina-o0", "O0"), ("sonatina-o2", "O2")):
                image.write_text(json.dumps({"backend": {"name": "sonatina", "revision": runner.BACKEND_COMMIT,
                                                        "optimization": level}}))
                ip = {"sources": hp["sources"], "hullProvenance": hp, "outputSha256": runner.file_digest(image),
                      "backendRevision": runner.BACKEND_COMMIT, "optimization": level}
                image.with_suffix(".json.provenance.json").write_text(json.dumps(ip))
                self.assertEqual(runner.validate_export(hull, image, source, 4096, backend), {"hull": hp, "images": ip})
                ip["optimization"] = "O0" if level == "O2" else "O2"
                image.with_suffix(".json.provenance.json").write_text(json.dumps(ip))
                with self.assertRaisesRegex(ValueError, "backend revision/optimization differs"):
                    runner.validate_export(hull, image, source, 4096, backend)


class YulAdapterBoundaryTests(unittest.TestCase):
    def test_yul_path_labels_keep_linked_hull_separate(self):
        self.assertEqual(runner.path_backends("yul"), {"directCore": "original-core",
            "importedHull": "sonatina-o0", "rustEvm": "yul"})
        for backend in runner.SONATINA_BACKENDS:
            self.assertEqual(runner.path_backends(backend), {"directCore": "original-core",
                "importedHull": backend, "rustEvm": backend})
        with self.assertRaisesRegex(ValueError, "only Sonatina"):
            runner.optimization_for_backend("yul")
        for explicit, saved in (("yul", None), (None, {"backend": "yul"})):
            with self.assertRaisesRegex(ValueError, "stateful comparisons require"):
                runner.resolve_sonatina_backend(explicit, saved)

    def test_foreign_transport_failure_retains_category_stage_and_detail(self):
        # The helper has a distinct importlib module/class. This tests exception
        # transport, not a simulated compiler or runtime result.
        spec = importlib.util.spec_from_file_location("test_yul_transport", ROOT / "scripts/semantic-yul.py")
        helper = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(helper)
        self.assertIsNot(helper.common.Finding, runner.Finding)
        for category in ("inconclusive-resource", "compilation-rejected", "compiler-crash", "adapter-error"):
            def operation():
                raise helper.common.Finding(category, "rust-yul-evm", "transport test")
            module = SimpleNamespace(common=helper.common, operation=operation)
            with patch.object(runner, "_yul_module", module), self.assertRaises(runner.Finding) as caught:
                runner.yul_transport("operation")
            self.assertEqual((caught.exception.category, caught.exception.stage, caught.exception.detail),
                             (category, "rust-yul-evm", "transport test"))

    def test_archive_cannot_relabel_imported_hull_as_yul(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            report = ArtifactTests().archive(directory)
            report.update(backend="yul", pathBackends={"directCore": "original-core", "importedHull": "yul", "rustEvm": "yul"})
            with self.assertRaisesRegex(ValueError, "execution path backends differ"):
                runner.verify_archive(directory, report)

    def test_malformed_replay_report_is_rejected_before_output_creation(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            archive = folder / "archive"
            archive.mkdir()
            for value in (None, [], "invalid", {"budgets": None}, {"budgets": []}, {"budgets": "invalid"}):
                (archive / "report.json").write_text(json.dumps(value))
                output = folder / "never-created"
                with patch.object(sys, "argv", ["semantic-differential.py", "--replay", str(archive),
                        "--output", str(output)]), patch.object(sys, "stderr", io.StringIO()), \
                        self.assertRaises(SystemExit) as caught:
                    runner.main()
                self.assertEqual(caught.exception.code, 2)
                self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
