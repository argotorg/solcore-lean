#!/usr/bin/env python3
"""Focused protocol/classification tests; these do not simulate EVM execution.

The process tests execute real bounded Python subprocesses. End-to-end compiler,
Core and Anvil validation is performed with semantic-differential.py itself.
"""
import importlib.util
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
                       runner.AGGREGATE_CASE_SCHEMA, runner.LOOP_CASE_SCHEMA, runner.GENERIC_CASE_SCHEMA, runner.CLOSURE_CASE_SCHEMA, runner.COMPTIME_CASE_SCHEMA):
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
                case["contract"].update(name=name,
                    deployPath=[name + "Deploy"], runtimePath=[name + "Deploy", name])
                runner.validate_case(case)
                with self.assertRaises(runner.Finding):
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
        image.write_text('{"image": 1}')
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


if __name__ == "__main__":
    unittest.main()
