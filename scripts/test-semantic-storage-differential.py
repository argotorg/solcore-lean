#!/usr/bin/env python3
"""Protocol and classification tests, not a Python storage execution oracle.

Synthetic histories test comparison policy only. RPC doubles test requests and
receipts without simulating a chain; the cancellation test owns a real bounded
Python subprocess. Compiler/Core/EVM agreement is tested by the actual adapter.
"""
from contextlib import contextmanager, redirect_stdout
import copy
import importlib.util
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
from unittest.mock import Mock, patch
import urllib.error

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("storage_differential", ROOT / "scripts/semantic-storage-differential.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def case(count=3):
    """Envelope fixture only: the native checker would reject the empty ASTs."""
    return {"schema": runner.CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "storagePlan": {"schema": "solcore-lean.storage-plan.v1", "stepProgram": {}},
        "initialState": {"storage": []}, "observedSlots": ["0", "1"],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedStorage", "method": "run", "signature": "run(uint256)",
            "selector": "0xa444f5e9", "deployPath": ["SynthesizedStorageDeploy"],
            "runtimePath": ["SynthesizedStorageDeploy", "SynthesizedStorage"], "constructorCalldata": "0x"},
        "transactions": [{"id": f"tx-{index}", "input": str(index), "value": "0",
            "calldata": "0xa444f5e9" + f"{index:064x}"} for index in range(count)]}


def slots(first=0, second=0):
    return [{"slot": "0", "value": str(first)}, {"slot": "1", "value": str(second)}]


def row(index, value=7, first=3, second=4, status="returned"):
    result = {"stage": "execution", "id": f"tx-{index}", "index": index,
        "status": status, "committedStorage": slots(first, second)}
    result.update({"output": "0x" + f"{value:064x}"} if status in ("returned", "reverted") else {"detail": "test resource"})
    return result


def history(value=None, rows=None):
    value = case() if value is None else value
    rows = [row(index) for index in range(len(value["transactions"]))] if rows is None else rows
    complete = len(rows) == len(value["transactions"]) and all(r["status"] in ("returned", "reverted") for r in rows)
    return {"schema": runner.HISTORY_SCHEMA, "initialStorage": slots(), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"] if rows else slots()),
        "status": "complete" if complete else "incomplete",
        "unexecuted": [tx["id"] for tx in value["transactions"][len(rows):]]}


def histories(value=None):
    return {name: history(value) for name in runner.PATHS}


class CaseTests(unittest.TestCase):
    def test_fixed_wrapper_and_canonical_abi_inputs(self):
        for count in (1, 2, 3):
            runner.validate_case(case(count))
        value = case(1)
        value["transactions"][0].update(input=str(2**256 - 1), calldata="0xa444f5e9" + "ff" * 32)
        runner.validate_case(value)
        for key, changed in (("input", "01"), ("input", str(2**256)), ("value", "1"),
                             ("calldata", "0x"), ("calldata", "0xa444f5e9" + "ff" * 31)):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)

    def test_scope_and_transaction_identity_are_explicit(self):
        for changed in ({"initialState": {"storage": slots(1, 0)}}, {"observedSlots": ["1", "0"]},
                        {"contract": {}}):
            with self.subTest(changed=changed), self.assertRaises(runner.Finding):
                runner.validate_case({**case(), **changed})
        for count in (0, 4):
            with self.assertRaises(ValueError):
                runner.validate_case(case(count))
        for identifier in (None, "", "../tx", "x" * 65, "tx-0"):
            invalid = case()
            invalid["transactions"][1]["id"] = identifier
            with self.subTest(identifier=identifier), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        with self.assertRaises(ValueError):
            runner.validate_case({**case(), "storagePlan": {}})


class HistoryTests(unittest.TestCase):
    def test_all_three_completed_histories_are_required(self):
        actual = histories()
        self.assertEqual(runner.compare(actual, case())["category"], "matched")
        del actual["importedHull"]
        self.assertEqual(runner.compare(actual, case())["category"], "adapter-error")
        actual = histories()
        actual["unexpected"] = history()
        self.assertEqual(runner.compare(actual, case())["category"], "adapter-error")

    def test_intermediate_differences_cannot_be_hidden_by_later_convergence(self):
        for field, changed in (("output", "0x" + f"{8:064x}"), ("committedStorage", slots(99, 4))):
            actual = histories()
            actual["rustEvm"]["transactions"][0][field] = changed
            self.assertEqual(actual["directCore"]["finalStorage"], actual["rustEvm"]["finalStorage"])
            result = runner.compare(actual, case())
            self.assertEqual((result["category"], result["transactionId"], result["index"]),
                             ("semantic-mismatch", "tx-0", 0))
            self.assertIn(field, result["fields"])
            self.assertEqual(result["pairs"], {"directCore/rustEvm": False,
                "directCore/importedHull": True, "importedHull/rustEvm": False})

    def test_secondary_path_difference_is_not_hidden_by_primary_agreement(self):
        actual = histories()
        actual["importedHull"]["transactions"][1]["committedStorage"] = slots(8, 4)
        result = runner.compare(actual, case())
        self.assertEqual(result["category"], "semantic-mismatch")
        self.assertTrue(result["pairs"]["directCore/rustEvm"])
        self.assertFalse(result["pairs"]["directCore/importedHull"])

    def test_wrong_abi_length_and_reverts_never_count_as_normal_agreement(self):
        for output in ("0x", "0x" + "00" * 31, "0x" + "00" * 33):
            actual = histories()
            for observed in actual.values():
                observed["transactions"][0]["output"] = output
            self.assertEqual(runner.compare(actual, case())["category"], "semantic-mismatch")
        actual = {name: history(rows=[row(i, status="reverted") for i in range(3)]) for name in runner.PATHS}
        self.assertEqual(runner.compare(actual, case())["category"], "semantic-mismatch")

    def test_identical_resource_rows_and_faults_are_not_matching_execution(self):
        for status in runner.RESOURCE_STATUSES | {"core-fault", "evm-exceptional", "not-executed"}:
            actual = {name: history(rows=[row(0), row(1, status=status)]) for name in runner.PATHS}
            result = runner.compare(actual, case())
            expected = "inconclusive-resource" if status in runner.RESOURCE_STATUSES else "execution-error"
            self.assertEqual((result["category"], result["index"]), (expected, 1))

    def test_earlier_mismatch_survives_a_later_resource_failure(self):
        actual = {name: history(rows=[row(0), row(1, status="out-of-gas")]) for name in runner.PATHS}
        actual["importedHull"]["transactions"][0]["output"] = "0x" + f"{9:064x}"
        result = runner.compare(actual, case())
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-0"))

    def test_a_missing_later_execution_is_inconclusive_with_exact_ids(self):
        actual = histories()
        actual["rustEvm"] = history(rows=[row(0)])
        result = runner.compare(actual, case())
        self.assertEqual((result["category"], result["transactionId"]), ("inconclusive-resource", "tx-1"))
        self.assertEqual(runner.normalize_history(actual["rustEvm"], case())["unexecuted"], ["tx-1", "tx-2"])
        for unexecuted in ([], ["tx-2", "tx-1"], ["tx-0", "tx-1", "tx-2"], 2):
            invalid = {**actual["rustEvm"], "unexecuted": unexecuted}
            with self.subTest(unexecuted=unexecuted), self.assertRaises(ValueError):
                runner.normalize_history(invalid, case())

    def test_attempted_resource_row_does_not_hide_remaining_transaction_ids(self):
        value = history(rows=[row(0), row(1, status="out-of-fuel")])
        self.assertEqual(runner.normalize_history(value, case())["unexecuted"], ["tx-2"])
        with self.assertRaises(ValueError):
            runner.normalize_history(history(rows=[row(0, status="timeout"), row(1)]), case())
        with self.assertRaises(ValueError):
            runner.normalize_history({**value, "status": "complete"}, case())

    def test_unknown_completion_is_distinct_from_transactions_never_submitted(self):
        value = history(rows=[row(0)])
        value.update(unobserved=["tx-1"], unexecuted=["tx-2"], finalStorage=None)
        normalized = runner.normalize_history(value, case())
        self.assertEqual((normalized["unobserved"], normalized["unexecuted"], normalized["finalStorage"]),
                         (["tx-1"], ["tx-2"], None))
        result = runner.compare({**histories(), "rustEvm": value}, case())
        self.assertEqual((result["category"], result["transactionId"]), ("inconclusive-resource", "tx-1"))
        for changes in ({"unobserved": ["tx-2"]}, {"unobserved": ["tx-1", "tx-2"]},
                        {"unexecuted": ["tx-1", "tx-2"]}, {"finalStorage": slots(3, 4)}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                runner.normalize_history({**value, **changes}, case())
        with self.assertRaises(ValueError):
            runner.normalize_history({**history(), "unobserved": ["tx-2"]}, case())

    def test_no_later_submission_after_an_incomplete_transaction(self):
        stopped = history(rows=[row(0, status="out-of-fuel")])
        stopped.update(unobserved=["tx-1"], unexecuted=["tx-2"], finalStorage=None)
        with self.assertRaisesRegex(ValueError, "submission continued"):
            runner.normalize_history(stopped, case())

    def test_prefix_difference_survives_unknown_later_completion(self):
        actual = histories()
        value = history(rows=[row(0, value=8)])
        value.update(unobserved=["tx-1"], unexecuted=["tx-2"], finalStorage=None)
        actual["rustEvm"] = value
        result = runner.compare(actual, case())
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-0"))

    def test_missing_misordered_duplicate_or_boolean_indices_are_rejected(self):
        for index, changed in ((0, {"id": None}), (1, {"id": "tx-0"}),
                               (1, {"index": 0}), (0, {"index": False})):
            invalid = history()
            invalid["transactions"][index].update(changed)
            self.assertEqual(runner.compare({**histories(), "rustEvm": invalid}, case())["category"], "adapter-error")
        invalid = history()
        invalid["transactions"][0], invalid["transactions"][1] = invalid["transactions"][1], invalid["transactions"][0]
        with self.assertRaises(ValueError):
            runner.normalize_history(invalid, case())

    def test_storage_and_final_observations_are_complete_and_canonical(self):
        for invalid in ([], slots()[:1], slots() + slots(), slots()[::-1],
                        [{"slot": "0", "value": "0"}] * 2, slots("01", 0), slots(-1, 0), slots(2**256, 0)):
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                runner.storage(invalid)
        with self.assertRaises(ValueError):
            runner.normalize_history({**history(), "finalStorage": slots(88, 99)}, case())
        actual = histories()
        for observed in actual.values():
            observed["initialStorage"] = slots(1, 0)
        result = runner.compare(actual, case())
        self.assertEqual((result["category"], result["stage"]), ("semantic-mismatch", "initial-storage"))


class HullProtocolTests(unittest.TestCase):
    def lines(self, *values):
        return "\n".join(json.dumps(value) for value in values)

    def test_completed_and_incomplete_committed_prefixes(self):
        deployment = {"stage": "deployment", "status": "returned", "committedStorage": slots()}
        complete = runner.hull_history(self.lines(deployment, row(0), row(1), row(2)), 0, case())
        self.assertEqual(complete["status"], "complete")
        partial = runner.hull_history(self.lines(deployment, row(0), row(1, status="out-of-fuel")), 1, case())
        self.assertEqual((partial["status"], partial["unexecuted"]), ("incomplete", ["tx-2"]))
        self.assertEqual(partial["finalStorage"], row(1)["committedStorage"])

    def test_unexplained_exit_and_corrupt_output_do_not_become_histories(self):
        deployment = {"stage": "deployment", "status": "returned", "committedStorage": slots()}
        for text, code in (("", 0), ("[]", 0), ("garbage", 0),
                           (self.lines(deployment, row(0), row(1), row(2)), 1),
                           (self.lines(deployment, row(0), row(1), row(2), row(3)), 0),
                           (self.lines(deployment, {**row(0), "stage": "unknown"}), 0),
                           (self.lines(deployment), -9)):
            with self.subTest(text=text, code=code), self.assertRaises(ValueError):
                runner.hull_history(text, code, case())

    def test_preparation_and_deployment_resources_remain_distinct(self):
        for stage, status, detail, expected in (("preparation", "rejected", "bad type", "compilation-rejected"),
                ("preparation", "rejected", "specialization budget exhausted", "inconclusive-resource"),
                ("deployment", "out-of-fuel", "", "inconclusive-resource"),
                ("deployment", "reverted", "", "execution-error")):
            with self.subTest(stage=stage, detail=detail), self.assertRaises(runner.Finding) as caught:
                runner.hull_history(self.lines({"stage": stage, "status": status, "detail": detail}), 1, case())
            self.assertEqual(caught.exception.category, expected)


class RpcProtocolTests(unittest.TestCase):
    tx_hash = "0x" + "12" * 32
    address = "0x" + "34" * 20

    def receipt_value(self, **changes):
        return {"transactionHash": self.tx_hash, "blockNumber": "0xa", "status": "0x1", **changes}

    def test_receipt_polling_retains_the_actual_block_and_transaction(self):
        rpc = Mock()
        rpc.call.side_effect = [None, self.receipt_value()]
        clock = SimpleNamespace(args=SimpleNamespace(timeout=10), remaining=lambda _: 10)
        with patch.object(runner.time, "sleep"):
            mined = runner.receipt(rpc, self.tx_hash, clock)
        self.assertEqual(mined["blockNumber"], "0xa")
        self.assertEqual(rpc.call.call_args_list, [unittest.mock.call("eth_getTransactionReceipt", [self.tx_hash])] * 2)
        rpc.reset_mock(side_effect=True)
        rpc.call.side_effect = ["0x" + f"{17:064x}", "0x" + f"{18:064x}"]
        self.assertEqual(runner.evm_storage(rpc, self.address, mined["blockNumber"]), slots(17, 18))
        self.assertEqual(rpc.call.call_args_list, [
            unittest.mock.call("eth_getStorageAt", [self.address, "0x0", "0xa"]),
            unittest.mock.call("eth_getStorageAt", [self.address, "0x1", "0xa"])])

    def test_bad_receipt_identity_status_block_and_storage_are_rejected(self):
        clock = SimpleNamespace(args=SimpleNamespace(timeout=1), remaining=lambda _: 1)
        for changes in ({"transactionHash": "0x" + "ff" * 32}, {"status": "0x2"},
                        {"blockNumber": "latest"}, {"blockNumber": "0x00"}):
            rpc = Mock()
            rpc.call.return_value = self.receipt_value(**changes)
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                runner.receipt(rpc, self.tx_hash, clock)
        rpc = Mock()
        with self.assertRaises(ValueError):
            runner.receipt(rpc, "0x12", clock)
        rpc.call.assert_not_called()
        for raw in ("0x", "0x0", "0x" + "00" * 31, "0x" + "00" * 33):
            rpc.call.return_value = raw
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                runner.evm_storage(rpc, self.address, "0xa")
        with self.assertRaises(ValueError):
            runner.evm_storage(rpc, self.address, "latest")

    def test_receipt_timeout_never_resubmits(self):
        rpc = Mock()
        rpc.call.return_value = None
        clock = SimpleNamespace(args=SimpleNamespace(timeout=1), remaining=lambda _: 1)
        with patch.object(runner.time, "monotonic", side_effect=[0, 2]), self.assertRaises(runner.Finding) as caught:
            runner.receipt(rpc, self.tx_hash, clock)
        self.assertEqual(caught.exception.category, "inconclusive-resource")
        self.assertIn("not resubmitted", caught.exception.detail)
        rpc.call.assert_called_once_with("eth_getTransactionReceipt", [self.tx_hash])

    def test_unknown_submission_timeout_is_recorded_and_never_retried(self):
        request = {"to": self.address, "data": "0x01"}
        for failure in (TimeoutError("socket timed out"), urllib.error.URLError("unknown response")):
            rpc = Mock()
            rpc.call.side_effect = failure
            record = {}
            with self.subTest(failure=failure), self.assertRaises(runner.Finding) as caught:
                runner.submit(rpc, request, record)
            self.assertEqual((caught.exception.category, caught.exception.stage), ("inconclusive-resource", "evm-submission"))
            self.assertEqual(record["submission"], "unknown")
            self.assertEqual(record["request"], request)
            self.assertIn("error", record)
            rpc.call.assert_called_once_with("eth_sendTransaction", [request])

    def test_successful_submission_keeps_hash_and_rejected_submission_is_explicit(self):
        rpc = Mock()
        rpc.call.return_value = self.tx_hash
        record = {}
        self.assertEqual(runner.submit(rpc, {"data": "0x"}, record), self.tx_hash)
        self.assertEqual((record["submission"], record["transactionHash"]), ("submitted", self.tx_hash))
        rpc.call.side_effect = runner.RpcError({"code": -32000, "message": "intrinsic gas too low"})
        record = {}
        with self.assertRaises(runner.Finding) as caught:
            runner.submit(rpc, {}, record)
        self.assertEqual((record["submission"], caught.exception.category), ("rejected", "inconclusive-resource"))


class TraceTests(unittest.TestCase):
    def test_mined_return_bytes_are_observed_without_a_second_call(self):
        for output in ("ab" * 32, "0x" + "AB" * 32):
            result = runner.trace_result({"status": "0x1"}, {"failed": False, "returnValue": output})
            self.assertEqual(result, {"status": "returned", "output": "0x" + "ab" * 32})

    def test_trace_completion_fields_and_receipt_must_agree(self):
        for trace in (None, {}, {"failed": False}, {"failed": 0, "returnValue": ""},
                      {"failed": False, "returnValue": "0"}, {"failed": False, "returnValue": "zz"},
                      {"failed": True, "returnValue": ""}):
            with self.subTest(trace=trace), self.assertRaises(ValueError):
                runner.trace_result({"status": "0x1"}, trace)
        with self.assertRaises(ValueError):
            runner.trace_result({"status": "0x0"}, {"failed": False, "returnValue": ""})

    def test_only_confirmed_revert_is_reverted_and_resources_take_priority(self):
        mined = {"status": "0x0"}
        trace = {"failed": True, "returnValue": "abcd", "structLogs": [{"op": "REVERT"}]}
        self.assertEqual(runner.trace_result(mined, trace), {"status": "reverted", "output": "0xabcd"})
        for message in ("out of gas", "OutOfGas", "gas required exceeds allowance"):
            result = runner.trace_result(mined, {**trace, "error": message})
            self.assertEqual(result["status"], "out-of-gas")
        self.assertEqual(runner.trace_result(mined, {**trace, "error": "stack overflow"})["status"], "resource-limit")
        for logs in ([], [{"op": "INVALID"}], "not logs"):
            result = runner.trace_result(mined, {**trace, "structLogs": logs})
            self.assertEqual(result["status"], "evm-exceptional")


class ReplayTests(unittest.TestCase):
    def execute_arguments(self, directory, value):
        output = directory / "run"
        output.mkdir()
        source = directory / "case.json"
        source.write_text(json.dumps(value))
        return SimpleNamespace(case=source, replay=None, output=output, artifact_limit=1 << 20,
            case_tool=Path("unused-case-tool"), core_runner=Path("unused-core-runner"), anvil=Path("unused-anvil"),
            direct_fuel=1000, timeout=1)

    def test_fresh_replay_must_preserve_every_semantic_case_field(self):
        for field in ("program", "source", "provenance", "contract", "transactions", "storagePlan", "initialState", "observedSlots"):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as temporary:
                original = case()
                arguments = self.execute_arguments(Path(temporary), original)
                fresh = copy.deepcopy(original)
                fresh[field] = None
                fake = Mock()
                fake.identity.return_value = {"sha256": "0" * 64}
                fake.process.return_value = {"returncode": 0, "stdout": "revision"}
                with patch.object(runner.common, "Runner", return_value=fake), \
                        patch.object(runner.common, "checked_process", return_value={"stdout": json.dumps(fresh)}) as replay:
                    with self.assertRaisesRegex(ValueError, "native storage replay changed " + field):
                        runner.execute(arguments, {"histories": {}, "processes": []})
                replay.assert_called_once()

    def test_later_interruption_preserves_only_an_established_prefix_mismatch(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            (directory / "case.json").write_text(json.dumps(case()))
            arguments = SimpleNamespace(output=directory)
            failure = {"category": "inconclusive-resource", "stage": "evm-submission", "detail": "unknown", "pairs": {}}
            observed = histories()
            observed["rustEvm"] = history(rows=[row(0)])
            observed["rustEvm"].update(unobserved=["tx-1"], unexecuted=["tx-2"], finalStorage=None)
            report = {"histories": observed}
            self.assertEqual(runner.interrupted_comparison(arguments, report, failure), failure)
            observed["rustEvm"]["transactions"][0]["output"] = "0x" + f"{8:064x}"
            result = runner.interrupted_comparison(arguments, report, failure)
            self.assertEqual((result["category"], result["transactionId"], result["laterInterruption"]),
                             ("semantic-mismatch", "tx-0", failure))
            del observed["importedHull"]
            self.assertEqual(runner.interrupted_comparison(arguments, report, failure), failure)

    def archive(self, directory):
        for name in ("case.json", "direct-history.json", "bindings.json"):
            (directory / name).write_text(json.dumps({"fixture": name}))
        hashes = {path.name: runner.common.file_digest(path) for path in directory.iterdir()}
        return {"schema": runner.REPORT_SCHEMA, "caseSha256": hashes["case.json"], "artifacts": hashes}

    def test_new_report_schema_and_every_archived_member_are_verified(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            report = self.archive(directory)
            runner.verify_archive(directory, report)
            with self.assertRaises(ValueError):
                runner.verify_archive(directory, {**report, "schema": runner.common.REPORT_SCHEMA})
            for malformed in ({**report, "artifacts": {}}, {**report, "caseSha256": "0" * 64}):
                with self.assertRaises(ValueError):
                    runner.verify_archive(directory, malformed)
            path = directory / "direct-history.json"
            path.write_text('{"tampered":true}')
            with self.assertRaisesRegex(ValueError, "hash changed"):
                runner.verify_archive(directory, report)
            path.unlink()
            with self.assertRaisesRegex(ValueError, "missing or is not a regular file"):
                runner.verify_archive(directory, report)

    def test_archive_paths_and_symlinks_cannot_escape_inventory(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            report = self.archive(directory)
            for name in ("../outside", "/absolute", "nested/file", "nested\\file", ".", "report.json"):
                with self.subTest(name=name), self.assertRaises(ValueError):
                    runner.verify_archive(directory, {**report, "artifacts": {**report["artifacts"], name: "0" * 64}})
            (directory / "alias").symlink_to(directory / "case.json")
            with self.assertRaises(ValueError):
                runner.verify_archive(directory, {**report, "artifacts": {**report["artifacts"], "alias": report["caseSha256"]}})


class InterruptedExecutionPolicyTests(unittest.TestCase):
    """Scripted observations exercise orchestration, never compute a state transition."""

    def run_scripted_interruption(self, directory, *, rejected):
        original = case()
        source = directory / "case.json"
        source.write_text(json.dumps(original))
        output = directory / "run"
        output.mkdir()
        arguments = SimpleNamespace(case=source, replay=None, output=output, artifact_limit=1 << 20,
            case_tool=Path("case-tool"), core_runner=Path("core-runner"), anvil=Path("anvil"),
            direct_fuel=1000, core_fuel=2000, gas=100000, timeout=1,
            upstream=directory / "upstream", target_dir=directory / "target")
        events = []
        sender, address = "0x" + "01" * 20, "0x" + "02" * 20
        deployment_hash, first_hash = "0x" + "10" * 32, "0x" + "20" * 32
        bindings = {"schema": "solcore-lean.storage-bindings.v1", "caller": str(int(sender, 16)), "address": str(int(address, 16))}
        direct = {**history(original), "bindings": bindings, "fuelPerTransaction": 1000}
        fake_runner = Mock()
        fake_runner.identity.return_value = {"sha256": "0" * 64}
        fake_runner.args = arguments
        fake_runner.remaining.return_value = 10

        def process(stage, *_args):
            events.append(stage)
            if stage == "imported-hull":
                observations = [{"stage": "deployment", "status": "returned", "committedStorage": slots()},
                                *direct["transactions"]]
                return {"returncode": 0, "stdout": "\n".join(json.dumps(item) for item in observations)}
            return {"returncode": 0, "stdout": "revision"}

        fake_runner.process.side_effect = process

        def checked_process(_runner, stage, *_args):
            events.append(stage)
            if stage == "direct-core-replay":
                return {"stdout": json.dumps(original)}
            if stage == "direct-core-observe":
                return {"stdout": json.dumps(direct)}
            if stage == "rust-code-images":
                (output / "images.json").write_text("{}")
            return {"stdout": ""}

        rpc = Mock()
        submitted = []

        def rpc_call(method, params):
            events.append(method)
            if method == "eth_accounts":
                return [sender]
            if method == "eth_sendTransaction":
                submitted.append(params[0])
                if len(submitted) == 1:
                    return deployment_hash
                if len(submitted) == 2:
                    return first_hash
                if rejected:
                    raise runner.RpcError({"code": -32602, "message": "explicit rejection"})
                raise TimeoutError("unknown submission outcome")
            if method == "eth_getTransactionReceipt":
                deploy = params[0] == deployment_hash
                return {"transactionHash": params[0], "status": "0x1", "blockNumber": "0x1" if deploy else "0x2",
                        "contractAddress": address if deploy else None}
            if method == "eth_getCode":
                return "0x6000"
            if method == "eth_getStorageAt":
                slot, block = params[1:]
                value = 0 if block == "0x1" else 3 if slot == "0x0" else 4
                return "0x" + f"{value:064x}"
            if method == "debug_traceTransaction":
                # An intentional prior output difference; the final failure
                # must not erase this already completed observation.
                return {"failed": False, "returnValue": f"{8:064x}"}
            self.fail(f"unexpected RPC method: {method}")

        rpc.call.side_effect = rpc_call

        @contextmanager
        def anvil(*_args):
            yield rpc

        report = {"histories": {}, "processes": []}
        with patch.object(runner.common, "Runner", return_value=fake_runner), \
                patch.object(runner.common, "checked_process", side_effect=checked_process), \
                patch.object(runner.common, "validate_export", return_value={}), \
                patch.object(runner.common, "image_bytes", return_value=b"\x60\x00"), \
                patch.object(runner.common, "anvil", side_effect=anvil):
            with self.assertRaises(runner.Finding) as caught:
                runner.execute(arguments, report)
        self.assertEqual(len(submitted), 3, "unknown/rejected transaction was retried")
        self.assertEqual(submitted[2]["data"], original["transactions"][1]["calldata"])
        self.assertTrue(all(request.get("data") != original["transactions"][2]["calldata"] for request in submitted))
        self.assertLess(events.index("imported-hull"), events.index("debug_traceTransaction"))
        value = report["histories"]["rustEvm"]
        runner.normalize_history(value, original)
        self.assertEqual([item["id"] for item in value["transactions"]], ["tx-0"])
        failure = {"category": caught.exception.category, "stage": caught.exception.stage,
                   "detail": caught.exception.detail, "pairs": {}}
        comparison = runner.interrupted_comparison(arguments, report, failure)
        self.assertEqual((comparison["category"], comparison["transactionId"]), ("semantic-mismatch", "tx-0"))
        self.assertEqual(comparison["laterInterruption"], failure)
        return value, report["evmTransactions"]

    def test_execute_checkpoints_unknown_transaction_without_claiming_rollback(self):
        with tempfile.TemporaryDirectory() as temporary:
            value, records = self.run_scripted_interruption(Path(temporary), rejected=False)
            self.assertEqual((value["unobserved"], value["unexecuted"], value["finalStorage"]),
                             (["tx-1"], ["tx-2"], None))
            self.assertEqual(records[-1]["submission"], "unknown")

    def test_execute_keeps_explicitly_rejected_transaction_unexecuted(self):
        with tempfile.TemporaryDirectory() as temporary:
            value, records = self.run_scripted_interruption(Path(temporary), rejected=True)
            self.assertEqual((value["unobserved"], value["unexecuted"], value["finalStorage"]),
                             ([], ["tx-1", "tx-2"], slots(3, 4)))
            self.assertEqual(records[-1]["submission"], "rejected")


class CancellationTests(unittest.TestCase):
    def test_sigterm_stops_a_real_owned_child_and_saves_storage_report(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            marker, helper = folder / "started", folder / "case-tool"
            helper.write_text("#!" + sys.executable + "\nimport os, sys, time\nfrom pathlib import Path\n"
                "if sys.argv[1:] == ['--version']:\n    print('storage-lifecycle-test 1')\nelse:\n"
                "    Path(" + repr(str(marker)) + ").write_text(str(os.getpid()))\n    time.sleep(20)\n")
            helper.chmod(0o700)
            source = folder / "case.json"
            source.write_text(json.dumps(case(1)))
            output = folder / "run"
            process = subprocess.Popen([sys.executable, str(ROOT / "scripts/semantic-storage-differential.py"),
                "--case", str(source), "--output", str(output), "--case-tool", str(helper),
                "--core-runner", str(helper), "--anvil", str(helper), "--timeout", "30", "--total-timeout", "60"],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
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
                self.assertEqual(process.returncode, 1, stdout + stderr)
                report = json.loads((output / "report.json").read_text())
                self.assertEqual(report["schema"], runner.REPORT_SCHEMA)
                self.assertEqual((report["comparison"]["category"], report["comparison"]["detail"]),
                                 ("inconclusive-resource", "interrupted"))
                runner.verify_archive(output, report)
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
            self.fail("CLI must temporarily replace the original handler")

        signal.signal(signal.SIGTERM, original_handler)
        try:
            with tempfile.TemporaryDirectory() as temporary:
                for interrupt in (False, True):
                    output = Path(temporary) / str(interrupt)

                    def execute(_arguments, report):
                        if interrupt:
                            os.kill(os.getpid(), signal.SIGTERM)
                        report["comparison"] = {"category": "matched", "pairs": {}}

                    with patch.object(sys, "argv", ["semantic-storage-differential", "--case", "unused.json", "--output", str(output)]), \
                            patch.object(runner, "execute", side_effect=execute), redirect_stdout(io.StringIO()):
                        self.assertEqual(runner.main(), int(interrupt))
                    self.assertIs(signal.getsignal(signal.SIGTERM), original_handler)
        finally:
            signal.signal(signal.SIGTERM, previous)


if __name__ == "__main__":
    unittest.main()
