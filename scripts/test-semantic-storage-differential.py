#!/usr/bin/env python3
"""Protocol and classification tests, not a Python storage execution oracle.

Synthetic histories test comparison policy only. RPC doubles test requests and
receipts without simulating a chain; the cancellation test owns a real bounded
Python subprocess. Compiler/Core/EVM agreement is tested by the actual adapter.
"""
from contextlib import contextmanager, redirect_stdout, redirect_stderr
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


# The fixtures' bound contract address on every path.
ADDRESS = "4096"


def whole(*declared, address=ADDRESS):
    """Fixture whole storage: the nonzero entries of declared and undeclared slot rows."""
    entries = {entry["slot"]: entry["value"] for rows in declared for entry in rows or [] if entry["value"] != "0"}
    return [{"role": "contract", "address": address,
             "storage": [{"slot": slot, "value": entries[slot]} for slot in sorted(entries, key=int)]}]


def with_whole(value, address=ADDRESS):
    """Add the whole committed storage that a fixture's slot rows imply."""
    value["initialAccountStorage"] = whole(value["initialStorage"], value.get("initialUndeclaredStorage"), address=address)
    for entry in value["transactions"]:
        entry["accountStorage"] = whole(entry["committedStorage"], entry.get("undeclaredStorage"), address=address)
    rows = value["transactions"]
    value["finalAccountStorage"] = None if value.get("finalStorage") is None else copy.deepcopy(
        rows[-1]["accountStorage"] if rows else value["initialAccountStorage"])
    return value


def slots(first=0, second=0):
    return [{"slot": "0", "value": str(first)}, {"slot": "1", "value": str(second)}]


def row(index, value=7, first=3, second=4, status="returned"):
    result = {"stage": "execution", "id": f"tx-{index}", "index": index,
        "status": status, "committedStorage": slots(first, second), "accountStorage": whole(slots(first, second))}
    result.update({"output": "0x" + f"{value:064x}"} if status in ("returned", "reverted") else {"detail": "test resource"})
    return result


def history(value=None, rows=None):
    value = case() if value is None else value
    rows = [row(index) for index in range(len(value["transactions"]))] if rows is None else rows
    complete = len(rows) == len(value["transactions"]) and all(r["status"] in ("returned", "reverted") for r in rows)
    return with_whole({"schema": runner.HISTORY_SCHEMA, "initialStorage": slots(), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"] if rows else slots()),
        "status": "complete" if complete else "incomplete",
        "unexecuted": [tx["id"] for tx in value["transactions"][len(rows):]]})


def histories(value=None):
    return {name: history(value) for name in runner.PATHS}


class CaseTests(unittest.TestCase):
    def test_fixed_wrapper_and_canonical_abi_inputs(self):
        for count in (1, 2, 3, runner.MAX_TRANSACTIONS):
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
        for count in (0, runner.MAX_TRANSACTIONS + 1):
            with self.assertRaises(ValueError):
                runner.validate_case(case(count))
        for identifier in (None, "", "../tx", "x" * 65, "tx-0"):
            invalid = case()
            invalid["transactions"][1]["id"] = identifier
            with self.subTest(identifier=identifier), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        with self.assertRaises(ValueError):
            runner.validate_case({**case(), "storagePlan": {}})


class RollbackTests(unittest.TestCase):
    def setUp(self):
        self.case = case()
        self.case["schema"] = runner.ROLLBACK_CASE_SCHEMA
        self.case["storagePlan"]["schema"] = "solcore-lean.storage-rollback-plan.v1"
        self.case["contract"].update(name="SynthesizedRollback", deployPath=["SynthesizedRollbackDeploy"],
            runtimePath=["SynthesizedRollbackDeploy", "SynthesizedRollback"])
        self.histories = histories(self.case)
        for observed in self.histories.values():
            observed["transactions"][1]["status"] = "reverted"

    def test_rollback_has_a_distinct_case_plan_and_wrapper(self):
        runner.validate_case(self.case)
        self.assertEqual(runner.profile(self.case)["caseTool"], "semantic-storage-rollback-tool")
        for key in ("schema", "storagePlan", "contract"):
            bad = copy.deepcopy(self.case)
            bad[key] = case()[key]
            with self.subTest(key=key), self.assertRaises((ValueError, runner.Finding)):
                runner.validate_case(bad)

    def test_mixed_completion_matches_only_the_declared_parities(self):
        self.assertEqual(runner.compare(self.histories, self.case)["category"], "matched")
        for observed in self.histories.values():
            observed["transactions"][1]["status"] = "returned"
        result = runner.compare(self.histories, self.case)
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-1"))
        self.assertTrue(all(result["pairs"].values()))

    def test_revert_payload_remains_observable_and_exactly_one_word(self):
        for observed in self.histories.values():
            observed["transactions"][1]["output"] = "0x" + "00" * 32
        self.assertEqual(runner.compare(self.histories, self.case)["category"], "matched")
        self.histories["importedHull"]["transactions"][1]["output"] = "0x"
        result = runner.compare(self.histories, self.case)
        self.assertEqual(result["category"], "semantic-mismatch")
        self.assertIn("output", result["fields"])
        for observed in self.histories.values():
            observed["transactions"][1]["output"] = "0x"
        self.assertEqual(runner.compare(self.histories, self.case)["category"], "semantic-mismatch")

    def test_agreed_revert_cannot_commit_tentative_storage(self):
        for observed in self.histories.values():
            observed["transactions"][1]["committedStorage"] = slots(0, 9)
        result = runner.compare(self.histories, self.case)
        self.assertEqual((result["category"], result["transactionId"], result["fields"]),
                         ("semantic-mismatch", "tx-1", ["committedStorage"]))
        self.assertTrue(all(result["pairs"].values()))

    def test_initial_and_consecutive_reverts_use_the_prior_committed_snapshot(self):
        for transaction in self.case["transactions"]:
            transaction.update(input="1", calldata="0xa444f5e9" + f"{1:064x}")
        for observed in self.histories.values():
            for record in observed["transactions"]:
                record.update(status="reverted", committedStorage=slots())
            observed["finalStorage"] = slots()
            with_whole(observed)
        self.assertEqual(runner.compare(self.histories, self.case)["category"], "matched")
        for observed in self.histories.values():
            observed["transactions"][0]["committedStorage"] = slots(1, 0)
        self.assertEqual(runner.compare(self.histories, self.case)["transactionId"], "tx-0")

    def test_incomplete_execution_is_not_an_observed_revert(self):
        observed = self.histories["importedHull"]
        observed["transactions"] = observed["transactions"][:2]
        observed["transactions"][1].pop("output")
        observed["transactions"][1]["status"] = "out-of-fuel"
        observed.update(status="incomplete", unexecuted=["tx-2"])
        self.assertEqual(runner.compare(self.histories, self.case)["category"], "inconclusive-resource")


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
        value.update(unobserved=["tx-1"], unexecuted=["tx-2"], finalStorage=None, finalAccountStorage=None)
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
        stopped.update(unobserved=["tx-1"], unexecuted=["tx-2"], finalStorage=None, finalAccountStorage=None)
        with self.assertRaisesRegex(ValueError, "submission continued"):
            runner.normalize_history(stopped, case())

    def test_prefix_difference_survives_unknown_later_completion(self):
        actual = histories()
        value = history(rows=[row(0, value=8)])
        value.update(unobserved=["tx-1"], unexecuted=["tx-2"], finalStorage=None, finalAccountStorage=None)
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
        deployment = {"stage": "deployment", "status": "returned", "committedStorage": slots(), "accountStorage": whole()}
        complete = runner.hull_history(self.lines(deployment, row(0), row(1), row(2)), 0, case())
        self.assertEqual(complete["status"], "complete")
        partial = runner.hull_history(self.lines(deployment, row(0), row(1, status="out-of-fuel")), 1, case())
        self.assertEqual((partial["status"], partial["unexecuted"]), ("incomplete", ["tx-2"]))
        self.assertEqual(partial["finalStorage"], row(1)["committedStorage"])

    def test_unexplained_exit_and_corrupt_output_do_not_become_histories(self):
        deployment = {"stage": "deployment", "status": "returned", "committedStorage": slots(), "accountStorage": whole()}
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
            observed["rustEvm"].update(unobserved=["tx-1"], unexecuted=["tx-2"], finalStorage=None, finalAccountStorage=None)
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
        direct = {**with_whole(history(original), bindings["address"]), "bindings": bindings, "fuelPerTransaction": 1000}
        fake_runner = Mock()
        fake_runner.identity.return_value = {"sha256": "0" * 64}
        fake_runner.args = arguments
        fake_runner.remaining.return_value = 10

        def process(stage, *_args):
            events.append(stage)
            if stage == "imported-hull":
                observations = [{"stage": "deployment", "status": "returned", "committedStorage": slots(),
                                 "accountStorage": whole(address=bindings["address"])}, *direct["transactions"]]
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
            if method == "debug_traceTransaction" and params[1] == runner.PRESTATE_DIFF:
                written = {"0x0": f"0x{3:064x}", "0x1": f"0x{4:064x}"} if params[0] == first_hash else {}
                return {"pre": {}, "post": {address: {"storage": written}} if written else {}}
            if method == "debug_traceTransaction":
                # An intentional prior output difference; the final failure
                # must not erase this already completed observation.
                return {"failed": False, "returnValue": f"{8:064x}"}
            self.fail(f"unexpected RPC method: {method}")

        rpc.call.side_effect = rpc_call

        @contextmanager
        def anvil(*_args, steps_tracing=False):
            self.assertTrue(steps_tracing)
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
        # Hull runs before any transaction is sent; only the deployment's diff precedes it.
        self.assertLess(events.index("imported-hull"), [index for index, event in enumerate(events) if event == "eth_sendTransaction"][1])
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
                case_path = Path(temporary) / "case.json"
                case_path.write_text(json.dumps(case()))
                for interrupt in (False, True):
                    output = Path(temporary) / str(interrupt)

                    def execute(_arguments, report):
                        if interrupt:
                            os.kill(os.getpid(), signal.SIGTERM)
                        report["comparison"] = {"category": "matched", "pairs": {}}

                    with patch.object(sys, "argv", ["semantic-storage-differential", "--case", str(case_path), "--output", str(output)]), \
                            patch.object(runner, "execute", side_effect=execute), redirect_stdout(io.StringIO()):
                        self.assertEqual(runner.main(), int(interrupt))
                    self.assertIs(signal.getsignal(signal.SIGTERM), original_handler)
        finally:
            signal.signal(signal.SIGTERM, previous)



class BackendTests(unittest.TestCase):
    """Backend selection policy only; mocked execution is not an EVM result."""

    def invoke(self, directory, *, backend=None, saved=..., solc=None):
        source = directory / "case.json"
        source.write_text(json.dumps(case()))
        output = directory / "run"
        arguments = ["adapter", "--output", str(output)]
        if saved is not ...:
            (directory / "report.json").write_text(json.dumps(saved))
            arguments += ["--replay", str(directory)]
        else:
            arguments += ["--case", str(source)]
        if backend is not None:
            arguments += ["--backend", backend]
        if solc is not None:
            arguments += ["--solc", str(solc)]
        captured = []
        def executed(args, report):
            captured.append((args.backend, report["backend"]))
            self.solc = args.solc
            report["comparison"] = {"category": "matched", "pairs": {}}
        with patch.object(sys, "argv", arguments), patch.object(runner, "execute", side_effect=executed), redirect_stdout(io.StringIO()):
            code = runner.main()
        return code, captured, json.loads((output / "report.json").read_text())

    def test_default_and_explicit_backends_are_recorded(self):
        for explicit, expected in ((None, "sonatina-o0"), ("sonatina-o2", "sonatina-o2"), ("yul", "yul")):
            with self.subTest(backend=explicit), tempfile.TemporaryDirectory() as temporary:
                code, captured, report = self.invoke(Path(temporary), backend=explicit)
                self.assertEqual(code, 0)
                self.assertEqual(captured, [(expected, expected)])
                self.assertEqual(report["backend"], expected)
                self.assertEqual(report["pathBackends"], runner.common.path_backends(expected))

    def test_exact_replay_inherits_o2_yul_and_legacy_o0(self):
        for saved, expected in (({}, "sonatina-o0"), ({"backend": "sonatina-o2"}, "sonatina-o2"), ({"backend": "yul"}, "yul")):
            with self.subTest(saved=saved), tempfile.TemporaryDirectory() as temporary:
                _, captured, report = self.invoke(Path(temporary), saved=saved)
                self.assertEqual(captured, [(expected, expected)])
                self.assertEqual(report["backend"], expected)

    def test_exact_replay_backend_change_or_null_is_rejected_before_execution(self):
        for saved, explicit in (({}, "sonatina-o2"), ({"backend": "sonatina-o2"}, "sonatina-o0"),
                                ({"backend": None}, None), ({"backend": "yul"}, "sonatina-o0"), ({}, "yul"),
                                ({"backend": "sonatina-o2"}, "yul"), ({"backend": "solc-yul"}, None)):
            with self.subTest(saved=saved, explicit=explicit), tempfile.TemporaryDirectory() as temporary:
                directory = Path(temporary)
                with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as caught:
                    self.invoke(directory, backend=explicit, saved=saved)
                self.assertEqual(caught.exception.code, 2)
                self.assertFalse((directory / "run").exists())

    def test_yul_cli_records_its_compiler_path_and_separated_path_backends(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            code, captured, report = self.invoke(directory, backend="yul", solc=directory / "pinned" / ".." / "solc")
            self.assertEqual((code, captured), (0, [("yul", "yul")]))
            self.assertEqual(self.solc, (directory / "solc").resolve())
            self.assertEqual(report["pathBackends"], {"directCore": "original-core", "importedHull": "sonatina-o0", "rustEvm": "yul"})

    def test_unknown_backends_have_no_fallback_and_yul_archives_use_the_shared_check(self):
        args = SimpleNamespace(replay=None, backend="solc-yul")
        with patch.object(runner.common, "Runner") as execution:
            with self.assertRaisesRegex(ValueError, "unsupported backend"):
                runner.execute(args, {})
            execution.assert_not_called()
        with patch.object(runner.common, "verify_archive") as archive:
            with self.assertRaisesRegex(ValueError, "unsupported saved backend"):
                runner.verify_archive(Path("unused"), {"schema": runner.REPORT_SCHEMA, "backend": "solc-yul"})
            archive.assert_not_called()
            saved = {"schema": runner.REPORT_SCHEMA, "backend": "yul", "pathBackends": runner.common.path_backends("yul")}
            runner.verify_archive(Path("unused"), saved)
            # The shared check validates images, provenance and the Yul evidence of the pure report form.
            archive.assert_called_once_with(Path("unused"), {**saved, "schema": runner.common.REPORT_SCHEMA})

    def test_invalid_replay_report_and_budgets_fail_before_output(self):
        for saved in (None, [], ["report"], True, "report", {"budgets": None}, {"budgets": []}):
            with self.subTest(saved=saved), tempfile.TemporaryDirectory() as temporary:
                directory = Path(temporary)
                with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as caught:
                    self.invoke(directory, saved=saved)
                self.assertEqual(caught.exception.code, 2)
                self.assertFalse((directory / "run").exists())

    def test_o2_reaches_exporter_and_provenance_validation(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            source, output = directory / "case.json", directory / "run"
            source.write_text(json.dumps(case())); output.mkdir()
            args = SimpleNamespace(case=source, replay=None, backend="sonatina-o2", output=output,
                artifact_limit=1 << 20, case_tool=Path("unused-case"), core_runner=Path("unused-core"),
                anvil=Path("unused-anvil"), direct_fuel=1000, timeout=1,
                upstream=directory / "upstream", target_dir=directory / "target")
            fake = Mock()
            fake.identity.return_value = {"sha256": "0" * 64}
            fake.process.return_value = {"returncode": 0, "stdout": "revision"}
            commands = []
            def checked(_runner, stage, command, *_limits):
                commands.append((stage, command))
                return {"stdout": json.dumps(case()) if stage == "direct-core-replay" else ""}
            report = {"processes": [], "histories": {}}
            with patch.object(runner.common, "Runner", return_value=fake), \
                 patch.object(runner.common, "checked_process", side_effect=checked), \
                 patch.object(runner.common, "validate_export", side_effect=ValueError("test stops before execution")) as validate:
                with self.assertRaisesRegex(ValueError, "test stops before execution"):
                    runner.execute(args, report)
            image_command = next(command for stage, command in commands if stage == "rust-code-images")
            self.assertEqual(image_command[image_command.index("--optimization") + 1], "O2")
            hull_command = next(command for stage, command in commands if stage == "rust-checked-source")
            self.assertNotIn("--optimization", hull_command)
            self.assertEqual(validate.call_args.kwargs["backend"], "sonatina-o2")
            self.assertEqual(report["backend"], "sonatina-o2")
            self.assertEqual(report["pathBackends"], runner.common.path_backends("sonatina-o2"))
            self.assertNotIn("solc", report["tools"])

    def test_yul_links_hull_to_o0_images_and_deploys_the_transported_yul_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            source, output = directory / "case.json", directory / "run"
            source.write_text(json.dumps(case())); output.mkdir()
            (output / "images.json").write_text("{}")
            args = SimpleNamespace(case=source, replay=None, backend="yul", solc=directory / "solc", output=output,
                artifact_limit=1 << 20, case_tool=Path("unused-case"), core_runner=Path("unused-core"),
                anvil=Path("unused-anvil"), direct_fuel=1000, timeout=1, gas=1000,
                upstream=directory / "upstream", target_dir=directory / "target")
            fake = Mock()
            fake.identity.return_value = {"sha256": "0" * 64, "version": "Version: policy"}
            fake.process.return_value = {"returncode": 0, "stdout": "revision"}
            commands, sent = [], []
            def checked(_runner, stage, command, *_limits):
                commands.append((stage, command))
                return {"stdout": json.dumps(case()) if stage == "direct-core-replay" else ""}
            class Rpc:
                def call(self, method, params):
                    if method == "eth_accounts":
                        return ["0x" + "11" * 20]
                    sent.append((method, params[0]))
                    raise ValueError("test stops at deployment")
            @contextmanager
            def anvil(*_arguments, **_options):
                yield Rpc()
            report = {"processes": [], "histories": {}}
            images = {"sonatina": True}
            with patch.object(runner.common, "Runner", return_value=fake), \
                 patch.object(runner.common, "checked_process", side_effect=checked), \
                 patch.object(runner.common, "validate_export", return_value={"hull": {}, "images": {}}) as validate, \
                 patch.object(runner.common, "read_json", side_effect=lambda path, *_: images if path.name == "images.json" else json.loads(path.read_text())), \
                 patch.object(runner.common, "image_bytes", side_effect=lambda _images, path: b"sonatina-" + path[-1].encode()), \
                 patch.object(runner.common, "yul_transport", return_value=(b"yul-init", b"yul-runtime")) as transport, \
                 patch.object(runner.common, "anvil", anvil):
                with self.assertRaisesRegex(ValueError, "test stops at deployment"):
                    runner.execute(args, report)
            image_command = next(command for stage, command in commands if stage == "rust-code-images")
            self.assertEqual(image_command[image_command.index("--optimization") + 1], "O0")
            self.assertEqual(validate.call_args.kwargs["backend"], "sonatina-o0")
            self.assertEqual(report["pathBackends"], {"directCore": "original-core", "importedHull": "sonatina-o0", "rustEvm": "yul"})
            self.assertEqual(report["tools"]["solc"], fake.identity.return_value)
            self.assertEqual(report["tools"]["yulExporterSha256"], runner.common.file_digest(ROOT / "scripts/export-rust-yul.py"))
            self.assertEqual(report["tools"]["yulTransportSha256"], runner.common.file_digest(ROOT / "scripts/semantic-yul.py"))
            self.assertEqual(transport.call_args.args, ("execute", args, fake, case(), output / "case.sol", output / "hull.json", report, None))
            # The EVM deploys the creation bytes of the Yul compilation, never the Sonatina image.
            self.assertEqual(sent, [("eth_sendTransaction", {"from": "0x" + "11" * 20, "data": "0x" + b"yul-init".hex(),
                                                              "value": "0x0", "gas": hex(1000)})])

    def test_yul_replay_rejects_compiler_or_transport_drift_before_export(self):
        tools = {"runnerSha256": runner.common.file_digest(ROOT / "scripts/semantic-storage-differential.py"),
                 "sharedRunnerSha256": runner.common.file_digest(ROOT / "scripts/semantic-differential.py"),
                 "leanToolchain": (ROOT / "lean-toolchain").read_text().strip(),
                 "exporters": {name: runner.common.file_digest(ROOT / "scripts" / name) for name in
                     ("export-rust-hull.py", "export-rust-code-image.py", "rust-hull-export.rs", "rust-code-image-export.rs")},
                 "yulExporterSha256": runner.common.file_digest(ROOT / "scripts/export-rust-yul.py"),
                 "yulTransportSha256": runner.common.file_digest(ROOT / "scripts/semantic-yul.py"),
                 "solc": {"sha256": "0" * 64, "version": "Version: policy"},
                 **{key: {"sha256": "0" * 64} for key in ("caseTool", "coreRunner", "anvil")}}
        for change, detail in ((("yulExporterSha256", "1" * 64), "yulExporterSha256"), (("yulTransportSha256", "1" * 64), "yulTransportSha256"),
                               (("solc", {"sha256": "1" * 64, "version": "Version: policy"}), "solc sha256"),
                               (("solc", {"sha256": "0" * 64, "version": "Version: other"}), "solc version"), (None, None)):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as temporary:
                directory = Path(temporary)
                replay, output = directory / "saved", directory / "run"
                replay.mkdir(); output.mkdir()
                (replay / "case.json").write_text(json.dumps(case()))
                saved = {"schema": runner.REPORT_SCHEMA, "backend": "yul", "tools": copy.deepcopy(tools)}
                if change is not None:
                    saved["tools"][change[0]] = change[1]
                (replay / "report.json").write_text(json.dumps(saved))
                args = SimpleNamespace(case=None, replay=replay, backend=None, solc=directory / "solc", output=output,
                    artifact_limit=1 << 20, case_tool=Path("unused-case"), core_runner=Path("unused-core"),
                    anvil=Path("unused-anvil"), direct_fuel=1000, timeout=1)
                fake = Mock()
                fake.identity.side_effect = lambda path, version=False: (
                    {"sha256": "0" * 64, **({"version": "Version: policy"} if version else {})})
                fake.process.return_value = {"returncode": 0, "stdout": "revision"}
                with patch.object(runner, "verify_archive"), patch.object(runner.common, "Runner", return_value=fake), \
                     patch.object(runner.common, "checked_process", side_effect=ValueError("replay reached the native tools")):
                    if detail is None:
                        with self.assertRaisesRegex(ValueError, "replay reached the native tools"):
                            runner.execute(args, {"processes": [], "histories": {}})
                    else:
                        with self.assertRaises(runner.Finding) as caught:
                            runner.execute(args, {"processes": [], "histories": {}})
                        self.assertEqual((caught.exception.category, caught.exception.stage), ("adapter-error", "replay"))
                        self.assertIn(detail, caught.exception.detail)


MAX_WORD = 2**256 - 1


def keyed_case(pairs=((5, 2), (0, 4), (MAX_WORD, 3))):
    """Envelope fixture only: native replay checks the actual keyed program."""
    transactions = [{"id": f"tx-{index}", "key": str(key), "input": str(value), "value": "0",
        "calldata": "0x7357f5d2" + f"{key:064x}" + f"{value:064x}"} for index, (key, value) in enumerate(pairs)]
    return {"schema": runner.KEYED_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "keyedStoragePlan": {"schema": "solcore-lean.keyed-storage-plan.v1", "stepProgram": {}},
        "initialState": {"storage": []}, "observedSlots": runner.keyed_slots(transactions),
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedKeyedStorage", "method": "run", "signature": "run(uint256,uint256)",
            "selector": "0x7357f5d2", "deployPath": ["SynthesizedKeyedStorageDeploy"],
            "runtimePath": ["SynthesizedKeyedStorageDeploy", "SynthesizedKeyedStorage"], "constructorCalldata": "0x"},
        "transactions": transactions}


def keyed_slots(value, counter=0):
    return [{"slot": slot, "value": str(counter if slot == "0" else 0)} for slot in value["observedSlots"]]


def keyed_history(value, path):
    """Committed counter rows; odd inputs revert and keep the prior snapshot."""
    rows, counter = [], 0
    for index, tx in enumerate(value["transactions"]):
        reverted = int(tx["input"]) % 2 == 1
        counter += 0 if reverted else 1
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned",
               "output": "0x" + f"{index + 3:064x}", "committedStorage": keyed_slots(value, counter)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
    result = {"schema": runner.KEYED_HISTORY_SCHEMA, "observedSlots": value["observedSlots"],
        "initialStorage": keyed_slots(value), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def keyed_histories(value=None):
    value = keyed_case() if value is None else value
    return {path: keyed_history(value, path) for path in runner.PATHS}


class KeyedStorageTests(unittest.TestCase):
    def test_keyed_case_declares_derived_slots_and_two_word_calldata(self):
        value = keyed_case()
        runner.validate_case(value)
        self.assertEqual(value["observedSlots"], ["0", "1", "5", "6", str(MAX_WORD)])
        self.assertEqual(runner.observed_slots(value), ("0", "1", "5", "6", str(MAX_WORD)))
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["rollback"]),
                         ("semantic-keyed-storage-tool", "rust-hull-keyed-storage-scenario", True))
        self.assertEqual(runner.keyed_slots([{"key": "7"}, {"key": "7"}]), ["0", "7", "8"])
        for slots in (["0", "5", "6", str(MAX_WORD)], ["1", "0", "5", "6", str(MAX_WORD)],
                      ["0", "1", "2", "5", "6", str(MAX_WORD)], ["0", "1"]):
            with self.subTest(slots=slots), self.assertRaises(runner.Finding):
                runner.validate_case({**value, "observedSlots": slots})
        for key, changed in (("key", "05"), ("key", str(2**256)), ("input", "01"),
                             ("calldata", "0xa444f5e9" + "00" * 32), ("calldata", value["transactions"][0]["calldata"][:-2])):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        for key in ("schema", "keyedStoragePlan", "contract"):
            mixed = copy.deepcopy(value)
            mixed[key] = case()[key] if key != "keyedStoragePlan" else {"schema": "solcore-lean.storage-plan.v1", "stepProgram": {}}
            with self.subTest(key=key), self.assertRaises((ValueError, runner.Finding)):
                runner.validate_case(mixed)
        self.assertIn("run(uint256,uint256)", runner.scope(value))

    def test_keyed_histories_match_and_containment_belongs_to_hull_and_evm(self):
        value = keyed_case()
        self.assertEqual(runner.compare(keyed_histories(value), value)["category"], "matched")
        claimed = keyed_histories(value)
        claimed["directCore"]["transactions"][0]["undeclaredStorage"] = []
        self.assertEqual(runner.compare(claimed, value)["category"], "adapter-error")
        for path in runner.CONTAINMENT_PATHS:
            for key in ("initialUndeclaredStorage", None):
                missing = keyed_histories(value)
                if key:
                    del missing[path][key]
                else:
                    del missing[path]["transactions"][1]["undeclaredStorage"]
                with self.subTest(path=path, key=key):
                    self.assertEqual(runner.compare(missing, value)["category"], "adapter-error")
        undeclared = keyed_histories(value)
        undeclared["rustEvm"]["observedSlots"] = ["0", "1"]
        self.assertEqual(runner.compare(undeclared, value)["category"], "adapter-error")

    def test_undeclared_nonzero_storage_is_a_semantic_mismatch_on_its_own_path(self):
        value = keyed_case()
        for path in runner.CONTAINMENT_PATHS:
            observed = keyed_histories(value)
            observed[path]["transactions"][1]["undeclaredStorage"] = [{"slot": "9", "value": "1"}]
            result = runner.compare(observed, value)
            with self.subTest(path=path):
                self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-1"))
                self.assertTrue(all(result["pairs"].values()))
                self.assertEqual((result["fields"], result["undeclaredPaths"]), (["undeclaredStorage"], [path]))
            initial = keyed_histories(value)
            initial[path]["initialUndeclaredStorage"] = [{"slot": "2", "value": "3"}]
            result = runner.compare(initial, value)
            with self.subTest(path=path, stage="initial"):
                self.assertEqual((result["category"], result["stage"], result["fields"], result["undeclaredPaths"]),
                                 ("semantic-mismatch", "initial-storage", ["undeclaredStorage"], [path]))
            for history in initial.values():
                history["initialStorage"][0]["value"] = "1"
            result = runner.compare(initial, value)
            with self.subTest(path=path, stage="initial-declared"):
                self.assertEqual((result["fields"], result["undeclaredPaths"]), (["committedStorage", "undeclaredStorage"], [path]))

    def test_undeclared_rows_are_canonical_and_never_declared_or_zero(self):
        value = keyed_case()
        widespread = [{"slot": str(100 + index), "value": "1"} for index in range(runner.MAX_UNDECLARED_SLOTS)]
        observed = keyed_histories(value)
        observed["rustEvm"]["transactions"][0]["undeclaredStorage"] = widespread
        self.assertEqual(runner.compare(observed, value)["category"], "semantic-mismatch")
        for rows in ([{"slot": "5", "value": "1"}], [{"slot": "9", "value": "0"}], widespread + [{"slot": "999", "value": "1"}],
                     [{"slot": "10", "value": "1"}, {"slot": "9", "value": "1"}], [{"slot": "09", "value": "1"}],
                     [{"slot": "9", "value": "1", "extra": True}], {"slot": "9"}):
            observed = keyed_histories(value)
            observed["importedHull"]["transactions"][0]["undeclaredStorage"] = rows
            with self.subTest(rows=rows):
                self.assertEqual(runner.compare(observed, value)["category"], "adapter-error")

    def test_declared_slot_difference_and_keyed_rollback_are_compared(self):
        value = keyed_case()
        observed = keyed_histories(value)
        observed["rustEvm"]["transactions"][0]["committedStorage"][2]["value"] = "4"
        result = runner.compare(observed, value)
        self.assertEqual((result["category"], result["transactionId"], result["fields"]),
                         ("semantic-mismatch", "tx-0", ["committedStorage"]))
        self.assertNotIn("undeclaredPaths", result)
        tentative = keyed_histories(value)
        for history in tentative.values():
            history["transactions"][2]["committedStorage"] = keyed_slots(value, 3)
            history["finalStorage"] = keyed_slots(value, 3)
        result = runner.compare(tentative, value)
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-2"))
        self.assertIn("committedStorage", result["fields"])

    def test_prestate_diff_names_only_contract_storage_changes(self):
        address = "0x" + "ab" * 20
        diff = {"pre": {address: {"storage": {"0x" + "00" * 31 + "09": "0x" + "00" * 32}},
                        "0x" + "cd" * 20: {"balance": "0x1", "nonce": 1}},
                "post": {address.upper().replace("0X", "0x"): {"storage": {"0x01": "0x" + "00" * 31 + "02"}},
                         "0x" + "cd" * 20: {"balance": "0x0", "nonce": 2}}}
        self.assertEqual(runner.changed_slots(diff, address), {"1", "9"})
        self.assertEqual(runner.changed_slots({"pre": {}, "post": {}}, address), set())
        other = copy.deepcopy(diff)
        other["post"]["0x" + "cd" * 20]["storage"] = {"0x01": "0x01"}
        for invalid in (other, {"post": {}}, {"pre": [], "post": {}}, {"pre": {"bad": {}}, "post": {}},
                        {"pre": {address: {"storage": {"0xzz": "0x0"}}}, "post": {}},
                        {"pre": {address: {"storage": []}}, "post": {}}):
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                runner.changed_slots(invalid, address)

    def test_evm_containment_rereads_outside_slots_at_the_receipt_block(self):
        calls = []
        class Rpc:
            def call(self, method, params):
                calls.append((method, params))
                return "0x" + f"{7 if params[1] == hex(10) else 0:064x}"
        rows = runner.evm_undeclared(Rpc(), "0x" + "ab" * 20, "0x5", {"0", "9", "10", "1"}, ("0", "1"))
        self.assertEqual(rows, [{"slot": "10", "value": "7"}])
        self.assertEqual([params[1:] for _, params in calls], [[hex(9), "0x5"], [hex(10), "0x5"]])
        self.assertEqual(runner.evm_undeclared(Rpc(), "0x" + "ab" * 20, "0x5", {"0"}, ("0",)), [])

    def test_keyed_hull_history_carries_declared_and_undeclared_rows(self):
        value = keyed_case()
        deployment = {"stage": "deployment", "status": "returned", "committedStorage": keyed_slots(value), "accountStorage": whole(), "undeclaredStorage": []}
        calls = [{"stage": "execution", **row} for row in keyed_history(value, "importedHull")["transactions"]]
        stdout = "\n".join(json.dumps(row) for row in [deployment, *calls])
        history = runner.hull_history(stdout, 0, value)
        self.assertEqual((history["schema"], history["observedSlots"], history["initialUndeclaredStorage"]),
                         (runner.KEYED_HISTORY_SCHEMA, value["observedSlots"], []))
        deployment["undeclaredStorage"] = [{"slot": "9", "value": "1"}]
        stdout = "\n".join(json.dumps(row) for row in [deployment, *calls])
        self.assertEqual(runner.hull_history(stdout, 0, value)["initialUndeclaredStorage"], [{"slot": "9", "value": "1"}])
        del deployment["undeclaredStorage"]
        with self.assertRaises(ValueError):
            runner.hull_history("\n".join(json.dumps(row) for row in [deployment, *calls]), 0, value)

    def test_two_slot_profiles_keep_their_fixed_observation(self):
        value = case()
        self.assertEqual(runner.observed_slots(value), runner.SLOTS)
        self.assertEqual(runner.profile(value)["coreRunner"], "rust-hull-storage-scenario")
        observed = histories(value)
        observed["importedHull"]["transactions"][0]["undeclaredStorage"] = []
        self.assertEqual(runner.compare(observed, value)["category"], "matched")
        self.assertEqual(runner.scope(value),
                         "ordered zero-value run(uint256) transactions; initially empty committed slots 0/1; no gas/balance/nonce equivalence; "
                         "the contract's whole committed storage on all paths after deployment and every transaction")


def array_calldata(flags, values):
    return "0x9a94c44b" + "".join(f"{word:064x}" for word in [flags, 64, len(values), *values])


def array_case(rows=((0, (1, 3, 7)), (1, (MAX_WORD,)), (2, ()))):
    """Envelope fixture only: native replay checks the actual array program."""
    transactions = [{"id": f"tx-{index}", "flags": str(flags), "values": [str(value) for value in values], "value": "0",
        "calldata": array_calldata(flags, values)} for index, (flags, values) in enumerate(rows)]
    return {"schema": runner.ARRAY_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "dynamicArrayPlan": {"schema": "solcore-lean.dynamic-array-plan.v1", "stepProgram": {}},
        "initialState": {"storage": []}, "observedSlots": list(runner.ARRAY_SLOTS),
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedDynamicArray", "method": "run", "signature": "run(uint256,uint256[])",
            "selector": "0x9a94c44b", "deployPath": ["SynthesizedDynamicArrayDeploy"],
            "runtimePath": ["SynthesizedDynamicArrayDeploy", "SynthesizedDynamicArray"], "constructorCalldata": "0x"},
        "transactions": transactions}


def array_history(value, path):
    """Committed count rows; odd flags revert and keep the prior snapshot."""
    result = keyed_history({**value, "transactions": [{**tx, "input": tx["flags"]} for tx in value["transactions"]]}, path)
    result["schema"] = runner.ARRAY_HISTORY_SCHEMA
    return with_whole(result)


def array_histories(value=None):
    value = array_case() if value is None else value
    return {path: array_history(value, path) for path in runner.PATHS}


class DynamicArrayTests(unittest.TestCase):
    def test_array_case_requires_canonical_head_tail_calldata(self):
        value = array_case()
        runner.validate_case(value)
        # `cast calldata "run(uint256,uint256[])" 1 "[5,6]"`
        self.assertEqual(array_calldata(1, (5, 6)), "0x9a94c44b" + "".join(
            f"{word:064x}" for word in (1, 0x40, 2, 5, 6)))
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"]),
                         ("semantic-dynamic-array-tool", "rust-hull-keyed-storage-scenario", True, "array"))
        self.assertEqual(runner.observed_slots(value), ("0", "1", "2", "3", "4"))
        for key, changed in (("values", ["1", "2", "3", "4"]), ("values", ["01"]), ("values", "1"), ("flags", "01"),
                             ("calldata", array_calldata(0, (1, 3))), ("calldata", array_calldata(0, (1, 3, 7))[:-64]),
                             ("calldata", "0x9a94c44b" + "".join(f"{word:064x}" for word in (0, 0x60, 3, 1, 3, 7))),
                             ("value", "1")):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        for slots in (["0", "1", "2", "3"], ["0", "1", "2", "3", "4", "5"], ["1", "0", "2", "3", "4"]):
            with self.subTest(slots=slots), self.assertRaises(runner.Finding):
                runner.validate_case({**value, "observedSlots": slots})
        mixed = copy.deepcopy(value)
        mixed["contract"]["selector"] = "0x7357f5d2"
        with self.assertRaises(runner.Finding):
            runner.validate_case(mixed)
        self.assertIn("run(uint256,uint256[])", runner.scope(value))

    def test_flags_parity_selects_completion_and_containment_applies(self):
        value = array_case()
        self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]], ["returned", "reverted", "returned"])
        self.assertEqual(runner.compare(array_histories(value), value)["category"], "matched")
        observed = array_histories(value)
        observed["rustEvm"]["transactions"][2]["undeclaredStorage"] = [{"slot": "5", "value": "1"}]
        result = runner.compare(observed, value)
        self.assertEqual((result["category"], result["transactionId"], result["undeclaredPaths"]), ("semantic-mismatch", "tx-2", ["rustEvm"]))
        flipped = array_histories(value)
        for history in flipped.values():
            history["transactions"][1]["status"] = "returned"
        self.assertEqual(runner.compare(flipped, value)["category"], "semantic-mismatch")
        keyed_schema = array_histories(value)
        keyed_schema["directCore"]["schema"] = runner.KEYED_HISTORY_SCHEMA
        self.assertEqual(runner.compare(keyed_schema, value)["category"], "adapter-error")

    def test_array_hull_history_uses_the_declared_slot_runner_rows(self):
        value = array_case()
        deployment = {"stage": "deployment", "status": "returned", "committedStorage": keyed_slots(value), "accountStorage": whole(), "undeclaredStorage": []}
        calls = [{"stage": "execution", **row} for row in array_history(value, "importedHull")["transactions"]]
        history = runner.hull_history("\n".join(json.dumps(row) for row in [deployment, *calls]), 0, value)
        self.assertEqual((history["schema"], history["observedSlots"]), (runner.ARRAY_HISTORY_SCHEMA, list(runner.ARRAY_SLOTS)))



HIGH_WORD = 2**255


def log_case(sites=((1, 2, 1), (3, 0, 2)), rows=((2, 5), (11, 1), (8, HIGH_WORD))):
    """Envelope fixture only: native replay checks the actual log program."""
    transactions = [{"id": f"tx-{index}", "flags": str(flags), "input": str(value), "value": "0",
        "calldata": "0x7357f5d2" + f"{flags:064x}" + f"{value:064x}"} for index, (flags, value) in enumerate(rows)]
    return {"schema": runner.LOG_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "logPlan": {"schema": "solcore-lean.log-plan.v1", "stepProgram": {},
                    "sites": [{"guard": guard, "topics": topics, "dataWords": data} for guard, topics, data in sites]},
        "initialState": {"storage": []}, "observedSlots": ["0", "1"],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedLogs", "method": "run", "signature": "run(uint256,uint256)",
            "selector": "0x7357f5d2", "deployPath": ["SynthesizedLogsDeploy"],
            "runtimePath": ["SynthesizedLogsDeploy", "SynthesizedLogs"], "constructorCalldata": "0x"},
        "transactions": transactions}


def log_entry(topics, words, address="101"):
    return {"address": address, "topics": [str(topic) for topic in topics], "data": "0x" + "".join(f"{word:064x}" for word in words)}


def log_history(value, path, address="101"):
    """Rows whose logs have the plan's static shapes; the topic and data values
    are protocol fixtures, not predictions of any step."""
    rows, counter = [], 0
    for index, tx in enumerate(value["transactions"]):
        reverted = int(tx["flags"]) % 2 == 1
        counter += 0 if reverted else 1
        logs = [] if reverted else [log_entry([100 * index + 10 * site["guard"] + j for j in range(1, site["topics"] + 1)],
                                              [index + site["guard"]] * site["dataWords"], address)
                                    for site in runner.guarded_sites(value, tx)]
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned",
               "output": "0x" + f"{index + 3:064x}", "committedStorage": slots(0, counter), "logs": logs}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
    result = {"schema": runner.LOG_HISTORY_SCHEMA, "observedSlots": ["0", "1"], "initialStorage": slots(),
        "initialLogs": [], "transactions": rows, "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]),
        "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    if path == "directCore":
        result["bindings"] = {"schema": "solcore-lean.storage-bindings.v1", "caller": "17", "address": address}
    if path == "rustEvm":
        result["chainLogs"] = [copy.deepcopy(log) for row in rows for log in row["logs"]]
    return with_whole(result, address)


def log_histories(value=None):
    value = log_case() if value is None else value
    return {path: log_history(value, path) for path in runner.PATHS}


class EventLogTests(unittest.TestCase):
    def test_log_case_validates_sites_flags_and_two_word_calldata(self):
        value = log_case()
        runner.validate_case(value)
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"], selected["logs"]),
                         ("semantic-log-tool", "rust-hull-keyed-storage-scenario", True, "flags", True))
        self.assertTrue(runner.has_logs(value))
        self.assertFalse(runner.has_logs(case()))
        self.assertEqual(runner.observed_slots(value), ("0", "1"))
        self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]], ["returned", "reverted", "returned"])
        self.assertEqual([runner.expected_log_shapes(value, tx) for tx in value["transactions"]], [[(2, 32)], [], [(0, 64)]])
        self.assertEqual([len(runner.guarded_sites(value, tx)) for tx in value["transactions"]], [1, 2, 1])
        noisy = log_case(rows=((HIGH_WORD + 16 + 2, 0),))
        self.assertEqual(runner.expected_log_shapes(noisy, noisy["transactions"][0]), [(2, 32)])
        for sites in ([{"guard": 0, "topics": 0, "dataWords": 0}], [{"guard": 4, "topics": 0, "dataWords": 0}],
                      [{"guard": 1, "topics": 5, "dataWords": 0}], [{"guard": 1, "topics": 0, "dataWords": 3}],
                      [{"guard": 2, "topics": 0, "dataWords": 0}, {"guard": 1, "topics": 0, "dataWords": 0}],
                      [{"guard": 1, "topics": 0, "dataWords": 0, "extra": 1}], [{"guard": True, "topics": 0, "dataWords": 0}],
                      [{"guard": 1, "topics": 0, "dataWords": 0}] * 4, {"guard": 1}):
            invalid = copy.deepcopy(value)
            invalid["logPlan"]["sites"] = sites
            with self.subTest(sites=sites), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        for key, changed in (("flags", "02"), ("flags", str(2**256)), ("input", "05"),
                             ("calldata", "0x7357f5d2" + "00" * 64), ("value", "1")):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        for slots_value in (["0"], ["1", "0"], ["0", "1", "2"]):
            with self.subTest(slots=slots_value), self.assertRaises(runner.Finding):
                runner.validate_case({**value, "observedSlots": slots_value})
        mixed = copy.deepcopy(value)
        mixed["contract"]["name"] = "SynthesizedKeyedStorage"
        with self.assertRaises(runner.Finding):
            runner.validate_case(mixed)
        self.assertIn("ordered committed logs", runner.scope(value))

    def test_ordered_committed_logs_are_compared_per_transaction_on_every_path(self):
        value = log_case()
        self.assertEqual(runner.compare(log_histories(value), value)["category"], "matched")
        changes = {"topic": lambda logs: logs[0]["topics"].__setitem__(0, "999"),
            "data": lambda logs: logs[0].__setitem__("data", "0x" + "00" * 31 + "09"),
            "address": lambda logs: logs[0].__setitem__("address", "102"),
            "extra": lambda logs: logs.append(copy.deepcopy(logs[0])),
            "missing": lambda logs: logs.pop()}
        for path in runner.PATHS:
            for name, change in changes.items():
                observed = log_histories(value)
                change(observed[path]["transactions"][0]["logs"])
                if path == "rustEvm":
                    observed[path]["chainLogs"] = [copy.deepcopy(log) for row in observed[path]["transactions"] for log in row["logs"]]
                result = runner.compare(observed, value)
                with self.subTest(path=path, change=name):
                    self.assertEqual((result["category"], result["transactionId"], result["fields"]), ("semantic-mismatch", "tx-0", ["logs"]))
                    self.assertFalse(all(result["pairs"].values()))
        reordered = log_case(sites=((1, 1, 0), (2, 1, 0)), rows=((6, 0),))
        observed = log_histories(reordered)
        observed["importedHull"]["transactions"][0]["logs"].reverse()
        self.assertEqual(runner.compare(observed, reordered)["fields"], ["logs"])

    def test_static_shapes_reject_agreed_protocol_violations(self):
        value = log_case()
        for name, change in (("dropped", lambda row: row["logs"].pop()),
                             ("widened", lambda row: row["logs"][0]["topics"].append("1")),
                             ("foreign", lambda row: row["logs"][0].__setitem__("address", "102"))):
            observed = log_histories(value)
            for path, history in observed.items():
                change(history["transactions"][0])
            observed["rustEvm"]["chainLogs"] = [log for row in observed["rustEvm"]["transactions"] for log in row["logs"]]
            result = runner.compare(observed, value)
            with self.subTest(change=name):
                self.assertTrue(all(result["pairs"].values()))
                self.assertEqual((result["category"], result["transactionId"], result["fields"]), ("semantic-mismatch", "tx-0", ["logs"]))
        committed = log_histories(value)
        for history in committed.values():
            history["transactions"][1]["logs"] = [log_entry([1], [])]
        result = runner.compare(committed, value)
        self.assertEqual((result["category"], result["transactionId"], result["fields"]), ("semantic-mismatch", "tx-1", ["logs"]))
        unbound = log_histories(value)
        del unbound["directCore"]["bindings"]
        self.assertEqual(runner.compare(unbound, value)["category"], "matched")
        for bound in ("0101", None):
            malformed = log_histories(value)
            malformed["directCore"]["bindings"]["address"] = bound
            with self.subTest(bound=bound):
                self.assertEqual(runner.compare(malformed, value)["category"], "adapter-error")

    def test_deployment_logs_and_the_evm_chain_list_are_committed_observations(self):
        value = log_case()
        for path in runner.PATHS:
            deployed = log_histories(value)
            deployed[path]["initialLogs"] = [log_entry([], [])]
            result = runner.compare(deployed, value)
            with self.subTest(path=path):
                self.assertEqual((result["category"], result["stage"], result["fields"], result["logPaths"]),
                                 ("semantic-mismatch", "initial-storage", ["initialLogs"], [path]))
        for name, change in (("lost", lambda logs: logs.pop(0)), ("extra", lambda logs: logs.append(log_entry([7], [7]))),
                             ("reordered", lambda logs: logs.reverse())):
            observed = log_histories(value)
            change(observed["rustEvm"]["chainLogs"])
            result = runner.compare(observed, value)
            with self.subTest(chain=name):
                self.assertEqual((result["category"], result["stage"], result["fields"], result["logPaths"]),
                                 ("semantic-mismatch", "committed-log-history", ["chainLogs"], ["rustEvm"]))
        unobserved = log_histories(value)
        unobserved["rustEvm"]["chainLogs"] = None
        self.assertEqual(runner.compare(unobserved, value)["category"], "adapter-error")
        for path in ("directCore", "importedHull"):
            claimed = log_histories(value)
            claimed[path]["chainLogs"] = []
            with self.subTest(path=path):
                self.assertEqual(runner.compare(claimed, value)["category"], "adapter-error")

    def test_log_records_are_canonical_and_unknown_after_incomplete_rows(self):
        value = log_case()
        for bad in ({"address": "101", "topics": ["1"] * 5, "data": "0x"}, {"address": str(2**160), "topics": [], "data": "0x"},
                    {"address": "101", "topics": ["01"], "data": "0x"}, {"address": "101", "topics": [], "data": "0x0"},
                    {"address": "101", "topics": [], "data": "0x", "extra": 1}, {"address": "101", "topics": "1", "data": "0x"}):
            observed = log_histories(value)
            observed["importedHull"]["transactions"][0]["logs"] = [bad]
            with self.subTest(bad=bad):
                self.assertEqual(runner.compare(observed, value)["category"], "adapter-error")
        missing = log_histories(value)
        del missing["directCore"]["transactions"][0]["logs"]
        self.assertEqual(runner.compare(missing, value)["category"], "adapter-error")
        stopped = log_histories(value)
        history = stopped["directCore"]
        history["transactions"] = history["transactions"][:2]
        history["transactions"][1] = {"id": "tx-1", "index": 1, "status": "out-of-fuel", "committedStorage": slots(0, 1), "logs": None,
                                      "accountStorage": whole(slots(0, 1), address="101")}
        history.update(status="incomplete", unexecuted=["tx-2"], finalStorage=slots(0, 1),
                       finalAccountStorage=whole(slots(0, 1), address="101"))
        normalized = runner.normalize_history(history, value, "directCore")
        self.assertIsNone(normalized["transactions"][1]["logs"])
        self.assertEqual(runner.compare(stopped, value)["category"], "inconclusive-resource")

    def test_receipt_logs_name_their_receipt_and_chain_logs_their_case(self):
        tx_hash, block, address = "0x" + "11" * 32, "0x5", "0x" + "ab" * 20
        event = lambda index, topics=("0x" + "00" * 31 + "07",), data="0x" + "00" * 31 + "02", hash_value=tx_hash, at=block: {
            "address": address, "topics": list(topics), "data": data, "transactionHash": hash_value,
            "blockNumber": at, "logIndex": hex(index), "removed": False}
        mined = {"transactionHash": tx_hash, "blockNumber": block, "logs": [event(0), event(1, (), "0x")]}
        self.assertEqual(runner.evm_logs(mined), [{"address": str(int(address, 16)), "topics": ["7"], "data": "0x" + "00" * 31 + "02"},
                                                  {"address": str(int(address, 16)), "topics": [], "data": "0x"}])
        for bad in (event(0, hash_value="0x" + "22" * 32), event(0, at="0x6"), {**event(0), "removed": True},
                    event(0, ("0x07",)), {**event(0), "address": "0x12"}, {**event(0), "logIndex": "0x01"}):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                runner.evm_logs({**mined, "logs": [bad]})
        with self.assertRaises(ValueError):
            runner.evm_logs({**mined, "logs": [event(1), event(0)]})
        with self.assertRaises(ValueError):
            runner.evm_logs({"transactionHash": tx_hash, "blockNumber": block})
        later = {"transactionHash": "0x" + "33" * 32, "blockNumber": "0x7", "logs": []}
        calls = []
        class Rpc:
            def __init__(self, events):
                self.events = events
            def call(self, method, params):
                calls.append((method, params))
                return self.events
        chain = [event(0, (), "0x", later["transactionHash"], "0x7"), event(0)]
        self.assertEqual(runner.evm_chain_logs(Rpc(chain), address, [mined, later]),
                         [runner.evm_log(event(0)), runner.evm_log(chain[0])])
        self.assertEqual(calls, [("eth_getLogs", [{"address": address, "fromBlock": "0x0", "toBlock": "0x7"}])])
        with self.assertRaises(ValueError):
            runner.evm_chain_logs(Rpc([event(0, hash_value="0x" + "44" * 32)]), address, [mined])
        with self.assertRaises(ValueError):
            runner.evm_chain_logs(Rpc({}), address, [mined])

    def test_log_hull_history_reads_deployment_and_receipt_logs(self):
        value = log_case()
        expected = log_history(value, "importedHull")
        deployment = {"stage": "deployment", "status": "returned", "committedStorage": slots(), "accountStorage": whole(), "undeclaredStorage": [], "logs": []}
        calls = [{"stage": "execution", **row} for row in expected["transactions"]]
        history = runner.hull_history("\n".join(json.dumps(row) for row in [deployment, *calls]), 0, value)
        self.assertEqual((history["schema"], history["initialLogs"], history["observedSlots"]), (runner.LOG_HISTORY_SCHEMA, [], ["0", "1"]))
        self.assertEqual([row["logs"] for row in history["transactions"]], [row["logs"] for row in expected["transactions"]])
        deployment["logs"] = [log_entry([], [])]
        self.assertEqual(runner.hull_history("\n".join(json.dumps(row) for row in [deployment, *calls]), 0, value)["initialLogs"],
                         [log_entry([], [])])
        del deployment["logs"]
        with self.assertRaises(ValueError):
            runner.hull_history("\n".join(json.dumps(row) for row in [deployment, *calls]), 0, value)

    def test_storage_profiles_without_logs_keep_their_observation(self):
        for value, observed in ((case(), histories(case())), (keyed_case(), keyed_histories()), (array_case(), array_histories())):
            with self.subTest(schema=value["schema"]):
                self.assertFalse(runner.has_logs(value))
                self.assertEqual(runner.compare(observed, value)["category"], "matched")
                normalized = runner.normalize_history(observed["rustEvm"], value, "rustEvm")
                self.assertNotIn("initialLogs", normalized)
                self.assertNotIn("logs", normalized["transactions"][0])



def value_case(deployment=5, rows=((0, 0, 7), (1, 1, 2**64), (0, 3, 1))):
    """Envelope fixture only: native replay checks the actual call-value program."""
    transactions = [{"id": f"tx-{index}", "flags": str(flags), "input": str(value), "value": str(sent),
        "calldata": "0x7357f5d2" + f"{flags:064x}" + f"{value:064x}"} for index, (flags, value, sent) in enumerate(rows)]
    return {"schema": runner.VALUE_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "callValuePlan": {"schema": "solcore-lean.call-value-plan.v1", "stepProgram": {}, "deploymentValue": str(deployment)},
        "initialState": {"storage": []}, "observedSlots": ["0", "1"],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedCallValue", "method": "run", "signature": "run(uint256,uint256)",
            "selector": "0x7357f5d2", "deployPath": ["SynthesizedCallValueDeploy"],
            "runtimePath": ["SynthesizedCallValueDeploy", "SynthesizedCallValue"], "constructorCalldata": "0x"},
        "transactions": transactions}


def value_history(value, path):
    """Rows that accept committed values and refund reverted ones; payloads and
    slot zero are protocol fixtures, not predictions of any step."""
    deployment = int(value["callValuePlan"]["deploymentValue"])
    rows, accepted = [], 0
    for index, tx in enumerate(value["transactions"]):
        reverted = int(tx["flags"]) % 2 == 1
        accepted += 0 if reverted else int(tx["value"])
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned",
               "output": "0x" + f"{index + 3:064x}", "committedStorage": slots(index, accepted),
               "committedBalance": str(deployment + accepted)}
        if reverted:
            row["committedStorage"] = copy.deepcopy(rows[-1]["committedStorage"]) if rows else slots()
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
    result = {"schema": runner.VALUE_HISTORY_SCHEMA, "observedSlots": ["0", "1"], "initialStorage": slots(),
        "initialBalance": str(deployment), "initialLogs": [], "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "finalBalance": rows[-1]["committedBalance"],
        "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def value_histories(value=None):
    value = value_case() if value is None else value
    return {path: value_history(value, path) for path in runner.PATHS}


class CallValueTests(unittest.TestCase):
    def test_value_case_validates_values_funds_and_two_word_calldata(self):
        value = value_case()
        runner.validate_case(value)
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"], selected["balances"]),
                         ("semantic-call-value-tool", "rust-hull-value-scenario", True, "value", True))
        self.assertTrue(runner.has_balances(value) and runner.deployment_logs(value))
        self.assertFalse(runner.has_logs(value) or runner.has_balances(log_case()) or runner.deployment_value(log_case()))
        self.assertEqual(runner.deployment_value(value), 5)
        self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]], ["returned", "reverted", "returned"])
        self.assertEqual(runner.expected_balance(value, {"committedStorage": slots(9, 8)}), "13")
        runner.validate_case(value_case(rows=((0, 0, 2**70), (0, 0, 2**70), (0, 0, 2**70)), deployment=2**70))
        for key, changed in (("value", "07"), ("value", str(2**70 + 1)), ("value", None), ("flags", "01"),
                             ("calldata", value["transactions"][0]["calldata"][:-2]), ("calldata", "0xa444f5e9" + "00" * 64)):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        for deployment in ("05", str(2**70 + 1), None, 5):
            invalid = copy.deepcopy(value)
            invalid["callValuePlan"]["deploymentValue"] = deployment
            with self.subTest(deployment=deployment), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        for slots_value in (["0"], ["0", "1", "2"]):
            with self.subTest(slots=slots_value), self.assertRaises(runner.Finding):
                runner.validate_case({**value, "observedSlots": slots_value})
        mixed = copy.deepcopy(value)
        mixed["contract"]["name"] = "SynthesizedLogs"
        with self.assertRaises(runner.Finding):
            runner.validate_case(mixed)
        self.assertIn("committed balance", runner.scope(value))
        zero = log_case()
        self.assertEqual(zero["transactions"][0]["value"], "0")
        zero["transactions"][0]["value"] = "1"
        with self.assertRaises(ValueError):
            runner.validate_case(zero)

    def test_committed_balances_are_compared_and_refunds_required(self):
        value = value_case()
        self.assertEqual(runner.compare(value_histories(value), value)["category"], "matched")
        for path in runner.PATHS:
            observed = value_histories(value)
            observed[path]["transactions"][2]["committedBalance"] = "14"
            observed[path]["finalBalance"] = "14"
            result = runner.compare(observed, value)
            with self.subTest(path=path):
                self.assertEqual((result["category"], result["transactionId"], result["fields"]),
                                 ("semantic-mismatch", "tx-2", ["committedBalance"]))
        kept = value_histories(value)
        for history in kept.values():
            history["transactions"][1]["committedBalance"] = str(12 + 2**64)
        result = runner.compare(kept, value)
        self.assertTrue(all(result["pairs"].values()))
        self.assertEqual((result["category"], result["transactionId"], result["fields"]), ("semantic-mismatch", "tx-1", ["committedBalance"]))
        drift = value_histories(value)
        for history in drift.values():
            for row in history["transactions"]:
                row["committedBalance"] = str(int(row["committedBalance"]) + 1)
            history["finalBalance"] = history["transactions"][-1]["committedBalance"]
        self.assertEqual(runner.compare(drift, value)["fields"], ["committedBalance"])
        for path in runner.PATHS:
            unfunded = value_histories(value)
            unfunded[path]["initialBalance"] = "0"
            result = runner.compare(unfunded, value)
            with self.subTest(path=path, stage="deployment"):
                self.assertEqual((result["category"], result["stage"], result["fields"]),
                                 ("semantic-mismatch", "initial-storage", ["committedBalance"]))
        logged = value_histories(value)
        logged["importedHull"]["initialLogs"] = [log_entry([], [])]
        result = runner.compare(logged, value)
        self.assertEqual((result["stage"], result["fields"], result["logPaths"]), ("initial-storage", ["initialLogs"], ["importedHull"]))

    def test_balance_observations_are_canonical_and_complete(self):
        value = value_case()
        for name, change in (("missing", lambda h: h["transactions"][0].pop("committedBalance")),
                             ("noncanonical", lambda h: h["transactions"][0].__setitem__("committedBalance", "012")),
                             ("final", lambda h: h.__setitem__("finalBalance", "99")),
                             ("initial", lambda h: h.pop("initialBalance")),
                             ("logs", lambda h: h.pop("initialLogs"))):
            observed = value_histories(value)
            change(observed["rustEvm"])
            with self.subTest(change=name):
                self.assertEqual(runner.compare(observed, value)["category"], "adapter-error")
        stopped = value_histories(value)
        history = stopped["directCore"]
        history["transactions"] = history["transactions"][:2]
        history["transactions"][1] = {"id": "tx-1", "index": 1, "status": "out-of-fuel", "committedStorage": slots(0, 7), "committedBalance": "12",
                                      "accountStorage": whole(slots(0, 7))}
        history.update(status="incomplete", unexecuted=["tx-2"], finalStorage=slots(0, 7), finalBalance="12",
                       finalAccountStorage=whole(slots(0, 7)))
        self.assertEqual(runner.normalize_history(history, value, "directCore")["finalBalance"], "12")
        self.assertEqual(runner.compare(stopped, value)["category"], "inconclusive-resource")

    def test_evm_balance_reads_the_receipt_block(self):
        calls = []
        class Rpc:
            def call(self, method, params):
                calls.append((method, params))
                return hex(12)
        self.assertEqual(runner.evm_balance(Rpc(), "0x" + "ab" * 20, "0x5"), "12")
        self.assertEqual(calls, [("eth_getBalance", ["0x" + "ab" * 20, "0x5"])])
        with self.assertRaises(ValueError):
            runner.evm_balance(Rpc(), "0x" + "ab" * 20, "5")

    def test_value_hull_history_reads_balances_and_deployment_logs(self):
        value = value_case()
        expected = value_history(value, "importedHull")
        deployment = {"stage": "deployment", "status": "returned", "committedStorage": slots(), "accountStorage": whole(), "undeclaredStorage": [],
                      "committedBalance": "5", "logs": []}
        calls = [{"stage": "execution", **row} for row in expected["transactions"]]
        history = runner.hull_history("\n".join(json.dumps(row) for row in [deployment, *calls]), 0, value)
        self.assertEqual((history["schema"], history["initialBalance"], history["finalBalance"], history["initialLogs"]),
                         (runner.VALUE_HISTORY_SCHEMA, "5", expected["finalBalance"], []))
        del deployment["committedBalance"]
        with self.assertRaises(ValueError):
            runner.hull_history("\n".join(json.dumps(row) for row in [deployment, *calls]), 0, value)

    def test_profiles_without_balances_keep_their_observation(self):
        for value, observed in ((case(), histories(case())), (keyed_case(), keyed_histories()), (log_case(), log_histories())):
            with self.subTest(schema=value["schema"]):
                self.assertEqual(runner.compare(observed, value)["category"], "matched")
                normalized = runner.normalize_history(observed["rustEvm"], value, "rustEvm")
                self.assertNotIn("initialBalance", normalized)
                self.assertNotIn("committedBalance", normalized["transactions"][0])


def bytes_calldata(flags, data):
    """Written from the ABI rules, independently of the adapter's encoder."""
    return "0x220eb9b6" + f"{flags:064x}" + f"{64:064x}" + f"{len(data):064x}" + data.hex() + "00" * (-len(data) % 32)


def bytes_case(rows=((0, bytes([1, 3, 7])), (1, b"\xff" * 33), (2, b""))):
    """Envelope fixture only: native replay checks the actual bytes program."""
    transactions = [{"id": f"tx-{index}", "flags": str(flags), "payload": "0x" + data.hex(), "value": "0",
        "calldata": bytes_calldata(flags, data)} for index, (flags, data) in enumerate(rows)]
    return {"schema": runner.BYTES_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "bytesPlan": {"schema": "solcore-lean.bytes-plan.v1", "stepProgram": {}},
        "initialState": {"storage": []}, "observedSlots": list(runner.BYTES_SLOTS),
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedBytes", "method": "run", "signature": "run(uint256,bytes)",
            "selector": "0x220eb9b6", "deployPath": ["SynthesizedBytesDeploy"],
            "runtimePath": ["SynthesizedBytesDeploy", "SynthesizedBytes"], "constructorCalldata": "0x"},
        "transactions": transactions}


def bytes_slots(values=(0, 0, 0, 0, 0)):
    return [{"slot": str(index), "value": str(value)} for index, value in enumerate(values)]


def bytes_history(value, path):
    """Rows that follow the bytes protocol: slots zero to two are fixtures,
    slot three counts committed payload bytes, slot four holds the last byte,
    and a returned payload is the committed sum plus the calldata size. Odd
    flags revert and keep the prior snapshot."""
    rows, prior = [], [0, 0, 0, 0, 0]
    for index, tx in enumerate(value["transactions"]):
        data = bytes.fromhex(tx["payload"][2:])
        reverted = int(tx["flags"]) % 2 == 1
        committed = list(prior) if reverted else [index + 10, index + 20, index + 30, prior[3] + len(data), data[-1] if data else 0]
        output = index + 3 if reverted else committed[0] + committed[3] + committed[4] + 100 + len(data) + -len(data) % 32
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned",
               "output": "0x" + f"{output:064x}", "committedStorage": bytes_slots(committed)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
        prior = committed
    result = {"schema": runner.BYTES_HISTORY_SCHEMA, "observedSlots": list(runner.BYTES_SLOTS),
        "initialStorage": bytes_slots(), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def bytes_histories(value=None):
    value = bytes_case() if value is None else value
    return {path: bytes_history(value, path) for path in runner.PATHS}


class BytesTests(unittest.TestCase):
    def test_bytes_case_requires_canonical_zero_padded_calldata(self):
        value = bytes_case()
        runner.validate_case(value)
        # `cast calldata "run(uint256,bytes)" 1 0xabab...ab` (33 bytes) from the pinned Foundry release.
        self.assertEqual(bytes_calldata(1, b"\xab" * 33), "0x220eb9b6" + "".join(
            f"{word:064x}" for word in (1, 0x40, 0x21)) + "ab" * 33 + "00" * 31)
        self.assertEqual(runner.bytes_calldata("0x220eb9b6", 1, b"\xab" * 33), bytes_calldata(1, b"\xab" * 33))
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"]),
                         ("semantic-bytes-tool", "rust-hull-keyed-storage-scenario", True, "bytes"))
        self.assertEqual(runner.observed_slots(value), ("0", "1", "2", "3", "4"))
        self.assertTrue(runner.has_bytes(value))
        self.assertFalse(runner.has_bytes(array_case()) or runner.has_logs(value) or runner.has_balances(value) or runner.deployment_logs(value))
        self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]], ["returned", "reverted", "returned"])
        self.assertEqual([runner.payload_chunks(tx) for tx in value["transactions"]],
                         [[int.from_bytes(bytes([1, 3, 7]) + bytes(29), "big")], [MAX_WORD, 0xff << 248], []])
        runner.validate_case(bytes_case(rows=((0, bytes(64)),)))
        original = value["transactions"][0]["calldata"]
        for key, changed in (("payload", "0x0103"), ("payload", "0x01030A"), ("payload", "010307"), ("payload", "0x0103070"),
                             ("payload", "0x" + "01" * 65), ("payload", None), ("payload", [1, 3, 7]), ("flags", "01"),
                             ("calldata", bytes_calldata(0, bytes([1, 3]))), ("calldata", original[:-2]),
                             ("calldata", original[:-2] + "01"), ("calldata", original.replace(f"{0x40:064x}", f"{0x60:064x}")),
                             ("calldata", "0x9a94c44b" + original[10:]), ("value", "1")):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        for slots in (["0", "1", "2", "3"], ["0", "1", "2", "3", "4", "5"], ["1", "0", "2", "3", "4"]):
            with self.subTest(slots=slots), self.assertRaises(runner.Finding):
                runner.validate_case({**value, "observedSlots": slots})
        mixed = copy.deepcopy(value)
        mixed["contract"]["selector"] = "0x9a94c44b"
        with self.assertRaises(runner.Finding):
            runner.validate_case(mixed)
        self.assertIn("run(uint256,bytes)", runner.scope(value))

    def test_returned_rows_record_length_last_byte_and_sum(self):
        value = bytes_case()
        self.assertEqual(runner.compare(bytes_histories(value), value)["category"], "matched")
        for path in runner.PATHS:
            for slot in (3, 4):
                observed = bytes_histories(value)
                row = observed[path]["transactions"][2]
                row["committedStorage"][slot]["value"] = str(int(row["committedStorage"][slot]["value"]) + 1)
                observed[path]["finalStorage"] = copy.deepcopy(row["committedStorage"])
                result = runner.compare(observed, value)
                with self.subTest(path=path, slot=slot):
                    self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-2"))
                    self.assertFalse(all(result["pairs"].values()))
                    self.assertIn("committedStorage", result["fields"])
        # All three paths agreeing on a wrong count, last byte or sum still break the protocol.
        for name, slot, text in (("count", 3, "4"), ("last byte", 4, "3")):
            agreed = bytes_histories(value)
            for history in agreed.values():
                history["transactions"][0]["committedStorage"][slot]["value"] = text
            result = runner.compare(agreed, value)
            with self.subTest(change=name):
                self.assertTrue(all(result["pairs"].values()))
                self.assertEqual((result["category"], result["transactionId"], result["fields"]),
                                 ("semantic-mismatch", "tx-0", ["committedStorage", "output"]))
        summed = bytes_histories(value)
        for history in summed.values():
            history["transactions"][0]["output"] = "0x" + f"{1:064x}"
        result = runner.compare(summed, value)
        self.assertTrue(all(result["pairs"].values()))
        self.assertEqual((result["category"], result["transactionId"], result["fields"]), ("semantic-mismatch", "tx-0", ["output"]))
        committed = bytes_histories(value)
        for history in committed.values():
            history["transactions"][1]["committedStorage"][3]["value"] = "36"
        result = runner.compare(committed, value)
        self.assertEqual((result["category"], result["transactionId"], result["fields"]), ("semantic-mismatch", "tx-1", ["committedStorage"]))
        observed = bytes_histories(value)
        observed["rustEvm"]["transactions"][2]["undeclaredStorage"] = [{"slot": "5", "value": "1"}]
        result = runner.compare(observed, value)
        self.assertEqual((result["category"], result["transactionId"], result["undeclaredPaths"]), ("semantic-mismatch", "tx-2", ["rustEvm"]))
        array_schema = bytes_histories(value)
        array_schema["directCore"]["schema"] = runner.ARRAY_HISTORY_SCHEMA
        self.assertEqual(runner.compare(array_schema, value)["category"], "adapter-error")

    def test_conforms_applies_the_bytes_protocol(self):
        value = bytes_case()
        history = runner.normalize_history(bytes_history(value, "rustEvm"), value, "rustEvm")
        prior = history["initialStorage"]
        for tx, row in zip(value["transactions"], history["transactions"]):
            self.assertTrue(runner.conforms(value, tx, row, prior))
            prior = row["committedStorage"]
        row = copy.deepcopy(history["transactions"][0])
        row["committedStorage"][4]["value"] = "8"
        self.assertFalse(runner.conforms(value, value["transactions"][0], row, history["initialStorage"]))
        self.assertEqual(runner.bytes_fields(value["transactions"][0], row, history["initialStorage"]), ["committedStorage", "output"])
        self.assertEqual(runner.bytes_fields(value["transactions"][1], history["transactions"][1], history["transactions"][0]["committedStorage"]), [])
        self.assertEqual(runner.bytes_fields(value["transactions"][2], history["transactions"][2], history["transactions"][1]["committedStorage"]), [])

    def test_bytes_hull_history_uses_the_declared_slot_runner_rows(self):
        value = bytes_case()
        deployment = {"stage": "deployment", "status": "returned", "committedStorage": bytes_slots(), "accountStorage": whole(), "undeclaredStorage": []}
        calls = [{"stage": "execution", **row} for row in bytes_history(value, "importedHull")["transactions"]]
        history = runner.hull_history("\n".join(json.dumps(row) for row in [deployment, *calls]), 0, value)
        self.assertEqual((history["schema"], history["observedSlots"]), (runner.BYTES_HISTORY_SCHEMA, list(runner.BYTES_SLOTS)))
        self.assertNotIn("initialLogs", history)
        self.assertEqual(runner.compare({**bytes_histories(value), "importedHull": history}, value)["category"], "matched")


# `cast to-dec $(cast keccak 0x$(printf %064x 1)$(printf %064x KEY))` from the
# pinned Foundry release: the pinned std's `keccak256(1 ++ key)` entry slots.
CAST_ENTRY_SLOTS = {
    0: 78541660797044910968829902406342334108369226379826116161446442989268089806461,
    1: 92458281274488595289803937127152923398167637295201432141969818930235769911599,
    5: 9247535584797915451057180664748820695544591120644449140157971996739901653371,
    6: 28212876883947467128917703474378516019173305230661588919942657668795042982449,
    7: 81222191986226809103279119994707868322855741819905904417953092666699096963112,
    MAX_WORD: 71124947674796991739310909576881207026731009306364129481614628957978744178186}
# Solidity's order, `keccak256(5 ++ 1)`, which the pinned std does not use.
CAST_SOLIDITY_SLOT_5 = 102407538280218558175650617366741421990572744813161403407894353239866642134028


def mapping_calldata(flags, key, value):
    """Written from the ABI rules, independently of the adapter's encoder."""
    return "0x24b912e5" + f"{flags:064x}" + f"{key:064x}" + f"{value:064x}"


def mapping_case(rows=((0, 5, 7), (1, 6, 3), (2, MAX_WORD, 1))):
    """Envelope fixture only: native replay checks the actual mapping program."""
    transactions = [{"id": f"tx-{index}", "flags": str(flags), "key": str(key), "input": str(value), "value": "0",
        "calldata": mapping_calldata(flags, key, value)} for index, (flags, key, value) in enumerate(rows)]
    slots = {0} | {CAST_ENTRY_SLOTS[(key + step) % 2**256] for _, key, _ in rows for step in (0, 1)}
    return {"schema": runner.MAPPING_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "mappingPlan": {"schema": "solcore-lean.mapping-plan.v1", "stepProgram": {}},
        "initialState": {"storage": []}, "observedSlots": [str(slot) for slot in sorted(slots)],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedMapping", "method": "run", "signature": "run(uint256,uint256,uint256)",
            "selector": "0x24b912e5", "deployPath": ["SynthesizedMappingDeploy"],
            "runtimePath": ["SynthesizedMappingDeploy", "SynthesizedMapping"], "constructorCalldata": "0x"},
        "transactions": transactions}


def mapping_slots(value, values=None):
    values = values or {}
    return [{"slot": slot, "value": str(values.get(slot, 0))} for slot in value["observedSlots"]]


def mapping_history(value, path):
    """Rows that count returned transactions at slot 0 and write the key's and
    successor's entry slots; odd flags revert and keep the prior snapshot."""
    rows, committed = [], {}
    for index, tx in enumerate(value["transactions"]):
        reverted = int(tx["flags"]) % 2 == 1
        if not reverted:
            key = int(tx["key"])
            committed = {**committed, "0": committed.get("0", 0) + 1, str(CAST_ENTRY_SLOTS[key]): int(tx["input"]) + index,
                         str(CAST_ENTRY_SLOTS[(key + 1) % 2**256]): 1}
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned",
               "output": "0x" + f"{index + 3:064x}", "committedStorage": mapping_slots(value, committed)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
    result = {"schema": runner.MAPPING_HISTORY_SCHEMA, "observedSlots": value["observedSlots"],
        "initialStorage": mapping_slots(value), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def mapping_histories(value=None):
    value = mapping_case() if value is None else value
    return {path: mapping_history(value, path) for path in runner.PATHS}


class MappingTests(unittest.TestCase):
    def test_adapter_keccak_matches_cast_vectors(self):
        # `cast keccak` of the empty string, "abc", 135 and 136 zero bytes (the
        # one-block padding edges) and 200 bytes 0xab (two blocks).
        for data, digest in ((b"", "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),
                             (b"abc", "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"),
                             (bytes(135), "29e3704feeca7fb9ba229f0fa04d9b36449cf3ad6e1d85d9cfff3a10df9abc3e"),
                             (bytes(136), "3a5912a7c5faa06ee4fe906253e339467a9ce87d533c65be3c15cb231cdb25f9"),
                             (b"\xab" * 200, "8ca353cee0a5c5b999a0916e88da37a16293cf14a73c735d6b5197b50c3d6656")):
            with self.subTest(size=len(data)):
                self.assertEqual(runner.keccak256(data).hex(), digest)
        for key, slot in CAST_ENTRY_SLOTS.items():
            with self.subTest(key=key):
                self.assertEqual(runner.entry_slot(key), slot)
        self.assertEqual(runner.entry_slot(2**256 + 5), CAST_ENTRY_SLOTS[5])
        self.assertNotIn(CAST_SOLIDITY_SLOT_5, CAST_ENTRY_SLOTS.values())

    def test_mapping_case_declares_entry_slots_and_three_word_calldata(self):
        value = mapping_case()
        runner.validate_case(value)
        self.assertEqual(len(value["observedSlots"]), 6)
        self.assertEqual(runner.mapping_slots(value["transactions"]), value["observedSlots"])
        self.assertEqual(runner.observed_slots(value), tuple(value["observedSlots"]))
        self.assertEqual(runner.mapping_slots([{"key": "6"}, {"key": "6"}, {"key": "5"}]),
                         [str(slot) for slot in sorted((0, CAST_ENTRY_SLOTS[5], CAST_ENTRY_SLOTS[6], CAST_ENTRY_SLOTS[7]))])
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["rollback"], selected["keyed"],
                          selected["declared"], selected["abi"], selected["shrinkBatch"]),
                         ("semantic-mapping-tool", "rust-hull-keyed-storage-scenario", True, False, True, "mapping", 16))
        self.assertFalse(runner.has_bytes(value) or runner.has_logs(value) or runner.has_balances(value) or runner.deployment_logs(value))
        self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]], ["returned", "reverted", "returned"])
        reverting = mapping_case(rows=((0, 5, 1), (3, 5, 2)))
        self.assertEqual([runner.expected_status(reverting, tx) for tx in reverting["transactions"]], ["returned", "reverted"])
        original = value["transactions"][0]["calldata"]
        for key, changed in (("flags", "01"), ("key", "05"), ("key", str(2**256)), ("key", None), ("input", "07"),
                             ("calldata", mapping_calldata(0, 7, 5)), ("calldata", original[:-2]),
                             ("calldata", "0x7357f5d2" + original[10:]), ("calldata", original + "00"), ("value", "1")):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        solidity = [str(slot) for slot in sorted({int(slot) for slot in value["observedSlots"]} - {CAST_ENTRY_SLOTS[5]}
                                                 | {CAST_SOLIDITY_SLOT_5})]
        for slots in (solidity, value["observedSlots"][:-1], value["observedSlots"] + [str(MAX_WORD)],
                      sorted(value["observedSlots"] + ["2"], key=int), list(reversed(value["observedSlots"])),
                      ["0", "1", "5", "6", "7", str(MAX_WORD)]):
            with self.subTest(slots=slots), self.assertRaises(runner.Finding):
                runner.validate_case({**value, "observedSlots": slots})
        for key in ("schema", "mappingPlan", "contract"):
            mixed = copy.deepcopy(value)
            mixed[key] = keyed_case()[key] if key != "mappingPlan" else {"schema": "solcore-lean.keyed-storage-plan.v1", "stepProgram": {}}
            with self.subTest(key=key), self.assertRaises((ValueError, runner.Finding)):
                runner.validate_case(mixed)
        self.assertIn("run(uint256,uint256,uint256)", runner.scope(value))
        self.assertIn("keccak256(1 ++ key)", runner.scope(value))

    def test_mapping_histories_compare_entry_slots_and_containment(self):
        value = mapping_case()
        self.assertEqual(runner.compare(mapping_histories(value), value)["category"], "matched")
        entry = value["observedSlots"].index(str(CAST_ENTRY_SLOTS[5]))
        for path in runner.PATHS:
            observed = mapping_histories(value)
            observed[path]["transactions"][0]["committedStorage"][entry]["value"] = "8"
            result = runner.compare(observed, value)
            with self.subTest(path=path):
                self.assertEqual((result["category"], result["transactionId"], result["fields"]),
                                 ("semantic-mismatch", "tx-0", ["committedStorage"]))
                self.assertFalse(all(result["pairs"].values()))
        # A path that wrote Solidity's slot instead of the std's leaves the
        # declared entry zero and an undeclared slot nonzero.
        for path in runner.CONTAINMENT_PATHS:
            observed = mapping_histories(value)
            row = observed[path]["transactions"][0]
            row["undeclaredStorage"] = [{"slot": str(CAST_SOLIDITY_SLOT_5), "value": row["committedStorage"][entry]["value"]}]
            row["committedStorage"][entry]["value"] = "0"
            result = runner.compare(observed, value)
            with self.subTest(path=path, layout="solidity"):
                self.assertEqual((result["category"], result["transactionId"], result["undeclaredPaths"]), ("semantic-mismatch", "tx-0", [path]))
                self.assertEqual(result["fields"], ["committedStorage", "undeclaredStorage"])
        tentative = mapping_histories(value)
        for history in tentative.values():
            history["transactions"][1]["committedStorage"][0]["value"] = "2"
        result = runner.compare(tentative, value)
        self.assertTrue(all(result["pairs"].values()))
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-1"))
        self.assertIn("committedStorage", result["fields"])
        keyed_schema = mapping_histories(value)
        keyed_schema["directCore"]["schema"] = runner.KEYED_HISTORY_SCHEMA
        self.assertEqual(runner.compare(keyed_schema, value)["category"], "adapter-error")
        undeclared = mapping_histories(value)
        undeclared["importedHull"]["observedSlots"] = ["0", "1", "2"]
        self.assertEqual(runner.compare(undeclared, value)["category"], "adapter-error")

    def test_mapping_hull_history_uses_the_declared_slot_runner_rows(self):
        value = mapping_case()
        deployment = {"stage": "deployment", "status": "returned", "committedStorage": mapping_slots(value), "accountStorage": whole(), "undeclaredStorage": []}
        calls = [{"stage": "execution", **row} for row in mapping_history(value, "importedHull")["transactions"]]
        history = runner.hull_history("\n".join(json.dumps(row) for row in [deployment, *calls]), 0, value)
        self.assertEqual((history["schema"], history["observedSlots"], history["initialUndeclaredStorage"]),
                         (runner.MAPPING_HISTORY_SCHEMA, value["observedSlots"], []))
        self.assertEqual(runner.compare({**mapping_histories(value), "importedHull": history}, value)["category"], "matched")


# Anvil's first three default accounts, from their checksummed hex, and
# `cast to-dec $(cast keccak 0x$(printf %064x 1)$(cast to-uint256 KEY | cut -c3-))`
# for every ledger key the fixtures use.
LEDGER_SENDERS = (0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266, 0x70997970C51812dc3A010C7d01b50e0d17dc79C8,
                  0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC)
CAST_LEDGER_SLOTS = {
    LEDGER_SENDERS[0]: 78570585682356430730071959328554860354235701529430903318287531160901974441362,
    LEDGER_SENDERS[1]: 20716297545289759526027067151373890095476849666992757577977631027685962156767,
    LEDGER_SENDERS[2]: 41239936133192089133110966148978916085433226010267689210672645629181891175976,
    0: CAST_ENTRY_SLOTS[0], 2**160 - 1: 43383778025841973631710988075798902187352068724127397131308783529513977091473,
    MAX_WORD: CAST_ENTRY_SLOTS[MAX_WORD]}
# Solidity's order for the first sender, `keccak256(sender ++ 1)`, which the pinned std does not use.
CAST_SOLIDITY_SENDER_SLOT = 74068266984026185789299592274225996433761640432391943524119001479168938317058


def ledger_calldata(flags, recipient, amount, value):
    """Written from the ABI rules, independently of the adapter's encoder."""
    return "0x15509d2b" + f"{flags:064x}" + f"{recipient:064x}" + f"{amount:064x}" + f"{value:064x}"


def ledger_case(rows=((0, 0, LEDGER_SENDERS[1], 1, 7), (1, 0, LEDGER_SENDERS[1], 2**64, 3), (2, 1, MAX_WORD, 7, 7))):
    """Envelope fixture only: native replay checks the actual ledger program.
    Rows are (sender position, flags, recipient, amount, input)."""
    transactions = [{"id": f"tx-{index}", "sender": str(LEDGER_SENDERS[position]), "flags": str(flags),
        "recipient": str(recipient), "amount": str(amount), "input": str(value), "value": "0",
        "calldata": ledger_calldata(flags, recipient, amount, value)}
        for index, (position, flags, recipient, amount, value) in enumerate(rows)]
    slots = {0} | {CAST_LEDGER_SLOTS[LEDGER_SENDERS[row[0]]] for row in rows} | {CAST_LEDGER_SLOTS[row[2]] for row in rows}
    return {"schema": runner.LEDGER_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "ledgerPlan": {"schema": "solcore-lean.ledger-plan.v1", "stepProgram": {}},
        "initialState": {"storage": []}, "observedSlots": [str(slot) for slot in sorted(slots)],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedLedger", "method": "run", "signature": "run(uint256,uint256,uint256,uint256)",
            "selector": "0x15509d2b", "deployPath": ["SynthesizedLedgerDeploy"],
            "runtimePath": ["SynthesizedLedgerDeploy", "SynthesizedLedger"], "constructorCalldata": "0x"},
        "transactions": transactions}


def ledger_slots(value, values=None):
    values = values or {}
    return [{"slot": slot, "value": str(values.get(slot, 0))} for slot in value["observedSlots"]]


def ledger_history(value, path):
    """Rows of the ledger protocol with the identity step: credit the input,
    revert with the credited balance when the amount exceeds it, otherwise move
    the amount, count the transaction and return both entries plus the
    counter; odd flags revert after the writes and keep the prior snapshot."""
    rows, committed = [], {}
    for index, tx in enumerate(value["transactions"]):
        source, target = str(CAST_LEDGER_SLOTS[int(tx["sender"])]), str(CAST_LEDGER_SLOTS[int(tx["recipient"])])
        amount = int(tx["amount"])
        balance = (committed.get(source, 0) + int(tx["input"])) % 2**256
        if amount > balance:
            status, output = "reverted", balance
        else:
            work = {**committed, source: balance - amount}
            work[target] = (work.get(target, 0) + amount) % 2**256
            work["0"] = work.get("0", 0) + 1
            output = (work[source] + work[target] + work["0"]) % 2**256
            status = "reverted" if int(tx["flags"]) % 2 else "returned"
            committed = work if status == "returned" else committed
        row = {"id": tx["id"], "index": index, "status": status, "output": "0x" + f"{output:064x}",
               "committedStorage": ledger_slots(value, committed)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
    result = {"schema": runner.LEDGER_HISTORY_SCHEMA, "observedSlots": value["observedSlots"],
        "initialStorage": ledger_slots(value), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def ledger_histories(value=None):
    value = ledger_case() if value is None else value
    return {path: ledger_history(value, path) for path in runner.PATHS}


class LedgerTests(unittest.TestCase):
    def test_ledger_case_requires_fixed_senders_four_word_calldata_and_derived_slots(self):
        value = ledger_case()
        runner.validate_case(value)
        self.assertEqual(runner.LEDGER_SENDERS, tuple(str(sender) for sender in LEDGER_SENDERS))
        for key, slot in CAST_LEDGER_SLOTS.items():
            with self.subTest(key=key):
                self.assertEqual(runner.entry_slot(key), slot)
        self.assertEqual(len(value["observedSlots"]), 5)
        self.assertEqual(runner.ledger_slots(value["transactions"]), value["observedSlots"])
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["scenarioSchema"], selected["declared"],
                          selected["abi"], selected["senders"], selected["shrinkBatch"]),
                         ("semantic-ledger-tool", "rust-hull-ledger-scenario", "solcore-lean.ledger-contract-scenario.v1",
                          True, "ledger", True, 16))
        self.assertTrue(runner.has_senders(value))
        self.assertFalse(runner.has_senders(mapping_case()) or runner.has_bytes(value) or runner.has_logs(value) or runner.has_balances(value))
        self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]], [None, None, "reverted"])
        original = value["transactions"][0]["calldata"]
        for key, changed in (("sender", "1"), ("sender", "0" + str(LEDGER_SENDERS[0])), ("sender", str(LEDGER_SENDERS[0] + 2**160)),
                             ("sender", None), ("flags", "01"), ("recipient", str(2**256)), ("amount", "01"), ("input", None),
                             ("calldata", ledger_calldata(0, 1, LEDGER_SENDERS[1], 7)), ("calldata", original[:-2]),
                             ("calldata", "0x24b912e5" + original[10:]), ("calldata", original + "00"), ("value", "1")):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        solidity = sorted({int(slot) for slot in value["observedSlots"]} - {CAST_LEDGER_SLOTS[LEDGER_SENDERS[0]]}
                          | {CAST_SOLIDITY_SENDER_SLOT})
        for slots in ([str(slot) for slot in solidity], value["observedSlots"][:-1],
                      sorted(value["observedSlots"] + ["2"], key=int), list(reversed(value["observedSlots"])),
                      runner.mapping_slots([{"key": tx["recipient"]} for tx in value["transactions"]])):
            with self.subTest(slots=slots), self.assertRaises(runner.Finding):
                runner.validate_case({**value, "observedSlots": slots})
        for key in ("schema", "ledgerPlan", "contract"):
            mixed = copy.deepcopy(value)
            mixed[key] = mapping_case()[key] if key != "ledgerPlan" else {"schema": "solcore-lean.mapping-plan.v1", "stepProgram": {}}
            with self.subTest(key=key), self.assertRaises((ValueError, runner.Finding)):
                runner.validate_case(mixed)
        self.assertIn("run(uint256,uint256,uint256,uint256)", runner.scope(value))
        self.assertIn("senders", runner.scope(value))

    def test_ledger_fields_apply_the_protocol_without_the_step(self):
        value = ledger_case()
        history = ledger_history(value, "rustEvm")
        prior, rows = history["initialStorage"], history["transactions"]
        transactions = value["transactions"]
        self.assertEqual([row["status"] for row in rows], ["returned", "reverted", "reverted"])
        for tx, row in zip(transactions, rows):
            self.assertEqual(runner.ledger_fields(tx, row, prior), [])
            self.assertTrue(runner.conforms(value, tx, row, prior))
            prior = row["committedStorage"] if row["status"] == "returned" else prior
        source = value["observedSlots"].index(str(CAST_LEDGER_SLOTS[LEDGER_SENDERS[0]]))
        target = value["observedSlots"].index(str(CAST_LEDGER_SLOTS[LEDGER_SENDERS[1]]))
        initial = history["initialStorage"]
        for name, change, fields in (("overpaid recipient", lambda r: r["committedStorage"][target].update(value="2"), ["committedStorage", "output"]),
                                     ("wrapped sender", lambda r: r["committedStorage"][source].update(value=str(MAX_WORD)), ["committedStorage", "output"]),
                                     ("counter", lambda r: r["committedStorage"][0].update(value="2"), ["committedStorage", "output"]),
                                     ("payload", lambda r: r.update(output="0x" + f"{7:064x}"), ["output"]),
                                     ("odd flags returned", lambda r: None, ["status"])):
            row = copy.deepcopy(rows[0])
            change(row)
            tx = dict(transactions[0], flags="1") if name == "odd flags returned" else transactions[0]
            with self.subTest(change=name):
                self.assertEqual(runner.ledger_fields(tx, row, initial), fields)
                self.assertFalse(runner.conforms(value, tx, row, initial))
        # Another declared slot that changed breaks the protocol even if all else holds.
        other = value["observedSlots"].index(str(CAST_LEDGER_SLOTS[LEDGER_SENDERS[2]]))
        row = copy.deepcopy(rows[0])
        row["committedStorage"][other]["value"] = "1"
        self.assertEqual(runner.ledger_fields(transactions[0], row, initial), ["committedStorage"])
        # An even-flag revert must report a credited balance below the amount.
        insufficient = copy.deepcopy(rows[1])
        insufficient["output"] = "0x" + f"{2**64:064x}"
        self.assertEqual(runner.ledger_fields(transactions[1], insufficient, rows[0]["committedStorage"]), ["output"])
        # A self-transfer leaves an entry of at least the amount.
        self_case = ledger_case(((2, 0, LEDGER_SENDERS[2], 7, 7),))
        self_rows = ledger_history(self_case, "rustEvm")["transactions"]
        self.assertEqual((self_rows[0]["status"], int(self_rows[0]["output"], 16)), ("returned", 15))
        self.assertEqual(runner.ledger_fields(self_case["transactions"][0], self_rows[0], ledger_slots(self_case)), [])
        short = copy.deepcopy(self_rows[0])
        short["committedStorage"][self_case["observedSlots"].index(str(CAST_LEDGER_SLOTS[LEDGER_SENDERS[2]]))]["value"] = "6"
        self.assertIn("committedStorage", runner.ledger_fields(self_case["transactions"][0], short, ledger_slots(self_case)))

    def test_ledger_histories_compare_entries_containment_and_agreed_protocol_breaks(self):
        value = ledger_case()
        self.assertEqual(runner.compare(ledger_histories(value), value)["category"], "matched")
        target = value["observedSlots"].index(str(CAST_LEDGER_SLOTS[LEDGER_SENDERS[1]]))
        for path in runner.PATHS:
            observed = ledger_histories(value)
            observed[path]["transactions"][0]["committedStorage"][target]["value"] = "5"
            result = runner.compare(observed, value)
            with self.subTest(path=path):
                self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-0"))
                self.assertFalse(all(result["pairs"].values()))
        # All three paths agreeing that an insufficient transfer went through is still wrong.
        agreed = ledger_histories(value)
        for history in agreed.values():
            row = history["transactions"][1]
            row["status"], row["output"] = "returned", "0x" + f"{3:064x}"
        result = runner.compare(agreed, value)
        self.assertTrue(all(result["pairs"].values()))
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-1"))
        # A path that keyed the sender in Solidity's order leaves an undeclared slot.
        for path in runner.CONTAINMENT_PATHS:
            observed = ledger_histories(value)
            row = observed[path]["transactions"][0]
            source = value["observedSlots"].index(str(CAST_LEDGER_SLOTS[LEDGER_SENDERS[0]]))
            row["undeclaredStorage"] = [{"slot": str(CAST_SOLIDITY_SENDER_SLOT), "value": row["committedStorage"][source]["value"]}]
            row["committedStorage"][source]["value"] = "0"
            result = runner.compare(observed, value)
            with self.subTest(path=path, layout="solidity"):
                self.assertEqual((result["category"], result["transactionId"], result["undeclaredPaths"]), ("semantic-mismatch", "tx-0", [path]))
        keyed_schema = ledger_histories(value)
        keyed_schema["directCore"]["schema"] = runner.MAPPING_HISTORY_SCHEMA
        self.assertEqual(runner.compare(keyed_schema, value)["category"], "adapter-error")

    def test_ledger_hull_history_uses_the_ledger_runner_rows(self):
        value = ledger_case()
        deployment = {"stage": "deployment", "status": "returned", "committedStorage": ledger_slots(value), "accountStorage": whole(), "undeclaredStorage": []}
        calls = [{"stage": "execution", **row} for row in ledger_history(value, "importedHull")["transactions"]]
        history = runner.hull_history("\n".join(json.dumps(row) for row in [deployment, *calls]), 0, value)
        self.assertEqual((history["schema"], history["observedSlots"], history["initialUndeclaredStorage"]),
                         (runner.LEDGER_HISTORY_SCHEMA, value["observedSlots"], []))
        self.assertEqual(runner.compare({**ledger_histories(value), "importedHull": history}, value)["category"], "matched")

    def run_ledger_execution(self, directory, accounts):
        """Mocked execution: returns every submitted request and the Hull scenario."""
        original = ledger_case()
        source = directory / "case.json"
        source.write_text(json.dumps(original))
        output = directory / "run"
        output.mkdir()
        arguments = SimpleNamespace(case=source, replay=None, output=output, artifact_limit=1 << 20,
            case_tool=Path("case-tool"), core_runner=Path("core-runner"), anvil=Path("anvil"),
            direct_fuel=1000, core_fuel=2000, gas=100000, timeout=1,
            upstream=directory / "upstream", target_dir=directory / "target")
        address = "0x" + "02" * 20
        bindings = {"schema": "solcore-lean.storage-bindings.v1", "caller": str(LEDGER_SENDERS[0]), "address": str(int(address, 16))}
        direct = {**ledger_history(original, "directCore"), "bindings": bindings, "fuelPerTransaction": 1000}
        scenarios = []
        fake_runner = Mock()
        fake_runner.identity.return_value = {"sha256": "0" * 64}
        fake_runner.args = arguments
        fake_runner.remaining.return_value = 10

        def process(stage, command, *_args):
            if stage == "imported-hull":
                scenarios.append(json.loads(Path(command[1]).read_text()))
                hull = ledger_history(original, "importedHull")
                observations = [{"stage": "deployment", "status": "returned", "committedStorage": ledger_slots(original), "accountStorage": whole(),
                                 "undeclaredStorage": []}, *[{"stage": "execution", **row} for row in hull["transactions"]]]
                return {"returncode": 0, "stdout": "\n".join(json.dumps(item) for item in observations)}
            return {"returncode": 0, "stdout": "revision"}

        fake_runner.process.side_effect = process

        def checked_process(_runner, stage, *_args):
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
            if method == "eth_accounts":
                return accounts
            if method == "eth_sendTransaction":
                submitted.append(params[0])
                return "0x" + f"{len(submitted):064x}"
            if method == "eth_getTransactionReceipt":
                deploy = params[0] == "0x" + f"{1:064x}"
                return {"transactionHash": params[0], "status": "0x1", "blockNumber": hex(int(params[0], 16)),
                        "contractAddress": address if deploy else None}
            if method == "eth_getCode":
                return "0x6000"
            if method == "eth_getStorageAt":
                return "0x" + "00" * 32
            if method == "debug_traceTransaction":
                if params[1] == runner.PRESTATE_DIFF:
                    return {"pre": {}, "post": {}}
                return {"failed": False, "returnValue": f"{0:064x}"}
            self.fail(f"unexpected RPC method: {method}")

        rpc.call.side_effect = rpc_call

        @contextmanager
        def anvil(*_args, steps_tracing=False):
            yield rpc

        report = {"histories": {}, "processes": []}
        with patch.object(runner.common, "Runner", return_value=fake_runner), \
                patch.object(runner.common, "checked_process", side_effect=checked_process), \
                patch.object(runner.common, "validate_export", return_value={}), \
                patch.object(runner.common, "image_bytes", return_value=b"\x60\x00"), \
                patch.object(runner.common, "anvil", side_effect=anvil):
            runner.execute(arguments, report)
        return original, submitted, scenarios

    def test_ledger_execution_sends_each_transaction_from_its_sender(self):
        accounts = [f"0x{sender:040x}" for sender in LEDGER_SENDERS] + ["0x" + "0a" * 20]
        with tempfile.TemporaryDirectory() as temporary:
            original, submitted, scenarios = self.run_ledger_execution(Path(temporary), accounts)
        self.assertEqual([request["from"] for request in submitted],
                         [accounts[0]] + [f"0x{int(tx['sender']):040x}" for tx in original["transactions"]])
        self.assertEqual(scenarios[0]["senders"], [str(sender) for sender in LEDGER_SENDERS])
        self.assertEqual(scenarios[0]["schema"], "solcore-lean.ledger-contract-scenario.v1")
        self.assertEqual(scenarios[0]["constructor"]["caller"], str(LEDGER_SENDERS[0]))
        self.assertEqual([call["context"]["caller"] for call in scenarios[0]["calls"]],
                         [tx["sender"] for tx in original["transactions"]])
        for missing in (accounts[1:], [accounts[0], accounts[1]], [accounts[1], accounts[0], accounts[2]]):
            with self.subTest(accounts=missing), tempfile.TemporaryDirectory() as temporary:
                with self.assertRaises(runner.Finding) as caught:
                    self.run_ledger_execution(Path(temporary), missing)
                self.assertEqual((caught.exception.category, caught.exception.stage), ("adapter-error", "evm-senders"))


def long_bytes_case(rows=((0, bytes(range(1, 98))), (1, b"\xff" * 256), (2, b""))):
    """Envelope fixture only: native replay checks the actual long-bytes program."""
    transactions = [{"id": f"tx-{index}", "flags": str(flags), "payload": "0x" + data.hex(), "value": "0",
        "calldata": bytes_calldata(flags, data)} for index, (flags, data) in enumerate(rows)]
    return {"schema": runner.LONG_BYTES_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "longBytesPlan": {"schema": "solcore-lean.long-bytes-plan.v1", "stepProgram": {}},
        "initialState": {"storage": []}, "observedSlots": [str(slot) for slot in range(11)],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedLongBytes", "method": "run", "signature": "run(uint256,bytes)",
            "selector": "0x220eb9b6", "deployPath": ["SynthesizedLongBytesDeploy"],
            "runtimePath": ["SynthesizedLongBytesDeploy", "SynthesizedLongBytes"], "constructorCalldata": "0x"},
        "transactions": transactions}


def long_bytes_slots(values=(0,) * 11):
    return [{"slot": str(index), "value": str(value)} for index, value in enumerate(values)]


def long_bytes_history(value, path):
    """Rows that follow the long-bytes protocol: slots zero to eight are
    fixtures, slot nine counts committed payload bytes, slot ten holds the last
    byte, and a returned payload is slots zero, nine and ten plus the calldata
    size. Odd flags revert and keep the prior snapshot."""
    rows, prior = [], [0] * 11
    for index, tx in enumerate(value["transactions"]):
        data = bytes.fromhex(tx["payload"][2:])
        reverted = int(tx["flags"]) % 2 == 1
        committed = list(prior) if reverted else [index + 10] + [index + 20 + slot for slot in range(8)] + [
            prior[9] + len(data), data[-1] if data else 0]
        output = index + 3 if reverted else committed[0] + committed[9] + committed[10] + 100 + len(data) + -len(data) % 32
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned",
               "output": "0x" + f"{output:064x}", "committedStorage": long_bytes_slots(committed)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
        prior = committed
    result = {"schema": runner.LONG_BYTES_HISTORY_SCHEMA, "observedSlots": [str(slot) for slot in range(11)],
        "initialStorage": long_bytes_slots(), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def long_bytes_histories(value=None):
    value = long_bytes_case() if value is None else value
    return {path: long_bytes_history(value, path) for path in runner.PATHS}


class LongBytesTests(unittest.TestCase):
    def test_long_bytes_case_admits_payloads_of_up_to_256_bytes(self):
        value = long_bytes_case()
        runner.validate_case(value)
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"],
                          selected["maxPayload"], selected["countSlot"], selected["tailSlot"], selected["shrinkBatch"]),
                         ("semantic-long-bytes-tool", "rust-hull-keyed-storage-scenario", True, "bytes", 256, "9", "10", 16))
        self.assertEqual(runner.bytes_layout(selected), (256, [str(slot) for slot in range(11)], "9", "10"))
        self.assertEqual(runner.bytes_layout(runner.profile(bytes_case())), (64, ["0", "1", "2", "3", "4"], "3", "4"))
        self.assertEqual(runner.observed_slots(value), tuple(str(slot) for slot in range(11)))
        self.assertTrue(runner.has_bytes(value))
        # `cast calldata "run(uint256,bytes)" 0 0x0102...ff00`, the 256-byte wrapping ramp, is 356 bytes long.
        ramp = bytes((index + 1) % 256 for index in range(256))
        self.assertEqual(bytes_calldata(0, ramp), "0x220eb9b6" + "".join(f"{word:064x}" for word in (0, 0x40, 0x100)) + ramp.hex())
        self.assertEqual(runner.bytes_calldata("0x220eb9b6", 0, ramp), bytes_calldata(0, ramp))
        self.assertEqual(len(runner.payload_chunks({"payload": "0x" + ramp.hex()})), 8)
        self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]], ["returned", "reverted", "returned"])
        runner.validate_case(long_bytes_case(rows=((0, ramp),)))
        original = value["transactions"][1]["calldata"]
        for key, changed in (("payload", "0x" + "01" * 257), ("payload", "0x" + "FF" * 256), ("payload", "ff" * 256),
                             ("calldata", original[:-2]), ("calldata", original[:-2] + "01"),
                             ("calldata", bytes_calldata(1, b"\xff" * 255)), ("value", "1")):
            invalid = copy.deepcopy(value)
            invalid["transactions"][1][key] = changed
            with self.subTest(key=key), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        for slots in (["0", "1", "2", "3", "4"], [str(slot) for slot in range(10)], [str(slot) for slot in range(12)]):
            with self.subTest(slots=slots), self.assertRaises(runner.Finding):
                runner.validate_case({**value, "observedSlots": slots})
        # The 64-byte profile keeps its own bound and slots.
        with self.assertRaises(ValueError):
            runner.validate_case(bytes_case(rows=((0, bytes(65)),)))
        with self.assertRaises(runner.Finding):
            runner.validate_case({**bytes_case(), "observedSlots": [str(slot) for slot in range(11)]})
        self.assertIn("0..256-byte payloads", runner.scope(value))
        self.assertIn("slots 0..10", runner.scope(value))
        self.assertIn("0..64-byte payloads", runner.scope(bytes_case()))

    def test_long_bytes_rows_record_length_last_byte_and_sum_in_slots_nine_and_ten(self):
        value = long_bytes_case()
        self.assertEqual(runner.compare(long_bytes_histories(value), value)["category"], "matched")
        for name, slot, text in (("count", 9, "98"), ("last byte", 10, "96")):
            agreed = long_bytes_histories(value)
            for history in agreed.values():
                history["transactions"][0]["committedStorage"][slot]["value"] = text
            result = runner.compare(agreed, value)
            with self.subTest(change=name):
                self.assertTrue(all(result["pairs"].values()))
                self.assertEqual((result["category"], result["transactionId"], result["fields"]),
                                 ("semantic-mismatch", "tx-0", ["committedStorage", "output"]))
        observed = long_bytes_histories(value)
        observed["importedHull"]["transactions"][2]["committedStorage"][8]["value"] = "5"
        observed["importedHull"]["finalStorage"] = copy.deepcopy(observed["importedHull"]["transactions"][2]["committedStorage"])
        result = runner.compare(observed, value)
        self.assertEqual((result["category"], result["transactionId"], result["fields"]), ("semantic-mismatch", "tx-2", ["committedStorage"]))
        history = runner.normalize_history(long_bytes_history(value, "rustEvm"), value, "rustEvm")
        self.assertEqual(runner.bytes_fields(value["transactions"][0], history["transactions"][0], history["initialStorage"], "9", "10"), [])
        self.assertTrue(runner.conforms(value, value["transactions"][0], history["transactions"][0], history["initialStorage"]))
        bytes_schema = long_bytes_histories(value)
        bytes_schema["directCore"]["schema"] = runner.BYTES_HISTORY_SCHEMA
        self.assertEqual(runner.compare(bytes_schema, value)["category"], "adapter-error")

    def test_long_bytes_hull_history_uses_the_declared_slot_runner_rows(self):
        value = long_bytes_case()
        deployment = {"stage": "deployment", "status": "returned", "committedStorage": long_bytes_slots(), "accountStorage": whole(), "undeclaredStorage": []}
        calls = [{"stage": "execution", **row} for row in long_bytes_history(value, "importedHull")["transactions"]]
        history = runner.hull_history("\n".join(json.dumps(row) for row in [deployment, *calls]), 0, value)
        self.assertEqual((history["schema"], history["observedSlots"]), (runner.LONG_BYTES_HISTORY_SCHEMA, [str(slot) for slot in range(11)]))
        self.assertEqual(runner.compare({**long_bytes_histories(value), "importedHull": history}, value)["category"], "matched")


def nested_calldata(flags, values):
    """Written from the ABI rules, independently of the adapter's encoder: the
    flags, the head offset, the outer length, each row's offset from the start
    of the offset table, then each row's length and elements."""
    offsets = [32 * len(values) + sum(32 + 32 * len(row) for row in values[:index]) for index in range(len(values))]
    tails = [word for row in values for word in (len(row), *row)]
    return "0x7095aff8" + "".join(f"{word:064x}" for word in (flags, 64, len(values), *offsets, *tails))


def nested_case(rows=((0, [[1, 3], [], [7]]), (1, [[MAX_WORD, 2**255], [0]]), (2, []))):
    """Envelope fixture only: native replay checks the actual nested-array program."""
    transactions = [{"id": f"tx-{index}", "flags": str(flags), "values": [[str(value) for value in row] for row in values],
        "value": "0", "calldata": nested_calldata(flags, values)} for index, (flags, values) in enumerate(rows)]
    return {"schema": runner.NESTED_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "nestedArrayPlan": {"schema": "solcore-lean.nested-array-plan.v1", "stepProgram": {}},
        "initialState": {"storage": []}, "observedSlots": [str(slot) for slot in range(9)],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedNestedArray", "method": "run", "signature": "run(uint256,uint256[][])",
            "selector": "0x7095aff8", "deployPath": ["SynthesizedNestedArrayDeploy"],
            "runtimePath": ["SynthesizedNestedArrayDeploy", "SynthesizedNestedArray"], "constructorCalldata": "0x"},
        "transactions": transactions}


def nested_slots(values=(0,) * 9):
    return [{"slot": str(index), "value": str(value)} for index, value in enumerate(values)]


def nested_history(value, path):
    """Rows that follow the nested-array protocol: slots zero to six are
    fixtures, slot seven counts committed rows and slot eight committed
    elements, and a returned value is slots zero, seven and eight. Odd flags
    revert and keep the prior snapshot."""
    rows, prior = [], [0] * 9
    for index, tx in enumerate(value["transactions"]):
        reverted = int(tx["flags"]) % 2 == 1
        committed = list(prior) if reverted else [index + 10] + [index + 20 + slot for slot in range(6)] + [
            prior[7] + len(tx["values"]), prior[8] + sum(len(row) for row in tx["values"])]
        output = index + 3 if reverted else committed[0] + committed[7] + committed[8]
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned",
               "output": "0x" + f"{output:064x}", "committedStorage": nested_slots(committed)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
        prior = committed
    result = {"schema": runner.NESTED_HISTORY_SCHEMA, "observedSlots": [str(slot) for slot in range(9)],
        "initialStorage": nested_slots(), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def nested_histories(value=None):
    value = nested_case() if value is None else value
    return {path: nested_history(value, path) for path in runner.PATHS}


class NestedArrayTests(unittest.TestCase):
    def test_nested_case_admits_three_rows_of_two_canonical_elements(self):
        value = nested_case()
        runner.validate_case(value)
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"], selected["shrinkBatch"]),
                         ("semantic-nested-array-tool", "rust-hull-keyed-storage-scenario", True, "nested", 16))
        self.assertEqual(runner.observed_slots(value), tuple(str(slot) for slot in range(9)))
        self.assertTrue(runner.has_nested(value))
        self.assertFalse(runner.has_bytes(value))
        # `cast calldata "run(uint256,uint256[][])" 1 VALUE` from the pinned Foundry release.
        for values, words in (([[5], [7, 8]], (1, 0x40, 2, 0x40, 0x80, 1, 5, 2, 7, 8)), ([], (1, 0x40, 0)),
                              ([[1, 2], [3, 4], [5, 6]], (1, 0x40, 3, 0x60, 0xc0, 0x120, 2, 1, 2, 2, 3, 4, 2, 5, 6))):
            expected = "0x7095aff8" + "".join(f"{word:064x}" for word in words)
            self.assertEqual((nested_calldata(1, values), runner.nested_calldata("0x7095aff8", 1, values)), (expected, expected))
        self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]], ["returned", "reverted", "returned"])
        runner.validate_case(nested_case(rows=((0, [[1, 2], [3, 4], [5, 6]]),)))
        original = value["transactions"][0]["calldata"]
        for key, changed in (("values", [["1", "3"], [], ["07"]]), ("values", [["1", "3"], [], ["7"], []]),
                             ("values", [["1", "3", "0"], [], ["7"]]), ("values", ["1", "3", "7"]), ("values", [[1, 3], [], [7]]),
                             ("values", [["1", "3"], [], [str(2**256)]]), ("values", [["1", "3"], ["7"]]),
                             ("calldata", original[:-64]), ("calldata", original.replace(f"{0x60:064x}", f"{0x80:064x}", 1)),
                             ("calldata", nested_calldata(0, [[1, 3], [7]])), ("value", "1")):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        for slots in (["0", "1", "2", "3", "4"], [str(slot) for slot in range(8)], [str(slot) for slot in range(10)]):
            with self.subTest(slots=slots), self.assertRaises(runner.Finding):
                runner.validate_case({**value, "observedSlots": slots})
        self.assertIn("run(uint256,uint256[][])", runner.scope(value))
        self.assertIn("slots 0..8", runner.scope(value))
        self.assertIn("slots 0..4", runner.scope(array_case()))

    def test_nested_rows_record_row_and_element_counts_and_sum_in_slots_seven_and_eight(self):
        value = nested_case()
        self.assertEqual(runner.compare(nested_histories(value), value)["category"], "matched")
        for name, slot, text in (("row count", 7, "4"), ("element count", 8, "2")):
            agreed = nested_histories(value)
            for history in agreed.values():
                history["transactions"][0]["committedStorage"][slot]["value"] = text
            result = runner.compare(agreed, value)
            with self.subTest(change=name):
                self.assertTrue(all(result["pairs"].values()))
                self.assertEqual((result["category"], result["transactionId"], result["fields"]),
                                 ("semantic-mismatch", "tx-0", ["committedStorage", "output"]))
        observed = nested_histories(value)
        observed["importedHull"]["transactions"][2]["committedStorage"][6]["value"] = "5"
        observed["importedHull"]["finalStorage"] = copy.deepcopy(observed["importedHull"]["transactions"][2]["committedStorage"])
        result = runner.compare(observed, value)
        self.assertEqual((result["category"], result["transactionId"], result["fields"]), ("semantic-mismatch", "tx-2", ["committedStorage"]))
        history = runner.normalize_history(nested_history(value, "rustEvm"), value, "rustEvm")
        self.assertEqual(runner.nested_fields(value["transactions"][0], history["transactions"][0], history["initialStorage"]), [])
        self.assertTrue(runner.conforms(value, value["transactions"][0], history["transactions"][0], history["initialStorage"]))
        broken = copy.deepcopy(history["transactions"][0])
        broken["output"] = "0x" + f"{1:064x}"
        self.assertEqual(runner.nested_fields(value["transactions"][0], broken, history["initialStorage"]), ["output"])
        self.assertFalse(runner.conforms(value, value["transactions"][0], broken, history["initialStorage"]))
        array_schema = nested_histories(value)
        array_schema["directCore"]["schema"] = runner.ARRAY_HISTORY_SCHEMA
        self.assertEqual(runner.compare(array_schema, value)["category"], "adapter-error")

    def test_nested_hull_history_uses_the_declared_slot_runner_rows(self):
        value = nested_case()
        deployment = {"stage": "deployment", "status": "returned", "committedStorage": nested_slots(), "accountStorage": whole(), "undeclaredStorage": []}
        calls = [{"stage": "execution", **row} for row in nested_history(value, "importedHull")["transactions"]]
        history = runner.hull_history("\n".join(json.dumps(row) for row in [deployment, *calls]), 0, value)
        self.assertEqual((history["schema"], history["observedSlots"]), (runner.NESTED_HISTORY_SCHEMA, [str(slot) for slot in range(9)]))
        self.assertEqual(runner.compare({**nested_histories(value), "importedHull": history}, value)["category"], "matched")


def stray(history, index, slot="12345", value="9"):
    """Add one nonzero entry to a fixture row's whole storage, as a stray write would."""
    entries = history["transactions"][index]["accountStorage"][0]["storage"]
    entries.append({"slot": slot, "value": value})
    entries.sort(key=lambda entry: int(entry["slot"]))
    if index == len(history["transactions"]) - 1 and history.get("finalAccountStorage") is not None:
        history["finalAccountStorage"] = copy.deepcopy(history["transactions"][index]["accountStorage"])


class WholeStorageTests(unittest.TestCase):
    """The whole committed storage is compared on all three paths after deployment
    and every transaction; zero and absent are the same observation."""

    def test_agreeing_whole_storage_matches_and_names_one_bound_contract(self):
        self.assertEqual(runner.compare(histories(), case())["category"], "matched")
        moved = histories()
        moved["rustEvm"] = with_whole(moved["rustEvm"], "4097")
        self.assertEqual(runner.compare(moved, case())["category"], "adapter-error")
        bound = histories()
        bound["directCore"]["bindings"] = {"schema": "solcore-lean.storage-bindings.v1", "caller": "17", "address": "4097"}
        self.assertEqual(runner.compare(bound, case())["category"], "adapter-error")
        bound["directCore"]["bindings"]["address"] = ADDRESS
        self.assertEqual(runner.compare(bound, case())["category"], "matched")

    def test_stray_write_outside_the_declaration_is_a_difference_on_its_own_path(self):
        for path in runner.PATHS:
            observed = histories()
            stray(observed[path], 1)
            result = runner.compare(observed, case())
            others = [other for other in runner.PATHS if other != path]
            with self.subTest(path=path):
                self.assertEqual((result["category"], result["stage"], result["transactionId"]), ("semantic-mismatch", "transaction", "tx-1"))
                self.assertEqual(result["fields"], ["accountStorage"])
                self.assertEqual(result["accountStorageDifferences"], [{"account": "contract", "slot": "undeclared", "zeroPaths": others}])
                self.assertEqual(sorted(pair for pair, same in result["pairs"].items() if not same),
                                 sorted(pair for pair in result["pairs"] if path in pair.split("/")))
                self.assertNotIn("accountStorageRollbackPaths", result)

    def test_declared_and_missing_writes_keep_their_slot_and_absent_paths(self):
        observed = histories()
        observed["importedHull"]["transactions"][0]["accountStorage"][0]["storage"][1]["value"] = "5"
        result = runner.compare(observed, case())
        self.assertEqual((result["transactionId"], result["accountStorageDifferences"]),
                         ("tx-0", [{"account": "contract", "slot": "1", "zeroPaths": []}]))
        missing = histories()
        for path in ("importedHull", "rustEvm"):
            del missing[path]["transactions"][0]["accountStorage"][0]["storage"][0]
        result = runner.compare(missing, case())
        self.assertEqual(result["accountStorageDifferences"], [{"account": "contract", "slot": "0", "zeroPaths": ["importedHull", "rustEvm"]}])
        # Both kinds in one row: declared slots first, then the undeclared class.
        stray(missing["directCore"], 0)
        self.assertEqual(runner.compare(missing, case())["accountStorageDifferences"],
                         [{"account": "contract", "slot": "0", "zeroPaths": ["importedHull", "rustEvm"]},
                          {"account": "contract", "slot": "undeclared", "zeroPaths": ["importedHull", "rustEvm"]}])

    def test_entries_are_canonical_nonzero_and_strictly_ordered(self):
        for name, entries in (("zero", [{"slot": "0", "value": "0"}]), ("duplicate", [{"slot": "2", "value": "1"}] * 2),
                              ("unordered", [{"slot": "3", "value": "1"}, {"slot": "2", "value": "1"}]),
                              ("noncanonical", [{"slot": "02", "value": "1"}]), ("wide", [{"slot": str(2**256), "value": "1"}]),
                              ("extra", [{"slot": "2", "value": "1", "path": "x"}])):
            observed = histories()
            observed["rustEvm"]["transactions"][0]["accountStorage"][0]["storage"] = entries
            with self.subTest(name=name):
                self.assertEqual(runner.compare(observed, case())["category"], "adapter-error")
        for name, change in (("missing", lambda h: h["transactions"][0].pop("accountStorage")),
                             ("role", lambda h: h["transactions"][0]["accountStorage"][0].update(role="parent")),
                             ("accounts", lambda h: h["transactions"][0]["accountStorage"].append(copy.deepcopy(h["transactions"][0]["accountStorage"][0]))),
                             ("initial", lambda h: h.pop("initialAccountStorage")),
                             ("final", lambda h: h.update(finalAccountStorage=[])),
                             ("address", lambda h: h["transactions"][0]["accountStorage"][0].update(address=str(2**160)))):
            observed = histories()
            change(observed["importedHull"])
            with self.subTest(name=name):
                self.assertEqual(runner.compare(observed, case())["category"], "adapter-error")
        stopped = history(rows=[row(0)])
        stopped.update(unobserved=["tx-1"], unexecuted=["tx-2"], finalStorage=None, finalAccountStorage=row(0)["accountStorage"])
        with self.assertRaisesRegex(ValueError, "final whole storage"):
            runner.normalize_history(stopped, case())

    def test_a_revert_keeps_the_whole_storage_even_if_all_paths_agree(self):
        value = case()
        value["schema"] = runner.ROLLBACK_CASE_SCHEMA
        value["storagePlan"]["schema"] = "solcore-lean.storage-rollback-plan.v1"
        value["contract"].update(name="SynthesizedRollback", deployPath=["SynthesizedRollbackDeploy"],
                                 runtimePath=["SynthesizedRollbackDeploy", "SynthesizedRollback"])
        observed = histories(value)
        for history_value in observed.values():
            history_value["transactions"][1]["status"] = "reverted"
        self.assertEqual(runner.compare(observed, value)["category"], "matched")
        for history_value in observed.values():
            stray(history_value, 1)
        result = runner.compare(observed, value)
        self.assertEqual((result["category"], result["transactionId"], result["fields"]), ("semantic-mismatch", "tx-1", ["accountStorage"]))
        self.assertEqual(result["accountStorageRollbackPaths"], list(runner.PATHS))
        self.assertTrue(all(result["pairs"].values()))
        self.assertNotIn("accountStorageDifferences", result)

    def test_deployment_whole_storage_must_be_empty_on_every_path(self):
        observed = histories()
        observed["rustEvm"]["initialAccountStorage"][0]["storage"] = [{"slot": "7", "value": "1"}]
        result = runner.compare(observed, case())
        self.assertEqual((result["category"], result["stage"], result["fields"]), ("semantic-mismatch", "initial-storage", ["accountStorage"]))
        self.assertEqual(result["accountStorageDifferences"], [{"account": "contract", "slot": "undeclared", "zeroPaths": ["directCore", "importedHull"]}])
        agreed = histories()
        for history_value in agreed.values():
            history_value["initialAccountStorage"][0]["storage"] = [{"slot": "1", "value": "2"}]
        result = runner.compare(agreed, case())
        self.assertEqual((result["stage"], result["accountStorageDifferences"]),
                         ("initial-storage", [{"account": "contract", "slot": "1", "zeroPaths": []}]))
        self.assertTrue(all(result["pairs"].values()))

    def test_containment_and_whole_storage_report_one_stray_write_together(self):
        value = keyed_case()
        observed = keyed_histories(value)
        observed["importedHull"]["transactions"][1]["undeclaredStorage"] = [{"slot": "9", "value": "1"}]
        observed["importedHull"] = with_whole(observed["importedHull"])
        result = runner.compare(observed, value)
        self.assertEqual((result["category"], result["transactionId"], result["fields"], result["undeclaredPaths"]),
                         ("semantic-mismatch", "tx-1", ["undeclaredStorage", "accountStorage"], ["importedHull"]))
        self.assertEqual(result["accountStorageDifferences"], [{"account": "contract", "slot": "undeclared", "zeroPaths": ["directCore", "rustEvm"]}])
        # A declared slot of this case is classified by number, not as undeclared.
        observed = keyed_histories(value)
        stray(observed["rustEvm"], 1, slot="6")
        result = runner.compare(observed, value)
        self.assertEqual(result["accountStorageDifferences"], [{"account": "contract", "slot": "6", "zeroPaths": ["directCore", "importedHull"]}])

    def test_prestate_diffs_name_every_observed_account_and_fail_closed_elsewhere(self):
        parent, child, other = "0x" + "ab" * 20, "0x" + "cd" * 20, "0x" + "ef" * 20
        diff = {"pre": {parent: {"storage": {"0x09": "0x" + "00" * 31 + "05"}}, other: {"balance": "0x1"}},
                "post": {child.upper().replace("0X", "0x"): {"storage": {"0x01": "0x02"}}, other: {"balance": "0x0"}}}
        self.assertEqual(runner.changed_storage(diff, [parent, child]), {parent: {"9"}, child: {"1"}})
        self.assertEqual(runner.changed_storage({"pre": {}, "post": {}}, [parent]), {parent: set()})
        with self.assertRaisesRegex(ValueError, "outside the deployed contract"):
            runner.changed_storage(diff, [parent])

    def test_evm_whole_storage_rereads_every_reported_slot_and_drops_zero(self):
        address = "0x" + "ab" * 20
        calls = []
        values = {"0": 3, "9": 0, "12": 2**256 - 1}
        class Rpc:
            def call(self, method, params):
                calls.append((method, params))
                return "0x" + f"{values[str(int(params[1], 16))]:064x}"
        accounts = [("contract", str(int(address, 16)))]
        expected = [{"role": "contract", "address": accounts[0][1],
                     "storage": [{"slot": "0", "value": "3"}, {"slot": "12", "value": str(2**256 - 1)}]}]
        self.assertEqual(runner.evm_account_storage(Rpc(), accounts, {address: {"12", "0", "9"}}, "0x4"), expected)
        self.assertEqual([(method, params[1:]) for method, params in calls],
                         [("eth_getStorageAt", [hex(0), "0x4"]), ("eth_getStorageAt", [hex(9), "0x4"]),
                          ("eth_getStorageAt", [hex(12), "0x4"])])
        # An account no diff has reported holds no storage, and needs no read.
        self.assertEqual(runner.evm_account_storage(Rpc(), accounts, {}, "0x4")[0]["storage"], [])
        self.assertEqual(len(calls), 3)


MALFORMED_SELECTOR = "0x9a94c44b"


def malformed_tx(index, flags, values, malformation):
    tx = {"id": f"tx-{index}", "flags": str(flags), "values": [str(value) for value in values], "malformation": malformation,
          "value": "0"}
    data = runner.malformed_calldata(MALFORMED_SELECTOR, tx)
    return {**tx, "calldata": "0x" + data.hex(), "stdRejection": runner.std_rejection(data, MALFORMED_SELECTOR)}


def malformed_case(rows=((0, (1, 3, 7), {"kind": "none"}), (2, (5,), {"kind": "selector", "mask": "1"}),
                         (1, (3, 7), {"kind": "trailing", "count": 2, "pattern": "ones"}))):
    """Envelope fixture only: native replay checks the actual std-modeling program."""
    return {"schema": runner.MALFORMED_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "malformedCalldataPlan": {"schema": "solcore-lean.malformed-calldata-plan.v1", "stepProgram": {}},
        "initialState": {"storage": []}, "observedSlots": list(runner.ARRAY_SLOTS),
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedDynamicArray", "method": "run", "signature": "run(uint256,uint256[])",
            "selector": MALFORMED_SELECTOR, "deployPath": ["SynthesizedDynamicArrayDeploy"],
            "runtimePath": ["SynthesizedDynamicArrayDeploy", "SynthesizedDynamicArray"], "constructorCalldata": "0x"},
        "transactions": [malformed_tx(index, *row) for index, row in enumerate(rows)]}


def selector_word(selector):
    return "0x" + int(selector, 16).to_bytes(32, "big").hex()


def malformed_history(value, path):
    """Counter rows: a std rejection reverts with its selector, as a Word on
    original Core and as four bytes on Hull and EVM; odd flags revert."""
    rows, counter = [], 0
    for index, tx in enumerate(value["transactions"]):
        rejection = tx["stdRejection"]
        reverted = rejection is not None or int(tx["flags"]) % 2 == 1
        counter += 0 if reverted else 1
        output = "0x" + f"{index + 3:064x}" if rejection is None else selector_word(rejection) if path == "directCore" else rejection
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned", "output": output,
               "committedStorage": keyed_slots(value, counter)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
    result = {"schema": runner.MALFORMED_HISTORY_SCHEMA, "observedSlots": value["observedSlots"],
        "initialStorage": keyed_slots(value), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def malformed_histories(value=None):
    value = malformed_case() if value is None else value
    return {path: malformed_history(value, path) for path in runner.PATHS}


class MalformedCalldataTests(unittest.TestCase):
    def test_a_case_records_its_malformation_calldata_and_std_outcome(self):
        value = malformed_case()
        runner.validate_case(value)
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"]),
                         ("semantic-malformed-calldata-tool", "rust-hull-keyed-storage-scenario", True, "malformed"))
        self.assertEqual([tx["stdRejection"] for tx in value["transactions"]], [None, runner.STD_NO_SELECTOR, None])
        self.assertTrue(value["transactions"][2]["calldata"].endswith("ffff"))
        self.assertIn("compared by its error selector", runner.scope(value))
        for key, changed in (("calldata", array_calldata(0, (1, 3, 7)) + "00"), ("stdRejection", runner.STD_TRUNCATED),
                             ("stdRejection", None), ("value", "1"), ("values", ["1", "2", "3", "4"]),
                             ("malformation", {"kind": "short", "bytes": 4}), ("malformation", {"kind": "selector", "mask": "0"}),
                             ("malformation", {"kind": "truncate", "kept": 196}), ("malformation", {"kind": "trailing", "count": 65, "pattern": "ones"}),
                             ("malformation", {"kind": "trailing", "count": 1, "pattern": "twos"}), ("malformation", {"kind": "none", "bytes": 1}),
                             ("malformation", {"kind": "reorder"})):
            invalid = copy.deepcopy(value)
            invalid["transactions"][1][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)

    def test_the_byte_model_follows_std_dispatch_and_decoding(self):
        """The golden decisions of the Lean model, from the pinned dispatch.sol and std.sol."""
        canonical = (2, (5, 7))
        size = 164
        cases = [({"kind": "none"}, None), ({"kind": "short", "bytes": 0}, runner.STD_NO_SELECTOR),
                 ({"kind": "short", "bytes": 3}, runner.STD_NO_SELECTOR), ({"kind": "selector", "mask": str(2**31)}, runner.STD_NO_SELECTOR),
                 ({"kind": "truncate", "kept": 4}, runner.STD_TRUNCATED), ({"kind": "truncate", "kept": 67}, runner.STD_TRUNCATED),
                 ({"kind": "truncate", "kept": 99}, runner.STD_TRUNCATED), ({"kind": "truncate", "kept": size - 1}, runner.STD_TRUNCATED),
                 ({"kind": "trailing", "count": 64, "pattern": "ramp"}, None),
                 ({"kind": "offset", "value": str(size - 3)}, runner.STD_TRUNCATED), ({"kind": "offset", "value": str(size - 35)}, runner.STD_TRUNCATED),
                 ({"kind": "offset", "value": str(2**255)}, runner.STD_TRUNCATED), ({"kind": "offset", "value": str(2**256 - 4)}, runner.STD_TRUNCATED),
                 ({"kind": "offset", "value": "0"}, None), ({"kind": "offset", "value": "32"}, runner.STD_TRUNCATED),
                 ({"kind": "length", "value": "3"}, runner.STD_TRUNCATED), ({"kind": "length", "value": str(2**251)}, runner.STD_TRUNCATED),
                 ({"kind": "length", "value": str(2**251 + 1)}, runner.STD_TRUNCATED), ({"kind": "length", "value": "1"}, None),
                 ({"kind": "length", "value": "0"}, None)]
        for malformation, expected in cases:
            with self.subTest(malformation=malformation):
                self.assertEqual(malformed_tx(0, *canonical, malformation)["stdRejection"], expected)
        head = bytes.fromhex(MALFORMED_SELECTOR[2:])
        word = lambda value: value.to_bytes(32, "big")
        # Decode order: dispatch before the head check, the head check before the offset.
        self.assertEqual(runner.std_rejection((int.from_bytes(head, "big") ^ 1).to_bytes(4, "big") + word(2), MALFORMED_SELECTOR),
                         runner.STD_NO_SELECTOR)
        self.assertEqual(runner.std_rejection(head + word(2) + word(2**256 - 4)[:31], MALFORMED_SELECTOR), runner.STD_TRUNCATED)
        self.assertEqual(runner.std_rejection(head + word(2) + word(64) + word(0), MALFORMED_SELECTOR), None)

    def test_the_selector_rule_compares_a_std_rejection_by_its_selector_only(self):
        value = malformed_case()
        result = runner.compare(malformed_histories(value), value)
        self.assertEqual(result["category"], "matched")
        self.assertEqual(result["selectorRows"], [{"id": "tx-1", "index": 1, "selector": runner.STD_NO_SELECTOR}])
        # EVM and Hull must revert with exactly the four bytes.
        for path, output in (("rustEvm", selector_word(runner.STD_NO_SELECTOR)), ("rustEvm", runner.STD_TRUNCATED),
                             ("importedHull", selector_word(runner.STD_NO_SELECTOR))):
            observed = malformed_histories(value)
            observed[path]["transactions"][1]["output"] = output
            result = runner.compare(observed, value)
            with self.subTest(path=path, output=output):
                self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-1"))
                self.assertIn("output", result["fields"])
        # Hull against EVM stays exact even when both differ from original Core alike.
        observed = malformed_histories(value)
        for path in ("rustEvm", "importedHull"):
            observed[path]["transactions"][1]["output"] = runner.STD_TRUNCATED
        self.assertEqual(runner.compare(observed, value)["category"], "semantic-mismatch")
        # A prescribed rejection that original Core returns from is compared exactly.
        observed = malformed_histories(value)
        observed["directCore"]["transactions"][1]["output"] = "0x" + f"{4:064x}"
        result = runner.compare(observed, value)
        self.assertEqual((result["category"], result["selectorRows"]), ("semantic-mismatch", []))
        # A body revert whose Word equals a selector is accepted by std, so it is
        # compared exactly: four EVM bytes do not match original Core's Word.
        body = malformed_case(((1, (3,), {"kind": "none"}),))
        observed = malformed_histories(body)
        for path in runner.PATHS:
            observed[path]["transactions"][0]["output"] = selector_word(runner.STD_TRUNCATED)
        self.assertEqual(runner.compare(observed, body)["selectorRows"], [])
        self.assertEqual(runner.compare(observed, body)["category"], "matched")
        observed["rustEvm"]["transactions"][0]["output"] = runner.STD_TRUNCATED
        self.assertEqual(runner.compare(observed, body)["category"], "semantic-mismatch")
        # Other profiles report no selector rows.
        self.assertNotIn("selectorRows", runner.compare(array_histories(), array_case()))

    def test_a_std_rejection_conforms_only_with_its_exact_selector(self):
        value = malformed_case()
        tx = value["transactions"][1]
        prior = keyed_slots(value, 1)
        row = {"status": "reverted", "output": runner.STD_NO_SELECTOR, "committedStorage": prior}
        self.assertTrue(runner.conforms(value, tx, row, prior))
        self.assertFalse(runner.conforms(value, tx, {**row, "output": selector_word(runner.STD_NO_SELECTOR)}, prior))
        self.assertFalse(runner.conforms(value, tx, {**row, "status": "returned"}, prior))
        self.assertFalse(runner.conforms(value, tx, {**row, "committedStorage": keyed_slots(value, 2)}, prior))


MALFORMED_NESTED_SELECTOR = "0x7095aff8"
THREE_ROWS = [[1, 4], [9], []]
FOUR_ROWS = [[3], [], [7, 1, 0], [1]]


def malformed_nested_tx(index, flags, values, malformation):
    tx = {"id": f"tx-{index}", "flags": str(flags), "values": [[str(value) for value in row] for row in values],
          "malformation": malformation, "value": "0"}
    data = runner.malformed_nested_calldata(MALFORMED_NESTED_SELECTOR, tx)
    return {**tx, "calldata": "0x" + data.hex(), "stdRejection": runner.nested_std_decode(data, MALFORMED_NESTED_SELECTOR)[0]}


def malformed_nested_case(rows=((0, THREE_ROWS, {"kind": "none"}),
                                (0, FOUR_ROWS, {"kind": "row-length", "row": 3, "value": str(MAX_WORD)}),
                                (0, THREE_ROWS, {"kind": "row-offset", "row": 1, "value": str(2**256 - 32)}),
                                (0, THREE_ROWS, {"kind": "row-length", "row": 0, "value": "3"}),
                                (1, THREE_ROWS, {"kind": "offset", "value": "0"}))):
    """Envelope fixture only: native replay checks the actual std-modeling program."""
    return {"schema": runner.MALFORMED_NESTED_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "malformedNestedArrayPlan": {"schema": "solcore-lean.malformed-nested-array-plan.v1", "stepProgram": {}},
        "initialState": {"storage": []}, "observedSlots": [str(slot) for slot in range(9)],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedNestedArray", "method": "run", "signature": "run(uint256,uint256[][])",
            "selector": MALFORMED_NESTED_SELECTOR, "deployPath": ["SynthesizedNestedArrayDeploy"],
            "runtimePath": ["SynthesizedNestedArrayDeploy", "SynthesizedNestedArray"], "constructorCalldata": "0x"},
        "transactions": [malformed_nested_tx(index, *row) for index, row in enumerate(rows)]}


def malformed_nested_history(value, path):
    """Rows that follow the nested-array protocol on the Words std decodes:
    slot seven counts the decoded outer lengths and slot eight the read rows'
    lengths. A std rejection reverts with its selector, as a Word on original
    Core and as four bytes on Hull and EVM; odd flags revert."""
    rows, prior = [], [0] * 9
    for index, tx in enumerate(value["transactions"]):
        rejection, outer, widths = runner.nested_std_decode(bytes.fromhex(tx["calldata"][2:]), MALFORMED_NESTED_SELECTOR)
        reverted = rejection is not None or int(tx["flags"]) % 2 == 1
        committed = list(prior) if reverted else [index + 10] + [index + 20 + slot for slot in range(6)] + [
            prior[7] + outer, prior[8] + sum(widths)]
        output = "0x" + f"{(committed[0] + committed[7] + committed[8]) if not reverted else index + 3:064x}"
        if rejection is not None:
            output = selector_word(rejection) if path == "directCore" else rejection
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned", "output": output,
               "committedStorage": nested_slots(committed)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
        prior = committed
    result = {"schema": runner.MALFORMED_NESTED_HISTORY_SCHEMA, "observedSlots": value["observedSlots"],
        "initialStorage": nested_slots(), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def malformed_nested_histories(value=None):
    value = malformed_nested_case() if value is None else value
    return {path: malformed_nested_history(value, path) for path in runner.PATHS}


class MalformedNestedArrayTests(unittest.TestCase):
    def test_a_nested_case_records_its_malformation_calldata_and_std_outcome(self):
        value = malformed_nested_case()
        runner.validate_case(value)
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"],
                          runner.encoding(selected), selected["shrinkBatch"]),
                         ("semantic-malformed-nested-array-tool", "rust-hull-keyed-storage-scenario", True, "malformed", "nested", 16))
        self.assertTrue(runner.has_malformed_nested(value) and runner.is_malformed(value))
        self.assertFalse(runner.has_nested(value) or runner.has_malformed_nested(malformed_case()))
        self.assertEqual(runner.observed_slots(value), tuple(str(slot) for slot in range(9)))
        self.assertEqual([tx["stdRejection"] for tx in value["transactions"]], [None, None, runner.STD_TRUNCATED, None, None])
        self.assertEqual(value["transactions"][0]["calldata"], nested_calldata(0, THREE_ROWS))
        self.assertIn("compared by its error selector", runner.scope(value))
        self.assertIn("uint256[][]", runner.scope(value))
        for key, changed in (("calldata", nested_calldata(0, FOUR_ROWS)), ("stdRejection", None), ("stdRejection", runner.STD_NO_SELECTOR),
                             ("value", "1"), ("values", [[str(value) for value in row] for row in FOUR_ROWS + [[]]]),
                             ("values", [["1", "2", "3", "4"]]),
                             ("malformation", {"kind": "row-offset", "row": 4, "value": "0"}),
                             ("malformation", {"kind": "row-length", "row": 0}),
                             ("malformation", {"kind": "row-length", "row": "0", "value": "1"}),
                             ("malformation", {"kind": "truncate", "kept": 388}), ("malformation", {"kind": "reorder"})):
            invalid = copy.deepcopy(value)
            invalid["transactions"][2][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        # The dynamic-array profile has no row malformations.
        array = malformed_case()
        array["transactions"][0]["malformation"] = {"kind": "row-offset", "row": 0, "value": "0"}
        with self.assertRaises(ValueError):
            runner.validate_case(array)

    def test_the_nested_byte_model_follows_std_lazy_decoding(self):
        """The golden decisions of the Lean model, from the pinned dispatch.sol and std.sol."""
        decode = lambda values, malformation: runner.nested_std_decode(
            bytes.fromhex(malformed_nested_tx(0, 2, values, malformation)["calldata"][2:]), MALFORMED_NESTED_SELECTOR)
        cases = [(THREE_ROWS, {"kind": "none"}, (None, 3, [2, 1, 0])),
                 (THREE_ROWS, {"kind": "short", "bytes": 3}, (runner.STD_NO_SELECTOR, 0, [])),
                 (THREE_ROWS, {"kind": "selector", "mask": "1"}, (runner.STD_NO_SELECTOR, 0, [])),
                 (THREE_ROWS, {"kind": "truncate", "kept": 99}, (runner.STD_TRUNCATED, 0, [])),
                 (THREE_ROWS, {"kind": "truncate", "kept": 116}, (runner.STD_TRUNCATED, 0, [])),
                 (THREE_ROWS, {"kind": "truncate", "kept": 291}, (runner.STD_TRUNCATED, 0, [])),
                 (THREE_ROWS, {"kind": "trailing", "count": 33, "pattern": "ones"}, (None, 3, [2, 1, 0])),
                 (THREE_ROWS, {"kind": "offset", "value": "0"}, (None, 2, [0, 0])),
                 (THREE_ROWS, {"kind": "offset", "value": "32"}, (runner.STD_TRUNCATED, 0, [])),
                 (THREE_ROWS, {"kind": "length", "value": "4"}, (None, 4, [2, 1, 0])),
                 (THREE_ROWS, {"kind": "length", "value": str(2**251 + 1)}, (runner.STD_TRUNCATED, 0, [])),
                 ([[1, 4], [9]], {"kind": "length", "value": "3"}, (runner.STD_TRUNCATED, 0, [])),
                 (THREE_ROWS, {"kind": "row-offset", "row": 1, "value": "289"}, (runner.STD_TRUNCATED, 0, [])),
                 (THREE_ROWS, {"kind": "row-offset", "row": 1, "value": "288"}, (runner.STD_TRUNCATED, 0, [])),
                 (THREE_ROWS, {"kind": "row-offset", "row": 1, "value": str(2**256 - 32)}, (runner.STD_TRUNCATED, 0, [])),
                 (THREE_ROWS, {"kind": "row-offset", "row": 0, "value": "0"}, (None, 3, [0, 1, 0])),
                 (THREE_ROWS, {"kind": "row-offset", "row": 1, "value": "0"}, (runner.STD_TRUNCATED, 0, [])),
                 (THREE_ROWS, {"kind": "row-offset", "row": 1, "value": "128"}, (None, 3, [2, 1, 0])),
                 (THREE_ROWS, {"kind": "row-length", "row": 0, "value": "5"}, (None, 3, [5, 1, 0])),
                 (THREE_ROWS, {"kind": "row-length", "row": 0, "value": "6"}, (runner.STD_TRUNCATED, 0, [])),
                 (THREE_ROWS, {"kind": "row-length", "row": 1, "value": str(2**251 + 1)}, (runner.STD_TRUNCATED, 0, [])),
                 (FOUR_ROWS, {"kind": "row-offset", "row": 3, "value": str(MAX_WORD)}, (None, 4, [1, 0, 3])),
                 (FOUR_ROWS, {"kind": "truncate", "kept": 515}, (None, 4, [1, 0, 3])),
                 (FOUR_ROWS, {"kind": "truncate", "kept": 212}, (runner.STD_TRUNCATED, 0, [])),
                 (FOUR_ROWS, {"kind": "truncate", "kept": 451}, (runner.STD_TRUNCATED, 0, []))]
        for values, malformation, expected in cases:
            with self.subTest(values=values, malformation=malformation):
                self.assertEqual(decode(values, malformation), expected)
        # Decode order: an outer length of two leaves a malformed row two unread.
        canonical = bytearray.fromhex(nested_calldata(2, THREE_ROWS)[2:])
        canonical[68:100] = (2).to_bytes(32, "big")
        canonical[356:388] = MAX_WORD.to_bytes(32, "big")
        self.assertEqual(runner.nested_std_decode(bytes(canonical), MALFORMED_NESTED_SELECTOR), (None, 2, [2, 1]))
        canonical[0:4] = bytes.fromhex("9a94c44b")
        self.assertEqual(runner.nested_std_decode(bytes(canonical), MALFORMED_NESTED_SELECTOR)[0], runner.STD_NO_SELECTOR)

    def test_the_selector_rule_applies_to_nested_rejections(self):
        value = malformed_nested_case()
        result = runner.compare(malformed_nested_histories(value), value)
        self.assertEqual(result["category"], "matched")
        self.assertEqual(result["selectorRows"], [{"id": "tx-2", "index": 2, "selector": runner.STD_TRUNCATED}])
        for path, output in (("rustEvm", selector_word(runner.STD_TRUNCATED)), ("importedHull", runner.STD_NO_SELECTOR)):
            observed = malformed_nested_histories(value)
            observed[path]["transactions"][2]["output"] = output
            result = runner.compare(observed, value)
            with self.subTest(path=path, output=output):
                self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-2"))

    def test_a_returned_nested_row_follows_the_protocol_on_decoded_words(self):
        value = malformed_nested_case()
        histories = malformed_nested_histories(value)
        rows = histories["directCore"]["transactions"]
        # Row three's maximal length is never read: slot seven adds the outer length 4.
        self.assertEqual(int(rows[1]["committedStorage"][7]["value"]) - int(rows[0]["committedStorage"][7]["value"]), 4)
        for index, tx in enumerate(value["transactions"]):
            prior = rows[index - 1]["committedStorage"] if index else histories["directCore"]["initialStorage"]
            self.assertTrue(runner.conforms(value, tx, {**rows[index], "output": tx["stdRejection"] or rows[index]["output"]}, prior))
        # Counting the canonical row lengths instead of the decoded ones breaks the protocol on every path.
        changed = malformed_nested_histories(value)
        for path in runner.PATHS:
            row = changed[path]["transactions"][3]
            row["committedStorage"][8]["value"] = str(int(row["committedStorage"][8]["value"]) - 1)
            row["output"] = "0x" + f"{int(row['output'], 16) - 1:064x}"
        prior = changed["directCore"]["transactions"][2]["committedStorage"]
        self.assertFalse(runner.conforms(value, value["transactions"][3], changed["directCore"]["transactions"][3], prior))
        self.assertNotEqual(runner.compare(changed, value)["category"], "matched")


MALFORMED_BYTES_SELECTOR = "0x220eb9b6"
RAMP_65 = bytes(range(1, 66))


def malformed_bytes_tx(index, flags, data, malformation):
    tx = {"id": f"tx-{index}", "flags": str(flags), "payload": "0x" + data.hex(), "malformation": malformation, "value": "0"}
    calldata = runner.malformed_bytes_calldata(MALFORMED_BYTES_SELECTOR, tx)
    return {**tx, "calldata": "0x" + calldata.hex(), "stdRejection": runner.bytes_std_decode(calldata, MALFORMED_BYTES_SELECTOR)[0]}


def malformed_bytes_case(rows=((0, RAMP_65, {"kind": "none"}), (0, RAMP_65, {"kind": "truncate", "kept": 180}),
                               (0, RAMP_65, {"kind": "truncate", "kept": 164}), (0, RAMP_65, {"kind": "padding", "pattern": "ramp"}),
                               (1, RAMP_65, {"kind": "length", "value": "66"}))):
    """Envelope fixture only: native replay checks the actual std-modeling program."""
    return {"schema": runner.MALFORMED_BYTES_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "malformedBytesPlan": {"schema": "solcore-lean.malformed-bytes-plan.v1", "stepProgram": {}},
        "initialState": {"storage": []}, "observedSlots": [str(slot) for slot in range(11)],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedLongBytes", "method": "run", "signature": "run(uint256,bytes)",
            "selector": MALFORMED_BYTES_SELECTOR, "deployPath": ["SynthesizedLongBytesDeploy"],
            "runtimePath": ["SynthesizedLongBytesDeploy", "SynthesizedLongBytes"], "constructorCalldata": "0x"},
        "transactions": [malformed_bytes_tx(index, *row) for index, row in enumerate(rows)]}


def malformed_bytes_slots(values):
    return [{"slot": str(index), "value": str(value)} for index, value in enumerate(values)]


def malformed_bytes_history(value, path):
    """Rows that follow the long-bytes protocol on the payload std decodes:
    slot nine counts decoded bytes, slot ten holds the last one, and a returned
    value adds the actual calldata size. A std rejection reverts with its
    selector, as a Word on original Core and as four bytes on Hull and EVM; odd
    flags revert."""
    rows, prior = [], [0] * 11
    for index, tx in enumerate(value["transactions"]):
        data = bytes.fromhex(tx["calldata"][2:])
        rejection, decoded = runner.bytes_std_decode(data, MALFORMED_BYTES_SELECTOR)
        reverted = rejection is not None or int(tx["flags"]) % 2 == 1
        committed = list(prior) if reverted else [index + 10] + [index + 20 + slot for slot in range(8)] + [
            prior[9] + len(decoded), decoded[-1] if decoded else 0]
        output = "0x" + f"{(committed[0] + committed[9] + committed[10] + len(data)) if not reverted else index + 3:064x}"
        if rejection is not None:
            output = selector_word(rejection) if path == "directCore" else rejection
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned", "output": output,
               "committedStorage": malformed_bytes_slots(committed)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
        prior = committed
    result = {"schema": runner.MALFORMED_BYTES_HISTORY_SCHEMA, "observedSlots": value["observedSlots"],
        "initialStorage": malformed_bytes_slots([0] * 11), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def malformed_bytes_histories(value=None):
    value = malformed_bytes_case() if value is None else value
    return {path: malformed_bytes_history(value, path) for path in runner.PATHS}


class MalformedBytesTests(unittest.TestCase):
    def test_a_bytes_case_records_its_malformation_calldata_and_std_outcome(self):
        value = malformed_bytes_case()
        runner.validate_case(value)
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"],
                          runner.encoding(selected), selected["shrinkBatch"]),
                         ("semantic-malformed-bytes-tool", "rust-hull-keyed-storage-scenario", True, "malformed", "bytes", 16))
        self.assertTrue(runner.has_malformed_bytes(value) and runner.is_malformed(value))
        self.assertFalse(runner.has_bytes(value) or runner.has_malformed_nested(value))
        self.assertEqual(runner.observed_slots(value), tuple(str(slot) for slot in range(11)))
        self.assertEqual([tx["stdRejection"] for tx in value["transactions"]], [None, None, runner.STD_TRUNCATED, None, None])
        self.assertEqual(value["transactions"][3]["calldata"][-62:], bytes(range(1, 32)).hex())
        self.assertIn("compared by its error selector", runner.scope(value))
        self.assertIn("run(uint256,bytes)", runner.scope(value))
        for key, changed in (("calldata", value["transactions"][0]["calldata"]), ("stdRejection", None), ("value", "1"),
                             ("payload", "0x" + bytes(257).hex()), ("payload", "0x0"),
                             ("malformation", {"kind": "padding", "pattern": "twos"}),
                             ("malformation", {"kind": "padding", "pattern": "ones", "count": 1}),
                             ("malformation", {"kind": "row-offset", "row": 0, "value": "0"}),
                             ("malformation", {"kind": "truncate", "kept": 196})):
            invalid = copy.deepcopy(value)
            invalid["transactions"][2][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        # Padding needs padding bytes.
        with self.assertRaises(ValueError):
            malformed_bytes_tx(0, 0, bytes(64), {"kind": "padding", "pattern": "ones"})

    def test_the_bytes_byte_model_follows_std_decoding(self):
        """The golden decisions of the Lean model, from the pinned dispatch.sol and std.sol."""
        decode = lambda data, malformation: runner.bytes_std_decode(
            bytes.fromhex(malformed_bytes_tx(0, 2, data, malformation)["calldata"][2:]), MALFORMED_BYTES_SELECTOR)
        cases = [(RAMP_65, {"kind": "none"}, (None, RAMP_65)),
                 (RAMP_65, {"kind": "short", "bytes": 3}, (runner.STD_NO_SELECTOR, b"")),
                 (RAMP_65, {"kind": "truncate", "kept": 99}, (runner.STD_TRUNCATED, b"")),
                 (RAMP_65, {"kind": "truncate", "kept": 164}, (runner.STD_TRUNCATED, b"")),
                 (RAMP_65, {"kind": "truncate", "kept": 165}, (None, RAMP_65)),
                 (RAMP_65, {"kind": "offset", "value": "0"}, (None, bytes(2))),
                 (RAMP_65, {"kind": "offset", "value": "32"}, (None, bytes(31) + bytes([65]))),
                 (RAMP_65, {"kind": "offset", "value": str(2**256 - 4)}, (runner.STD_TRUNCATED, b"")),
                 (RAMP_65, {"kind": "length", "value": "66"}, (None, RAMP_65 + bytes(1))),
                 (RAMP_65, {"kind": "length", "value": "96"}, (None, RAMP_65 + bytes(31))),
                 (RAMP_65, {"kind": "length", "value": "97"}, (runner.STD_TRUNCATED, b"")),
                 (RAMP_65, {"kind": "length", "value": str(2**256 - 63)}, (runner.STD_TRUNCATED, b"")),
                 (RAMP_65, {"kind": "length", "value": "0"}, (None, b"")),
                 (RAMP_65, {"kind": "padding", "pattern": "ones"}, (None, RAMP_65)),
                 (bytes(range(1, 65)), {"kind": "length", "value": "65"}, (runner.STD_TRUNCATED, b""))]
        for data, malformation, expected in cases:
            with self.subTest(malformation=malformation):
                self.assertEqual(decode(data, malformation), expected)

    def test_the_selector_rule_applies_to_bytes_rejections(self):
        value = malformed_bytes_case()
        result = runner.compare(malformed_bytes_histories(value), value)
        self.assertEqual(result["category"], "matched")
        self.assertEqual(result["selectorRows"], [{"id": "tx-2", "index": 2, "selector": runner.STD_TRUNCATED}])
        observed = malformed_bytes_histories(value)
        observed["rustEvm"]["transactions"][2]["output"] = selector_word(runner.STD_TRUNCATED)
        self.assertEqual(runner.compare(observed, value)["category"], "semantic-mismatch")

    def test_a_returned_bytes_row_follows_the_protocol_on_the_decoded_payload(self):
        value = malformed_bytes_case()
        histories = malformed_bytes_histories(value)
        rows = histories["directCore"]["transactions"]
        for index, tx in enumerate(value["transactions"]):
            prior = rows[index - 1]["committedStorage"] if index else histories["directCore"]["initialStorage"]
            self.assertTrue(runner.conforms(value, tx, {**rows[index], "output": tx["stdRejection"] or rows[index]["output"]}, prior))
        # A result that counts the canonical calldata size instead of the cut one breaks the protocol on every path.
        changed = malformed_bytes_histories(value)
        for path in runner.PATHS:
            row = changed[path]["transactions"][1]
            row["output"] = "0x" + f"{int(row['output'], 16) + 16:064x}"
        prior = changed["directCore"]["transactions"][0]["committedStorage"]
        self.assertFalse(runner.conforms(value, value["transactions"][1], changed["directCore"]["transactions"][1], prior))
        self.assertNotEqual(runner.compare(changed, value)["category"], "matched")


METHODS_MISSING = "0x43c9d5b5"
METHOD_FIXTURES = (("m_00000001", 1), ("m_00000002", 0), ("m_00000003", 2))


def methods_case(methods=METHOD_FIXTURES, rows=(("m_00000001", (6,)), ("m_00000002", ()), (None, (1,)),
                                                 ("m_00000003", (2, 3)), ("m_00000003", (2, 4)))):
    """Envelope fixture only: native replay checks the actual several-methods program."""
    table = [{"name": name, "signature": runner.method_signature(name, arity),
              "selector": runner.method_selector(runner.method_signature(name, arity)), "arity": arity} for name, arity in methods]
    transactions = []
    for index, (name, inputs) in enumerate(rows):
        selector = METHODS_MISSING if name is None else next(method["selector"] for method in table if method["name"] == name)
        calldata = selector + "".join(f"{value:064x}" for value in inputs)
        rejection = runner.STD_NO_SELECTOR if name is None else None
        transactions.append({"id": f"tx-{index}", "method": name, "selector": selector, "inputs": [str(value) for value in inputs],
                             "calldata": calldata, "stdRejection": rejection, "value": "0"})
    return {"schema": runner.METHODS_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "methodsPlan": {"schema": "solcore-lean.methods-plan.v1", "missingSelector": METHODS_MISSING,
                        "methods": [{"name": name, "arity": arity, "stepProgram": {}} for name, arity in methods]},
        "initialState": {"storage": []}, "observedSlots": [str(slot) for slot in range(6)],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedMethods", "methods": table,
            "selectorOrder": runner.selector_order([method["selector"] for method in table]),
            "deployPath": ["SynthesizedMethodsDeploy"], "runtimePath": ["SynthesizedMethodsDeploy", "SynthesizedMethods"],
            "constructorCalldata": "0x"},
        "transactions": transactions}


def methods_slots(values):
    return [{"slot": str(index), "value": str(value)} for index, value in enumerate(values)]


def methods_history(value, path):
    """Rows that follow the shared-slot protocol: a call sets slot zero to its
    input plus slot zero plus one, counts itself in slot one, copies slot zero
    to its own slot and returns the sum; an odd input reverts and the missing
    selector reverts with std's selector, a Word on original Core and four
    bytes on Hull and EVM."""
    names = [method["name"] for method in value["contract"]["methods"]]
    rows, prior = [], [0] * 6
    for index, tx in enumerate(value["transactions"]):
        x = sum(int(item) for item in tx["inputs"])
        if tx["stdRejection"] is not None:
            committed, output = list(prior), selector_word(tx["stdRejection"]) if path == "directCore" else tx["stdRejection"]
            status = "reverted"
        else:
            own = 2 + names.index(tx["method"])
            after = list(prior)
            after[0] = prior[0] + x + 1
            after[1] = prior[1] + 1
            after[own] = after[0]
            result = after[0] + after[1] + after[own]
            status = "reverted" if x % 2 else "returned"
            committed = list(prior) if x % 2 else after
            output = "0x" + f"{result:064x}"
        row = {"id": tx["id"], "index": index, "status": status, "output": output, "committedStorage": methods_slots(committed)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
        prior = committed
    result = {"schema": runner.METHODS_HISTORY_SCHEMA, "observedSlots": value["observedSlots"],
        "initialStorage": methods_slots([0] * 6), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def methods_histories(value=None):
    value = methods_case() if value is None else value
    return {path: methods_history(value, path) for path in runner.PATHS}


class MethodsTests(unittest.TestCase):
    def test_a_methods_case_records_its_methods_selectors_and_calls(self):
        value = methods_case()
        runner.validate_case(value)
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"], selected["shrinkBatch"]),
                         ("semantic-methods-tool", "rust-hull-keyed-storage-scenario", True, "methods", 16))
        self.assertTrue(runner.has_methods(value) and runner.uses_selector_rule(value))
        self.assertFalse(runner.has_methods(malformed_case()) or runner.uses_selector_rule(nested_case()))
        self.assertEqual([method["selector"] for method in value["contract"]["methods"]], ["0x935853e4", "0xf3cfdf58", "0x336e1e08"])
        self.assertEqual(value["contract"]["selectorOrder"], "mixed")
        self.assertEqual(runner.selector_order(["0x06d154aa", "0x336e1e08"]), "ascending")
        self.assertEqual(runner.selector_order(["0xf3cfdf58", "0x336e1e08"]), "descending")
        self.assertEqual([tx["stdRejection"] for tx in value["transactions"]], [None, None, runner.STD_NO_SELECTOR, None, None])
        self.assertIn("missing selector compared by std's error selector", runner.scope(value))
        changed_contract = lambda key, item: {**value["contract"], key: item}
        for key, changed in (("contract", changed_contract("selectorOrder", "ascending")),
                             ("contract", changed_contract("methods", value["contract"]["methods"][:2]))):
            invalid = copy.deepcopy(value)
            invalid[key] = changed
            with self.subTest(key=key), self.assertRaises(Exception):
                runner.validate_case(invalid)
        for methods in ((("m_00000001", 1),), (("m_0000000G", 1), ("m_00000002", 0)), (("m_00000001", 1), ("m_00000001", 0)),
                        (("m_00000001", 3), ("m_00000002", 0)), (("m_00000001", 1), ("m_00000002", 0)) * 3):
            with self.subTest(methods=methods), self.assertRaises(Exception):
                runner.validate_case(methods_case(methods, rows=(("m_00000002", ()),)))
        colliding = methods_case()
        colliding["methodsPlan"]["missingSelector"] = "0x935853e4"
        with self.assertRaises(Exception):
            runner.validate_case(colliding)
        for key, changed in (("method", "m_0000000f"), ("selector", METHODS_MISSING), ("inputs", ["6", "7"]),
                             ("calldata", "0x935853e4"), ("stdRejection", runner.STD_NO_SELECTOR), ("value", "1")):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)

    def test_the_dispatch_model_follows_std(self):
        """The golden decisions of the Lean model, from the pinned dispatch.sol."""
        methods, missing = runner.contract_methods(methods_case())
        word = lambda value: value.to_bytes(32, "big")
        selector = lambda position: bytes.fromhex(methods[position]["selector"][2:])
        cases = [(selector(0) + word(6), (None, 0)), (selector(1), (None, 1)), (selector(2) + word(2) + word(4), (None, 2)),
                 (bytes.fromhex(missing[2:]) + word(1), (runner.STD_NO_SELECTOR, None)), (selector(0)[:3], (runner.STD_NO_SELECTOR, None)),
                 (b"", (runner.STD_NO_SELECTOR, None)), (selector(0), (runner.STD_TRUNCATED, None)),
                 (selector(2) + word(2), (runner.STD_TRUNCATED, None)), (selector(1) + word(9), (None, 1))]
        for data, expected in cases:
            with self.subTest(data=data.hex()):
                self.assertEqual(runner.methods_dispatch(methods, data), expected)

    def test_the_selector_rule_applies_to_the_missing_selector(self):
        value = methods_case()
        result = runner.compare(methods_histories(value), value)
        self.assertEqual(result["category"], "matched")
        self.assertEqual(result["selectorRows"], [{"id": "tx-2", "index": 2, "selector": runner.STD_NO_SELECTOR}])
        observed = methods_histories(value)
        observed["rustEvm"]["transactions"][2]["output"] = selector_word(runner.STD_NO_SELECTOR)
        self.assertEqual((runner.compare(observed, value)["category"], runner.compare(observed, value)["transactionId"]),
                         ("semantic-mismatch", "tx-2"))

    def test_a_returned_call_follows_the_shared_slot_protocol(self):
        value = methods_case()
        histories = methods_histories(value)
        rows = histories["directCore"]["transactions"]
        for index, tx in enumerate(value["transactions"]):
            prior = rows[index - 1]["committedStorage"] if index else histories["directCore"]["initialStorage"]
            self.assertTrue(runner.conforms(value, tx, {**rows[index], "output": tx["stdRejection"] or rows[index]["output"]}, prior))
        # A call that writes another method's slot breaks the protocol on every path.
        changed = methods_histories(value)
        for path in runner.PATHS:
            row = changed[path]["transactions"][1]
            row["committedStorage"][4]["value"] = "5"
        prior = changed["directCore"]["transactions"][0]["committedStorage"]
        self.assertFalse(runner.conforms(value, value["transactions"][1], changed["directCore"]["transactions"][1], prior))
        self.assertNotEqual(runner.compare(changed, value)["category"], "matched")


def loop_case(mask=7, rows=((0, 7), (1, 3), (2, 2**255 + 1))):
    """Envelope fixture only: native replay checks the actual storage-loop program."""
    transactions = [{"id": f"tx-{index}", "flags": str(flags), "input": str(value), "iterations": value & mask,
                     "calldata": "0x7357f5d2" + f"{flags:064x}" + f"{value:064x}", "value": "0"}
                    for index, (flags, value) in enumerate(rows)]
    return {"schema": runner.LOOP_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "storageLoopPlan": {"schema": "solcore-lean.storage-loop-plan.v1", "stepProgram": {}, "mask": mask},
        "initialState": {"storage": []}, "observedSlots": [str(slot) for slot in range(9)],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedStorageLoops", "method": "run", "signature": "run(uint256,uint256)",
            "selector": "0x7357f5d2", "deployPath": ["SynthesizedStorageLoopsDeploy"],
            "runtimePath": ["SynthesizedStorageLoopsDeploy", "SynthesizedStorageLoops"], "constructorCalldata": "0x"},
        "transactions": transactions}


def loop_history(value, path, step=lambda x: x + 1, copy_last=True):
    """Rows of the loop protocol with a known step: iteration i writes
    step(slot 0 + slot 1 + slot (1 + i) + slot (2 + i) + input) to slot 2 + i
    and slot 0, slot one then grows by the count, and odd flags revert with
    slot 0 + slot 1. Without `copy_last` the last iteration skips slot 0."""
    mask = value["storageLoopPlan"]["mask"]
    rows, prior = [], [0] * 9
    for index, tx in enumerate(value["transactions"]):
        after, x = list(prior), int(tx["input"])
        count = x & mask
        for i in range(count):
            written = step((after[0] + after[1] + after[1 + i] + after[2 + i] + x) % 2**256) % 2**256
            after[2 + i] = written
            if copy_last or i + 1 < count:
                after[0] = written
        after[1] = (after[1] + count) % 2**256
        result = (after[0] + after[1]) % 2**256
        reverted = int(tx["flags"]) % 2 == 1
        committed = list(prior) if reverted else after
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned",
               "output": "0x" + f"{result:064x}", "committedStorage": methods_slots(committed)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
        prior = committed
    result = {"schema": runner.LOOP_HISTORY_SCHEMA, "observedSlots": value["observedSlots"],
        "initialStorage": methods_slots([0] * 9), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def loop_histories(value=None, **options):
    value = loop_case() if value is None else value
    return {path: loop_history(value, path, **options) for path in runner.PATHS}


class LoopTests(unittest.TestCase):
    def test_a_loop_case_records_its_mask_and_each_transactions_iterations(self):
        value = loop_case()
        runner.validate_case(value)
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"], selected["selector"]),
                         ("semantic-storage-loop-tool", "rust-hull-keyed-storage-scenario", True, "loops", "0x7357f5d2"))
        self.assertTrue(runner.has_loops(value))
        self.assertFalse(runner.has_loops(methods_case()) or runner.uses_selector_rule(value))
        self.assertEqual([runner.loop_iterations(value, tx) for tx in value["transactions"]], [7, 3, 1])
        self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]], ["returned", "reverted", "returned"])
        self.assertEqual(runner.observed_slots(value), tuple(str(slot) for slot in range(9)))
        self.assertIn("source while loop", runner.scope(value))
        for mask in (0, 1, 3):
            runner.validate_case(loop_case(mask))
        for mask in (2, 5, 8, True, "7", None):
            invalid = loop_case()
            invalid["storageLoopPlan"]["mask"] = mask
            with self.subTest(mask=mask), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        for key, changed in (("iterations", 6), ("iterations", "7"), ("iterations", None),
                             ("calldata", "0x7357f5d2" + "00" * 64), ("value", "1"), ("flags", "2")):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        # A recorded count follows the plan's mask, so another mask needs other counts.
        invalid = copy.deepcopy(value)
        invalid["storageLoopPlan"]["mask"] = 3
        with self.assertRaises(ValueError):
            runner.validate_case(invalid)
        invalid = copy.deepcopy(value)
        invalid["observedSlots"] = invalid["observedSlots"][:5]
        with self.assertRaises(runner.Finding):
            runner.validate_case(invalid)

    def test_a_returned_row_follows_the_loop_protocol(self):
        value = loop_case()
        histories = loop_histories(value)
        self.assertEqual(runner.compare(histories, value)["category"], "matched")
        rows = histories["directCore"]["transactions"]
        for index, tx in enumerate(value["transactions"]):
            prior = rows[index - 1]["committedStorage"] if index else histories["directCore"]["initialStorage"]
            self.assertTrue(runner.conforms(value, tx, rows[index], prior))
            self.assertEqual(runner.loop_fields(value, tx, rows[index], prior), [])
        # tx-2 runs one iteration: slot one grows by one, slot zero equals slot
        # two, slots three to eight keep their values and the output is their sum.
        prior, tx = rows[1]["committedStorage"], value["transactions"][2]
        for slot in ("0", "1", "8"):
            changed = copy.deepcopy(rows[2])
            entry = next(item for item in changed["committedStorage"] if item["slot"] == slot)
            entry["value"] = str(int(entry["value"]) + 1)
            with self.subTest(slot=slot):
                self.assertIn("committedStorage", runner.loop_fields(value, tx, changed, prior))
        changed = copy.deepcopy(rows[2])
        changed["output"] = "0x" + f"{int(changed['output'], 16) + 1:064x}"
        self.assertEqual(runner.loop_fields(value, tx, changed, prior), ["output"])
        # A revert is checked by rollback, not by the protocol.
        self.assertEqual(runner.loop_fields(value, value["transactions"][1], {**rows[1], "output": "0x" + "00" * 32},
                                            rows[0]["committedStorage"]), [])
        # Zero iterations leave slot zero and every iteration slot unchanged.
        zero = loop_case(rows=((0, 7), (0, 8)))
        prior, row = loop_histories(zero)["directCore"]["transactions"]
        self.assertEqual(runner.loop_fields(zero, zero["transactions"][1], row, prior["committedStorage"]), [])

    def test_a_protocol_break_on_every_path_is_a_mismatch_although_the_paths_agree(self):
        value = loop_case()
        broken = loop_histories(value, copy_last=False)
        result = runner.compare(broken, value)
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-0"))
        self.assertTrue(all(result["pairs"].values()))
        self.assertIn("committedStorage", result["fields"])
        # A different step on one path is an ordinary difference.
        changed = loop_histories(value)
        changed["importedHull"] = loop_history(value, "importedHull", step=lambda x: x + 2)
        result = runner.compare(changed, value)
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-0"))
        self.assertFalse(result["pairs"]["directCore/importedHull"])


def keccak_loop_case(mask=7, key_mask=1, rows=((0, 7), (1, 3), (2, 2))):
    """Envelope fixture only: native replay checks the actual Keccak-loop program.
    Its keys stay among the cast-derived entry slots, so the observed slots are
    written independently of the adapter's Keccak."""
    transactions = [{"id": f"tx-{index}", "flags": str(flags), "input": str(value), "iterations": value & mask,
                     "calldata": "0x7357f5d2" + f"{flags:064x}" + f"{value:064x}", "value": "0"}
                    for index, (flags, value) in enumerate(rows)]
    keys = {(value & (2**256 - 8)) | (i & key_mask) for _, value in rows for i in range(value & mask)}
    return {"schema": runner.KECCAK_LOOP_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "keccakLoopPlan": {"schema": "solcore-lean.keccak-loop-plan.v1", "stepProgram": {}, "mask": mask, "keyMask": key_mask},
        "initialState": {"storage": []},
        "observedSlots": [str(slot) for slot in sorted({0} | {CAST_ENTRY_SLOTS[key] for key in keys})],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedKeccakLoops", "method": "run", "signature": "run(uint256,uint256)",
            "selector": "0x7357f5d2", "deployPath": ["SynthesizedKeccakLoopsDeploy"],
            "runtimePath": ["SynthesizedKeccakLoopsDeploy", "SynthesizedKeccakLoops"], "constructorCalldata": "0x"},
        "transactions": transactions}


def keccak_loop_history(value, path, step=lambda x: x + 1, copy_last=True, address="101"):
    """Rows of the Keccak-loop protocol with a known step: iteration i writes
    step(entry + slot 0 + input) to the entry of its key and to slot 0 and logs
    the counter, the key and the value; odd flags revert with slot 0 plus the
    count, committing nothing. Without `copy_last` the last iteration skips slot 0."""
    plan, slots = value["keccakLoopPlan"], [int(slot) for slot in value["observedSlots"]]
    prior, rows = {slot: 0 for slot in slots}, []
    storage = lambda values: [{"slot": str(slot), "value": str(values[slot])} for slot in slots]
    for index, tx in enumerate(value["transactions"]):
        after, x, logs = dict(prior), int(tx["input"]), []
        count = x & plan["mask"]
        for i in range(count):
            key = (x & (2**256 - 8)) | (i & plan["keyMask"])
            written = step((after[CAST_ENTRY_SLOTS[key]] + after[0] + x) % 2**256) % 2**256
            after[CAST_ENTRY_SLOTS[key]] = written
            if copy_last or i + 1 < count:
                after[0] = written
            logs.append(log_entry([i, key], [written], address))
        reverted = int(tx["flags"]) % 2 == 1
        committed = dict(prior) if reverted else after
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned",
               "output": "0x" + f"{(after[0] + count) % 2**256:064x}", "committedStorage": storage(committed),
               "logs": [] if reverted else logs}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
        prior = committed
    result = {"schema": runner.KECCAK_LOOP_HISTORY_SCHEMA, "observedSlots": value["observedSlots"],
        "initialStorage": storage({slot: 0 for slot in slots}), "initialLogs": [], "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    if path == "directCore":
        result["bindings"] = {"schema": "solcore-lean.storage-bindings.v1", "caller": "17", "address": address}
    if path == "rustEvm":
        result["chainLogs"] = [copy.deepcopy(log) for row in rows for log in row["logs"]]
    return with_whole(result, address)


def keccak_loop_histories(value=None, **options):
    value = keccak_loop_case() if value is None else value
    return {path: keccak_loop_history(value, path, **options) for path in runner.PATHS}


class KeccakLoopTests(unittest.TestCase):
    def test_a_keccak_loop_case_records_its_masks_iterations_and_entry_slots(self):
        value = keccak_loop_case()
        runner.validate_case(value)
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"],
                          selected["logs"], selected["selector"], selected["shrinkBatch"]),
                         ("semantic-keccak-loop-tool", "rust-hull-keyed-storage-scenario", True, "keccak-loops", True,
                          "0x7357f5d2", 16))
        self.assertTrue(runner.has_keccak_loops(value) and runner.has_logs(value))
        self.assertFalse(runner.has_loops(value) or runner.has_keccak_loops(loop_case()))
        self.assertEqual([runner.loop_iterations(value, tx) for tx in value["transactions"]], [7, 3, 2])
        self.assertEqual([runner.keccak_loop_keys(value, tx) for tx in value["transactions"]],
                         [[0, 1, 0, 1, 0, 1, 0], [0, 1, 0], [0, 1]])
        self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]], ["returned", "reverted", "returned"])
        self.assertEqual([runner.expected_log_shapes(value, tx) for tx in value["transactions"]], [[(2, 32)] * 7, [], [(2, 32)] * 2])
        self.assertEqual(runner.observed_slots(value), ("0", str(CAST_ENTRY_SLOTS[0]), str(CAST_ENTRY_SLOTS[1])))
        self.assertEqual(runner.keccak_loop_slots(value), list(runner.observed_slots(value)))
        self.assertIn("keccak256(1 ++ key)", runner.scope(value))
        self.assertIn("log2", runner.scope(value))
        # Key mask 7 gives every iteration its own key, and the high part keys every entry.
        wide = copy.deepcopy(value)
        wide["keccakLoopPlan"]["keyMask"] = 7
        self.assertEqual(runner.keccak_loop_keys(wide, wide["transactions"][0]), list(range(7)))
        self.assertEqual(runner.keccak_loop_keys(wide, {"input": str(MAX_WORD)}), [2**256 - 8 + i for i in range(7)])
        for mask, key_mask in ((0, 0), (1, 7), (3, 1), (7, 0)):
            runner.validate_case(keccak_loop_case(mask, key_mask))
        for key in ("mask", "keyMask"):
            for changed in (2, 5, 8, True, "7", None):
                invalid = keccak_loop_case()
                invalid["keccakLoopPlan"][key] = changed
                with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                    runner.validate_case(invalid)
        for key, changed in (("iterations", 6), ("iterations", "7"), ("iterations", None),
                             ("calldata", "0x7357f5d2" + "00" * 64), ("value", "1"), ("flags", "2")):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        # A recorded count follows the loop mask; the observed slots follow the
        # key mask and every transaction's keys.
        invalid = copy.deepcopy(value)
        invalid["keccakLoopPlan"]["mask"] = 3
        with self.assertRaises(ValueError):
            runner.validate_case(invalid)
        for change in (lambda case: case["keccakLoopPlan"].update(keyMask=3), lambda case: case["observedSlots"].pop(),
                       lambda case: case["observedSlots"].reverse(), lambda case: case.update(observedSlots=["0", "1"]),
                       lambda case: case["transactions"][2].update(input=str(2**255 + 2),
                           calldata="0x7357f5d2" + f"{2:064x}" + f"{2**255 + 2:064x}")):
            invalid = copy.deepcopy(value)
            change(invalid)
            with self.assertRaises(runner.Finding):
                runner.validate_case(invalid)

    def test_a_returned_row_follows_the_keccak_loop_protocol(self):
        value = keccak_loop_case()
        histories = keccak_loop_histories(value)
        self.assertEqual(runner.compare(histories, value)["category"], "matched")
        rows = histories["directCore"]["transactions"]
        for index, tx in enumerate(value["transactions"]):
            prior = rows[index - 1]["committedStorage"] if index else histories["directCore"]["initialStorage"]
            self.assertTrue(runner.conforms(value, tx, rows[index], prior, address="101"))
            self.assertEqual(runner.keccak_loop_fields(value, tx, rows[index], prior), [])
        # tx-2 runs two iterations on keys 0 and 1 after the revert.
        prior, tx = rows[1]["committedStorage"], value["transactions"][2]
        for slot in value["observedSlots"]:
            changed = copy.deepcopy(rows[2])
            entry = next(item for item in changed["committedStorage"] if item["slot"] == slot)
            entry["value"] = str(int(entry["value"]) + 1)
            with self.subTest(slot=slot):
                self.assertIn("committedStorage", runner.keccak_loop_fields(value, tx, changed, prior))
                self.assertFalse(runner.conforms(value, tx, changed, prior))
        for change in (lambda logs: logs[0]["topics"].__setitem__(1, "1"), lambda logs: logs.reverse(),
                       lambda logs: logs.pop(), lambda logs: logs.append(copy.deepcopy(logs[0])),
                       lambda logs: logs[0].update(data="0x" + "00" * 31)):
            changed = copy.deepcopy(rows[2])
            change(changed["logs"])
            with self.subTest(change=change):
                self.assertEqual(runner.keccak_loop_fields(value, tx, changed, prior)[0], "logs")
                self.assertFalse(runner.conforms(value, tx, changed, prior))
        # A log whose data the storage does not hold breaks the committed slots.
        changed = copy.deepcopy(rows[2])
        changed["logs"][1]["data"] = "0x" + f"{7:064x}"
        self.assertEqual(runner.keccak_loop_fields(value, tx, changed, prior), ["committedStorage"])
        changed = copy.deepcopy(rows[2])
        changed["output"] = "0x" + f"{int(changed['output'], 16) + 1:064x}"
        self.assertEqual(runner.keccak_loop_fields(value, tx, changed, prior), ["output"])
        # A revert is checked by rollback and the log shapes, not by the protocol.
        self.assertEqual(runner.keccak_loop_fields(value, value["transactions"][1], {**rows[1], "output": "0x" + "00" * 32},
                                                   rows[0]["committedStorage"]), [])
        self.assertFalse(runner.conforms(value, value["transactions"][1], {**rows[1], "logs": copy.deepcopy(rows[0]["logs"][:3])},
                                         rows[0]["committedStorage"]))
        # Zero iterations leave every observed slot unchanged and log nothing.
        zero = keccak_loop_case(rows=((0, 3), (0, 8)))
        prior, row = keccak_loop_histories(zero)["directCore"]["transactions"]
        self.assertEqual((row["logs"], runner.keccak_loop_fields(zero, zero["transactions"][1], row, prior["committedStorage"])), ([], []))

    def test_a_keccak_protocol_break_on_every_path_is_a_mismatch_although_the_paths_agree(self):
        value = keccak_loop_case()
        broken = keccak_loop_histories(value, copy_last=False)
        result = runner.compare(broken, value)
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-0"))
        self.assertTrue(all(result["pairs"].values()))
        self.assertIn("committedStorage", result["fields"])
        # The same wrong topic on every path breaks the logs.
        relabelled = keccak_loop_histories(value)
        for path in runner.PATHS:
            relabelled[path]["transactions"][0]["logs"][2]["topics"][0] = "3"
        relabelled["rustEvm"]["chainLogs"] = [log for row in relabelled["rustEvm"]["transactions"] for log in row["logs"]]
        result = runner.compare(relabelled, value)
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-0"))
        self.assertTrue(all(result["pairs"].values()))
        self.assertIn("logs", result["fields"])
        # A different step on one path is an ordinary difference.
        changed = keccak_loop_histories(value)
        changed["importedHull"] = keccak_loop_history(value, "importedHull", step=lambda x: x + 2)
        result = runner.compare(changed, value)
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-0"))
        self.assertFalse(result["pairs"]["directCore/importedHull"])
        # The EVM chain keeps every committed log.
        dropped = keccak_loop_histories(value)
        dropped["rustEvm"]["chainLogs"].pop()
        self.assertEqual(runner.compare(dropped, value)["stage"], "committed-log-history")


def assembly_case(value, form="carried"):
    """A loop fixture as its inline Yul profile's case: the same plan and
    transactions with a form, under the inline Yul schemas and wrapper."""
    value = copy.deepcopy(value)
    keccak = value["schema"] == runner.KECCAK_LOOP_CASE_SCHEMA
    key, kind = ("keccakLoopPlan", "Keccak") if keccak else ("storageLoopPlan", "Storage")
    value["schema"] = runner.ASSEMBLY_KECCAK_LOOP_CASE_SCHEMA if keccak else runner.ASSEMBLY_LOOP_CASE_SCHEMA
    value[key].update(schema=f"solcore-lean.assembly-{kind.lower()}-loop-plan.v1", form=form)
    name = f"SynthesizedAssembly{kind}Loops"
    value["contract"].update(name=name, deployPath=[name + "Deploy"], runtimePath=[name + "Deploy", name])
    return value


class AssemblyLoopTests(unittest.TestCase):
    def test_inline_yul_loop_cases_take_their_parents_protocol_and_history(self):
        for parent, histories in ((loop_case(), loop_histories), (keccak_loop_case(), keccak_loop_histories)):
            for form in ("split", "carried", "pipelined"):
                value = assembly_case(parent, form)
                runner.validate_case(value)
                selected, original = runner.profile(value), runner.profile(parent)
                with self.subTest(schema=value["schema"], form=form):
                    self.assertEqual(selected["forms"], ("split", "carried", "pipelined"))
                    for field in ("planKey", "coreRunner", "scenarioSchema", "historySchema", "signature", "selector",
                                  "rollback", "declared", "abi", "shrinkBatch"):
                        self.assertEqual(selected[field], original[field])
                    self.assertEqual(selected.get("logs"), original.get("logs"))
                    self.assertNotEqual(selected["caseTool"], original["caseTool"])
                    self.assertEqual(runner.observed_slots(value), runner.observed_slots(parent))
                    self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]],
                                     [runner.expected_status(parent, tx) for tx in parent["transactions"]])
                    # The parent's rows match, and a protocol break on every path is a mismatch.
                    self.assertEqual(runner.compare(histories(value), value)["category"], "matched")
                    result = runner.compare(histories(value, copy_last=False), value)
                    self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-0"))
                    self.assertTrue(all(result["pairs"].values()))

    def test_an_inline_yul_loop_plan_requires_a_known_form_and_its_parents_slots(self):
        for parent in (loop_case(), keccak_loop_case()):
            key = "keccakLoopPlan" if "keccakLoopPlan" in parent else "storageLoopPlan"
            for form in ("blocks", "for", "", None, 1):
                invalid = assembly_case(parent)
                invalid[key]["form"] = form
                with self.subTest(key=key, form=form), self.assertRaises(ValueError):
                    runner.validate_case(invalid)
            invalid = assembly_case(parent)
            del invalid[key]["form"]
            with self.assertRaises(ValueError):
                runner.validate_case(invalid)
            # The plan schema is the inline Yul profile's, not the parent's.
            invalid = assembly_case(parent)
            invalid[key]["schema"] = parent[key]["schema"]
            with self.assertRaises(ValueError):
                runner.validate_case(invalid)
            invalid = assembly_case(parent)
            invalid["observedSlots"].pop()
            with self.assertRaises(runner.Finding):
                runner.validate_case(invalid)
        # The parents' plans admit no form check of their own.
        self.assertNotIn("forms", runner.profile(loop_case()))
        self.assertNotIn("forms", runner.profile(keccak_loop_case()))


# Entry slots keccak256(base ++ key) from Foundry's `cast keccak`, for the enum
# and struct fixture's mapping bases 9 and 10 and its keys 2^256 - 1 and 0, and
# its methods' selectors from `cast sig`, all independent of the adapter's Keccak.
CAST_ADT_ENTRIES = {
    (9, MAX_WORD): 4951835114823754866708375840211612671190448154855786638499095948215603667702,
    (9, 0): 22756765779589845761170775236260874230900367805402455632653690919156678150133,
    (10, MAX_WORD): 92386539972242642649209974360938212169604720364531104164352636696906078334069,
    (10, 0): 28316780231992663356899387360795050299752000032466988729594309499906746629572}
CAST_ADT_SELECTORS = {"putChoice": "0x1f7e5b11", "clearChoice": "0xa1c23d7b", "getChoice": "0xd149174a",
                      "putRecordAt": "0x1e56f3c9", "setRecordAt": "0x7d3a712d", "getRecordAt": "0xbb468a61"}
ADT_K = 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95
ADT_PARAMETERS = {"putChoice": ("flags", "variant", "input"), "clearChoice": ("flags", "input"), "getChoice": ("flags",),
                  "putRecordAt": ("flags", "key", "variant", "input"),
                  "setRecordAt": ("flags", "key", "field", "variant", "input"), "getRecordAt": ("flags", "key")}
ADT_ROWS = (("putChoice", {"flags": 0, "variant": 0, "input": 2}), ("clearChoice", {"flags": 0, "input": 1}),
            ("getChoice", {"flags": 1}), ("putRecordAt", {"flags": 0, "key": MAX_WORD, "variant": 0, "input": 0}),
            ("setRecordAt", {"flags": 0, "key": 0, "field": 1, "variant": 0, "input": 3}),
            ("getRecordAt", {"flags": 0, "key": MAX_WORD}))


def adt_slots():
    """The fixture's observed slots: the accumulator, the enum at 1 to 3, the
    record at 4 to 8, and at both keys three enum and five record entry slots."""
    values = {0} | set(range(1, 9))
    for (base, _), first in CAST_ADT_ENTRIES.items():
        values |= {first + offset for offset in range(3 if base == 9 else 5)}
    return [str(value) for value in sorted(values)]


def adt_case(rows=ADT_ROWS):
    """Envelope fixture only: native replay checks the actual contract. The
    shape `V0(word, word) | V1` puts the enum at slots 1 to 3, the record (its
    enum first) at 4 to 8, `choices` at 9 and `records` at 10; keys 2^256 - 1
    and 0."""
    methods = [name for name in ("putChoice", "clearChoice", "getChoice", "putRecordAt", "setRecordAt", "getRecordAt")
               if any(row[0] == name for row in rows)]
    transactions = []
    for index, (method, args) in enumerate(rows):
        words = [args[parameter] for parameter in ADT_PARAMETERS[method]]
        transaction = {"id": f"tx-{index}", "method": method,
                       **{parameter: args[parameter] if parameter in ("field", "variant") else str(args[parameter])
                          for parameter in ADT_PARAMETERS[method]},
                       "calldata": CAST_ADT_SELECTORS[method] + "".join(f"{word:064x}" for word in words), "value": "0"}
        transactions.append(transaction)
    return {"schema": runner.ADT_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "adtStoragePlan": {"schema": "solcore-lean.adt-storage-plan.v1", "stepProgram": {}, "keyBase": str(MAX_WORD),
                           "methods": methods, "shape": {"variants": ["words2", "words0"], "position": 0, "wordType": "word"}},
        "initialState": {"storage": []}, "observedSlots": adt_slots(),
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedAdtStorage",
            "methods": [{"name": name, "signature": name + "(" + ",".join(["uint256"] * len(ADT_PARAMETERS[name])) + ")",
                         "selector": CAST_ADT_SELECTORS[name], "parameters": list(ADT_PARAMETERS[name])} for name in methods],
            "layout": {"accumulatorSlot": 0, "choiceSlot": 1, "choiceSlots": 3, "recordSlot": 4, "recordSlots": 5,
                       "fieldOffsets": [0, 3, 4], "choicesSlot": 9, "recordsSlot": 10, "clearVariant": 1},
            "deployPath": ["SynthesizedAdtStorageDeploy"],
            "runtimePath": ["SynthesizedAdtStorageDeploy", "SynthesizedAdtStorage"], "constructorCalldata": "0x"},
        "transactions": transactions}


def adt_expected():
    """Each fixture row written out by hand with the step `x + 5`: status,
    output and every nonzero observed slot."""
    top, zero = CAST_ADT_ENTRIES[(10, MAX_WORD)], CAST_ADT_ENTRIES[(10, 0)]
    kv = lambda r, o: (r + o * ADT_K) % 2**256
    digest = 0
    for token in (0, kv(18, 1), kv(18, 2), kv(18, 3), kv(18, 4)):
        digest = (digest * ADT_K + token) % 2**256
    # r = 2 + 0 + 5: tag zero at slot 1, the payload at offsets 1 and 2.
    first = {0: 7, 2: kv(7, 1), 3: kv(7, 2)}
    # r = 1 + 7 + 5: tag one; slots 2 and 3 keep their stale payload.
    cleared = {0: 13, 1: 1, 2: kv(7, 1), 3: kv(7, 2)}
    # r = 0 + 13 + 5 at the top key: the enum's tag zero and pair of Words, then the record's Words.
    record = {**cleared, 0: 18, top + 1: kv(18, 1), top + 2: kv(18, 2), top + 3: kv(18, 3), top + 4: kv(18, 4)}
    # r = 3 + 18 + 5: key 0's middle Word, at offset 3.
    updated = {**record, 0: 26, zero + 3: kv(26, 3)}
    return [("returned", 7, first), ("returned", 13, cleared), ("reverted", 1, cleared), ("returned", 18, record),
            ("returned", 26, updated), ("returned", digest, {**updated, 0: digest})]


def adt_history(value, path, expected=None):
    slots = [int(slot) for slot in value["observedSlots"]]
    storage = lambda values: [{"slot": str(slot), "value": str(values.get(slot, 0))} for slot in slots]
    rows = []
    for index, (tx, (status, output, values)) in enumerate(zip(value["transactions"], expected or adt_expected())):
        row = {"id": tx["id"], "index": index, "status": status, "output": "0x" + f"{output:064x}",
               "committedStorage": storage(values)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
    result = {"schema": runner.ADT_HISTORY_SCHEMA, "observedSlots": value["observedSlots"],
        "initialStorage": storage({}), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def adt_histories(value=None, **options):
    value = adt_case() if value is None else value
    return {path: adt_history(value, path, **options) for path in runner.PATHS}


class AdtStorageTests(unittest.TestCase):
    def test_an_adt_storage_case_records_its_shape_methods_keys_and_layout(self):
        value = adt_case()
        runner.validate_case(value)
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"],
                          selected["selector"], selected["shrinkBatch"], selected["contract"]),
                         ("semantic-adt-storage-tool", "rust-hull-keyed-storage-scenario", True, "adts", None, 16,
                          "SynthesizedAdtStorage"))
        self.assertTrue(runner.has_adts(value))
        self.assertFalse(runner.has_adts(keccak_loop_case()) or runner.has_methods(value))
        self.assertEqual(runner.adt_layout(value), value["contract"]["layout"])
        self.assertEqual(runner.adt_slots(value), adt_slots())
        self.assertEqual(len(runner.observed_slots(value)), 25)
        self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]],
                         ["returned", "returned", "reverted", "returned", "returned", "returned"])
        self.assertIn("std.StorageGeneric", runner.scope(value))
        # The enum's size follows the nested sums: one tag and the larger branch.
        self.assertEqual([runner.adt_choice_size(widths) for widths in ([0, 0], [2, 0], [0, 1, 1, 1], [3, 0, 1, 0], [2, 0, 1])],
                         [1, 3, 4, 4, 3])
        shapes = ({"variants": ["words1", "words1"], "position": 0, "wordType": "word"},
                  {"variants": ["words0", "words1", "words3"], "position": 0, "wordType": "word"},
                  {"variants": ["words0", "words0", "words0", "words0", "words0"], "position": 0, "wordType": "word"},
                  {"variants": ["words2", "words0"], "position": 3, "wordType": "word"},
                  {"variants": ["words2", "words0"], "position": 0, "wordType": "bytes32"},
                  {"variants": ["words2", "words4"], "position": 0, "wordType": "word"},
                  {"variants": ["words2", "words0"], "position": True, "wordType": "word"})
        for shape in shapes:
            invalid = copy.deepcopy(value)
            invalid["adtStoragePlan"]["shape"] = shape
            with self.subTest(shape=shape), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        for methods in ([], ["clearChoice", "putChoice", "getChoice", "putRecordAt", "setRecordAt", "getRecordAt"],
                        ["putChoice", "putChoice", "clearChoice", "getChoice", "putRecordAt", "setRecordAt", "getRecordAt"]):
            invalid = copy.deepcopy(value)
            invalid["adtStoragePlan"]["methods"] = methods
            with self.subTest(methods=methods), self.assertRaises((ValueError, runner.Finding)):
                runner.validate_case(invalid)
        for index, key, changed in ((3, "key", "5"), (0, "variant", 2), (4, "field", 3), (4, "field", True),
                                    (0, "input", None), (2, "input", "1"), (0, "calldata", "0x1f7e5b11" + "00" * 96),
                                    (0, "value", "1"), (0, "method", "getRecord")):
            invalid = copy.deepcopy(value)
            if changed is None:
                del invalid["transactions"][index][key]
            else:
                invalid["transactions"][index][key] = changed
            with self.subTest(index=index, key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        # The observed slots and the recorded layout follow the shape and the key base.
        for change in (lambda case: case["observedSlots"].pop(), lambda case: case["observedSlots"].reverse(),
                       lambda case: case["adtStoragePlan"].update(keyBase="5"),
                       lambda case: case["contract"]["layout"].update(recordSlot=5),
                       lambda case: case["contract"]["methods"][0].update(selector="0x00000000")):
            invalid = copy.deepcopy(value)
            change(invalid)
            with self.assertRaises((ValueError, runner.Finding)):
                runner.validate_case(invalid)

    def test_a_returned_row_follows_the_layout_protocol(self):
        value = adt_case()
        histories = adt_histories(value)
        self.assertEqual(runner.compare(histories, value)["category"], "matched")
        rows = histories["directCore"]["transactions"]
        for index, tx in enumerate(value["transactions"]):
            prior = rows[index - 1]["committedStorage"] if index else histories["directCore"]["initialStorage"]
            self.assertTrue(runner.conforms(value, tx, rows[index], prior))
            self.assertEqual(runner.adt_fields(value, tx, rows[index], prior), [])
        # Every observed slot of a write, an update and a read is checked, stale ones included.
        for index in (0, 1, 3, 4, 5):
            prior, tx = (rows[index - 1]["committedStorage"] if index else histories["directCore"]["initialStorage"],
                         value["transactions"][index])
            for slot in value["observedSlots"]:
                changed = copy.deepcopy(rows[index])
                entry = next(item for item in changed["committedStorage"] if item["slot"] == slot)
                entry["value"] = str((int(entry["value"]) + 1) % 2**256)
                with self.subTest(index=index, slot=slot):
                    self.assertIn("committedStorage", runner.adt_fields(value, tx, changed, prior))
                    self.assertFalse(runner.conforms(value, tx, changed, prior))
        # A read's output is its digest; a write's output is the r its Words carry.
        for index in (0, 5):
            prior, tx = rows[index - 1]["committedStorage"] if index else histories["directCore"]["initialStorage"], \
                value["transactions"][index]
            changed = copy.deepcopy(rows[index])
            changed["output"] = "0x" + f"{int(changed['output'], 16) ^ 1:064x}"
            with self.subTest(index=index):
                self.assertTrue(runner.adt_fields(value, tx, changed, prior))
        # A path that decodes the stale payload of the cleared enum differs.
        stale = adt_expected()
        stale[2] = ("reverted", (1 * ADT_K + (7 + ADT_K)) % 2**256, stale[2][2])
        changed = adt_histories(value)
        changed["importedHull"] = adt_history(value, "importedHull", stale)
        self.assertEqual(runner.compare(changed, value)["category"], "semantic-mismatch")


def tuple_case(arity=4, rows=((0, 5), (1, 9), (2, 7))):
    """Envelope fixture only: native replay checks the actual tuple-return program."""
    transactions = [{"id": f"tx-{index}", "flags": str(flags), "input": str(value),
                     "calldata": "0x7357f5d2" + f"{flags:064x}" + f"{value:064x}", "value": "0"}
                    for index, (flags, value) in enumerate(rows)]
    return {"schema": runner.TUPLE_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "tupleReturnPlan": {"schema": "solcore-lean.tuple-return-plan.v1", "stepProgram": {}, "arity": arity},
        "initialState": {"storage": []}, "observedSlots": ["0", "1", "2"],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedTupleReturns", "method": "run", "signature": "run(uint256,uint256)",
            "selector": "0x7357f5d2", "deployPath": ["SynthesizedTupleReturnsDeploy"],
            "runtimePath": ["SynthesizedTupleReturnsDeploy", "SynthesizedTupleReturns"], "constructorCalldata": "0x"},
        "transactions": transactions}


def tuple_history(value, path, step=lambda x: x + 1, order=(0, 1, 2, 3), revert_words=1):
    """Rows of the tuple protocol with a known step: r = step(slot 0 + input)
    goes to slot 0, slot one grows by one and the input goes to slot two. A
    return carries (r, slot 1, prior slot 0, prior slot 2) in `order`, cut to
    the arity, and odd flags revert with `revert_words` copies of r."""
    arity = value["tupleReturnPlan"]["arity"]
    rows, prior = [], [0, 0, 0]
    for index, tx in enumerate(value["transactions"]):
        x = int(tx["input"])
        result = step((prior[0] + x) % 2**256) % 2**256
        after = [result, (prior[1] + 1) % 2**256, x]
        reverted = int(tx["flags"]) % 2 == 1
        protocol = [result, after[1], prior[0], prior[2]]
        words = [result] * revert_words if reverted else [protocol[position] for position in order][:arity]
        committed = list(prior) if reverted else after
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned",
               "output": "0x" + "".join(f"{word:064x}" for word in words), "committedStorage": methods_slots(committed)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
        prior = committed
    result = {"schema": runner.TUPLE_HISTORY_SCHEMA, "observedSlots": value["observedSlots"],
        "initialStorage": methods_slots([0, 0, 0]), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def tuple_histories(value=None, **options):
    value = tuple_case() if value is None else value
    return {path: tuple_history(value, path, **options) for path in runner.PATHS}


class TupleTests(unittest.TestCase):
    def test_a_tuple_case_records_its_arity(self):
        value = tuple_case()
        runner.validate_case(value)
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"], selected["selector"]),
                         ("semantic-tuple-return-tool", "rust-hull-keyed-storage-scenario", True, "tuples", "0x7357f5d2"))
        self.assertTrue(runner.has_tuples(value))
        self.assertFalse(runner.has_tuples(loop_case()) or runner.has_loops(value) or runner.uses_selector_rule(value))
        self.assertEqual(runner.tuple_arity(value), 4)
        self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]], ["returned", "reverted", "returned"])
        self.assertEqual(runner.observed_slots(value), ("0", "1", "2"))
        self.assertIn("static tuple", runner.scope(value))
        for arity in (2, 3):
            runner.validate_case(tuple_case(arity))
        for arity in (0, 1, 5, True, "4", None):
            invalid = tuple_case()
            invalid["tupleReturnPlan"]["arity"] = arity
            with self.subTest(arity=arity), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        for key, changed in (("calldata", "0x7357f5d2" + "00" * 64), ("value", "1"), ("flags", "2"), ("input", "6")):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        invalid = copy.deepcopy(value)
        invalid["observedSlots"] = ["0", "1"]
        with self.assertRaises(runner.Finding):
            runner.validate_case(invalid)

    def test_a_returned_tuple_carries_its_arity_and_a_revert_one_word(self):
        for arity in (2, 3, 4):
            value = tuple_case(arity)
            histories = tuple_histories(value)
            with self.subTest(arity=arity):
                self.assertEqual(runner.compare(histories, value)["category"], "matched")
                rows = histories["directCore"]["transactions"]
                self.assertEqual([len(runner.common.hex_bytes(row["output"], "output")) for row in rows], [32 * arity, 32, 32 * arity])
                self.assertEqual([runner.output_words(value, row) for row in rows], [arity, 1, arity])
                for index, tx in enumerate(value["transactions"]):
                    prior = rows[index - 1]["committedStorage"] if index else histories["directCore"]["initialStorage"]
                    self.assertTrue(runner.conforms(value, tx, rows[index], prior))
                    self.assertEqual(runner.tuple_fields(value, tx, rows[index], prior), [])
        # Every other profile keeps its one-Word rule.
        self.assertEqual(runner.output_words(loop_case(), {"status": "returned"}), 1)
        value = tuple_case()
        histories = tuple_histories(value)
        rows = histories["directCore"]["transactions"]
        # tx-2 returns (r, slot 1, prior slot 0, prior slot 2) = (6 + 7 + 1, 2, 6, 5),
        # past the revert of tx-1, which wrote neither slot.
        self.assertEqual(rows[2]["output"], "0x" + "".join(f"{word:064x}" for word in (14, 2, 6, 5)))
        prior, tx = rows[1]["committedStorage"], value["transactions"][2]
        for slot in ("1", "2"):
            changed = copy.deepcopy(rows[2])
            entry = next(item for item in changed["committedStorage"] if item["slot"] == slot)
            entry["value"] = str(int(entry["value"]) + 1)
            with self.subTest(slot=slot):
                self.assertIn("committedStorage", runner.tuple_fields(value, tx, changed, prior))
        for word in range(4):
            changed = copy.deepcopy(rows[2])
            output = bytearray(runner.common.hex_bytes(changed["output"], "output"))
            output[32 * word + 31] ^= 1
            changed["output"] = "0x" + output.hex()
            with self.subTest(word=word):
                self.assertEqual(runner.tuple_fields(value, tx, changed, prior), ["output"])
                self.assertFalse(runner.conforms(value, tx, changed, prior))
        # A truncated or extended tuple breaks the length rule and the protocol.
        for output in (rows[2]["output"][:-64], rows[2]["output"] + "00" * 32, rows[2]["output"] + "00"):
            changed = {**rows[2], "output": output}
            with self.subTest(length=len(output)):
                self.assertFalse(runner.conforms(value, tx, changed, prior))
                self.assertEqual(runner.tuple_fields(value, tx, changed, prior), ["output"])
        # A revert is checked by rollback and its one-Word length, not by the protocol.
        self.assertEqual(runner.tuple_fields(value, value["transactions"][1], {**rows[1], "output": "0x" + "00" * 32},
                                             rows[0]["committedStorage"]), [])
        self.assertFalse(runner.conforms(value, value["transactions"][1], {**rows[1], "output": rows[1]["output"] + "00" * 32},
                                         rows[0]["committedStorage"]))

    def test_a_protocol_break_on_every_path_is_a_mismatch_although_the_paths_agree(self):
        value = tuple_case()
        for options, field in (({"order": (0, 1, 3, 2)}, "output"), ({"revert_words": 2}, "output")):
            broken = tuple_histories(value, **options)
            result = runner.compare(broken, value)
            with self.subTest(options=options):
                self.assertEqual(result["category"], "semantic-mismatch")
                self.assertTrue(all(result["pairs"].values()))
                self.assertIn(field, result["fields"])
        # A two-Word tuple on every path of a four-Word case is a mismatch too.
        short = tuple_histories(tuple_case(2))
        result = runner.compare(short, value)
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-0"))
        self.assertTrue(all(result["pairs"].values()))
        # A different step on one path is an ordinary difference.
        changed = tuple_histories(value)
        changed["rustEvm"] = tuple_history(value, "rustEvm", step=lambda x: x + 2)
        result = runner.compare(changed, value)
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-0"))
        self.assertFalse(result["pairs"]["directCore/rustEvm"])
        self.assertIn("output", result["fields"])


MULTIPLIER = 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95


def bytes_return_case(rows=((0, 5, 0), (1, 9, 31), (2, 7, 33), (0, 3, 64))):
    """Envelope fixture only: native replay checks the actual bytes-return program."""
    transactions = [{"id": f"tx-{index}", "flags": str(flags), "input": str(value), "length": str(length),
                     "calldata": "0x24b912e5" + f"{flags:064x}" + f"{value:064x}" + f"{length:064x}", "value": "0"}
                    for index, (flags, value, length) in enumerate(rows)]
    return {"schema": runner.BYTES_RETURN_CASE_SCHEMA, "program": {}, "source": "protocol fixture only",
        "bytesReturnPlan": {"schema": "solcore-lean.bytes-return-plan.v1", "stepProgram": {}},
        "initialState": {"storage": []}, "observedSlots": ["0", "1", "2"],
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "contract": {"name": "SynthesizedBytesReturns", "method": "run", "signature": "run(uint256,uint256,uint256)",
            "selector": "0x24b912e5", "deployPath": ["SynthesizedBytesReturnsDeploy"],
            "runtimePath": ["SynthesizedBytesReturnsDeploy", "SynthesizedBytesReturns"], "constructorCalldata": "0x"},
        "transactions": transactions}


def bytes_return_history(value, path, step=lambda x: x + 1, padding=0, revert_words=1):
    """Rows of the bytes-return protocol with a known step: r = step(slot 0 +
    input) goes to slot 0, slot one grows by one and the input goes to slot two.
    A return carries the offset 32, the length and the first `length` bytes of
    r * K and (slot 1 * K) xor (prior slot 2), then `padding` up to a whole
    Word; odd flags revert with `revert_words` copies of r."""
    rows, prior = [], [0, 0, 0]
    for index, tx in enumerate(value["transactions"]):
        x, length = int(tx["input"]), int(tx["length"]) % 65
        result = step((prior[0] + x) % 2**256) % 2**256
        after = [result, (prior[1] + 1) % 2**256, x]
        reverted = int(tx["flags"]) % 2 == 1
        if reverted:
            output = result.to_bytes(32, "big") * revert_words
        else:
            data = (result * MULTIPLIER % 2**256).to_bytes(32, "big") + (
                (after[1] * MULTIPLIER % 2**256) ^ prior[2]).to_bytes(32, "big")
            output = (32).to_bytes(32, "big") + length.to_bytes(32, "big") + data[:length] + bytes([padding]) * (-length % 32)
        committed = list(prior) if reverted else after
        row = {"id": tx["id"], "index": index, "status": "reverted" if reverted else "returned",
               "output": "0x" + output.hex(), "committedStorage": methods_slots(committed)}
        if path != "directCore":
            row["undeclaredStorage"] = []
        rows.append(row)
        prior = committed
    result = {"schema": runner.BYTES_RETURN_HISTORY_SCHEMA, "observedSlots": value["observedSlots"],
        "initialStorage": methods_slots([0, 0, 0]), "transactions": rows,
        "finalStorage": copy.deepcopy(rows[-1]["committedStorage"]), "status": "complete", "unexecuted": []}
    if path != "directCore":
        result["initialUndeclaredStorage"] = []
    return with_whole(result)


def bytes_return_histories(value=None, **options):
    value = bytes_return_case() if value is None else value
    return {path: bytes_return_history(value, path, **options) for path in runner.PATHS}


class BytesReturnTests(unittest.TestCase):
    def test_a_bytes_return_case_records_its_lengths(self):
        value = bytes_return_case()
        runner.validate_case(value)
        selected = runner.profile(value)
        self.assertEqual((selected["caseTool"], selected["coreRunner"], selected["declared"], selected["abi"], selected["selector"]),
                         ("semantic-bytes-return-tool", "rust-hull-keyed-storage-scenario", True, "bytes-returns", "0x24b912e5"))
        self.assertTrue(runner.has_bytes_returns(value))
        self.assertFalse(runner.has_bytes_returns(tuple_case()) or runner.has_tuples(value) or runner.has_bytes(value)
                         or runner.uses_selector_rule(value))
        self.assertEqual([runner.expected_status(value, tx) for tx in value["transactions"]],
                         ["returned", "reverted", "returned", "returned"])
        self.assertEqual([runner.return_length(tx) for tx in value["transactions"]], [0, 31, 33, 64])
        self.assertEqual(runner.observed_slots(value), ("0", "1", "2"))
        self.assertIn("bytes value", runner.scope(value))
        # A length above 64 is refused even with its own calldata.
        invalid = bytes_return_case(rows=((0, 5, 65),))
        with self.assertRaises(ValueError):
            runner.validate_case(invalid)
        for key, changed in (("calldata", "0x24b912e5" + "00" * 96), ("value", "1"), ("flags", "2"), ("input", "6"),
                             ("length", "1")):
            invalid = copy.deepcopy(value)
            invalid["transactions"][0][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                runner.validate_case(invalid)
        invalid = copy.deepcopy(value)
        invalid["observedSlots"] = ["0", "1"]
        with self.assertRaises(runner.Finding):
            runner.validate_case(invalid)

    def test_a_returned_value_carries_its_padded_length_and_a_revert_one_word(self):
        value = bytes_return_case()
        histories = bytes_return_histories(value)
        self.assertEqual(runner.compare(histories, value)["category"], "matched")
        rows = histories["directCore"]["transactions"]
        self.assertEqual([len(runner.common.hex_bytes(row["output"], "output")) for row in rows], [64, 32, 128, 128])
        self.assertEqual([runner.output_words(value, row) for row in rows], [2, 1, 4, 4])
        for index, tx in enumerate(value["transactions"]):
            prior = rows[index - 1]["committedStorage"] if index else histories["directCore"]["initialStorage"]
            self.assertTrue(runner.conforms(value, tx, rows[index], prior))
            self.assertEqual(runner.bytes_return_fields(value, tx, rows[index], prior), [])
        # tx-2 returns 33 bytes of (6 + 7 + 1) * K and (2 * K) xor 5, past the
        # revert of tx-1, which wrote no slot; the rest of its last Word is zero.
        output = runner.common.hex_bytes(rows[2]["output"], "output")
        self.assertEqual(output[:64], (32).to_bytes(32, "big") + (33).to_bytes(32, "big"))
        self.assertEqual(output[64:97], (14 * MULTIPLIER % 2**256).to_bytes(32, "big") +
                         ((2 * MULTIPLIER % 2**256) ^ 5).to_bytes(32, "big")[:1])
        self.assertEqual(output[97:], bytes(31))
        prior, tx = rows[1]["committedStorage"], value["transactions"][2]
        for slot in ("1", "2"):
            changed = copy.deepcopy(rows[2])
            entry = next(item for item in changed["committedStorage"] if item["slot"] == slot)
            entry["value"] = str(int(entry["value"]) + 1)
            with self.subTest(slot=slot):
                self.assertIn("committedStorage", runner.bytes_return_fields(value, tx, changed, prior))
        # The offset, the length, a data byte and a padding byte are each checked.
        for position in (31, 63, 64, 96, 97, 127):
            changed = copy.deepcopy(rows[2])
            broken = bytearray(output)
            broken[position] ^= 1
            changed["output"] = "0x" + broken.hex()
            with self.subTest(position=position):
                self.assertEqual(runner.bytes_return_fields(value, tx, changed, prior), ["output"])
                self.assertFalse(runner.conforms(value, tx, changed, prior))
        # A truncated or extended value breaks the length rule and the protocol.
        for changed_output in (rows[2]["output"][:-64], rows[2]["output"] + "00" * 32, rows[2]["output"] + "00"):
            changed = {**rows[2], "output": changed_output}
            with self.subTest(length=len(changed_output)):
                self.assertFalse(runner.conforms(value, tx, changed, prior))
                self.assertEqual(runner.bytes_return_fields(value, tx, changed, prior), ["output"])
        # A revert is checked by rollback and its one-Word length, not by the protocol.
        self.assertEqual(runner.bytes_return_fields(value, value["transactions"][1], {**rows[1], "output": "0x" + "00" * 32},
                                                    rows[0]["committedStorage"]), [])
        self.assertFalse(runner.conforms(value, value["transactions"][1], {**rows[1], "output": rows[1]["output"] + "00" * 32},
                                         rows[0]["committedStorage"]))

    def test_a_protocol_break_on_every_path_is_a_mismatch_although_the_paths_agree(self):
        value = bytes_return_case()
        for options in ({"padding": 1}, {"revert_words": 2}):
            broken = bytes_return_histories(value, **options)
            result = runner.compare(broken, value)
            with self.subTest(options=options):
                self.assertEqual(result["category"], "semantic-mismatch")
                self.assertTrue(all(result["pairs"].values()))
                self.assertIn("output", result["fields"])
        # Shorter lengths on every path of the case are a mismatch too.
        short = bytes_return_histories(bytes_return_case(rows=((0, 5, 0), (1, 9, 31), (2, 7, 32), (0, 3, 64))))
        result = runner.compare(short, value)
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-2"))
        self.assertTrue(all(result["pairs"].values()))
        # A different step on one path is an ordinary difference.
        changed = bytes_return_histories(value)
        changed["rustEvm"] = bytes_return_history(value, "rustEvm", step=lambda x: x + 2)
        result = runner.compare(changed, value)
        self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-0"))
        self.assertFalse(result["pairs"]["directCore/rustEvm"])
        self.assertIn("committedStorage", result["fields"])


if __name__ == "__main__":
    unittest.main()
