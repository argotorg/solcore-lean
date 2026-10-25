#!/usr/bin/env python3
"""Protocol tests with explicit history fixtures, not a contract execution oracle.

The hand-written histories exercise comparison and transport policy. Actual
Core/Hull/EVM execution is covered by the external suite and fixed campaigns.
"""
from contextlib import redirect_stdout, redirect_stderr
import copy
import io
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("call_differential", ROOT / "scripts/semantic-call-differential.py")
adapter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(adapter)
BINDINGS = {"schema": adapter.BINDINGS_SCHEMA, "caller": "1", "parent": "101", "child": "102"}


def case():
    return {"schema": adapter.CASE_SCHEMA, "callPlan": {"schema": "solcore-lean.call-plan.v1", "stepProgram": {}},
        "programs": {"parent": {}, "child": {}}, "source": "protocol fixture only; no checked AST",
        "contracts": adapter.contract_metadata(), "observedSlots": ["0", "1"],
        "initialState": {"accounts": [{"role": "parent", "balance": "8", "storage": []},
            {"role": "child", "balance": "0", "storage": []}], "callerBalance": "0"},
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "transactions": [{"id": f"tx-{index}", "input": str(value), "target": "parent", "callee": "child", "value": "0"}
            for index, value in enumerate((4, 5, 6))]}


def word(value):
    return "0x" + f"{value:064x}"


def account_rows(parent_balance, parent_slots, child_balance, child_slots):
    return [{"role": role, "address": BINDINGS[role], "balance": str(balance),
        "storage": [{"slot": str(index), "value": str(value)} for index, value in enumerate(slots)]}
        for role, balance, slots in (("parent", parent_balance, parent_slots), ("child", child_balance, child_slots))]


def event(role, topic, payload):
    return {"address": BINDINGS[role], "topics": [str(topic)], "data": word(payload)}


def history():
    after_first = account_rows(7, (4, 4), 1, (4, 1))
    after_second = account_rows(7, (9, 10), 1, (4, 1))
    return {"schema": adapter.HISTORY_SCHEMA, "initialAccounts": adapter.initial_accounts(BINDINGS),
        "transactions": [
            {"id": "tx-0", "index": 0, "status": "returned", "output": word(8), "committedAccounts": after_first,
                "logs": [event("parent", 1, 4), event("child", 2, 4), event("parent", 3, 4)]},
            {"id": "tx-1", "index": 1, "status": "returned", "output": word(19), "committedAccounts": after_second,
                "logs": [event("parent", 1, 9), event("parent", 3, 10)]},
            {"id": "tx-2", "index": 2, "status": "reverted", "output": word(25), "committedAccounts": copy.deepcopy(after_second), "logs": []}],
        "finalAccounts": copy.deepcopy(after_second), "status": "complete", "unexecuted": []}


def histories():
    return {path: history() for path in adapter.PATHS}


class EnvelopeTests(unittest.TestCase):
    def test_roles_and_actual_address_binding_define_the_abi(self):
        adapter.validate_case(case())
        adapter.validate_bindings(BINDINGS)
        self.assertEqual(adapter.calldata(BINDINGS, case()["transactions"][0]), "0x7357f5d2" + f"{102:064x}{4:064x}")
        for value in ("0", "9", "10", "17", "256", str(2**160), "0101", BINDINGS["caller"], BINDINGS["child"]):
            with self.subTest(value=value), self.assertRaises(ValueError):
                adapter.validate_bindings({**BINDINGS, "parent": value})
        for field, value in (("callee", "parent"), ("value", "1"), ("input", "01"), ("id", "../tx")):
            invalid = case()
            invalid["transactions"][0][field] = value
            with self.subTest(field=field), self.assertRaises((ValueError, adapter.Finding)):
                adapter.validate_case(invalid)

    def test_constructor_funding_and_initial_state_are_fixed(self):
        invalid = case()
        invalid["contracts"]["parent"]["constructorValue"] = "0"
        with self.assertRaises(ValueError):
            adapter.validate_case(invalid)
        invalid = case()
        invalid["initialState"]["accounts"][0]["balance"] = "9"
        with self.assertRaises(adapter.Finding):
            adapter.validate_case(invalid)
        invalid = case()
        invalid["transactions"][0]["calldata"] = "0x"
        with self.assertRaises(ValueError):
            adapter.validate_case(invalid)


class ComparisonTests(unittest.TestCase):
    def test_return_child_rollback_and_root_rollback_history_matches(self):
        self.assertEqual(adapter.compare(histories(), case(), BINDINGS)["category"], "matched")

    def test_balance_and_slot_differences_are_visible_before_later_convergence(self):
        for role in (0, 1):
            for field in ("balance", "storage"):
                data = histories()
                account = data["rustEvm"]["transactions"][0]["committedAccounts"][role]
                if field == "balance":
                    account[field] = "99"
                else:
                    account[field][1]["value"] = "99"
                result = adapter.compare(data, case(), BINDINGS)
                self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-0"))
                self.assertIn("committedAccounts", result["fields"])

    def test_log_order_topics_payload_and_emitter_are_observable(self):
        edits = (lambda logs: logs.reverse(), lambda logs: logs[1].update(topics=["9"]),
                 lambda logs: logs[1].update(data=word(9)), lambda logs: logs[1].update(address="101"))
        for edit in edits:
            data = histories()
            edit(data["importedHull"]["transactions"][0]["logs"])
            result = adapter.compare(data, case(), BINDINGS)
            self.assertEqual((result["category"], result["transactionId"], result["fields"]),
                             ("semantic-mismatch", "tx-0", ["logs"]))

    def test_root_revert_cannot_commit_accounts_or_logs_even_if_all_paths_agree(self):
        for field in ("committedAccounts", "logs"):
            data = histories()
            for observed in data.values():
                last = observed["transactions"][-1]
                if field == "logs":
                    last[field] = [event("parent", 3, 25)]
                else:
                    last[field][0]["balance"] = "6"
                    observed["finalAccounts"] = copy.deepcopy(last[field])
            result = adapter.compare(data, case(), BINDINGS)
            self.assertEqual((result["category"], result["transactionId"]), ("semantic-mismatch", "tx-2"))
            self.assertIn(field, result["fields"])
            self.assertTrue(all(result["pairs"].values()))

    def test_unknown_completion_has_no_final_account_snapshot_and_keeps_prior_difference(self):
        data = histories()
        evm = data["rustEvm"]
        evm["transactions"] = evm["transactions"][:1]
        evm.update(status="incomplete", finalAccounts=None, unobserved=["tx-1"], unexecuted=["tx-2"])
        self.assertEqual(adapter.compare(data, case(), BINDINGS)["category"], "inconclusive-resource")
        evm["transactions"][0]["output"] = word(9)
        self.assertEqual(adapter.compare(data, case(), BINDINGS)["transactionId"], "tx-0")
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            adapter.save(output / "case.json", case())
            failure = {"category": "inconclusive-resource", "stage": "evm-submission", "pairs": {}}
            result = adapter.interrupted_comparison(SimpleNamespace(output=output), {"histories": data, "bindings": BINDINGS}, failure)
            self.assertEqual(result["transactionId"], "tx-0")
            self.assertEqual(result["laterInterruption"], failure)
        evm["finalAccounts"] = evm["transactions"][0]["committedAccounts"]
        self.assertEqual(adapter.compare(data, case(), BINDINGS)["category"], "adapter-error")

    def test_incomplete_child_execution_cannot_be_a_completed_revert(self):
        data = histories()
        observed = data["directCore"]
        observed["transactions"] = observed["transactions"][:2]
        observed["transactions"][-1].update(status="out-of-fuel", logs=None)
        observed.update(status="incomplete", unexecuted=["tx-2"])
        self.assertEqual(adapter.compare(data, case(), BINDINGS)["category"], "inconclusive-resource")


class ReceiptTests(unittest.TestCase):
    def test_both_hull_constructor_receipts_verify_the_exact_linked_runtime(self):
        runtimes = {"parent": b"\x60\x01", "child": b"\x60\x02"}
        rows = [{"stage": "deployment-" + role, "status": "returned", "output": "0x" + runtimes[role].hex(),
                 "imageVerified": True, "codeBytes": 2} for role in ("child", "parent")]
        rows += [{"stage": "initialization", "committedAccounts": adapter.initial_accounts(BINDINGS)}]
        rows += [{**row, "stage": "execution"} for row in history()["transactions"]]
        encode = lambda values: "\n".join(json.dumps(row) for row in values)
        self.assertEqual(adapter.hull_history(encode(rows), 0, case(), BINDINGS, runtimes)["status"], "complete")
        for index in (0, 1):
            for field, value in (("imageVerified", False), ("imageVerified", None), ("codeBytes", 1), ("output", "0x6003")):
                invalid = copy.deepcopy(rows)
                invalid[index][field] = value
                with self.subTest(index=index, field=field), self.assertRaises(ValueError):
                    adapter.hull_history(encode(invalid), 0, case(), BINDINGS, runtimes)

    def test_nested_resource_failure_is_not_hidden_by_a_returning_parent(self):
        result = adapter.trace_result({"status": "0x1"}, {"failed": False, "returnValue": word(1),
            "structLogs": [{"depth": 2, "op": "SSTORE", "error": "out of gas"}, {"depth": 1, "op": "RETURN"}]})
        self.assertEqual(result["status"], "out-of-gas")

    def test_mined_logs_belong_to_the_exact_transaction_and_block(self):
        receipt = {"transactionHash": "0x" + "ab" * 32, "blockNumber": "0x3", "logs": []}
        log = {"address": "0x" + f"{102:040x}", "topics": [word(2)], "data": word(4),
               "transactionHash": receipt["transactionHash"], "blockNumber": "0x3", "removed": False}
        receipt["logs"] = [log]
        self.assertEqual(adapter.evm_logs(receipt), [event("child", 2, 4)])
        for field, changed in (("removed", True), ("blockNumber", "0x2"), ("transactionHash", "0x" + "00" * 32), ("topics", ["0x01"])):
            invalid = copy.deepcopy(receipt)
            invalid["logs"][0][field] = changed
            with self.subTest(field=field), self.assertRaises(ValueError):
                adapter.evm_logs(invalid)



class BackendTests(unittest.TestCase):
    """Backend selection policy only; mocked execution is not an EVM result."""

    def invoke(self, directory, *, backend=None, saved=None):
        source = directory / "case.json"
        source.write_text(json.dumps(case()))
        output = directory / "run"
        arguments = ["adapter", "--output", str(output)]
        if saved is not None:
            (directory / "report.json").write_text(json.dumps(saved))
            arguments += ["--replay", str(directory)]
        else:
            arguments += ["--case", str(source)]
        if backend is not None:
            arguments += ["--backend", backend]
        captured = []
        def executed(args, report):
            captured.append((args.backend, report["backend"]))
            report["comparison"] = {"category": "matched", "pairs": {}}
        with patch.object(sys, "argv", arguments), patch.object(adapter, "execute", side_effect=executed), redirect_stdout(io.StringIO()):
            code = adapter.main()
        return code, captured, json.loads((output / "report.json").read_text())

    def test_default_and_explicit_backends_are_recorded(self):
        for explicit, expected in ((None, "sonatina-o0"), ("sonatina-o2", "sonatina-o2")):
            with self.subTest(backend=explicit), tempfile.TemporaryDirectory() as temporary:
                code, captured, report = self.invoke(Path(temporary), backend=explicit)
                self.assertEqual(code, 0)
                self.assertEqual(captured, [(expected, expected)])
                self.assertEqual(report["backend"], expected)

    def test_exact_replay_inherits_o2_and_legacy_o0(self):
        for saved, expected in (({}, "sonatina-o0"), ({"backend": "sonatina-o2"}, "sonatina-o2")):
            with self.subTest(saved=saved), tempfile.TemporaryDirectory() as temporary:
                _, captured, report = self.invoke(Path(temporary), saved=saved)
                self.assertEqual(captured, [(expected, expected)])
                self.assertEqual(report["backend"], expected)

    def test_exact_replay_backend_change_or_null_is_rejected_before_execution(self):
        for saved, explicit in (({}, "sonatina-o2"), ({"backend": "sonatina-o2"}, "sonatina-o0"),
                                ({"backend": None}, None), ({"backend": "yul"}, None)):
            with self.subTest(saved=saved, explicit=explicit), tempfile.TemporaryDirectory() as temporary:
                directory = Path(temporary)
                with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as caught:
                    self.invoke(directory, backend=explicit, saved=saved)
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
            with patch.object(adapter.common, "Runner", return_value=fake), \
                 patch.object(adapter.common, "checked_process", side_effect=checked), \
                 patch.object(adapter.common, "validate_export", side_effect=ValueError("test stops before execution")) as validate:
                with self.assertRaisesRegex(ValueError, "test stops before execution"):
                    adapter.execute(args, report)
            image_command = next(command for stage, command in commands if stage == "rust-code-images")
            self.assertEqual(image_command[image_command.index("--optimization") + 1], "O2")
            hull_command = next(command for stage, command in commands if stage == "rust-checked-source")
            self.assertNotIn("--optimization", hull_command)
            self.assertEqual(validate.call_args.kwargs["backend"], "sonatina-o2")
            self.assertEqual(report["backend"], "sonatina-o2")


if __name__ == "__main__":
    unittest.main()
