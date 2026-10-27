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


def whole(accounts):
    """Fixture whole storage: both contracts' nonzero slot rows."""
    return [{"role": account["role"], "address": account["address"],
             "storage": [copy.deepcopy(entry) for entry in account["storage"] if entry["value"] != "0"]} for account in accounts]


def with_whole(value):
    """Add the whole committed storage that a fixture's account rows imply."""
    value["initialAccountStorage"] = whole(value["initialAccounts"])
    for row in value["transactions"]:
        row["accountStorage"] = whole(row["committedAccounts"])
    value["finalAccountStorage"] = None if value.get("finalAccounts") is None else whole(value["finalAccounts"])
    return value


def event(role, topic, payload):
    return {"address": BINDINGS[role], "topics": [str(topic)], "data": word(payload)}


def history():
    after_first = account_rows(7, (4, 4), 1, (4, 1))
    after_second = account_rows(7, (9, 10), 1, (4, 1))
    return with_whole({"schema": adapter.HISTORY_SCHEMA, "initialAccounts": adapter.initial_accounts(BINDINGS),
        "transactions": [
            {"id": "tx-0", "index": 0, "status": "returned", "output": word(8), "committedAccounts": after_first,
                "logs": [event("parent", 1, 4), event("child", 2, 4), event("parent", 3, 4)]},
            {"id": "tx-1", "index": 1, "status": "returned", "output": word(19), "committedAccounts": after_second,
                "logs": [event("parent", 1, 9), event("parent", 3, 10)]},
            {"id": "tx-2", "index": 2, "status": "reverted", "output": word(25), "committedAccounts": copy.deepcopy(after_second), "logs": []}],
        "finalAccounts": copy.deepcopy(after_second), "status": "complete", "unexecuted": []})


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

    def test_a_case_has_one_to_the_bound_of_transactions(self):
        for count in (1, adapter.MAX_TRANSACTIONS, 0, adapter.MAX_TRANSACTIONS + 1):
            value = case()
            value["transactions"] = [{**value["transactions"][0], "id": f"tx-{index}"} for index in range(count)]
            with self.subTest(count=count):
                if 1 <= count <= adapter.MAX_TRANSACTIONS:
                    adapter.validate_case(value)
                else:
                    with self.assertRaisesRegex(ValueError, "transactions"):
                        adapter.validate_case(value)


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
        evm.update(status="incomplete", finalAccounts=None, finalAccountStorage=None, unobserved=["tx-1"], unexecuted=["tx-2"])
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
        rows += [{"stage": "initialization", "committedAccounts": adapter.initial_accounts(BINDINGS),
                  "accountStorage": whole(adapter.initial_accounts(BINDINGS))}]
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

    def invoke(self, directory, *, backend=None, saved=...):
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

    def test_yul_cli_is_rejected_before_output_or_execution(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as caught:
                self.invoke(directory, backend="yul")
            self.assertEqual(caught.exception.code, 2)
            self.assertFalse((directory / "run").exists())

    def test_yul_programmatic_execution_and_saved_archive_have_no_fallback(self):
        args = SimpleNamespace(replay=None, backend="yul")
        with patch.object(adapter.common, "Runner") as execution:
            with self.assertRaisesRegex(ValueError, "stateful comparisons require a Sonatina backend"):
                adapter.execute(args, {})
            execution.assert_not_called()
        with patch.object(adapter.common, "verify_archive") as archive:
            with self.assertRaisesRegex(ValueError, "stateful comparisons require a Sonatina backend"):
                adapter.verify_archive(Path("unused"), {"schema": adapter.REPORT_SCHEMA, "backend": "yul"})
            archive.assert_not_called()

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


FORWARD_ENDOWMENT = 2**72


def forward_case(rows=((0, 7, 5), (1, 0, 2**70), (2, 1, 1))):
    """Envelope fixture only: native replay checks the actual forwarding programs."""
    return {"schema": adapter.FORWARD_CASE_SCHEMA, "forwardPlan": {"schema": "solcore-lean.forward-plan.v1", "stepProgram": {}},
        "programs": {"parent": {}, "child": {}}, "source": "protocol fixture only; no checked AST",
        "contracts": adapter.contract_metadata(True), "observedSlots": ["0", "1"],
        "initialState": {"accounts": [{"role": "parent", "balance": str(FORWARD_ENDOWMENT), "storage": []},
            {"role": "child", "balance": "0", "storage": []}], "callerBalance": str(2**80)},
        "provenance": {key: "protocol-test" for key in ("generatorVersion", "emitterVersion", "wrapperVersion")},
        "transactions": [{"id": f"tx-{index}", "input": str(given), "value": str(value), "amount": str(amount),
            "target": "parent", "callee": "child"} for index, (given, value, amount) in enumerate(rows)]}


def forward_history(value):
    """Rows that follow the forwarding protocol: slots zero are fixtures, the
    child's slot one is what it accepted and equals its balance, a child revert
    keeps the child and its amount with the parent, a root revert keeps both,
    and the balances sum to the endowment plus every committed call value."""
    parent, child = [FORWARD_ENDOWMENT, 0, 0], [0, 0, 0]
    rows = []
    for index, tx in enumerate(value["transactions"]):
        given, sent, amount = int(tx["input"]), int(tx["value"]), int(tx["amount"])
        if not given & 2:
            parent = [parent[0] + sent, index + 10, index + 20]
            if not given & 1:
                parent[0] -= amount
                child = [child[0] + amount, index + 30, child[2] + amount]
        rows.append({"id": tx["id"], "index": index, "status": "reverted" if given & 2 else "returned", "output": word(index + 3),
                     "committedAccounts": account_rows(parent[0], parent[1:], child[0], child[1:]), "logs": []})
    return with_whole({"schema": adapter.FORWARD_HISTORY_SCHEMA, "initialAccounts": adapter.initial_accounts(BINDINGS, True),
        "transactions": rows, "finalAccounts": copy.deepcopy(rows[-1]["committedAccounts"]), "status": "complete", "unexecuted": []})


def forward_histories(value=None):
    value = forward_case() if value is None else value
    return {path: forward_history(value) for path in adapter.PATHS}


class ForwardedValueTests(unittest.TestCase):
    def test_forward_case_requires_payable_bank_values_and_three_word_calldata(self):
        value = forward_case()
        adapter.validate_case(value)
        self.assertTrue(adapter.forwarding(value))
        self.assertFalse(adapter.forwarding(case()))
        self.assertEqual((adapter.profile(value)["caseTool"], adapter.profile(value)["coreRunner"]),
                         ("semantic-forward-tool", "rust-hull-forward-scenario"))
        # `cast calldata "run(uint256,uint256,uint256)" 102 5 1180591620717411303424`
        self.assertEqual(adapter.calldata(BINDINGS, {"input": "5", "amount": str(2**70)}),
                         "0x24b912e5" + f"{102:064x}{5:064x}" + "0" * 46 + "40" + "0" * 16)
        self.assertEqual(adapter.calldata(BINDINGS, case()["transactions"][0]), "0x7357f5d2" + f"{102:064x}{4:064x}")
        self.assertEqual(adapter.initial_accounts(BINDINGS, True)[0]["balance"], str(FORWARD_ENDOWMENT))
        adapter.validate_case(forward_case(rows=((0, 2**70, 2**70),) * 3))
        for field, changed in (("value", str(2**70 + 1)), ("amount", str(2**70 + 1)), ("amount", "05"), ("value", None),
                               ("callee", "parent"), ("input", "01")):
            invalid = forward_case()
            invalid["transactions"][0][field] = changed
            with self.subTest(field=field, changed=changed), self.assertRaises((ValueError, adapter.Finding)):
                adapter.validate_case(invalid)
        missing = forward_case()
        del missing["transactions"][0]["amount"]
        with self.assertRaises(ValueError):
            adapter.validate_case(missing)
        for change in (lambda v: v["contracts"]["parent"].update(constructorValue="8"),
                       lambda v: v.update(contracts=adapter.contract_metadata()),
                       lambda v: v.update(forwardPlan={"schema": "solcore-lean.call-plan.v1", "stepProgram": {}})):
            invalid = forward_case()
            change(invalid)
            with self.assertRaises(ValueError):
                adapter.validate_case(invalid)
        for change in (lambda v: v["initialState"].update(callerBalance="0"),
                       lambda v: v["initialState"]["accounts"][0].update(balance="8")):
            invalid = forward_case()
            change(invalid)
            with self.assertRaises(adapter.Finding):
                adapter.validate_case(invalid)
        legacy = case()
        legacy["transactions"][0]["amount"] = "1"
        with self.assertRaises(ValueError):
            adapter.validate_case(legacy)

    def test_forwarding_histories_match_and_refund_rules_hold_on_every_path(self):
        value = forward_case()
        self.assertEqual(adapter.compare(forward_histories(value), value, BINDINGS)["category"], "matched")
        # One path that kept a child-reverted forward differs pairwise and breaks the refund rule.
        for path in adapter.PATHS:
            observed = forward_histories(value)
            row = observed[path]["transactions"][1]
            parent, child = row["committedAccounts"]
            parent["balance"] = str(int(parent["balance"]) - 2**70)
            child["balance"] = str(int(child["balance"]) + 2**70)
            child["storage"][1]["value"] = str(int(child["storage"][1]["value"]) + 2**70)
            result = adapter.compare(observed, value, BINDINGS)
            with self.subTest(path=path):
                self.assertEqual((result["category"], result["transactionId"], result["fields"]),
                                 ("semantic-mismatch", "tx-1", ["committedAccounts"]))
                self.assertFalse(all(result["pairs"].values()))
        # All paths agreeing on a balance that breaks the accounting still fail.
        for name, change in (("child balance", lambda accounts: accounts[1].update(balance=str(int(accounts[1]["balance"]) + 1))),
                             ("conservation", lambda accounts: accounts[0].update(balance=str(int(accounts[0]["balance"]) + 1))),
                             ("child slot", lambda accounts: accounts[1]["storage"][1].update(value="6"))):
            agreed = forward_histories(value)
            for history in agreed.values():
                change(history["transactions"][0]["committedAccounts"])
            result = adapter.compare(agreed, value, BINDINGS)
            with self.subTest(change=name):
                self.assertTrue(all(result["pairs"].values()))
                self.assertEqual((result["category"], result["transactionId"], result["fields"]),
                                 ("semantic-mismatch", "tx-0", ["committedAccounts"]))
        logged = forward_histories(value)
        for history in logged.values():
            history["transactions"][0]["logs"] = [event("parent", 1, 4)]
        result = adapter.compare(logged, value, BINDINGS)
        self.assertEqual((result["category"], result["transactionId"], result["fields"]), ("semantic-mismatch", "tx-0", ["logs"]))
        legacy_endowment = forward_histories(value)
        for history in legacy_endowment.values():
            history["initialAccounts"] = adapter.initial_accounts(BINDINGS)
        self.assertEqual(adapter.compare(legacy_endowment, value, BINDINGS)["stage"], "initial-accounts")
        call_schema = forward_histories(value)
        call_schema["directCore"]["schema"] = adapter.HISTORY_SCHEMA
        self.assertEqual(adapter.compare(call_schema, value, BINDINGS)["category"], "adapter-error")
        # The nested-call profile keeps its eight-unit endowment and log rules.
        self.assertEqual(adapter.compare(histories(), case(), BINDINGS)["category"], "matched")

    def test_forward_hull_history_uses_its_schema_and_endowment(self):
        value = forward_case()
        runtimes = {"parent": b"\x60\x01", "child": b"\x60\x02"}
        rows = [{"stage": "deployment-" + role, "status": "returned", "output": "0x" + runtimes[role].hex(),
                 "imageVerified": True, "codeBytes": 2} for role in ("child", "parent")]
        rows += [{"stage": "initialization", "committedAccounts": adapter.initial_accounts(BINDINGS, True),
                  "accountStorage": whole(adapter.initial_accounts(BINDINGS, True))}]
        rows += [{**row, "stage": "execution"} for row in forward_history(value)["transactions"]]
        encode = lambda values: "\n".join(json.dumps(row) for row in values)
        history = adapter.hull_history(encode(rows), 0, value, BINDINGS, runtimes)
        self.assertEqual((history["schema"], history["status"]), (adapter.FORWARD_HISTORY_SCHEMA, "complete"))
        self.assertEqual(adapter.compare({**forward_histories(value), "importedHull": history}, value, BINDINGS)["category"], "matched")
        rejected = rows[:4] + [{"stage": "execution", "id": "tx-1", "index": 1, "status": "transfer-rejected",
                                "committedAccounts": rows[3]["committedAccounts"], "accountStorage": rows[3]["accountStorage"], "logs": None}]
        observed = adapter.hull_history(encode(rejected), 1, value, BINDINGS, runtimes)
        self.assertEqual(observed["status"], "incomplete")
        self.assertEqual(adapter.compare({**forward_histories(value), "importedHull": observed}, value, BINDINGS)["category"],
                         "execution-error")


def stray(value, index, role, slot="12345"):
    """Add one nonzero entry to a contract's whole storage in one fixture row."""
    row = value["transactions"][index]
    entries = next(account for account in row["accountStorage"] if account["role"] == role)["storage"]
    entries.append({"slot": slot, "value": "9"})
    entries.sort(key=lambda entry: int(entry["slot"]))
    if index == len(value["transactions"]) - 1:
        value["finalAccountStorage"] = copy.deepcopy(row["accountStorage"])


class WholeStorageTests(unittest.TestCase):
    """Both contracts' whole committed storage is compared after deployment and
    every transaction; root and child reverts keep the storage they roll back."""

    def test_stray_writes_are_classified_by_contract_and_absent_paths(self):
        for role in adapter.ROLES:
            for path in adapter.PATHS:
                data = histories()
                stray(data[path], 0, role)
                result = adapter.compare(data, case(), BINDINGS)
                with self.subTest(role=role, path=path):
                    self.assertEqual((result["category"], result["transactionId"], result["fields"]),
                                     ("semantic-mismatch", "tx-0", ["accountStorage"]))
                    self.assertEqual(result["accountStorageDifferences"],
                                     [{"account": role, "slot": "undeclared", "zeroPaths": [other for other in adapter.PATHS if other != path]}])
        data = histories()
        next(account for account in data["importedHull"]["transactions"][0]["accountStorage"] if account["role"] == "child")["storage"][0]["value"] = "7"
        self.assertEqual(adapter.compare(data, case(), BINDINGS)["accountStorageDifferences"],
                         [{"account": "child", "slot": "0", "zeroPaths": []}])

    def test_child_and_root_reverts_keep_the_whole_storage_they_roll_back(self):
        # tx-1 has an odd input, so its child reverts under a returned root; tx-2's root reverts.
        for index, role in ((1, "child"), (2, "parent"), (2, "child")):
            data = histories()
            for observed in data.values():
                stray(observed, index, role)
            result = adapter.compare(data, case(), BINDINGS)
            with self.subTest(index=index, role=role):
                self.assertEqual((result["category"], result["transactionId"], result["fields"]),
                                 ("semantic-mismatch", f"tx-{index}", ["accountStorage"]))
                self.assertEqual(result["accountStorageRollbackPaths"], list(adapter.PATHS))
                self.assertTrue(all(result["pairs"].values()))
        # A returned root keeps the parent's writes beside a child revert.
        data = histories()
        for observed in data.values():
            stray(observed, 1, "parent")
            for later in observed["transactions"][2:]:
                later["accountStorage"] = copy.deepcopy(observed["transactions"][1]["accountStorage"])
            observed["finalAccountStorage"] = copy.deepcopy(observed["transactions"][2]["accountStorage"])
        self.assertEqual(adapter.compare(data, case(), BINDINGS)["category"], "matched")

    def test_deployment_storage_is_empty_and_bound_to_both_contracts(self):
        data = histories()
        data["rustEvm"]["initialAccountStorage"][1]["storage"] = [{"slot": "3", "value": "1"}]
        result = adapter.compare(data, case(), BINDINGS)
        self.assertEqual((result["category"], result["stage"], result["fields"]), ("semantic-mismatch", "initial-accounts", ["accountStorage"]))
        self.assertEqual(result["accountStorageDifferences"], [{"account": "child", "slot": "undeclared", "zeroPaths": ["directCore", "importedHull"]}])
        for change in (lambda h: h["transactions"][0]["accountStorage"][0].update(address="999"),
                       lambda h: h["transactions"][0]["accountStorage"].reverse(),
                       lambda h: h.update(finalAccountStorage=None)):
            data = histories()
            change(data["importedHull"])
            self.assertEqual(adapter.compare(data, case(), BINDINGS)["category"], "adapter-error")


if __name__ == "__main__":
    unittest.main()
