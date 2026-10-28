#!/usr/bin/env python3
"""Fixture cross-path harness tests; no compiler, Lean runner or EVM is executed."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import stat
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("semantic_fixtures", ROOT / "scripts/semantic-fixtures.py")
fixtures = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fixtures)
U256 = 2**256


def word(value: int) -> bytes:
    return (value % U256).to_bytes(32, "big")


def selector(signature: str) -> bytes:
    return fixtures.storage.keccak256(signature.encode())[:4]


def step(kind="raw", calldata="0x", value=0, index=1, expected=None):
    return {"index": index, "kind": kind, "label": "test", "calldata": calldata, "value": value,
            "caller": fixtures.scenario.RAW_SENDER, "persist": kind != "call", "gas": fixtures.RAW_GAS,
            "expected": expected or {"status": "returned", "output": None}}


def observation(status="returned", output="0x", logs=(), storage=None, balances=None):
    return {"status": status, "output": output, "logs": list(logs), "storage": storage or {},
            "balances": balances or {"1": "0"}}


class InventoryAndStreamTests(unittest.TestCase):
    def test_the_two_parity_manifests_pin_all_168_fixtures_once(self):
        inventory = fixtures.inventory()
        raw = [item for item in inventory if item["mode"] == "raw"]
        self.assertEqual((len(inventory), len(raw)), (168, 72))
        self.assertEqual((sum(item["calls"] for item in raw), sum(item["calls"] for item in inventory) - 626), (626, 618))
        self.assertEqual(len({item["id"] for item in inventory}), 168)
        basic = next(item for item in inventory if item["id"] == "basic")
        self.assertEqual((basic["fuel"], basic["availableGas"]), (15000000, "30000000"))
        self.assertEqual(next(item for item in inventory if item["id"] == "00answer")["fuel"], fixtures.DEFAULT_FUEL)

    def test_streams_are_reference_splitmix64_and_seeds_depend_on_every_part(self):
        stream = fixtures.Stream(0)
        self.assertEqual([stream.next(), stream.next()], [0xE220A8397B1DCDAF, 0x6E789E6AA1B965F4])
        seeds = {fixtures.derive(1, "a", 0), fixtures.derive(1, "a", 1), fixtures.derive(1, "b", 0), fixtures.derive(2, "a", 0)}
        self.assertEqual(len(seeds), 4)
        self.assertEqual(fixtures.derive(7, "x", 3), fixtures.derive(7, "x", 3))
        self.assertLess(fixtures.Stream(5).word(), U256)


class ClassificationTests(unittest.TestCase):
    def test_standard_types_parse_and_derived_spellings_do_not(self):
        cases = {"uint256": "uint256", "uint": "uint256", "word": "uint256", "int8": "int8", "address": "address",
                 "bool": "bool", "bytes4": "bytes4", "bytes": "bytes", "string": "string", "uint256[]": "uint256[]",
                 "address[3][]": "address[3][]"}
        for text, expected in cases.items():
            self.assertEqual(fixtures.canonical(fixtures.abi_type({"type": text})), expected)
        pair = {"type": "tuple[]", "components": [{"type": "uint256"}, {"type": "bytes"}]}
        self.assertEqual(fixtures.canonical(fixtures.abi_type(pair)), "(uint256,bytes)[]")
        for text in ("DynSum[]", "Batch", "uint7", "bytes33", "tuple"):
            node = fixtures.abi_type({"type": text, "components": [{"type": "Opt"}]})
            self.assertIsNone(node, text)
        node = fixtures.abi_type({"type": "uint256[2]"})
        self.assertEqual((fixtures.dynamic(node), fixtures.head_size(node)), (False, 64))
        self.assertTrue(fixtures.dynamic(fixtures.abi_type(pair)))

    def test_offsets_lengths_leaves_and_content_words_are_located(self):
        nodes = [fixtures.abi_type({"type": "address"}), fixtures.abi_type({"type": "bytes"}),
                 fixtures.abi_type({"type": "uint256[]"})]
        body = word(7) + word(96) + word(192) + word(33) + bytes(32) + b"\xaa" + bytes(31) + word(1) + word(9)
        classes = fixtures.classify(body, nodes)
        self.assertEqual({index: fixtures.class_label(value) for index, value in classes.items()},
                         {0: "leaf:address", 1: "offset", 2: "offset", 3: "length", 4: "content", 5: "content",
                          6: "length", 7: "leaf:uint256"})
        # Unpadded content shorter than a word stays outside the word grid.
        short = word(32) + word(2) + b"\xaa\xbb"
        self.assertEqual(fixtures.classify(short, [fixtures.abi_type({"type": "bytes"})]), {0: ("offset",), 1: ("length",)})
        for broken in (word(64), word(32) + word(5), word(31) + word(0), b""):
            with self.assertRaises(ValueError):
                fixtures.classify(broken, [fixtures.abi_type({"type": "bytes"})])

    def test_steps_take_classes_only_from_a_standard_method_with_their_selector(self):
        abi = [{"type": "function", "name": "f", "inputs": [{"type": "bool"}, {"type": "bytes4"}]},
               {"type": "function", "name": "g", "inputs": [{"type": "DynSum[]"}]},
               {"type": "constructor", "inputs": [{"type": "uint256"}]}]
        call = step(calldata="0x" + (selector("f(bool,bytes4)") + word(1) + word(0x12 << 248)).hex())
        classes, origin = fixtures.step_classes(call, abi)
        self.assertEqual((origin, [fixtures.class_label(classes[index]) for index in (0, 1)]), ("abi", ["leaf:bool", "leaf:bytes4"]))
        derived = step(calldata="0x" + (selector("g(sum(uint256,bytes)[])") + word(32)).hex())
        self.assertEqual(fixtures.step_classes(derived, abi), (None, "no standard-ABI method with this selector"))
        malformed = step(calldata="0x" + (selector("f(bool,bytes4)") + word(1)).hex())
        self.assertIsNone(fixtures.step_classes(malformed, abi)[0])
        self.assertEqual(fixtures.step_classes(step(calldata="0x01"), abi), (None, "no selector"))
        deploy = step(kind="deploy", calldata="0x" + word(3).hex(), index=0)
        self.assertEqual(fixtures.class_label(fixtures.step_classes(deploy, abi)[0][0]), "leaf:uint256")


class MutationTests(unittest.TestCase):
    def test_boundary_words_follow_each_class_and_never_repeat_the_recorded_word(self):
        address = ("leaf", ("address",))
        self.assertEqual(fixtures.boundary_values(address, 1, 64), [0, 2**160 - 1, 2**160, U256 - 1])
        self.assertEqual(fixtures.boundary_values(("leaf", ("bool",)), 0, 32), [1, 2, U256 - 1])
        fixed = fixtures.boundary_values(("leaf", ("fixed", 4)), 0x12345678 << 224, 32)
        self.assertIn(0x12345678, fixed)
        self.assertIn((0x12345678 << 224) | 1, fixed)
        self.assertEqual(fixtures.boundary_values(("length",), 2, 96), [0, 1, 3, 2**32, 2**64, U256 - 1])
        offset = fixtures.boundary_values(("offset",), 32, 96)
        self.assertEqual(offset[:4], [0, 64, 33, 96])
        for value in fixtures.boundary_values(("unclassified",), 0, 32):
            self.assertNotEqual(value, 0)
        self.assertEqual(fixtures.seeded_value(("leaf", ("bool",)), 7), 1)
        self.assertLess(fixtures.seeded_value(address, U256 - 1), 2**160)
        self.assertEqual(fixtures.seeded_value(("leaf", ("int", 8)), 255), U256 - 1)

    def test_candidates_cover_every_family_and_sampling_is_seeded_and_bounded(self):
        abi = [{"type": "function", "name": "h", "inputs": [{"type": "address"}, {"type": "bytes"}]}]
        data = selector("h(address,bytes)") + word(5) + word(64) + word(1) + (b"\x01" + bytes(31))
        recorded = step(calldata="0x" + data.hex(), value=0)
        classes, _ = fixtures.step_classes(recorded, abi)
        families = fixtures.candidates(recorded, classes, fixtures.Stream(9))
        self.assertEqual(sorted(families), ["content", "frame", "leaf", "length", "offset", "seeded"])
        self.assertEqual(families["frame"][-1], {"operator": "value", "recorded": 0, "value": 1})
        self.assertEqual([item["operator"] for item in families["frame"]],
                         ["truncate", "truncate", "extend-zero", "extend-ones", "drop-arguments", "value"])
        drawn = fixtures.sample(families, fixtures.Stream(3), 4)
        again = fixtures.sample(fixtures.candidates(recorded, classes, fixtures.Stream(9)), fixtures.Stream(3), 4)
        self.assertEqual(drawn, again)
        self.assertEqual(len(drawn), 4)
        self.assertEqual(len({json.dumps(item, sort_keys=True) for item in drawn}), 4)
        everything = fixtures.sample(families, fixtures.Stream(3), 10**6)
        self.assertEqual(len(everything), sum(len(items) for items in families.values()))
        typed = step(kind="call", calldata="0x" + (selector("h(address,bytes)") + word(5)).hex())
        self.assertNotIn("value", [item["operator"] for item in fixtures.candidates(typed, None, fixtures.Stream(1))["frame"]])

    def test_each_mutant_changes_one_word_the_length_or_the_value_and_keeps_the_selector(self):
        head = selector("k(uint256)")
        recorded = step(calldata="0x" + (head + word(7)).hex(), value=3)
        changed = fixtures.apply(recorded, {"operator": "word", "word": 0, "value": hex(9)})
        self.assertEqual(changed["calldata"], "0x" + (head + word(9)).hex())
        self.assertEqual(fixtures.apply(recorded, {"operator": "truncate", "bytes": 1})["calldata"],
                         "0x" + (head + word(7))[:-1].hex())
        self.assertEqual(fixtures.apply(recorded, {"operator": "extend-ones", "bytes": 32})["calldata"],
                         "0x" + (head + word(7) + b"\xff" * 32).hex())
        self.assertEqual(fixtures.apply(recorded, {"operator": "drop-arguments", "bytes": 32})["calldata"], "0x" + head.hex())
        self.assertEqual(fixtures.apply(recorded, {"operator": "value", "value": 0})["value"], 0)
        with self.assertRaises(ValueError):
            fixtures.apply(recorded, {"operator": "truncate", "bytes": 33})
        with self.assertRaises(ValueError):
            fixtures.apply(recorded, {"operator": "word", "word": 1, "value": "0x0"})
        constructor = step(kind="deploy", calldata="0x" + word(1).hex(), index=0)
        self.assertEqual(fixtures.apply(constructor, {"operator": "word", "word": 0, "value": "0x2"})["calldata"],
                         "0x" + word(2).hex())


class ObservationTests(unittest.TestCase):
    chain = {"address": "0x" + "00" * 19 + "0a", "accounts": [("0x" + "00" * 19 + "0b", 5)]}

    def test_core_receipts_keep_only_nonzero_storage_and_the_compared_balances(self):
        row = {"stage": "execution", "status": "returned", "output": "0x01", "logs": [{"address": "10", "topics": [], "data": "0x"}],
               "storage": [["0", "4"], ["1", "0"]], "balances": [["10", "2"], ["99", "1"]],
               "world": [{"address": "10", "storage": [["0", "3"]]}, {"address": "12", "storage": [["5", "6"], ["6", "0"]]}]}
        observed = fixtures.hull_observation(row, self.chain)
        self.assertEqual(observed["storage"], {"12": {"5": "6"}, "10": {"0": "4"}})
        self.assertEqual(observed["balances"], {"10": "2", "11": "0"})
        self.assertEqual(fixtures.hull_observation({"status": "invalid"}, self.chain)["output"], "0x")
        self.assertEqual(fixtures.hull_observation({"status": "out-of-fuel", "detail": "x"}, self.chain),
                         {"status": "out-of-fuel", "detail": "x"})
        reverted = fixtures.hull_observation({"status": "reverted", "output": "0x08"}, self.chain)
        self.assertNotIn("storage", reverted)

    def test_evm_outcomes_separate_revert_exceptional_halts_and_gas(self):
        self.assertEqual(fixtures.evm_status({"status": "0x1"}, {}), "returned")
        self.assertEqual(fixtures.evm_status({"status": "0x0"}, {"error": "execution reverted"}), "reverted")
        self.assertEqual(fixtures.evm_status({"status": "0x0"}, {"error": "invalid opcode: INVALID"}), "exceptional")
        self.assertEqual(fixtures.evm_status({"status": "0x0"}, {"error": "out of gas"}), "out-of-gas")

    def test_paths_agree_only_on_every_compared_field(self):
        same = {path: observation(output="0x2a") for path in fixtures.PATHS}
        self.assertEqual(fixtures.agreement(same, False)["status"], "agree")
        different = dict(same, yul=observation(output="0x2b"))
        result = fixtures.agreement(different, False)
        self.assertEqual((result["status"], result["fields"], result["groups"]),
                         ("disagree", ["output"], [["hull", "sonatina-o0", "sonatina-o2"], ["yul"]]))
        self.assertEqual(fixtures.agreement(different, True)["status"], "agree")  # deployments return code bytes
        logs = dict(same, hull=observation(output="0x2a", logs=[{"address": "1", "topics": [], "data": "0x"}]))
        self.assertEqual(fixtures.agreement(logs, False)["fields"], ["logs"])
        fuel = dict(same, hull={"status": "out-of-fuel"})
        self.assertEqual((fixtures.agreement(fuel, False)["status"], fixtures.agreement(fuel, False)["inconclusive"]),
                         ("incomplete", ["hull"]))
        fault = dict(same, hull={"status": "core-fault"})
        self.assertEqual(fixtures.agreement(fault, False)["failed"], ["hull"])
        halted = dict(same, yul={"status": "exceptional", "output": "0x", "logs": []})
        self.assertEqual(fixtures.agreement(halted, False)["fields"], ["status", "output", "storage", "balances"])

    def test_expectations_follow_upstream_raw_and_typed_rules(self):
        returned = step(expected={"status": "returned", "output": "0x2a"})
        self.assertEqual(fixtures.expectation(returned, observation(output="0x2a"), True), "match")
        self.assertEqual(fixtures.expectation(returned, observation(output="0x2b"), True), "mismatch")
        any_revert = step(expected={"status": "reverted", "output": None})
        self.assertEqual(fixtures.expectation(any_revert, observation("reverted", "0x01"), False), "match")
        self.assertEqual(fixtures.expectation(any_revert, observation("exceptional"), True), "match")
        self.assertEqual(fixtures.expectation(any_revert, observation("exceptional"), False), "mismatch")
        exact = step(expected={"status": "reverted", "output": "0x7f52b2bf"})
        self.assertEqual(fixtures.expectation(exact, observation("reverted", "0x"), True), "mismatch")
        self.assertEqual(fixtures.expectation(exact, {"status": "timeout"}, True), "inconclusive")
        self.assertEqual(fixtures.expectation(exact, {"status": "not-executed"}, True), "not-executed")

    def test_findings_name_each_disagreement_failure_and_unmet_expectation(self):
        fixture = {"id": "f", "mode": "raw"}
        entry = {**step(expected={"status": "returned", "output": "0x2a"}), "id": "1", "step": 1}
        observed = {"hull": observation(output="0x2a"), "sonatina-o0": observation(output="0x2a"),
                    "sonatina-o2": observation(output="0x2b"), "yul": {"status": "evm-rejected", "detail": "funds"}}
        found = fixtures.entry_findings(fixture, entry, observed)
        self.assertEqual(sorted((item["category"], item.get("path")) for item in found),
                         [("expectation-mismatch", "sonatina-o2"), ("expectation-mismatch", "yul"),
                          ("path-failure", "yul"), ("path-mismatch", None)])
        mutant = {**entry, "id": "1.1", "mutant": {"operator": "value", "value": 1}}
        self.assertNotIn("expectation-mismatch", [item["category"] for item in fixtures.entry_findings(fixture, mutant, observed)])

    def test_a_hull_memory_range_failure_is_a_resource_limit_only_where_no_evm_path_completed(self):
        failure = {"status": "language-failure", "detail": fixtures.MEMORY_RANGE}
        gas = {"status": "out-of-gas", "detail": "out of gas"}
        limited = {"hull": failure, "sonatina-o0": gas, "sonatina-o2": gas, "yul": {"status": "resource-limit", "detail": "x"}}
        fixture = {"id": "f", "mode": "methods"}
        entry = {**step(kind="call"), "id": "1.1", "step": 1, "mutant": {"operator": "word"}}
        classified = fixtures.memory_range(limited)
        self.assertEqual(classified["hull"], {"status": "memory-range", "detail": fixtures.MEMORY_RANGE})
        self.assertEqual(fixtures.agreement(classified, False)["status"], "unobserved")
        self.assertEqual(fixtures.entry_findings(fixture, entry, classified), [])
        # An EVM path that returned, reverted or halted otherwise did not reach the access.
        for other in (observation(), observation("reverted", "0x01"), {"status": "exceptional", "output": "0x", "logs": []}):
            kept = fixtures.memory_range(dict(limited, yul=other))
            self.assertEqual(kept["hull"], failure)
            self.assertEqual([(item["category"], item["path"]) for item in fixtures.entry_findings(fixture, entry, kept)],
                             [("path-failure", "hull")])
        # Another failure reason, no EVM path, or one that never ran the entry keeps the failure as well.
        for observations in (dict(limited, hull={"status": "language-failure", "detail": "Solcore.Core.Value.word 7"}),
                             {"hull": failure}, dict(limited, yul={"status": "not-executed", "detail": "no deployment"})):
            self.assertEqual(fixtures.memory_range(observations), observations)

    def test_observing_classifies_each_entry_against_the_evm_paths_of_that_entry(self):
        run = fixtures.FixtureRun.__new__(fixtures.FixtureRun)
        run.args, run.fixture, run.prepared, run.chain, run.evm = None, {}, {}, {}, None
        run.admitted, run.bytecode = ["hull", "yul"], {"yul": (b"", b"")}
        failure = {"status": "language-failure", "detail": fixtures.MEMORY_RANGE}
        with patch.object(fixtures, "run_hull", return_value=[observation(), failure, failure]), \
                patch.object(fixtures, "run_evm", return_value=[observation(), {"status": "out-of-gas"}, observation()]):
            observed = run.observe(step(kind="deploy", index=0), [step(), step(index=2)])
        self.assertEqual([row["status"] for row in observed["hull"]], ["returned", "memory-range", "language-failure"])


class HullRunnerTests(unittest.TestCase):
    chain = {"address": "0x" + "00" * 19 + "0a", "accounts": []}

    def prepare(self, directory: Path, body: str) -> tuple[SimpleNamespace, dict]:
        hull_path = directory / "hull.json"
        hull_path.write_text(json.dumps({"program": {"objects": [{"name": "CDeploy", "inners": [{"name": "C", "inners": []}]}]}}))
        runner = directory / "runner"
        runner.write_text("#!" + sys.executable + "\nimport json, sys, time\nconfig = json.load(open(sys.argv[1]))\n" + body)
        runner.chmod(runner.stat().st_mode | stat.S_IXUSR)
        args = SimpleNamespace(hull_runner=runner, hull_timeout=30, hull_entry_timeout=30)
        return args, {"O0": {"hull": hull_path, "images": hull_path}}

    # Every call returns its own calldata; one calldata never finishes; each invocation is logged.
    ECHO = ("with open(sys.argv[0] + '.log', 'a') as log:\n    log.write(json.dumps([call['calldata'] for call in config['calls']]) + '\\n')\n"
            "print(json.dumps({'stage': 'deployment', 'status': 'returned', 'output': '0x00', 'storage': [], 'balances': [],"
            " 'world': [], 'logs': []}), flush=True)\n"
            "for index, call in enumerate(config['calls']):\n"
            "    if call['calldata'] == '0xdead':\n        time.sleep(60)\n"
            "    print(json.dumps({'stage': 'execution', 'index': index, 'status': 'returned', 'output': call['calldata'],"
            " 'storage': [], 'balances': [], 'world': [], 'logs': []}), flush=True)\n")

    def test_rows_are_ordered_and_missing_rows_keep_their_reason(self):
        with tempfile.TemporaryDirectory() as directory:
            rows = [{"stage": "deployment", "status": "returned", "output": "0x00", "storage": [], "balances": [], "world": [], "logs": []},
                    {"stage": "execution", "index": 0, "status": "reverted", "output": "0x01", "logs": []}]
            args, exports = self.prepare(Path(directory), "assert config['calls'][0]['persist'] is False and "
                                         "config['deployPath'] == ['CDeploy']\n"
                                         f"print('\\n'.join(json.dumps(row) for row in {rows!r}))\nsys.exit(1)\n")
            fixture = {"mode": "raw", "contract": "C", "fuel": 10, "availableGas": None}
            calls = [{**step(kind="call"), "persist": False}, step()]
            observed = fixtures.run_hull(args, fixture, exports, self.chain, step(kind="deploy", index=0), calls)
            self.assertEqual([item["status"] for item in observed], ["returned", "reverted", "core-runner-error"])
            args.hull_runner.write_text(args.hull_runner.read_text().replace("'index': 0", "'index': 4"))
            with self.assertRaisesRegex(ValueError, "result order"):
                fixtures.run_hull(args, fixture, exports, self.chain, step(kind="deploy", index=0), calls)

    def test_method_entries_run_alone_after_the_sends_before_them(self):
        with tempfile.TemporaryDirectory() as directory:
            args, exports = self.prepare(Path(directory), self.ECHO)
            fixture = {"mode": "methods", "contract": "C", "fuel": 10, "availableGas": None}
            entries = [step(kind="call", calldata="0x01"), step(kind="send", calldata="0x02"),
                       step(kind="call", calldata="0xdead"), step(kind="call", calldata="0x03")]
            args.hull_entry_timeout = 1
            observed = fixtures.run_hull(args, fixture, exports, self.chain, step(kind="deploy", index=0), entries)
            self.assertEqual([item["status"] for item in observed], ["returned", "returned", "returned", "timeout", "returned"])
            self.assertEqual([item["output"] for item in observed if item["status"] == "returned"], ["0x00", "0x01", "0x02", "0x03"])
            invocations = [json.loads(line) for line in Path(str(args.hull_runner) + ".log").read_text().splitlines()]
            self.assertEqual(invocations, [[], ["0x01"], ["0x02"], ["0x02", "0xdead"], ["0x02", "0x03"]])

    def test_a_raw_scenario_resumes_past_an_entry_that_stalls(self):
        with tempfile.TemporaryDirectory() as directory:
            args, exports = self.prepare(Path(directory), self.ECHO)
            fixture = {"mode": "raw", "contract": "C", "fuel": 10, "availableGas": None}
            entries = [step(calldata="0x01"), {**step(calldata="0xdead"), "persist": False}, step(calldata="0x02")]
            args.hull_timeout = 1
            observed = fixtures.run_hull(args, fixture, exports, self.chain, step(kind="deploy", index=0), entries)
            self.assertEqual([item["status"] for item in observed], ["returned", "returned", "timeout", "returned"])
            self.assertEqual((observed[1]["output"], observed[3]["output"]), ("0x01", "0x02"))
            invocations = [json.loads(line) for line in Path(str(args.hull_runner) + ".log").read_text().splitlines()]
            self.assertEqual(invocations, [["0x01", "0xdead", "0x02"], ["0x01", "0xdead", "0x02"], ["0x01", "0xdead"],
                                           ["0x01", "0x02"]])

    def test_a_buffering_runner_that_reports_nothing_is_resumed_entry_by_entry(self):
        with tempfile.TemporaryDirectory() as directory:
            args, exports = self.prepare(Path(directory), self.ECHO.replace(", flush=True", ""))
            fixture = {"mode": "raw", "contract": "C", "fuel": 10, "availableGas": None}
            entries = [step(calldata="0x01"), {**step(calldata="0xdead"), "persist": False}, step(calldata="0x02")]
            args.hull_timeout = 1
            observed = fixtures.run_hull(args, fixture, exports, self.chain, step(kind="deploy", index=0), entries)
            self.assertEqual([item["status"] for item in observed], ["returned", "returned", "timeout", "returned"])
            invocations = [json.loads(line) for line in Path(str(args.hull_runner) + ".log").read_text().splitlines()]
            self.assertEqual(invocations, [["0x01", "0xdead", "0x02"], [], ["0x01"], ["0x01", "0xdead", "0x02"],
                                           ["0x01", "0xdead"], ["0x01", "0x02"]])


class ReductionTests(unittest.TestCase):
    def run_for(self, observe):
        record = fixtures.FixtureRun.__new__(fixtures.FixtureRun)
        record.args = SimpleNamespace(reduction_runs=40, reduction_seconds=60)
        record.raw, record.admitted = True, ["hull", "yul"]
        record.steps = [step(kind="deploy", index=0)] + [step(index=index, calldata="0x" + (selector("k(uint256)") + word(index)).hex())
                                                       for index in (1, 2, 3)]
        record.observe = observe
        return record

    def test_reduction_drops_unneeded_steps_then_moves_the_word_toward_the_recorded_one(self):
        def observe(deploy, entries):
            last = entries[-1]
            needs_two = any(entry["index"] == 2 and "mutant" not in entry for entry in entries[:-1])
            value = int(last["calldata"][10:], 16)
            outputs = {"hull": "0x01", "yul": "0x02" if needs_two and value >= 1000 else "0x01"}
            return {path: [observation()] + [observation(output=outputs[path])] * len(entries) for path in self.paths}

        self.paths = ["hull", "yul"]
        run = self.run_for(observe)
        mutant = {"operator": "word", "class": "leaf:uint256", "word": 0, "recorded": hex(3), "value": hex(2**200)}
        target = {**fixtures.apply(run.steps[3], mutant), "id": "3.1", "step": 3, "persist": False, "mutant": mutant}
        observations = {path: rows[-1] for path, rows in observe(None, run.steps[1:3] + [target]).items()}
        finding = {"category": "path-mismatch", "entry": "3.1", "step": 3, "mutant": mutant,
                   "signature": fixtures.signature("path-mismatch", target, observations, True)}
        reduction = run.reduce(finding)
        self.assertEqual((reduction["status"], reduction["steps"]), ("reduced", [2]))
        self.assertEqual(int(reduction["mutant"]["value"], 16), 1000)

    def test_a_finding_that_does_not_recur_is_reported_as_such(self):
        self.paths = ["hull", "yul"]
        run = self.run_for(lambda deploy, entries: {path: [observation()] * (1 + len(entries)) for path in self.paths})
        finding = {"category": "path-mismatch", "entry": "2", "step": 2, "signature": ["path-mismatch", ["output"], []]}
        self.assertEqual(run.reduce(finding), {"status": "not-reproduced", "runs": 1})


class SummaryTests(unittest.TestCase):
    def test_excluded_fixtures_count_their_exclusions_and_nothing_else(self):
        excluded = {"id": "x", "admitted": None, "counts": None, "expectations": None, "findings": [],
                    "exclusions": [{"paths": list(fixtures.PATHS), "stage": "rust-checked-source", "reason": "compile-failure"}]}
        crashed = {"id": "y", "admitted": ["hull", "yul"], "findings": [{"category": "compiler-crash"}],
                   "counts": {"agree": 3, "disagree": 0, "incomplete": 1, "unobserved": 0, "recorded": 2, "mutants": 2},
                   "expectations": {"hull": {"match": 2, "mismatch": 0, "inconclusive": 0, "not-executed": 0}},
                   "statuses": {"hull": {"returned": 3, "memory-range": 1}, "yul": {"returned": 3, "out-of-gas": 1}},
                   "exclusions": [{"paths": ["sonatina-o2"], "stage": "rust-code-images-O2", "reason": "compiler-crash"}]}
        totals = fixtures.summarize([excluded, crashed, dict(crashed, exclusions=[], findings=[])])
        self.assertEqual(totals["statuses"], {"hull": {"returned": 6, "memory-range": 2}, "yul": {"returned": 6, "out-of-gas": 2}})
        totals = fixtures.summarize([excluded, crashed])
        self.assertEqual((totals["fixtures"], totals["admitted"]["hull"], totals["admitted"]["sonatina-o0"]), (2, 1, 0))
        self.assertEqual((totals["agree"], totals["incomplete"], totals["mutants"]), (3, 1, 2))
        self.assertEqual(totals["findings"], {"compiler-crash": 1})
        self.assertEqual(totals["exclusions"], {"rust-checked-source:compile-failure": 1,
                                                "rust-code-images-O2:compiler-crash": 1})
        self.assertEqual(totals["expectations"]["hull"]["match"], 2)


class CommandLineTests(unittest.TestCase):
    def test_modes_seeds_and_bounds_are_checked_before_any_work(self):
        for extra in (["--mode", "mutation"], ["--seed", "1"], ["--mode", "mutation", "--seed", "1", "--mutants", "0"],
                      ["--jobs", "0"]):
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                fixtures.main(["--output", "/nonexistent/out", *extra])
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            fixtures.main(["--fixture", "abi-*"])
        with contextlib.redirect_stdout(io.StringIO()) as listed:
            self.assertEqual(fixtures.main(["--list", "--fixture", "abi-*"]), 0)
        self.assertIn("abi-dyn-sum raw DynSumArr 3", listed.getvalue())
        with self.assertRaisesRegex(ValueError, "no pinned fixture"):
            fixtures.main(["--output", "/nonexistent/out", "--list", "--fixture", "missing-*"])


if __name__ == "__main__":
    unittest.main()
