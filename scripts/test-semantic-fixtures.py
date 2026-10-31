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
import threading
import time
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


# Declarations as the pinned extractor prints them: one field bare, several or none as a tuple.
def named(name, *args):
    return {"named": name, "qualifier": None, "args": list(args)}


def data(name, *constructors, params=()):
    return {"name": name, "params": list(params), "constructors": [
        {"name": ctor, "fields": types[0] if len(types) == 1 else {"tuple": list(types)}, "fieldCount": len(types),
         "fieldNames": None} for ctor, *types in constructors]}


def method(name, *types, public=True, kind="function"):
    return {"name": name, "kind": kind, "public": public, "payable": False, "returns": None,
            "params": [{"name": f"p{index}", "comptime": False, "type": item} for index, item in enumerate(types)]}


def declared(contract, datas=(), methods=(), aliases=(), local=()):
    return {"schema": "solcore-rs.declarations.v1", "imports": [["std"]], "data": list(datas), "aliases": list(aliases),
            "functions": [], "contracts": [{"name": contract, "params": [], "runtimeMain": False, "data": list(local),
                                            "aliases": [], "functions": list(methods)}]}


UINT, ADDRESS, BYTES32, BYTES = named("uint256"), named("address"), named("bytes32"), named("memory", named("bytes"))


def calldata_array(item):
    return named("calldata", named("array", item))


# The declarations and recorded calls of abi-sum-roundtrip, storage-adt-abi and abi-batch-adt.
SUMS = declared("SumRoundtrip", [data("D2", ("L", UINT), ("R", BYTES)), data("D3", ("X", UINT), ("Y", UINT), ("Z", BYTES)),
                                 data("S2", ("P", UINT), ("Q", UINT)), data("S3", ("A",), ("B", UINT), ("C", UINT, UINT, UINT))],
                [method("constructor", kind="constructor", public=False), method("rtD2", named("D2")), method("rtD3", named("D3")),
                 method("rtS3", named("S3")), method("rtS2", named("S2")), method("plain", UINT),
                 method("hidden", named("D2"), public=False)])
OPTION = declared("C", [data("Option", ("None",), ("Some", named("a")), params=["a"])],
                  [method("setOpt", named("Option", UINT)), method("getOpt"), method("echo", named("Option", UINT))])
BATCH = declared("BatchDecoder", [data("Operation", ("AddSigner", ADDRESS), ("RemoveSigner", ADDRESS)),
                                  data("Signature", ("ECDSA", BYTES32, BYTES32), ("Contract", ADDRESS)),
                                  data("Batch", ("Queue", named("Operation"), named("Signature")), ("Execute", UINT, BYTES))],
                 [method("queueSigner", calldata_array(named("Batch")), UINT),
                  method("execPayload", calldata_array(named("Batch")), UINT)])
D2_BLOB = ("0x219ee3fb0000000000000000000000000000000000000000000000000000000000000020"
           "86c01c8118a42b422dd5ce2f69a3259cf8ea4606b78834ab34f9c573e887ea81"
           "0000000000000000000000000000000000000000000000000000000000000040"
           "0000000000000000000000000000000000000000000000000000000000000002"
           "beef000000000000000000000000000000000000000000000000000000000000")
D2_UNKNOWN = "0x219ee3fb" + word(32).hex() + word(0).hex() + word(42).hex()
S3_NULLARY = "0xe096e642f446c1d0ceceeffa77e664bc78fba57853bda372d626a510062480375fa80e90" + word(0).hex() * 3
OPTION_NONE = "0x9e0708f2312343540cf19bad8e24ee12fb32c550e430a21136a53271f61c15371c880b91" + word(0).hex()
QUEUE_SIGNER = ("0x773db49a" + word(64).hex() + word(0).hex() + word(2).hex() + word(64).hex() + word(256).hex() +
                "f427fbe982814deabb25b520b94c8a4aacc13735a4565bc505272a7ea25e3deb"
                "637c77a2d598a51d085d4a2413332c45a235a25ee855bf3dfcdc2c8fcf02860f" + word(0xaa).hex() +
                "680caed2a15cfb63556552d700ce53480b9d43a7f3bae18fb71abfb52505d31d" + word(0xcc).hex() + word(0).hex() +
                "79db8da505fc8b36b2cabb9ee929bfe4b3b84ec91966dd325fdb184869c6a005" + word(7).hex() + word(96).hex() +
                word(2).hex() + "beef" + "00" * 30)


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

    def test_a_mutant_budget_keeps_a_seeded_sample_with_draw_order_and_numbers(self):
        def draw(limit):
            run = fixtures.FixtureRun.__new__(fixtures.FixtureRun)
            run.args = SimpleNamespace(seed=11, mutants=4, fixture_mutants=limit)
            run.fixture, run.abi, run.derived, run.record = {"id": "f"}, [], {}, {}
            run.steps = [step(kind="deploy", index=0)] + [step(index=index, calldata="0x" + (selector("k(uint256)") + word(index)).hex())
                                                        for index in (1, 2, 3)]
            return run.draw_mutants(), run.record
        everything, record = draw(None)
        self.assertNotIn("mutantBudget", record)
        self.assertEqual([[number for number, _ in everything[index]] for index in (1, 2, 3)], [[1, 2, 3, 4]] * 3)
        kept, record = draw(5)
        self.assertEqual(record["mutantBudget"], {"limit": 5, "drawn": 12, "kept": 5})
        self.assertEqual(sum(len(items) for items in kept.values()), 5)
        for index, items in kept.items():
            self.assertEqual(items, [item for item in everything[index] if item in items])
        self.assertEqual(draw(5)[0], kept)
        self.assertEqual(draw(12)[0], everything)
        run = fixtures.FixtureRun.__new__(fixtures.FixtureRun)
        ids = [entry["id"] for entry in run.entries([step(index=1)], {1: [(2, {"operator": "value", "value": 1})]})]
        self.assertEqual(ids, ["1.2", "1"])

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


class DerivedArgumentTests(unittest.TestCase):
    def labels(self, calldata, document, contract):
        derived = fixtures.derived_methods(document, contract)
        classes, origin = fixtures.step_classes(step(calldata=calldata), [], derived)
        self.assertEqual(origin, "derived")
        return [fixtures.class_label(classes[index]) for index in sorted(classes)], classes

    def test_std_structures_give_the_recorded_structural_selectors_and_tags(self):
        sums = fixtures.derived_methods(SUMS, "SumRoundtrip")
        self.assertEqual({key.hex(): text for key, (text, _) in sums.items()},
                         {"219ee3fb": "rtD2(sum(uint256,bytes))", "05e758d3": "rtD3(sum(uint256,sum(uint256,bytes)))",
                          "e096e642": "rtS3(sum(,sum(uint256,uint256,uint256,uint256)))", "1def993a": "rtS2(sum(uint256,uint256))"})
        d2, s3 = sums[bytes.fromhex("219ee3fb")][1], sums[bytes.fromhex("e096e642")][1]
        self.assertEqual([hex(tag)[:10] for tag in fixtures.tags(d2)], ["0x9579c5dd", "0x86c01c81"])
        self.assertEqual(hex(fixtures.tags(s3)[0])[:10], "0xf446c1d0")
        self.assertEqual((fixtures.attribs(d2), fixtures.attribs(s3)), ((False, 32), (True, 128)))
        option = fixtures.derived_methods(OPTION, "C")
        self.assertEqual({key.hex(): text for key, (text, _) in option.items()},
                         {"9e0708f2": "setOpt(sum(,uint256))", "f12ca2db": "echo(sum(,uint256))"})
        self.assertEqual(hex(fixtures.tags(option[bytes.fromhex("9e0708f2")][1])[0])[:10], "0x31234354")
        batch = fixtures.derived_methods(BATCH, "BatchDecoder")
        self.assertEqual(batch[bytes.fromhex("773db49a")][0],
                         "queueSigner(sum(sum(address,address),sum(bytes32,bytes32,address),uint256,bytes)[],uint256)")
        self.assertEqual(sorted(text.split("(")[0] for text, _ in batch.values()), ["execPayload", "queueSigner"])
        # A one-constructor type is its fields, without a tag or parentheses even as an array element.
        pair = declared("P", local=[data("Pair", ("Pair", UINT, UINT))], methods=[method("f", calldata_array(named("Pair")))])
        text, node = fixtures.derived_methods(pair, "P")[selector("f(uint256,uint256[])")]
        self.assertEqual((text, node[0], node[1][0]), ("f(uint256,uint256[])", "array", "struct"))
        # Aliases expand; a structure without a data type is standard, and units and tuples sign as std does.
        units = declared("U", aliases=[{"name": "UnitAlias", "params": [], "type": {"tuple": []}},
                                       {"name": "Units", "params": [], "type": calldata_array(named("UnitAlias"))}],
                         methods=[method("units", named("Units")), method("wrapped", calldata_array({"tuple": [named("Units"), UINT]}))])
        self.assertEqual(fixtures.derived_methods(units, "U"), {})
        scope = {"Units": ("alias", units["aliases"][1]), "UnitAlias": ("alias", units["aliases"][0])}
        self.assertEqual(fixtures.signature_text(fixtures.structure(calldata_array({"tuple": [named("Units"), UINT]}), scope)),
                         "(()[],uint256)[]")
        broken = declared("B", [data("Never"), data("Option", ("None",), ("Some", named("a")), params=["a"])], [
            method("qualified", {"named": "D", "qualifier": "std", "args": []}), method("unknown", named("Mystery")),
            method("arity", named("Option")), method("empty", named("Never")), method("function", {"fn": {}}),
            method("untyped", None), method("word", named("word"))])
        self.assertEqual(fixtures.derived_methods(broken, "B"), {})
        with self.assertRaisesRegex(fixtures.Underived, "takes 1 type arguments"):
            fixtures.structure(named("Option"), {"Option": ("data", broken["data"][1])})
        self.assertEqual(fixtures.derived_methods(None, "C"), {})
        self.assertEqual(fixtures.derived_methods(SUMS, "Other"), {})

    def test_recorded_derived_calls_classify_under_their_layout(self):
        labels, classes = self.labels(D2_BLOB, SUMS, "SumRoundtrip")
        self.assertEqual(labels, ["dynamic-offset:sum", "tag:D2", "dynamic-offset:bytes", "bytes-length", "content"])
        self.assertEqual((classes[0][2], classes[2][2], classes[3][1]), (0, 32, 128))
        self.assertEqual(self.labels(S3_NULLARY, SUMS, "SumRoundtrip")[0], ["tag:S3", "unused", "unused", "unused"])
        self.assertEqual(self.labels(OPTION_NONE, OPTION, "C")[0], ["tag:Option", "unused"])
        labels, classes = self.labels(QUEUE_SIGNER, BATCH, "BatchDecoder")
        self.assertEqual(labels, ["dynamic-offset:array", "leaf:uint256", "length", "dynamic-offset:sum", "dynamic-offset:sum",
                                  "tag:Batch", "tag:Operation", "leaf:address", "tag:Signature", "leaf:address", "unused",
                                  "tag:Batch", "leaf:uint256", "dynamic-offset:bytes", "bytes-length", "content"])
        self.assertEqual([classes[index][2] for index in (0, 3, 4, 13)], [0, 96, 96, 352])
        derived = fixtures.derived_methods(SUMS, "SumRoundtrip")
        self.assertEqual(fixtures.step_classes(step(calldata=D2_UNKNOWN), [], derived),
                         (None, "recorded input is not the derived layout of rtD2(sum(uint256,bytes)): "
                                "the tag matches no constructor of D2"))
        self.assertEqual(fixtures.step_classes(step(calldata="0xdeadc0de"), [], derived),
                         (None, "no standard-ABI method with this selector"))
        node = derived[bytes.fromhex("219ee3fb")][1]
        body = bytes.fromhex(D2_BLOB[10:])
        broken = {"misaligned offset": word(33) + body[32:], "offset outside": word(4096) + body[32:],
                  "content outside": body[:-32], "overlapping": body[:64] + word(0) + body[96:], "empty": b""}
        for name, value in broken.items():
            with self.subTest(name), self.assertRaises(ValueError):
                fixtures.derived_classify(value, node)

    def test_derived_boundary_words_are_exhaustive_and_relative_to_their_base(self):
        d2 = fixtures.derived_methods(SUMS, "SumRoundtrip")[bytes.fromhex("219ee3fb")][1]
        low, high = fixtures.tags(d2)
        tag = ("tag", "D2", (low, high))
        self.assertEqual(fixtures.boundary_values(tag, low, 96), [high, 0, low + 1, low - 1, U256 - 1])
        self.assertEqual(fixtures.boundary_values(("dynamic-offset", "sum", 0), 32, 160), [0, 161, 2**255, U256 - 4, 64])
        self.assertEqual(fixtures.boundary_values(("dynamic-offset", "bytes", 32), 64, 160),
                         [0, 32, 129, 2**255, U256 - 36, 96])
        self.assertEqual(fixtures.boundary_values(("bytes-length", 128), 2, 160), [33, U256 - 1, 32])
        self.assertEqual(fixtures.boundary_values(("bytes-length", 128), 32, 160), [33, U256 - 1])
        self.assertEqual(fixtures.boundary_values(("unused",), 0, 64), [1, U256 - 1])
        recorded = step(calldata=D2_BLOB)
        classes, _ = fixtures.step_classes(recorded, [], fixtures.derived_methods(SUMS, "SumRoundtrip"))
        self.assertEqual(sorted(fixtures.candidates(recorded, classes, fixtures.Stream(5))), ["content", "frame", "seeded"])
        boundaries = fixtures.exhaustive(recorded, classes)
        self.assertEqual([(item["word"], item["class"]) for item in boundaries],
                         [(0, "dynamic-offset:sum")] * 5 + [(1, "tag:D2")] * 5 + [(2, "dynamic-offset:bytes")] * 6 +
                         [(3, "bytes-length")] * 3)
        self.assertEqual(boundaries[5], {"operator": "word", "class": "tag:D2", "word": 1, "recorded": hex(high),
                                         "value": hex(low)})
        changed = fixtures.apply(recorded, boundaries[-1])
        self.assertEqual(changed["calldata"], D2_BLOB[:10 + 64 * 3] + word(32).hex() + D2_BLOB[10 + 64 * 4:])
        self.assertEqual(fixtures.exhaustive(step(calldata="0x" + (selector("k(uint256)") + word(1)).hex()), None), [])

    def draw(self, cap, budget=None, derived=True):
        run = fixtures.FixtureRun.__new__(fixtures.FixtureRun)
        run.args = SimpleNamespace(seed=11, mutants=4, fixture_mutants=budget, derived_mutants=cap)
        run.fixture, run.abi, run.record = {"id": "abi-sum-roundtrip"}, [], {}
        run.derived = fixtures.derived_methods(SUMS, "SumRoundtrip") if derived else {}
        run.steps = [step(kind="deploy", index=0), step(index=1, calldata=D2_BLOB), step(index=2, calldata=S3_NULLARY),
                     step(index=3, calldata="0x" + (selector("plain(uint256)") + word(5)).hex())]
        return run.draw_mutants(), run.record

    def test_derived_boundaries_follow_the_draws_and_a_fixture_keeps_at_most_its_cap(self):
        everything, record = self.draw(256)
        self.assertEqual(record["classification"], {"1": "derived", "2": "derived", "3": "no standard-ABI method with this selector"})
        self.assertEqual(record["derivedMutants"], {"limit": 256, "drawn": 19 + 6, "kept": 25})
        self.assertEqual([number for number, _ in everything[1]], list(range(1, 24)))
        self.assertEqual([number for number, _ in everything[2]], list(range(1, 11)))
        self.assertFalse(any(fixtures.derived_boundary(mutant) for _, mutant in everything[1][:4] + everything[2][:4]))
        self.assertTrue(all(fixtures.derived_boundary(mutant) for _, mutant in everything[1][4:] + everything[2][4:]))
        self.assertEqual([mutant["class"] for _, mutant in everything[2][4:]], ["tag:S3"] * 6)
        # Steps without a derived layout draw exactly as before.
        plain, _ = self.draw(256, derived=False)
        self.assertEqual(everything[3], plain[3])
        self.assertEqual([len(plain[index]) for index in (1, 2, 3)], [4, 4, 4])
        kept, record = self.draw(5)
        self.assertEqual(record["derivedMutants"], {"limit": 5, "drawn": 25, "kept": 5})
        boundary = [(index, item) for index in (1, 2) for item in kept[index][4:]]
        self.assertEqual(len(boundary), 5)
        self.assertTrue(all(item in everything[index] for index, item in boundary))
        self.assertEqual([kept[index][:4] for index in (1, 2)], [everything[index][:4] for index in (1, 2)])
        self.assertEqual(self.draw(5)[0], kept)
        none, record = self.draw(0)
        self.assertEqual((record["derivedMutants"]["kept"], [len(none[index]) for index in (1, 2)]), (0, [4, 4]))
        budgeted, record = self.draw(256, budget=6)
        self.assertEqual(record["mutantBudget"], {"limit": 6, "drawn": 12 + 25, "kept": 6})
        self.assertEqual(sum(len(items) for items in budgeted.values()), 6)

    def test_declarations_are_extracted_once_and_reused_only_by_the_same_build(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "main.sol"
            source.write_text("contract C {}\n")
            exports = fixtures.Exports.__new__(fixtures.Exports)
            exports.args = SimpleNamespace(upstream=root, target_dir=root, timeout=5)
            exports.source, exports.directory = source, root / "out"
            exports.directory.mkdir()
            calls = []

            def extract(command, timeout, **_):
                calls.append(command)
                output = Path(command[command.index("--output") + 1])
                output.write_text(json.dumps(OPTION))
                output.with_suffix(".json.provenance.json").write_text(json.dumps({
                    "schema": fixtures.declarations.SCHEMA, "toolBuild": {"build": len(calls)}, "source": source.as_uri(),
                    "sourceSha256": fixtures.common.file_digest(source), "outputSha256": fixtures.common.file_digest(output)}))
                return {"returncode": 0, "resource": None, "stdout": "", "stderr": ""}
            with patch.object(fixtures, "run_process", side_effect=extract):
                self.assertEqual(exports.declarations({"build": 1}, False), OPTION)
                self.assertEqual(exports.declarations({"build": 1}, True), OPTION)
                self.assertEqual(len(calls), 1)
                self.assertEqual(exports.declarations({"build": 3}, True), OPTION)
                self.assertEqual(len(calls), 2)
                self.assertIn("export-rust-declarations.py", calls[0][1])
            failed = {"returncode": 2, "resource": None, "stdout": "", "stderr": "parser diagnostics"}
            with patch.object(fixtures, "run_process", return_value=failed), \
                    self.assertRaisesRegex(ValueError, "declaration extraction failed: parser diagnostics"):
                exports.declarations({"build": 4}, False)

    def test_the_tool_check_requires_the_declaration_extractor_receipt(self):
        version = SimpleNamespace(stdout="solc\nVersion: " + fixtures.exporter.SOLC_VERSION + "\n")
        args = SimpleNamespace(upstream=ROOT, target_dir=ROOT, solc=Path("solc"))
        with patch.object(fixtures.scenario, "identities", return_value=(1, 2, 3)), \
                patch.object(fixtures.methods.resolver, "checked_identity", return_value=4), \
                patch.object(fixtures.declarations, "checked_identity", return_value=5), \
                patch.object(fixtures.subprocess, "run", return_value=version), \
                patch.object(fixtures.exporter, "validate_version", return_value=None):
            self.assertEqual(fixtures.check_tools(args)["declaration"], 5)
        with patch.object(fixtures.scenario, "identities", return_value=(1, 2, 3)), \
                patch.object(fixtures.methods.resolver, "checked_identity", return_value=4), \
                patch.object(fixtures.declarations, "checked_identity", side_effect=ValueError("receipt is stale")), \
                self.assertRaisesRegex(ValueError, "stale"):
            fixtures.check_tools(args)

    def test_records_count_the_derived_boundary_entries(self):
        run = fixtures.FixtureRun.__new__(fixtures.FixtureRun)
        run.fixture, run.raw, run.admitted = {"id": "f", "mode": "raw"}, True, ["sonatina-o0", "yul"]
        run.record = {"findings": [], "statuses": {}}
        run.steps = [step(kind="deploy", index=0), step(index=1, calldata=D2_BLOB)]
        mutants = [{"operator": operator, "class": label, "word": 0, "recorded": "0x20", "value": "0x0"}
                   for operator, label in (("word", "tag:D2"), ("word", "dynamic-offset:sum"), ("word", "bytes-length"),
                                           ("seeded-word", "tag:D2"), ("word", "unused"))]
        entries = [{**run.steps[1], "id": f"1.{number}", "step": 1, "persist": False, "mutant": mutant}
                   for number, mutant in enumerate(mutants, 1)] + [{**run.steps[1], "id": "1", "step": 1}]
        run.compare(entries, {path: [observation()] * 7 for path in run.admitted})
        self.assertEqual((run.record["counts"]["mutants"], run.record["counts"]["derivedBoundaries"]), (5, 3))
        totals = fixtures.summarize([{**run.record, "id": "f", "admitted": run.admitted, "exclusions": []}] * 2)
        self.assertEqual(totals["derivedBoundaries"], 6)


class SequenceTests(unittest.TestCase):
    PATHS = ["hull", "sonatina-o0", "yul"]
    FIVE = {"10": {"0": "5"}}

    def steps(self, kind="raw", count=3):
        return [step(kind="deploy", index=0)] + [step(kind=kind, index=index, calldata="0x" + (selector("k(uint256)") + word(index)).hex())
                                                for index in range(1, count + 1)]

    def held(self, storage=None, **extra):
        """The same observation on every path."""
        return {path: observation(storage=storage, **extra) for path in self.PATHS}

    def run_for(self, steps, observe, **args):
        run = fixtures.FixtureRun.__new__(fixtures.FixtureRun)
        run.args = SimpleNamespace(**{"seed": 5, "sequence_mutants": 64, "reduction_runs": 40, "reduction_seconds": 60, **args})
        run.fixture, run.raw, run.admitted, run.steps = {"id": "f", "mode": "raw"}, True, list(self.PATHS), steps
        run.record = {"findings": [], "statuses": {}, "counts": {}}
        run.deadline = run.run_deadline = None
        run.draws, run.seen, run.reference, run.recorded_findings = {}, {}, {}, set()
        run.observe = observe
        return run

    def test_operators_change_exactly_one_thing_and_mark_where_the_change_starts(self):
        steps = self.steps()
        mutant = {"operator": "word", "class": "leaf:uint256", "word": 0, "recorded": hex(2), "value": hex(9)}
        cases = {"commit": ({"operator": "commit", "step": 2, "of": "2.1", "mutant": mutant}, ["1", "2.1", "3"], 2),
                 "drop": ({"operator": "drop", "step": 2}, ["1", "3"], 2),
                 "duplicate": ({"operator": "duplicate", "step": 2}, ["1", "2", "2", "3"], 3),
                 "swap": ({"operator": "swap", "step": 1}, ["2", "1", "3"], 1)}
        for name, (candidate, order, change) in cases.items():
            deploy, items, at = fixtures.sequence_items(steps, candidate)
            self.assertEqual(([item["id"] for item in items], at), (order, change), name)
            self.assertEqual(fixtures.change_position(deploy, items), change, name)
            self.assertTrue(all(item["role"] == "prefix" for item in items[:change - 1]), name)
            self.assertTrue(all(item["persist"] for item in items), name)
        _, items, _ = fixtures.sequence_items(steps, cases["commit"][0])
        self.assertEqual((items[1]["calldata"], items[1]["mutant"]), ("0x" + (selector("k(uint256)") + word(9)).hex(), mutant))
        _, items, _ = fixtures.sequence_items(steps, cases["duplicate"][0])
        self.assertEqual([item["role"] for item in items], ["prefix", "prefix", "change", "tail"])
        # A rolled-back directive commits as recorded, and every other step keeps its persistence.
        _, items, at = fixtures.sequence_items(self.steps(kind="call"), {"operator": "persist", "step": 1})
        self.assertEqual(([item["persist"] for item in items], at), ([True, False, False], 1))
        # A deployment's commit changes the deployment, and every recorded call follows it.
        value = {"operator": "value", "recorded": 0, "value": 1}
        deploy, items, at = fixtures.sequence_items(steps, {"operator": "commit", "step": 0, "of": "0.1", "mutant": value})
        self.assertEqual((deploy["id"], deploy["value"], at, [item["id"] for item in items]), ("0.1", 1, 0, ["1", "2", "3"]))
        self.assertEqual(fixtures.change_position(deploy, items), 0)
        with self.assertRaisesRegex(ValueError, "unknown sequence operator"):
            fixtures.sequence_items(steps, {"operator": "reverse", "step": 1})

    def test_candidates_are_numbered_over_every_operator_and_kept_only_for_a_new_continuation(self):
        def mutant(value):
            return {"operator": "word", "class": "leaf:uint256", "word": 0, "recorded": "0x1", "value": hex(value)}
        draws = {1: [(number, mutant(number + 6)) for number in (1, 2, 3, 4)], 2: [(1, mutant(11))], 3: [(1, mutant(12))]}
        six, seven = {"10": {"0": "6"}}, {"10": {"0": "7"}}
        seen = {"0": self.held(), "1": self.held(self.FIVE), "2": self.held(self.FIVE), "3": self.held(six),
                "1.1": self.held(seven), "1.2": self.held(status="reverted"), "1.4": dict(self.held(seven), hull={"status": "timeout"}),
                "2.1": self.held(self.FIVE)}
        kept, counts = fixtures.sequence_candidates(self.steps(), draws, seen, self.PATHS)
        # Step 1 writes, step 2 leaves the state as it found it, and step 3 writes again.
        self.assertEqual([(item["id"], item["operator"], item["step"]) for item in kept],
                         [("s1", "drop", 1), ("s2", "commit", 1), ("s6", "duplicate", 1), ("s7", "swap", 1),
                          ("s11", "swap", 2), ("s12", "duplicate", 3)])
        self.assertEqual((kept[1]["of"], kept[1]["mutant"]), ("1.1", draws[1][0][1]))
        # 1.2 reverts, so it is step 1's drop; 1.3 did not run; 1.4 did not complete; 2.1 leaves the recorded state.
        self.assertEqual(counts, {"structural": 12, "redundant": 4, "unobserved": 1, "incomplete": 1, "candidates": 6})
        self.assertEqual(fixtures.sequence_candidates(self.steps(), draws, seen, self.PATHS), (kept, counts))

    def test_a_committed_directive_or_deployment_counts_only_when_it_changes_the_state(self):
        seen = {"0": self.held(), "1": self.held(self.FIVE), "2": self.held(), "3": self.held(self.FIVE)}
        kept, counts = fixtures.sequence_candidates(self.steps(kind="call"), {}, seen, self.PATHS)
        # Only the first directive writes and has a later one; nothing persists, so nothing drops, repeats or swaps.
        self.assertEqual([(item["id"], item["operator"], item["step"]) for item in kept], [("s1", "persist", 1)])
        self.assertEqual(counts, {"structural": 2, "redundant": 1, "unobserved": 0, "incomplete": 0, "candidates": 1})
        value = {"operator": "value", "recorded": 0, "value": 1}
        draws = {0: [(1, value), (2, {**value, "value": 2})]}
        seen = {"0": self.held(), "1": self.held(self.FIVE), "0.1": self.held(balances={"1": "1"}), "0.2": self.held(status="reverted")}
        kept, counts = fixtures.sequence_candidates(self.steps(count=1), draws, seen, self.PATHS)
        self.assertEqual([(item["id"], item["operator"], item["step"]) for item in kept], [("s1", "commit", 0), ("s3", "duplicate", 1)])
        self.assertEqual(counts["redundant"], 1)
        # Without a completed deployment nothing can continue.
        failed = {"0": self.held(status="reverted"), "1": {path: {"status": "not-executed"} for path in self.PATHS}}
        self.assertEqual(fixtures.sequence_candidates(self.steps(count=1), draws, failed, self.PATHS)[0], [])

    def test_a_path_leaves_a_sequence_after_a_step_it_did_not_complete(self):
        same, live = self.held(), set(self.PATHS)
        self.assertEqual(fixtures.sequence_agreement(same, live, False)["status"], "agree")
        result = fixtures.sequence_agreement(same, live - {"hull"}, False)
        self.assertEqual((result["status"], result["left"]), ("incomplete", ["hull"]))
        self.assertEqual(fixtures.sequence_agreement(dict(same, yul=observation(output="0x01")), live - {"hull"}, False)["status"],
                         "disagree")
        self.assertEqual(fixtures.sequence_agreement({path: dict(fixtures.BUDGET) for path in self.PATHS}, live, False)["status"],
                         "budget")
        self.assertEqual(fixtures.sequence_agreement(same, set(), False)["status"], "unobserved")
        observed = {"hull": [observation(), {"status": "timeout"}, observation()], "sonatina-o0": [observation()] * 3,
                    "yul": [observation()] * 3}
        self.assertEqual([alive for _, _, alive in fixtures.walk(self.PATHS, observed, 2)],
                         [live, live, {"sonatina-o0", "yul"}])

    def test_a_sequence_checks_its_prefix_by_expectations_and_compares_the_rest_across_paths(self):
        def observe(deploy, items, sequence=False):
            self.assertTrue(sequence)
            order = [item["id"] for item in items]
            rows = {path: [observation()] + [observation(storage=self.FIVE) for _ in items] for path in self.PATHS}
            if order == ["2", "1", "3"]:
                rows["hull"][1] = {"status": "timeout"}
            if order == ["1", "2", "2", "3"]:
                rows["yul"][3] = observation(storage=self.FIVE, output="0x01")
            return rows

        run = self.run_for(self.steps(), observe)
        recorded = [{**item, "id": str(item["index"]), "step": item["index"]} for item in run.steps[1:]]
        run.compare(recorded, {path: [observation(), observation(storage=self.FIVE), observation(storage=self.FIVE), observation()]
                               for path in self.PATHS})
        self.assertEqual(sorted(run.seen), ["0", "1", "2", "3"])
        self.assertEqual(run.reference["2"], fixtures.comparable(observation(storage=self.FIVE), False))
        tallies = dict.fromkeys(fixtures.SEQUENCE_COUNTS, 0)
        rows = [run.sequence({"id": f"s{number}", **candidate}, tallies) for number, candidate in enumerate(
            ({"operator": "drop", "step": 1}, {"operator": "swap", "step": 1}, {"operator": "duplicate", "step": 2}), 1)]
        self.assertEqual([[line["agreement"]["status"] for line in row["rows"]] for row in rows],
                         [["agree", "agree"], ["incomplete"] * 3, ["disagree"]])
        # The dropped step's successor reaches the recorded state; the last step then observes something new.
        self.assertEqual([line["same"] for line in rows[0]["rows"]], [True, False])
        self.assertEqual(rows[1]["rows"][1]["agreement"]["left"], ["hull"])
        self.assertEqual((rows[2]["change"], rows[2]["stop"], rows[2]["prefix"]["yul"]["match"]), (3, 3, 3))
        self.assertEqual(tallies, {"mutants": 3, "unrun": 0, "steps": 6, "agree": 2, "disagree": 1, "incomplete": 3,
                                   "unobserved": 0, "budget": 0, "stopped": 1, "changed": 1, "prefixSteps": 5})
        found = run.record["findings"]
        self.assertEqual([(item["category"], item["entry"], item["sequence"], item["operator"], item["position"], item["step"])
                          for item in found], [("path-mismatch", "s3@3", "s3", "duplicate", 3, 2)])
        self.assertEqual(run.record["statuses"]["hull"]["timeout"], 1)
        run.deadline = time.monotonic() - 1
        self.assertEqual(run.sequence({"id": "s9", "operator": "drop", "step": 1}, tallies)["status"], "budget")
        self.assertEqual((tallies["unrun"], tallies["budget"], tallies["steps"]), (1, 2, 8))

    def test_a_fixture_keeps_a_seeded_sample_within_its_cap_and_the_runs_share(self):
        candidates = [{"id": f"s{number}", "operator": "drop", "step": 1} for number in range(1, 11)]
        counts = {"structural": 12, "redundant": 2, "unobserved": 0, "incomplete": 0, "candidates": 10}

        def kept(limit, share=None):
            run, ran = self.run_for(self.steps(), None, sequence_mutants=limit, sequence_share=share), []
            with patch.object(fixtures, "sequence_candidates", return_value=(candidates, counts)), \
                    patch.object(fixtures.FixtureRun, "sequence", lambda self, candidate, tallies: ran.append(candidate["id"]) or {}):
                run.sequence_mutants()
            return ran, run.record
        ran, record = kept(4)
        self.assertEqual((len(ran), ran), (4, sorted(ran, key=lambda name: int(name[1:]))))
        self.assertGreaterEqual(record["sequenceMutants"].pop("seconds"), 0)
        self.assertEqual(record["sequenceMutants"], {"limit": 4, **counts, "kept": 4})
        self.assertEqual(kept(4)[0], ran)
        self.assertEqual(kept(64)[0], [item["id"] for item in candidates])
        self.assertEqual((len(kept(4, share=2)[0]), kept(4, share=2)[1]["sequenceMutants"]["limit"]), (2, 2))
        self.assertEqual(kept(0), ([], {"findings": [], "statuses": {}, "counts": {}}))
        totals = fixtures.summarize([{**record, "id": "f", "admitted": [], "exclusions": [],
                                      "counts": {"sequence": dict.fromkeys(fixtures.SEQUENCE_COUNTS, 2)}}] * 2)
        self.assertEqual((totals["sequence"]["agree"], totals["sequenceMutants"]["kept"]), (4, 8))

    def test_a_sequence_finding_reduces_to_a_shortest_prefix_with_its_operator(self):
        mutant = {"operator": "word", "class": "leaf:uint256", "word": 0, "recorded": hex(3), "value": hex(2**200)}
        candidate = {"id": "s1", "operator": "commit", "step": 3, "of": "3.1", "mutant": mutant}

        def observe(deploy, items, sequence=False):
            ids = [item["id"] for item in items]
            committed = next((int(item["calldata"][10:], 16) for item in items if "mutant" in item), 0)
            rows = {path: [observation()] * (1 + len(items)) for path in self.PATHS}
            # Yul differs on step 4 only after step 2 and a committed word of at least 1000.
            if "2" in ids[:-1] and committed >= 1000 and ids[-1] == "4":
                rows["yul"] = rows["yul"][:-1] + [observation(output="0x01")]
            return rows

        run = self.run_for(self.steps(count=4), observe)
        run.candidates = {"s1": candidate}
        deploy, items, change = fixtures.sequence_items(run.steps, candidate)
        last = {path: rows[-1] for path, rows in observe(deploy, items).items()}
        result = fixtures.sequence_agreement(last, set(self.PATHS), False)
        finding = {"sequence": "s1", "operator": "commit", "change": change, "position": len(items), "step": 4,
                   "entry": "s1@4", "category": "path-mismatch", "signature": ["path-mismatch", result["fields"], result["groups"]]}
        reduction = run.reduce(finding)
        self.assertEqual((reduction["status"], reduction["operator"], reduction["position"]), ("reduced", "commit", 3))
        self.assertEqual([(item["step"], "mutant" in item) for item in reduction["sequence"]],
                         [(0, False), (2, False), (3, True), (4, False)])
        self.assertEqual(int(reduction["mutant"]["value"], 16), 1000)
        self.assertEqual(run.reduce({**finding, "signature": ["path-mismatch", ["logs"], []]}),
                         {"status": "not-reproduced", "runs": 1})


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

    def test_an_entry_left_unrun_by_a_budget_is_neither_a_failure_nor_a_resource_limit(self):
        same = {path: observation() for path in fixtures.PATHS}
        budget = dict(same, hull=dict(fixtures.BUDGET))
        result = fixtures.agreement(budget, False)
        self.assertEqual((result["status"], result["failed"], result["inconclusive"]), ("incomplete", [], []))
        entry = {**step(expected={"status": "returned", "output": "0x"}), "id": "1", "step": 1}
        self.assertEqual(fixtures.entry_findings({"id": "f", "mode": "raw"}, entry, budget), [])
        self.assertEqual(fixtures.expectation(entry, fixtures.BUDGET, True), "budget")
        failure = {"status": "language-failure", "detail": fixtures.MEMORY_RANGE}
        unrun = {"hull": failure, **{path: dict(fixtures.BUDGET) for path in fixtures.EVM_PATHS}}
        self.assertEqual(fixtures.memory_range(unrun), unrun)
        late = time.monotonic() - 1
        self.assertEqual(fixtures.run_evm(None, "yul", b"", b"", step(kind="deploy", index=0), [step()], late),
                         [fixtures.BUDGET] * 2)

    def test_observing_classifies_each_entry_against_the_evm_paths_of_that_entry(self):
        run = fixtures.FixtureRun.__new__(fixtures.FixtureRun)
        run.args, run.fixture, run.prepared, run.chain, run.evm, run.deadline = None, {}, {}, {}, None, None
        run.admitted, run.bytecode = ["hull", "yul"], {"yul": (b"", b"")}
        failure = {"status": "language-failure", "detail": fixtures.MEMORY_RANGE}
        order = []
        with patch.object(fixtures, "run_hull", side_effect=lambda *_: order.append("hull") or [observation(), failure, failure]), \
                patch.object(fixtures, "run_evm", side_effect=lambda *_: order.append("evm") or
                             [observation(), {"status": "out-of-gas"}, observation()]):
            observed = run.observe(step(kind="deploy", index=0), [step(), step(index=2)])
        self.assertEqual([row["status"] for row in observed["hull"]], ["returned", "memory-range", "language-failure"])
        self.assertEqual(order, ["evm", "hull"])


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

    def test_a_deadline_stops_the_running_invocation_and_leaves_later_entries_unrun(self):
        with tempfile.TemporaryDirectory() as directory:
            args, exports = self.prepare(Path(directory), self.ECHO)
            deploy = step(kind="deploy", index=0)
            methods = {"mode": "methods", "contract": "C", "fuel": 10, "availableGas": None}
            entries = [step(kind="call", calldata="0x01"), step(kind="call", calldata="0xdead"), step(kind="call", calldata="0x02")]
            started = time.monotonic()
            observed = fixtures.run_hull(args, methods, exports, self.chain, deploy, entries, started + 2)
            self.assertLess(time.monotonic() - started, 20)
            self.assertEqual([item["status"] for item in observed], ["returned", "returned", "budget", "budget"])
            raw = {**methods, "mode": "raw"}
            entries = [step(calldata="0x01"), {**step(calldata="0xdead"), "persist": False}, step(calldata="0x02")]
            observed = fixtures.run_hull(args, raw, exports, self.chain, deploy, entries, time.monotonic() + 2)
            self.assertEqual([item["status"] for item in observed], ["returned", "returned", "budget", "budget"])
            self.assertEqual(fixtures.run_hull(args, raw, exports, self.chain, deploy, entries, time.monotonic() - 1),
                             [fixtures.BUDGET] * 4)

    def test_a_sequence_runs_in_one_invocation_and_is_not_resumed_after_a_limit(self):
        with tempfile.TemporaryDirectory() as directory:
            args, exports = self.prepare(Path(directory), self.ECHO)
            fixture = {"mode": "methods", "contract": "C", "fuel": 10, "availableGas": None}
            entries = [step(kind="call", calldata="0x01"), {**step(kind="call", calldata="0x02"), "persist": True},
                       step(kind="call", calldata="0xdead"), step(kind="call", calldata="0x03")]
            # Long enough for a loaded machine to start the runner and report the rows before the stall.
            args.hull_timeout = 3
            deploy = step(kind="deploy", index=0)
            observed = fixtures.run_hull_sequence(args, fixture, exports, self.chain, deploy, entries)
            self.assertEqual([item["status"] for item in observed], ["returned", "returned", "returned", "timeout", "timeout"])
            invocations = [json.loads(line) for line in Path(str(args.hull_runner) + ".log").read_text().splitlines()]
            self.assertEqual(invocations, [["0x01", "0x02", "0xdead", "0x03"]])
            self.assertEqual(fixtures.run_hull_sequence(args, fixture, exports, self.chain, deploy, entries, time.monotonic() - 1),
                             [fixtures.BUDGET] * 5)

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
        record.run_deadline = record.deadline = None
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


class RunTests(unittest.TestCase):
    def setUp(self):
        self.addCleanup(fixtures.STOP.clear)
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.output = Path(self.temporary.name) / "out"

    def main(self, *extra, run=None, delay=0.0):
        def check(_):
            time.sleep(delay)
            return {"driver": {}}
        with patch.object(fixtures, "check_tools", side_effect=check), patch.object(fixtures, "tool_identity", return_value={"tools": 1}), \
                patch.object(fixtures.FixtureRun, "run", run or (lambda self: {**self.record, "seconds": 0})), \
                contextlib.redirect_stdout(io.StringIO()) as printed:
            code = fixtures.main(["--output", str(self.output), "--fixture", "abi-*", "--mode", "mutation", "--seed", "1", *extra])
        return code, json.loads((self.output / "report.json").read_text()) if (self.output / "report.json").exists() else None, printed.getvalue()

    def test_fixtures_after_the_run_budget_are_recorded_unexecuted(self):
        code, report, _ = self.main("--seconds", "0.05", "--fixture-mutants", "8", "--fixture-seconds", "30", delay=0.1)
        self.assertEqual(code, 0)
        self.assertEqual(report["stop"], "run time budget")
        self.assertEqual(report["totals"]["unexecuted"], report["totals"]["fixtures"])
        self.assertTrue(all(record["unexecuted"] and record["stop"] == "run time budget" for record in report["fixtures"]))
        self.assertEqual((report["bounds"]["fixtureMutants"], report["bounds"]["fixtureSeconds"], report["bounds"]["runSeconds"]),
                         (8, 30.0, 0.05))
        self.assertEqual((report["mutantsPerStep"], report["derivedMutants"]), (4, fixtures.DERIVED_MUTANTS))
        self.assertEqual((report["sequenceMutants"], report["runSequenceMutants"], report["sequenceShare"]),
                         (fixtures.SEQUENCE_MUTANTS, None, None))
        self.output = self.output.with_name("capped")
        self.assertEqual(self.main("--derived-mutants", "8", "--seconds", "0.01", delay=0.05)[1]["derivedMutants"], 8)
        self.output = self.output.with_name("shared")
        report = self.main("--sequence-mutants", "16", "--run-sequence-mutants", "40", "--seconds", "0.01", delay=0.05)[1]
        recorded = [item for item in fixtures.inventory() if item["id"].startswith("abi-") and item["calls"]]
        self.assertEqual((report["sequenceMutants"], report["runSequenceMutants"], report["sequenceShare"]),
                         (16, 40, max(1, 40 // len(recorded))))

    def test_a_stop_signal_ends_the_run_with_its_report(self):
        def run(self):
            fixtures.STOP.set()
            return {**self.record, "seconds": 0, "stop": "signal"}
        code, report, _ = self.main("--jobs", "1", run=run)
        self.assertEqual((code, report["stop"]), (130, "signal"))
        self.assertEqual(report["totals"]["budgetStopped"], 1)
        self.assertEqual(report["totals"]["unexecuted"], report["totals"]["fixtures"] - 1)

    def test_check_prints_the_identity_of_what_a_run_reads(self):
        with patch.object(fixtures, "check_tools", return_value={"driver": {}}), patch.object(fixtures, "tool_identity", return_value={"tools": 1}), \
                contextlib.redirect_stdout(io.StringIO()) as printed:
            self.assertEqual(fixtures.main(["--check"]), 0)
        checked = json.loads(printed.getvalue())
        self.assertEqual((checked["status"], checked["tools"], len(checked["fixtures"])), ("ready", {"tools": 1}, 168))
        self.assertEqual(sorted(checked["manifests"]), ["rust-method-parity.json", "rust-scenario-parity.json"])

    def test_a_fixture_lock_holds_off_a_second_run_of_the_same_fixture(self):
        args = SimpleNamespace(work=Path(self.temporary.name) / "work")
        first, second = (fixtures.FixtureRun(args, {"id": "f", "mode": "raw", "contract": "C", "source": "s", "sha256": "0"}, {}, {})
                         for _ in range(2))
        entered = threading.Event()

        def hold():
            with second.locked():
                entered.set()
        with first.locked():
            thread = threading.Thread(target=hold)
            thread.start()
            self.assertFalse(entered.wait(0.3))
        self.assertTrue(entered.wait(5))
        thread.join()


class CommandLineTests(unittest.TestCase):
    def test_modes_seeds_and_bounds_are_checked_before_any_work(self):
        for extra in (["--mode", "mutation"], ["--seed", "1"], ["--mode", "mutation", "--seed", "1", "--mutants", "0"],
                      ["--jobs", "0"], ["--fixture-mutants", "4"], ["--mode", "mutation", "--seed", "1", "--fixture-mutants", "0"],
                      ["--seconds", "0"], ["--fixture-seconds", "-1"],
                      ["--mode", "mutation", "--seed", "1", "--derived-mutants", "-1"],
                      ["--mode", "mutation", "--seed", "1", "--derived-mutants", "4097"],
                      ["--mode", "mutation", "--seed", "1", "--sequence-mutants", "-1"],
                      ["--mode", "mutation", "--seed", "1", "--sequence-mutants", "4097"],
                      ["--mode", "mutation", "--seed", "1", "--run-sequence-mutants", "0"], ["--run-sequence-mutants", "4"]):
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
