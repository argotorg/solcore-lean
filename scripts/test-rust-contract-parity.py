#!/usr/bin/env python3
"""Guard expectation parsing and ABI encoding used by the runtime parity gate."""

import importlib.util
import json
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("contract_parity", Path(__file__).with_name("rust-contract-parity.py"))
assert spec and spec.loader
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)


class Expectations(unittest.TestCase):
    def test_nested_tuple_and_top_level_outputs(self):
        parsed = parity.DirectiveParser("#[((7, 1), 9) -> (7, 1, 9)]").parse()
        self.assertEqual(parsed["arguments"], [[7, 1], 9])
        self.assertEqual(parsed["expected"], {"status": "returned", "values": [7, 1, 9]})
        self.assertEqual(parity.DirectiveParser("#[((7, 1, 9)) -> ((7, 1, 9))]").parse()
            ["expected"]["values"], [[7, 1, 9]])

    def test_revert_payload_and_unspecified_payload(self):
        self.assertEqual(parity.DirectiveParser("#[(7) -> revert(0xDEADbeef)]").parse()
            ["expected"], {"status": "reverted", "output": "0xdeadbeef"})
        self.assertIsNone(parity.DirectiveParser("#[() -> revert]").parse()["expected"]["output"])
        self.assertEqual(parity.DirectiveParser("#[() -> revert(0x)]").parse()["expected"]["output"], "0x")

    def test_numeric_and_boolean_values_remain_distinct(self):
        parsed = parity.DirectiveParser("#[(false, true, 0XFF, 001) -> ()]").parse()
        self.assertEqual(parsed["arguments"], [False, True, 255, 1])
        self.assertEqual(parsed["expected"]["values"], [])

    def test_malformed_directives_reject(self):
        for source in ["#[(1,) -> 1]", "#[() -> truex]", "#[() -> -1]", "#[() -> 1] trailing",
                       "#[() -> revert(0xabc)]", "#[() -> revert(ab)]", f"#[() -> {2**256}]"]:
            with self.subTest(source=source), self.assertRaises(ValueError):
                parity.DirectiveParser(source).parse()
        with self.assertRaises(parity.Unsupported):
            parity.DirectiveParser("#[send(1)]").parse()

    def test_only_directly_attached_function_directives(self):
        source = "contract C {\n// #[(true) -> 7]\n// #[(false) -> 9]\nfunction run(x: bool) {}\n}"
        self.assertEqual([(x["method"], x["vector"]) for x in parity.source_directives(source)],
            [("run", 1), ("run", 2)])
        for text in [source.replace("function run", "let run"), source + "\n// #[() -> 1]",
                     source + "\ncontract D {}", source.replace("// #[(true) -> 7]", "/* #[() -> 1] */")]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                parity.source_directives(text)

    def test_static_encoding_and_arity_checks(self):
        word = {"type": "uint256"}
        pair = {"type": "tuple", "components": [word, {"type": "bool"}]}
        self.assertEqual(parity.canonical_type(pair), "(uint256,bool)")
        self.assertEqual(parity.encode_values([pair, word], [[7, True], 9]),
            b"".join(value.to_bytes(32, "big") for value in [7, 1, 9]))
        for shape, value in [(word, True), ({"type": "bool"}, 1), (pair, [7]), (pair, 7),
                             ({"type": "address"}, 2**160), (word, 2**256)]:
            with self.subTest(shape=shape, value=value), self.assertRaises(ValueError):
                parity.encode_value(shape, value)
        with self.assertRaises(parity.Unsupported):
            parity.encode_value({"type": "bytes"}, 7)
        with self.assertRaises(ValueError):
            parity.encode_values([word], [])

    def test_batch_failures_do_not_taint_other_call_results(self):
        actuals = [{"stage": "execution", "status": "returned", "output": "0x00"},
                   {"stage": "execution", "status": "out-of-fuel"}]
        rows = parity.batch_results("\n".join(json.dumps(row) for row in actuals), "", 1, 2)
        observations = [{"expected": {"status": "returned", "output": "0x00"}} for _ in rows]
        for observation, actual in zip(observations, rows):
            parity.record_result(observation, actual, 1, 2)
        self.assertEqual([row["status"] for row in observations], ["succeeded", "out-of-fuel"])
        rejection = {"stage": "lowering", "status": "rejected", "detail": "unsupported"}
        self.assertEqual(parity.batch_results(json.dumps(rejection), "", 1, 2), [rejection, rejection])
        for stdout, exit_code, count in [(json.dumps(actuals[0]), 1, 1),
                                         (json.dumps(actuals[0]), 0, 2), ("[]", 0, 1), ("broken", 1, 1)]:
            with self.subTest(stdout=stdout, exit_code=exit_code):
                self.assertTrue(all(row["status"] == "error" for row in
                    parity.batch_results(stdout, "", exit_code, count)))


if __name__ == "__main__":
    unittest.main()
