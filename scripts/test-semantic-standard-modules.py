#!/usr/bin/env python3
"""Tests for standard-modules.py: how it reads export blocks, re-exports and declarations, and the generated Lean
tables against the pinned upstream checkout, where that checkout is present."""

import importlib.util
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location("standard_modules", ROOT / "scripts/standard-modules.py")
standard = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(standard)


def library(**sources: str):
    return standard.Library({f"{path.replace('__', '/')}.sol": text for path, text in sources.items()})


class ReadingTests(unittest.TestCase):
    def test_module_names_follow_the_file_paths(self):
        self.assertEqual(standard.module_name("std/std.sol"), "std")
        self.assertEqual(standard.module_name("std/opcodes.sol"), "std.opcodes")
        self.assertEqual(standard.module_name("std/unchecked/signed.sol"), "std.unchecked.signed")

    def test_exports_carry_their_namespaces_and_constructors_are_no_items(self):
        modules = library(std__std="""pragma solcore;
export { f, T(*), C, E, P(A) };
function f(x: word) returns (word) { return x; }
enum T { T(word), Other }
trait C<a> { function method(x: a) returns (a); }
struct E { x: word }
enum P { A, B }
impl C<word> { function method(x: word) returns (word) { return x; } }
""")
        self.assertEqual(modules.exports("std"),
                         [("f", "function"), ("T", "type"), ("C", "trait"), ("E", "type"), ("P", "type")])

    def test_nested_declarations_comments_and_strings_do_not_count(self):
        modules = library(std__std="""pragma solcore;
// function commented(x: word) returns (word)
export { g };
/* trait Hidden<a> {} */
function g(x: word) returns (word) {
    let s = "function inString() {";
    return x;
}
""")
        self.assertEqual(modules.module("std").declarations, {"g": ["function"]})
        self.assertEqual(modules.exports("std"), [("g", "function")])

    def test_reexports_and_imported_names_take_their_origin_namespace(self):
        modules = library(
            std__a="pragma solcore;\nexport { x, Y };\n"
                   "function x(v: word) returns (word) { return v; }\ntrait Y<a> {}\n",
            std__b="pragma solcore;\nimport { x as z } from std.a;\nexport { z };\nexport std.a.{ Y };\n",
            std__c="pragma solcore;\nimport * from std.a hiding { x };\nexport { Y };\nexport std.a.*;\n")
        self.assertEqual(modules.exports("std.b"), [("z", "function"), ("Y", "trait")])
        self.assertEqual(modules.exports("std.c"), [("Y", "trait"), ("x", "function")])

    def test_exports_carry_their_origins_and_the_constructors_they_show(self):
        modules = library(
            std__a="pragma solcore;\nexport { x, T(*), U, V(B) };\n"
                   "function x(v: word) returns (word) { return v; }\n"
                   "enum T { T(word), Other(memory<word>, word) }\nenum U { U }\nenum V { A, B }\n",
            std__b="pragma solcore;\nimport { x as z, T } from std.a;\nexport { z, T(*) };\n"
                   "export std.a.{ U, V(*) };\n",
            std__c="pragma solcore;\nexport std.a.*;\n")
        self.assertEqual(modules.module("std.a").constructors,
                         {"T": ["T", "Other"], "U": ["U"], "V": ["A", "B"]})
        self.assertEqual(modules.details("std.a"), {"x": ("std.a", "x", []), "T": ("std.a", "T", ["T", "Other"]),
                                                    "U": ("std.a", "U", []), "V": ("std.a", "V", ["B"])})
        self.assertEqual(modules.details("std.b"), {"z": ("std.a", "x", []), "T": ("std.a", "T", ["T", "Other"]),
                                                    "U": ("std.a", "U", []), "V": ("std.a", "V", ["B"])})
        self.assertEqual(modules.details("std.c"), modules.details("std.a"))
        text = standard.render({f"{name.replace('.', '/')}.sol": text for name, text in {
            "std/std": "pragma solcore;\nexport std.a.{ x, T(*) };\n",
            "std/a": "pragma solcore;\nexport { x, T(*) };\nfunction x(v: word) returns (word) { return v; }\n"
                     "enum T { T(word), Other }\n",
            "std/opcodes": "pragma solcore;\nexport { add };\n"
                           "function add(x: word, y: word) returns (word) { return x; }\n"}.items()})
        self.assertIn('(["std"], [\n      ("x", ["std", "a"], "x"), ("T", ["std", "a"], "T")])]', text)
        self.assertIn('(["std"], [\n      ("T", ["T", "Other"])]),\n'
                      '  (["std", "a"], [\n      ("T", ["T", "Other"])])]', text)

    def test_a_constructor_a_type_does_not_show_fails(self):
        modules = library(std__a="pragma solcore;\nexport { T };\nenum T { A }\n",
                          std__b="pragma solcore;\nexport std.a.{ T(A) };\n")
        with self.assertRaises(standard.StandardError):
            modules.details("std.b")

    def test_forms_it_does_not_read_fail(self):
        undeclared = library(std__std="pragma solcore;\nexport { missing };\n")
        with self.assertRaises(standard.StandardError):
            undeclared.exports("std")
        module_export = library(std__std="pragma solcore;\nexport std.other;\n",
                                std__other="pragma solcore;\nexport { f };\n"
                                           "function f(x: word) returns (word) { return x; }\n")
        with self.assertRaises(standard.StandardError):
            module_export.exports("std")
        missing_source = library(std__std="pragma solcore;\nexport std.nowhere.{ f };\n")
        with self.assertRaises(standard.StandardError):
            missing_source.exports("std")

    def test_rendering_keeps_the_opcodes_apart_and_every_line_within_one_hundred(self):
        text = standard.render({
            "std/std.sol": "pragma solcore;\nexport { f };\nfunction f(x: word) returns (word) { return x; }\n",
            "std/opcodes.sol": "pragma solcore;\nexport { add, mload };\n"
                               "function add(x: word, y: word) returns (word) { return x; }\n"
                               "function mload(p: word) returns (word) { return p; }\n"})
        self.assertIn('def standardOpcodeNames : List String :=\n  ["add", "mload"]', text)
        self.assertIn('(["std"], [\n      ("f", .function)])]', text)
        self.assertNotIn('"opcodes"], [', text)
        self.assertTrue(all(len(line) <= 100 for line in text.splitlines()))


class CheckoutTests(unittest.TestCase):
    def test_the_lean_tables_match_the_pinned_checkout(self):
        if not (standard.UPSTREAM / ".git").exists():
            self.skipTest("the pinned upstream checkout is absent")
        expected = standard.render(standard.read_checkout(standard.UPSTREAM))
        self.assertEqual(standard.TARGET.read_text(), expected,
                         "StandardModules.lean differs from std at the pin; run standard-modules.py --write")

    def test_the_check_reports_a_match(self):
        if not (standard.UPSTREAM / ".git").exists():
            self.skipTest("the pinned upstream checkout is absent")
        self.assertEqual(standard.main(["--check"]), 0)


if __name__ == "__main__":
    unittest.main()
