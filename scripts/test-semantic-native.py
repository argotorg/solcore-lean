#!/usr/bin/env python3
"""Native frontend harness tests; no case tool, Lean or native tool runs: a stub script stands in for the tool."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import stat
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("semantic_native", ROOT / "scripts/semantic-native.py")
native = importlib.util.module_from_spec(spec)
spec.loader.exec_module(native)

SOURCE = """pragma solcore;
import * from std;
import * from std.dispatch;
import { div as sc_div, mod as sc_mod } from std.opcodes;

function sc_fn0(sc_arg: word) returns (word) {
    return sc_arg;
}

contract SynthesizedFunctions {
    // the method, with a brace { in its comment
    function run(input: uint256) public returns (uint256) {
        let sc_x: word = Typedef.rep(input);
        return uint256(sc_fn0(sc_x));
    }
}
"""
# A memory-array case's source as its emitter writes it (fixed corpus, runtime-memory-arrays).
ARRAYS = """pragma solcore;
import * from std;
import * from std.unsigned;
import * from std.dispatch;

function sc_mk(sc_p: uint64, sc_q: uint64) returns (uint64[]) {
    return [sc_p, sc_q];
}

contract SynthesizedMemoryArrays {
    function run(input: uint256) public returns (uint256) {
        let sc_x: word = Typedef.rep(input);
        let sc_v1: uint64 = Typedef.abs(((sc_x + 9223372036854775807) & 0xffffffffffffffff));
        let sc_k0: uint256 = uint256(((sc_x >> 1) & 1));
        let sc_r: word = 0;
        let sc_a0: uint64[] = new uint64[](4);
        let sc_a1: uint64[] = sc_mk(sc_v1, 1);
        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_a1[sc_k0]));
        return uint256(sc_r);
    }
}
"""
SELECTOR = "0xa444f5e9"
INFERENCE = ("Solcore.Frontend.ProgramCheckError.inference { declaration := { moduleId := { library := "
             "Solcore.Workspace.LibraryId.main }, declarationIndex := 2 }, "
             "error := Solcore.Frontend.SourceInference.Error.")


def calldata(*words: int) -> str:
    return SELECTOR + "".join(f"{word:064x}" for word in words)


def make_case(source=SOURCE, emitter="solcore-source-functions-v2", program=None, signature="run(uint256)",
              data=None, core=None, **provenance):
    return {"schema": "solcore-lean.semantic-function-case.v1", "source": source,
            "program": program or {"tag": "apply", "argument": {"tag": "binary", "op": "wordAdd"}},
            "provenance": {"emitterVersion": emitter, **provenance},
            "contract": {"method": "run", "signature": signature, "calldata": data or calldata(7)},
            "directCore": core or {"stage": "execution", "status": "returned", "word": "7"}}


def binary(operator: str) -> dict:
    node = {"tag": "binary", "op": operator, "left": {"tag": "var"}, "right": {"tag": "word"}}
    return {"tag": "lambda", "body": node}


class AdmissionTests(unittest.TestCase):
    def test_the_adapter_lifts_the_contract_drops_std_imports_but_std_opcodes_and_appends_a_word_entry(self):
        lifted = native.lift(SOURCE, "run")
        self.assertIsNone(lifted["reason"])
        text = lifted["source"]
        self.assertTrue(text.startswith("pragma solcore;\n\n\nimport { div as sc_div, mod as sc_mod } from "
                                        "std.opcodes;\n\nfunction sc_fn0"))
        self.assertEqual(text.count("import"), 1)
        self.assertNotIn("contract", text)
        kept = native.lift(SOURCE.replace("import * from std.dispatch;", "import std.opcodes;\nimport * from "
                                          "std.unchecked.signed;"), "run")["source"]
        self.assertIn("\nimport std.opcodes;\n\nimport { div as sc_div", kept)
        self.assertNotIn("unchecked", kept)
        self.assertNotIn("public", text)
        self.assertIn("function run(input: uint256)  returns (uint256) {", text)
        self.assertIn("// the method, with a brace { in its comment", text)
        self.assertTrue(text.endswith("function sc_native_run(sc_native_a0: word) returns (word) {\n"
                                      "    return Typedef.rep(run(uint256(sc_native_a0)));\n}\n"))
        self.assertEqual((lifted["function"], lifted["parameters"]), ("sc_native_run", 1))
        closed = native.lift(SOURCE.replace("run(input: uint256)", "run()").replace("Typedef.rep(input)", "0")
                             .replace("returns (uint256) {\n        let", "returns (word) {\n        let"), "run")
        self.assertTrue(closed["source"].endswith("function sc_native_run() returns (word) {\n    return run();\n}\n"))

    def test_fields_members_contracts_and_other_signatures_are_refused_with_their_reason(self):
        def reason(source, method="run"):
            return native.lift(source, method)["reason"]
        self.assertEqual(reason(SOURCE.replace("{\n    // the", "{\n    acc: word;\n    // the")), "storage field")
        constructor = SOURCE.replace("{\n    // the", "{\n    constructor() { }\n    // the")
        self.assertEqual(reason(constructor), "contract member")
        self.assertEqual(reason(SOURCE + "\ncontract Other {\n}\n"), "contract shape")
        self.assertEqual(reason(SOURCE.replace("input: uint256", "input: bool")), "parameters or result")
        self.assertEqual(reason(SOURCE.replace("returns (uint256)", "returns (bool)")), "parameters or result")
        # The twelve types: a parameter by `Typedef.abs` at a local of its type, a result by `Typedef.rep`.
        typed = native.lift(SOURCE.replace("input: uint256", "input: int16").replace("returns (uint256)",
                                                                                     "returns (uint8)"), "run")
        self.assertIsNone(typed["reason"])
        self.assertEqual(typed["types"], ["int16"])
        self.assertTrue(typed["source"].endswith(
            "function sc_native_run(sc_native_a0: word) returns (word) {\n"
            "    let sc_native_p0: int16 = Typedef.abs(sc_native_a0);\n"
            "    return Typedef.rep(run(sc_native_p0));\n}\n"))
        self.assertEqual(reason(SOURCE, "missing"), "parameters or result")
        self.assertEqual(reason(SOURCE.replace("sc_fn0(sc_x)", "sc_native_run(sc_x)")), "contract shape")

    def test_admission_follows_the_emitter_table_in_a_fixed_order(self):
        def decided(**changes):
            result = native.admission(make_case(**changes))
            return result["reason"] if not result["admitted"] else "admitted"
        self.assertEqual(decided(), "admitted")
        self.assertEqual(decided(emitter="solcore-source-assembly-v2"), "emitter")
        self.assertEqual(decided(emitter="solcore-source-unknown-v9"), "emitter")
        # std.opcodes' aliases and the plans' `signextend` come from the import the adapter keeps.
        self.assertEqual(decided(program=binary("wordDiv")), "admitted")
        # Core sums are upstream's builtin `sum`, which the native frontend builds in.
        self.assertEqual(decided(program={"tag": "case", "scrutinee": {"tag": "inLeft"}}), "admitted")
        self.assertEqual(decided(program={"tag": "inRight", "value": binary("wordSmod")}), "admitted")
        shifts = "solcore-source-shifts-v2"
        self.assertEqual(decided(emitter=shifts, program=binary("wordShl")), "admitted")
        self.assertEqual(decided(emitter=shifts, program=binary("wordSignExtend")), "admitted")
        self.assertEqual(decided(emitter=shifts, shiftShapes={"values": ["int8"]}), "admitted")
        arithmetic = "solcore-source-checked-arithmetic-v2"
        self.assertEqual(decided(emitter=arithmetic, checkedArithmeticShapes={"types": ["int16"]}), "admitted")
        # std's `tobool`, called and not defined, in code and not in a comment: the adapter adds std's own, once.
        called = "let sc_x: word = Typedef.rep(input);\n        let sc_b: bool = tobool(sc_x);"
        tobool = SOURCE.replace("let sc_x: word = Typedef.rep(input);", called)
        added = native.admission(make_case(source=tobool))
        self.assertTrue(added["admitted"])
        self.assertEqual(added["source"].count("function tobool"), 1)
        self.assertIn("\n" + native.STD_TOBOOL + "\nfunction sc_native_run(", added["source"])
        commented = native.admission(make_case(source=SOURCE.replace("// the method,", "// tobool(sc_x), the method,")))
        self.assertTrue(commented["admitted"])
        self.assertNotIn("function tobool", commented["source"])
        defined = tobool.replace("\ncontract", "\nfunction tobool(x: word) returns (bool) {\n    return x != 0;\n}\n"
                                                "\ncontract")
        own = native.admission(make_case(source=defined))
        self.assertTrue(own["admitted"])
        self.assertEqual(own["source"].count("function tobool"), 1)
        self.assertNotIn(native.STD_TOBOOL, own["source"])
        self.assertEqual(decided(emitter=arithmetic, checkedArithmeticShapes={"types": ["uint16", "int256"]}),
                         "admitted")
        self.assertEqual(decided(emitter="solcore-source-enums-v2", program={"tag": "case"}), "admitted")
        self.assertEqual(decided(signature="run(uint8)"), "parameters or result")
        signed = SOURCE.replace("input: uint256", "input: int16")
        self.assertEqual(decided(source=signed, signature="run(int16)", data=calldata(2**15 - 1)), "admitted")
        self.assertEqual(decided(source=signed, signature="run(int16)", data=calldata(2**256 - 2**15)), "admitted")
        self.assertEqual(decided(source=signed, signature="run(int16)", data=calldata(2**15)), "calldata range")
        self.assertEqual(decided(source=signed, signature="run(int16)", data=calldata(2**256 - 2**15 - 1)),
                         "calldata range")
        narrow = SOURCE.replace("input: uint256", "input: uint8")
        self.assertEqual(decided(source=narrow, signature="run(uint8)", data=calldata(255)), "admitted")
        self.assertEqual(decided(source=narrow, signature="run(uint8)", data=calldata(256)), "calldata range")
        self.assertEqual(decided(source=signed, signature="run(uint256)"), "parameters or result")
        self.assertEqual(decided(data=calldata(7, 8)), "calldata")
        bundle = make_case()
        bundle["sourceBundle"] = {"entry": "main.sol", "files": []}
        self.assertEqual(native.admission(bundle)["reason"], "sources")
        admitted = native.admission(make_case(data=calldata(2**256 - 1)))
        self.assertEqual((admitted["function"], admitted["arguments"]), ("sc_native_run", [str(2**256 - 1)]))
        self.assertEqual(set(native.EMITTERS) & set(native.NOT_ADMITTED), set())
        # Array forms are read only in the array emitter's sources: v1's rules for the others stay.
        self.assertEqual(decided(source=SOURCE.replace("sc_fn0(sc_x)", "sc_fn0(ridx(lidx(sc_x, 0), 1))")), "admitted")

    def test_memory_arrays_are_admitted_without_std_array_traits(self):
        def decided(source=ARRAYS, types=("uint64",)):
            result = native.admission(make_case(source=source, emitter="solcore-source-memory-arrays-v2",
                                                memoryArrayShapes={"types": list(types)}))
            return (result["reason"], result["detail"]) if not result["admitted"] else "admitted"

        def edited(*statements, helper=""):
            return ARRAYS.replace("\ncontract", helper + "\ncontract").replace(
                "        return uint256(sc_r);", "".join(f"        {item}\n" for item in statements) +
                "        return uint256(sc_r);")
        length = "function sc_len<c>(sc_c: c) returns (uint256) where c: Length {\n    return sc_c.length;\n}\n"
        get = ("function sc_get<c>(sc_c: c, sc_i: uint256) returns (uint64) where (c, uint256): "
               "RValueIdxAccess<uint64> {\n    return ridx(sc_c, sc_i);\n}\n")
        put = "function sc_put(sc_c: memref<uint64>, sc_w: uint64) {\n    CanStore.store(sc_c, sc_w);\n}\n"
        tail = ("function sc_tail(sc_v: uint64[], sc_s: uint256) returns (arraySlice<uint64[]>) {\n"
                "    return sc_v[sc_s:];\n}\n")
        self.assertEqual(decided(), "admitted")
        self.assertEqual(decided(edited("sc_r = sc_r ^ Typedef.rep(Length.length(sc_a0) + sc_a0.length);",
                                        "// lidx(sc_a0, 1) and RValueIdxAccess in a comment")), "admitted")
        # Slices, copies and memrefs are admitted, with any `lidx` index, an integer literal among them.
        for cut in ("[1:sc_k0]", "[1:]", "[:2]", "[:]", "[sc_a1[0]:2]"):
            self.assertEqual(decided(edited(f"let sc_s0 = sc_a0{cut};", "let sc_a2: uint64[] = toArray(sc_s0);")),
                             "admitted", cut)
        self.assertEqual(decided(edited("let sc_s0 = sc_tail(sc_a0, 1);", helper=tail)), "admitted")
        for index in ("sc_k0", "uint256(1)", "sc_k0 + 1", "1", "0x1", "((7))"):
            self.assertEqual(decided(edited(f"sc_put(lidx(sc_a0, {index}), sc_v1);", helper=put)), "admitted", index)
        self.assertEqual(decided(types=["int8"]), "admitted")
        storage = ARRAYS.replace("{\n    function run", "{\n    sc_st: uint64[];\n    function run")
        self.assertEqual(decided(storage.replace("return uint256", "sc_st.setLength(2);\n        return uint256")),
                         ("storage field", "1 fields"))
        self.assertEqual(decided(edited(helper=length)), ("std's array trait", "Length"))
        self.assertEqual(decided(edited(helper=get)), ("std's array trait", "RValueIdxAccess, ridx"))
        literal = edited("sc_put(lidx(sc_a0, 1), sc_v1);", "sc_put(lidx(sc_a0 , 0x1), sc_v1);", helper=put)
        self.assertEqual(decided(literal), "admitted")
        self.assertEqual(decided(literal, types=["int16"]), "admitted")
        # The first reason in a fixed order: the lift's, then std's array traits.
        self.assertEqual(decided(edited("sc_put(lidx(sc_a0, 1), sc_v1);", helper=length + put))[0],
                         "std's array trait")
        stored = storage.replace("return uint256", "sc_put(lidx(sc_a0, 1), sc_v1);\n        return uint256")
        self.assertEqual(decided(stored)[0], "storage field")

    def test_the_array_forms_are_std_array_traits_alone(self):
        code = "sc_put(lidx(m, 1), v); // ridx(m, 2)\nlet n = Length.length(m) + m.length + lidx(f(a, 1), 0xff);"
        self.assertEqual(native.array_forms(code), {})
        self.assertEqual(native.array_forms(code + "\nlet k = ridx(m, 0x1);"), {"std's array trait": ["ridx"]})
        self.assertEqual(native.ARRAY_REASONS, ("std's array trait",))


class ComparisonTests(unittest.TestCase):
    RETURNED = {"stage": "execution", "status": "returned", "word": "7"}
    PANIC = "0x4e487b71" + "0" * 62 + "11"

    def test_words_and_revert_data_agree_and_other_observations_are_classified(self):
        compare = native.compare
        self.assertEqual(compare(self.RETURNED, {"status": "returned", "word": "7"}), {"verdict": "agree"})
        self.assertEqual(compare(self.RETURNED, {"status": "returned", "word": "8"}),
                         {"verdict": "mismatch", "core": "returned", "native": "returned", "label": None})
        reverted = {"stage": "execution", "status": "reverted", "output": self.PANIC}
        self.assertEqual(compare(reverted, {"status": "reverted", "error": "panic",
                                            "output": self.PANIC.upper().replace("0X", "0x")}), {"verdict": "agree"})
        self.assertEqual(compare(reverted, {"status": "reverted", "error": "dirtyHigherBitsForInteger",
                                            "output": "0x6cc54a63"})["native"], "reverted:0x6cc54a63")
        self.assertEqual(compare(self.RETURNED, {"status": "reverted", "error": "dirtyHigherBitsForInteger",
                                                 "output": "0x6cc54a63"}),
                         {"verdict": "mismatch", "core": "returned", "native": "reverted:0x6cc54a63",
                          "label": "dirty-conversion"})
        self.assertEqual(compare(self.RETURNED, {"status": "failed", "error": "uninitializedLocal"}),
                         {"verdict": "mismatch", "core": "returned", "native": "failed:uninitializedLocal",
                          "label": "uninitialized-local"})
        self.assertEqual(compare(self.RETURNED, {"status": "out-of-fuel"}),
                         {"verdict": "inconclusive", "reason": "out-of-fuel"})
        self.assertEqual(compare({"stage": "execution", "status": "invalid"}, {"status": "returned", "word": "0"}),
                         {"verdict": "inconclusive", "reason": "direct Core execution/invalid"})
        refused = {"status": "rejected", "stage": "invocation", "detail": "x"}
        self.assertEqual(compare(self.RETURNED, refused)["verdict"], "rejected")

    def test_symptoms_are_stable_and_known_differences_are_labelled_by_their_error(self):
        typedef = INFERENCE + 'operatorNotSupported "Typedef" (Solcore.TypeSystem.Ty.variable { index := 8 }) }'
        lambda_ = INFERENCE + 'operatorNotSupported "Add" (Solcore.TypeSystem.Ty.variable { index := 1 }) }'
        equality = INFERENCE + ('operatorNotSupported "Eq" (Solcore.TypeSystem.Ty.constructor (Solcore.TypeSystem.'
                                'TypeConstructorId.builtin (Solcore.TypeSystem.BuiltinType.bool))) }')
        exhaustive = INFERENCE + "nonExhaustiveMatch { source := { path := \"main.sol\" }, startByte := 3326 } }"
        # Row 4's array operations on an open base, as the native tool reports them, match before an operator on a
        # generalized lambda parameter; a read on such a base fails unification, which no label takes.
        operators = [(INFERENCE + f'operatorNotSupported "{name}" (Solcore.TypeSystem.Ty.variable {{ index := 1 }}) }}',
                      f'operatorNotSupported "{name}" at variable', "open-array-base")
                     for name in ("Length", "toArray", "lidx", "CanStore")]
        read = INFERENCE + ("unification (Solcore.TypeSystem.Unification.Error.mismatch (Solcore.TypeSystem.Ty."
                            "application (Solcore.TypeSystem.Ty.constructor (Solcore.TypeSystem.TypeConstructorId."
                            "builtin (Solcore.TypeSystem.BuiltinType.memoryArray))) (Solcore.TypeSystem.Ty.variable "
                            "{ index := 7 })) (Solcore.TypeSystem.Ty.mapping (Solcore.TypeSystem.Ty.variable "
                            "{ index := 5 }) (Solcore.TypeSystem.Ty.variable { index := 6 }))) }")
        expectations = [(typedef, 'operatorNotSupported "Typedef" at variable', "open-typedef-call"),
                        *operators, (INFERENCE + 'unsupportedExpression "slice" }', 'unsupportedExpression "slice"',
                                     "open-array-base"),
                        (read, "unification", None),
                        (lambda_, 'operatorNotSupported "Add" at variable', "generalized-lambda-parameter"),
                        (equality, 'operatorNotSupported "Eq" at bool', "bool-equality"),
                        (INFERENCE + 'unknownVariable "ne" }', 'unknownVariable "ne"', "not-equal"),
                        (INFERENCE + 'noMatchingOverload "sc_div" [] }', 'noMatchingOverload "sc_div"', None),
                        (exhaustive, "nonExhaustiveMatch", None)]
        for detail, found, label in expectations:
            self.assertEqual(native.symptom(detail), found)
            self.assertEqual(native.rejection_label("inference", found), label)
        self.assertIsNone(native.rejection_label("signatures", 'unknownVariable "ne"'))
        self.assertEqual(set(native.KNOWN), {"open-typedef-call", "open-array-base", "generalized-lambda-parameter",
                                             "bool-equality", "not-equal", "uninitialized-local",
                                             "dirty-conversion"})
        self.assertEqual(set(native.MISMATCH_LABELS.values()) - set(native.KNOWN), set())


STUB = """#!/usr/bin/env python3
import json, sys
request = json.load(open(sys.argv[1]))
source = request["sources"][0]["content"]
if "REJECTED" in source:
    detail = %r
    print(json.dumps({"schema": "solcore-lean.semantic-native-result.v1", "status": "rejected", "stage": "inference",
                      "detail": detail, "milliseconds": {}, "observations": []}))
elif "CRASHED" in source:
    sys.exit(3)
else:
    print(json.dumps({"schema": "solcore-lean.semantic-native-result.v1", "status": "compiled", "stage": "compiled",
                      "detail": "", "milliseconds": {}, "observations": [{"status": "returned", "word": words[0]}
                                                                         for words in request["inputs"]]}))
""" % (INFERENCE + "nonExhaustiveMatch { startByte := 10 } }")


class RunTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        self.tool = self.root / "semantic-native-tool"
        self.tool.write_text(STUB)
        self.tool.chmod(self.tool.stat().st_mode | stat.S_IXUSR)
        (self.root / "bin").mkdir()
        (self.root / "bin/semantic-case-tool").write_text("case tool\n")

    def tearDown(self):
        self.directory.cleanup()

    def arguments(self, *extra):
        return native.parse_args(["--output", str(self.root / "out"), "--native-tool", str(self.tool),
                                  "--bin-dir", str(self.root / "bin"), "--profile", "runtime-functions", *extra])

    def test_cases_of_one_program_run_once_and_findings_keep_signatures_and_replays(self):
        returned = lambda word: {"stage": "execution", "status": "returned", "word": word}
        rejected = SOURCE.replace("sc_fn0(sc_x)", "sc_fn0(sc_x) /* REJECTED */")
        cases = [make_case(data=calldata(7)), make_case(data=calldata(8), core=returned("9")),
                 make_case(source=rejected), make_case(source=rejected, data=calldata(5)),
                 make_case(emitter="solcore-source-halt-v2"),
                 make_case(signature="run(uint8)")]
        args, suite_args = self.arguments()
        args.output.mkdir()
        run = native.NativeRun(args, suite_args)
        with patch.object(native, "prepare", return_value={"cases": cases, "excluded": [{"id": "x"}]}), \
                patch.object(native.suite, "command", return_value=["python", "runner", "--output", "unused"]):
            run.run_profile("runtime-functions")
        counts = run.profiles["runtime-functions"]["counts"]
        self.assertEqual(counts, {"cases": 6, "generationExcluded": 1, "notAdmitted": 2, "admitted": 4, "programs": 2,
                                  "agree": 1, "mismatch": 1, "rejected": 2, "inconclusive": 0, "unexecuted": 0})
        self.assertEqual(run.profiles["runtime-functions"]["reasons"], {"emitter": 1, "parameters or result": 1})
        self.assertEqual([program["cases"] for program in run.programs], [[0, 1], [2, 3]])
        findings = sorted(run.findings.values(), key=lambda item: item["kind"])
        self.assertEqual([(item["kind"], item["count"], item["known"]) for item in findings],
                         [("native-mismatch", 1, False), ("native-rejection", 2, False)])
        self.assertEqual((findings[1]["stage"], findings[1]["symptom"]), ("inference", "nonExhaustiveMatch"))
        self.assertEqual((findings[0]["core"], findings[0]["native"]), ("returned", "returned"))
        replay = json.loads(Path(findings[1]["replay"]).read_text())
        self.assertEqual((replay["function"], replay["inputs"]), ("sc_native_run", [["7"], ["5"]]))
        report = run.report({"same": 1}, {"same": 1}, 0.0)
        self.assertEqual((report["status"], report["totals"]["findings"]),
                         ("failed", {"signatures": 2, "known": 0, "new": 2}))

    def test_a_crash_is_a_finding_and_a_changed_identity_fails_the_run(self):
        args, suite_args = self.arguments()
        args.output.mkdir()
        run = native.NativeRun(args, suite_args)
        crashed = make_case(source=SOURCE.replace("sc_fn0(sc_x)", "sc_fn0(sc_x) /* CRASHED */"))
        with patch.object(native, "prepare", return_value={"cases": [crashed, make_case()], "excluded": []}), \
                patch.object(native.suite, "command", return_value=["python", "runner"]):
            run.run_profile("runtime-functions")
        self.assertEqual([(item["kind"], item["stage"]) for item in run.findings.values()],
                         [("native-rejection", "tool")])
        self.assertEqual(run.report({"a": 1}, {"a": 1}, 0.0)["status"], "failed")
        clean = native.NativeRun(args, suite_args)
        with patch.object(native, "prepare", return_value={"cases": [make_case()], "excluded": []}), \
                patch.object(native.suite, "command", return_value=["python", "runner"]):
            clean.run_profile("runtime-functions")
        self.assertEqual(clean.report({"a": 1}, {"a": 1}, 0.0)["status"], "passed")
        self.assertEqual(clean.report({"a": 1}, {"a": 2}, 0.0)["status"], "failed")

    def test_preparation_replaces_only_the_runners_run_for_its_call(self):
        calls = []

        class Campaign:
            def __init__(self, args):
                self.summary = {}

            def prepare_cases(self):
                calls.append("prepare")
                return {"cases": [{"id": 1}], "excluded": []}

            def run(self):
                calls.append("run")

        def main():
            calls.append(sys.argv[1:])
            fake.Campaign(None).run()  # as the runner's main, through its module's current Campaign
            print("runner output")
            return 0

        fake = SimpleNamespace(Campaign=Campaign, main=main)
        with patch.object(native, "runner", fake):
            response = native.prepare(["--output", str(self.root / "prepared"), "--profile", "runtime-word"])
            self.assertIs(fake.Campaign, Campaign)
        self.assertEqual(response["cases"], [{"id": 1}])
        self.assertEqual(calls, [["--output", str(self.root / "prepared"), "--profile", "runtime-word"], "prepare"])

    def test_the_check_reports_every_identity_and_random_defaults_take_admitted_emitters(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            code = native.main(["--check", "--native-tool", str(self.tool), "--bin-dir", str(self.root / "bin"),
                                "--profile", "runtime-word"])
        check = json.loads(output.getvalue())
        self.assertEqual((code, check["status"], sorted(check["corpora"])), (0, "ready", ["runtime-word"]))
        self.assertEqual(check["versions"], {"admission": "native-admission-v8", "adapter": "native-lift-v4",
                                             "comparison": "native-compare-v1"})
        self.assertEqual(sorted(check["scripts"]), sorted(native.SCRIPTS))
        args, _ = native.parse_args(["--check", "--mode", "random", "--seed", "5"])
        self.assertIn("runtime-shifts", args.profile)
        self.assertIn("runtime-memory-arrays", args.profile)
        self.assertNotIn("runtime-assembly", args.profile)
        self.assertTrue(all(native.profile_emitter(profile) in native.EMITTERS for profile in args.profile))
        args, _ = native.parse_args(["--check"])
        self.assertEqual(args.profile, list(native.PURE_PROFILES))
        with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
            native.parse_args(["--check", "--cases", "3"])


if __name__ == "__main__":
    unittest.main()
