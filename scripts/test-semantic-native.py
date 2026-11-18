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
    def test_operations_are_node_tags_with_the_operators_of_operator_nodes(self):
        branch = {"tag": "unary", "op": "wordNot"}
        program = {"tag": "apply", "function": binary("wordDiv"),
                   "argument": {"tag": "case", "scrutinee": {"tag": "inLeft"}, "branches": [branch]}}
        self.assertEqual(native.operations(program),
                         {"apply", "lambda", "binary:wordDiv", "var", "word", "case", "inLeft", "unary:wordNot"})

    def test_the_adapter_lifts_the_contract_drops_std_imports_and_appends_a_word_entry(self):
        lifted = native.lift(SOURCE, "run")
        self.assertIsNone(lifted["reason"])
        text = lifted["source"]
        self.assertTrue(text.startswith("pragma solcore;\n\n\n\n\nfunction sc_fn0"))
        self.assertNotIn("import", text)
        self.assertNotIn("contract", text)
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
        self.assertEqual(reason(SOURCE.replace("input: uint256", "input: int16")), "parameters or result")
        self.assertEqual(reason(SOURCE.replace("returns (uint256)", "returns (bool)")), "parameters or result")
        self.assertEqual(reason(SOURCE, "missing"), "parameters or result")
        self.assertEqual(reason(SOURCE.replace("sc_fn0(sc_x)", "sc_native_run(sc_x)")), "contract shape")

    def test_admission_follows_the_emitter_table_in_a_fixed_order(self):
        def decided(**changes):
            result = native.admission(make_case(**changes))
            return result["reason"] if not result["admitted"] else "admitted"
        self.assertEqual(decided(), "admitted")
        self.assertEqual(decided(emitter="solcore-source-assembly-v2"), "emitter")
        self.assertEqual(decided(emitter="solcore-source-unknown-v9"), "emitter")
        self.assertEqual(decided(program=binary("wordDiv")), "std.opcodes operation")
        self.assertEqual(decided(program={"tag": "case", "scrutinee": {"tag": "inLeft"}}), "sum")
        self.assertEqual(decided(program={"tag": "inRight", "value": binary("wordSmod")}), "std.opcodes operation")
        shifts = "solcore-source-shifts-v2"
        self.assertEqual(decided(emitter=shifts, program=binary("wordShl")), "admitted")
        self.assertEqual(decided(emitter=shifts, program=binary("wordSignExtend")), "std.opcodes operation")
        self.assertEqual(decided(emitter=shifts, shiftShapes={"values": ["int8"]}), "signed narrow type")
        arithmetic = "solcore-source-checked-arithmetic-v2"
        self.assertEqual(decided(emitter=arithmetic, checkedArithmeticShapes={"types": ["int16"]}),
                         "signed narrow type")
        self.assertEqual(decided(emitter=arithmetic, checkedArithmeticShapes={"types": ["uint16", "int256"]}),
                         "admitted")
        self.assertEqual(decided(emitter="solcore-source-enums-v2", program={"tag": "case"}), "admitted")
        self.assertEqual(decided(signature="run(uint8)"), "parameters or result")
        self.assertEqual(decided(data=calldata(7, 8)), "calldata")
        bundle = make_case()
        bundle["sourceBundle"] = {"entry": "main.sol", "files": []}
        self.assertEqual(native.admission(bundle)["reason"], "sources")
        admitted = native.admission(make_case(data=calldata(2**256 - 1)))
        self.assertEqual((admitted["function"], admitted["arguments"]), ("sc_native_run", [str(2**256 - 1)]))
        self.assertEqual(set(native.EMITTERS) & set(native.NOT_ADMITTED), set())


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
        expectations = [(typedef, 'operatorNotSupported "Typedef" at variable', "open-typedef-call"),
                        (lambda_, 'operatorNotSupported "Add" at variable', "generalized-lambda-parameter"),
                        (equality, 'operatorNotSupported "Eq" at bool', "bool-equality"),
                        (INFERENCE + 'unknownVariable "ne" }', 'unknownVariable "ne"', "not-equal"),
                        (INFERENCE + 'noMatchingOverload "sc_div" [] }', 'noMatchingOverload "sc_div"', None),
                        (exhaustive, "nonExhaustiveMatch", None)]
        for detail, found, label in expectations:
            self.assertEqual(native.symptom(detail), found)
            self.assertEqual(native.rejection_label("inference", found), label)
        self.assertIsNone(native.rejection_label("signatures", 'unknownVariable "ne"'))
        self.assertEqual(set(native.KNOWN), {"open-typedef-call", "generalized-lambda-parameter", "bool-equality",
                                             "not-equal", "uninitialized-local"})


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
                 make_case(emitter="solcore-source-halt-v2"), make_case(program=binary("wordMod"))]
        args, suite_args = self.arguments()
        args.output.mkdir()
        run = native.NativeRun(args, suite_args)
        with patch.object(native, "prepare", return_value={"cases": cases, "excluded": [{"id": "x"}]}), \
                patch.object(native.suite, "command", return_value=["python", "runner", "--output", "unused"]):
            run.run_profile("runtime-functions")
        counts = run.profiles["runtime-functions"]["counts"]
        self.assertEqual(counts, {"cases": 6, "generationExcluded": 1, "notAdmitted": 2, "admitted": 4, "programs": 2,
                                  "agree": 1, "mismatch": 1, "rejected": 2, "inconclusive": 0, "unexecuted": 0})
        self.assertEqual(run.profiles["runtime-functions"]["reasons"], {"emitter": 1, "std.opcodes operation": 1})
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
        self.assertEqual(check["versions"], {"admission": "native-admission-v1", "adapter": "native-lift-v1",
                                             "comparison": "native-compare-v1"})
        self.assertEqual(sorted(check["scripts"]), sorted(native.SCRIPTS))
        args, _ = native.parse_args(["--check", "--mode", "random", "--seed", "5"])
        self.assertIn("runtime-shifts", args.profile)
        self.assertNotIn("runtime-assembly", args.profile)
        self.assertTrue(all(native.profile_emitter(profile) in native.EMITTERS for profile in args.profile))
        args, _ = native.parse_args(["--check"])
        self.assertEqual(args.profile, list(native.PURE_PROFILES))
        with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
            native.parse_args(["--check", "--cases", "3"])


if __name__ == "__main__":
    unittest.main()
