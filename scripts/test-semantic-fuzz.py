#!/usr/bin/env python3
"""Continuous-fuzzing driver tests; fake suite outputs are not executions."""
from __future__ import annotations

import contextlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("semantic_fuzz", ROOT / "scripts/semantic-fuzz.py")
fuzz = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fuzz)

CRASH = ("\nthread '<unnamed>' ({thread}) panicked at /home/{user}/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/"
         "primitive-types-0.14.0/src/lib.rs:43:1:\n{message}\nnote: run with `RUST_BACKTRACE=1`\n"
         "Exported checked Hull: /tmp/{user}/.work/run-000013/hull.json\n")


def crash(message="Integer overflow when casting to usize", thread=7, user="a", site=None):
    return ("compiler-crash", CRASH.format(thread=thread, user=user, message=message), "a" * 64, site)

# A stand-in for a crashing Rust stage: it needs the case in its rewritten root
# and prints a backtrace only when RUST_BACKTRACE=1 reaches it.
FAKE_STAGE = """import os, sys
root = sys.argv[sys.argv.index("--root") + 1]
assert os.path.exists(os.path.join(root, "case.sol")), root
sys.stderr.write("thread '<unnamed>' (5) panicked at /x/index.crates.io-1949cf8c6b5b557f/primitive-types-0.14.0/src/lib.rs:43:1:\\n"
                 "Integer overflow when casting to usize\\n")
if os.environ.get("RUST_BACKTRACE") == "1":
    frames = sys.argv[sys.argv.index("--frame") + 1:]
    sys.stderr.write("stack backtrace:\\n   0: __rustc::rust_begin_unwind\\n   1: core::panicking::panic_fmt\\n"
                     "   2: primitive_types::U256::as_usize::h0123456789abcdef\\n"
                     + "".join(f"   {3 + index}: {frame}::h0123456789abcdef\\n             at /x/crates/codegen/src/a.rs:1:2\\n"
                               for index, frame in enumerate(frames))
                     + f"   {3 + len(frames)}: sonatina_codegen::driver::run\\n")
sys.exit(101)
"""


def mismatch(program):
    return ("semantic-mismatch", "", program)


# Real occurrences of the upstream findings in questions.md, as (source, profile,
# backend, category, stage, detail, crash site): one fuzz-driver run from root
# seed 1 with eight functions per profile, the retained suite runs of the
# recorded observations replayed through the driver's signature code, and the
# two O2 crashes of the mixed streams' random matrix. Home
# directories are shortened, and each detail ends at the line its symptom reads.
def panic(thread, message):
    return (f"\nthread '<unnamed>' ({thread}) panicked at /Users/u/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/"
            f"primitive-types-0.14.0/src/lib.rs:43:1:\n{message}\n")


NOT_CONCRETE = "error[SC0401]: cannot specialize expression: type is not concrete\n"
STACK_TOO_DEEP = ("export-rust-yul: Yul compilation rejected: Uncaught exception:\n/solidity/libyul/backends/evm/"
                  "EVMObjectCompiler.cpp(133): Throw in function void solidity::yul::EVMObjectCompiler::run(const Object &, "
                  "bool, bool)\nDynamic exception type: boost::wrapexcept<solidity::yul::StackTooDeepError>\n")
DEMANDED_BITS = ["<sonatina_codegen::analysis::demanded_bits::DemandedBitsQuery>::propagate_binary",
                 "<sonatina_codegen::analysis::demanded_bits::DemandedBitsQuery>::propagate_from_value"]
SIGNEXTEND_FOLD = ["sonatina_codegen::optim::simplify_expr::fold_evm_signextend_raw",
                   "sonatina_codegen::optim::simplify_expr::fold_evm_signextend"]
UPSTREAM_OCCURRENCES = [
    ("fuzz-driver", "runtime-assembly-loops", "sonatina-o2", "compiler-crash", "rust-code-images",
     panic(44674409, "Integer overflow when casting to usize"), DEMANDED_BITS),
    ("fuzz-driver", "runtime-trait-hierarchies", "yul", "source-rejected", "rust-checked-source",
     NOT_CONCRETE, None),
    ("fuzz-driver", "runtime-assembly", "yul", "compiler-crash", "rust-code-images",
     panic(44931323, "Integer overflow when casting to usize"), DEMANDED_BITS),
    ("fuzz-driver", "runtime-traits", "yul", "compilation-rejected", "rust-yul-evm",
     STACK_TOO_DEEP, None),
    ("fuzz-driver", "runtime-trait-hierarchies", "sonatina-o2", "source-rejected", "rust-checked-source",
     NOT_CONCRETE, None),
    ("fuzz-driver", "runtime-comptime", "sonatina-o2", "compiler-crash", "rust-code-images",
     panic(44552049, "arithmetic operation overflow"), SIGNEXTEND_FOLD),
    ("fuzz-driver", "runtime-assembly", "sonatina-o0", "compiler-crash", "rust-code-images",
     panic(44575855, "Integer overflow when casting to usize"), DEMANDED_BITS),
    ("fuzz-driver", "runtime-trait-hierarchies", "sonatina-o0", "source-rejected", "rust-checked-source",
     NOT_CONCRETE, None),
    ("semantic-log-sonatina-o2-random", "stateful-logs", "sonatina-o2", "compiler-crash", "rust-code-images",
     panic(10515142, "arithmetic operation overflow"), SIGNEXTEND_FOLD),
    ("semantic-dynamic-array-sonatina-o2-random-8tx", "stateful-dynamic-array", "sonatina-o2", "compiler-crash", "rust-code-images",
     panic(17103123, "arithmetic operation overflow"), SIGNEXTEND_FOLD),
    ("semantic-forward-sonatina-o2-random", "stateful-forwarded-value", "sonatina-o2", "compiler-crash", "rust-code-images",
     panic(12156346, "Integer overflow when casting to usize"), DEMANDED_BITS),
    ("semantic-primitive-sonatina-o2-random", "runtime-primitives", "sonatina-o2", "compiler-crash", "rust-code-images",
     panic(5298705, "Integer overflow when casting to usize"), DEMANDED_BITS),
    ("semantic-call-graph-sonatina-o2-random", "runtime-call-graphs", "sonatina-o2", "compiler-crash", "rust-code-images",
     panic(5864229, "Integer overflow when casting to usize"), DEMANDED_BITS),
    ("semantic-aggregate-call-graph-sonatina-o2-random", "runtime-aggregate-call-graphs", "sonatina-o2", "compiler-crash", "rust-code-images",
     panic(7454700, "Integer overflow when casting to usize"), DEMANDED_BITS),
    ("semantic-dynamic-array-sonatina-o2-random", "stateful-dynamic-array", "sonatina-o2", "compiler-crash", "rust-code-images",
     panic(9974443, "Integer overflow when casting to usize"), DEMANDED_BITS),
    ("semantic-comptime-sonatina-o2-random-g0v3", "runtime-comptime", "sonatina-o2", "compiler-crash", "rust-code-images",
     panic(17285329, "arithmetic operation overflow"), SIGNEXTEND_FOLD),
    ("unit-13-random-o2", "stateful-keyed-storage", "sonatina-o2", "compiler-crash", "rust-code-images",
     panic(52219250, "arithmetic operation overflow"), SIGNEXTEND_FOLD),
    ("unit-13-random-o2", "stateful-adt-storage", "sonatina-o2", "compiler-crash", "rust-code-images",
     panic(53252371, "arithmetic operation overflow"), SIGNEXTEND_FOLD),
    ("semantic-unit13-traits/fixed-yul", "runtime-traits", "yul", "compilation-rejected", "rust-yul-evm",
     STACK_TOO_DEEP, None),
    ("semantic-unit14-hierarchies/fixed-yul", "runtime-trait-hierarchies", "yul", "compilation-rejected", "rust-yul-evm",
     STACK_TOO_DEEP, None),
]

# Real occurrences of Sonatina O0's recorded defect "Sonatina O0 returns other Words
# for loops that write std memory values" (questions.md), all with this fingerprint:
# lane A's fixed and random O0 suites of runtime-memory-values at 35925b5f8, and a
# fuzz-driver run on O0 alone from root seed 1 with eight functions per iteration on
# main 2575105be, whose iteration 0 repeats lane A's random suite. Each row is one
# final plan's steps, reduced or the original, with the cases that ended at it.
MEMORY_LOOP_FINGERPRINT = {"backend": "sonatina-o0", "category": "semantic-mismatch",
                           "disagreeingPairs": ["directCore/rustEvm", "importedHull/rustEvm"],
                           "pathShapes": {"directCore": {"payload": "word", "status": "returned"},
                                          "importedHull": {"payload": "word", "status": "returned"},
                                          "rustEvm": {"payload": "word", "status": "returned"}},
                           "stage": None, "synthetic": False}
MEMORY_LOOP_PLANS = [
    ("lane A fixed O0 cases 185, 187 (reduced)", 2,
     '[{"action":{"build":"to_bytes","kind":"bytes","parts":[{"operand":{"operand":"input"},"part":"word"}]}},'
     '{"action":{"cut":"take","kind":"slice","length":26,"source":"sc_b0"}},{"body":[{"access":{"access":"length"},'
     '"constant":3,"fold":"add","kind":"observe","value":"sc_b0"},{"cut":"drop","kind":"slice","source":"sc_s0",'
     '"start":12}],"loop":{"form":"single","mask":1}}]'),
    ("lane A fixed O0 case 189 (reduced)", 1,
     '[{"action":{"elements":[{"constant":118,"operand":"mul"},{"operand":"acc"}],"form":"literal","kind":"array"}},'
     '{"action":{"build":"to_bytes","kind":"bytes","parts":[{"operand":{"operand":"input"},"part":"word"}]}},'
     '{"action":{"cut":"take","kind":"slice","length":26,"source":"sc_b0"}},{"body":[{"access":{"access":"hash"},'
     '"constant":11,"fold":"add","kind":"observe","value":"sc_s0"},{"access":{"access":"byte",'
     '"index":{"index":"literal","value":22}},"constant":13,"fold":"add","kind":"observe","value":"sc_b0"},'
     '{"cut":"drop","kind":"slice","source":"sc_s0","start":12}],"loop":{"form":"single","mask":1}}]'),
    ("lane A fixed O0 case 191 (original)", 1,
     '[{"action":{"elements":[{"constant":118,"operand":"mul"},{"operand":"acc"}],"form":"literal","kind":"array"}},'
     '{"action":{"build":"to_bytes","kind":"bytes","parts":[{"operand":{"operand":"input"},"part":"word"}]}},'
     '{"action":{"cut":"take","kind":"slice","length":26,"source":"sc_b0"}},{"action":{"access":{"access":"hash"},'
     '"constant":31,"fold":"add","kind":"observe","value":"sc_b0"}},{"action":{"access":{"access":"element",'
     '"form":"index","index":{"index":"input","modulus":2,"shift":3}},"constant":9,"fold":"xor","kind":"observe",'
     '"value":"sc_a0"}},{"body":[{"access":{"access":"hash"},"constant":11,"fold":"add","kind":"observe",'
     '"value":"sc_s0"},{"access":{"access":"byte","index":{"index":"literal","value":22}},"constant":13,"fold":"add",'
     '"kind":"observe","value":"sc_b0"},{"cut":"drop","kind":"slice","source":"sc_s0","start":12}],'
     '"loop":{"form":"single","mask":1}}]'),
    ("lane A random O0 case 25; driver iteration 0 case 25 (reduced)", 2,
     '[{"action":{"build":"to_bytes","kind":"bytes","parts":[{"operand":{"operand":"input"},"part":"word"}]}},'
     '{"action":{"kind":"alias","source":"sc_b0"}},{"body":[{"access":{"access":"length"},"constant":3,"fold":"add",'
     '"kind":"observe","value":"sc_b1"},{"form":"helper","index":{"index":"literal","value":0},"kind":"write",'
     '"target":"sc_b1","value":{"operand":"input"},"width":"byte"}],"loop":{"form":"single","mask":1}}]'),
    ("lane A random O0 case 26; driver iteration 0 case 26 (reduced)", 2,
     '[{"action":{"build":"concat","kind":"bytes","parts":[{"operand":{"operand":"input"},"part":"word"},{"count":32,'
     '"part":"zeros"}]}},{"action":{"kind":"alias","source":"sc_b0"}},{"body":[{"access":{"access":"word",'
     '"index":{"index":"literal","value":9}},"constant":13,"fold":"add","kind":"observe","value":"sc_b1"},'
     '{"form":"helper","index":{"index":"literal","value":58},"kind":"write","target":"sc_b1",'
     '"value":{"constant":145,"operand":"xor"},"width":"byte"}],"loop":{"form":"single","mask":3}},'
     '{"action":{"elements":[{"operand":"acc"},{"constant":252,"operand":"mul"}],"form":"literal","kind":"array"}}]'),
    ("lane A random O0 cases 27, 29, 31, 33, 34, 35; driver iteration 0 cases 27, 29, 31, 33, 34, 35 (original)", 12,
     '[{"action":{"build":"concat","kind":"bytes","parts":[{"operand":{"operand":"input"},"part":"word"},{"count":32,'
     '"part":"zeros"}]}},{"action":{"kind":"alias","source":"sc_b0"}},{"action":{"access":{"access":"length"},'
     '"constant":17,"fold":"xor","kind":"observe","value":"sc_b0"}},{"body":[{"access":{"access":"word",'
     '"index":{"index":"literal","value":9}},"constant":13,"fold":"add","kind":"observe","value":"sc_b1"},'
     '{"form":"helper","index":{"index":"literal","value":58},"kind":"write","target":"sc_b1",'
     '"value":{"constant":145,"operand":"xor"},"width":"byte"}],"loop":{"form":"single","mask":3}},'
     '{"action":{"elements":[{"constant":211,"operand":"mul"}],"form":"allocated","kind":"array"}},'
     '{"action":{"elements":[{"operand":"acc"},{"constant":252,"operand":"mul"}],"form":"literal","kind":"array"}}]'),
    ("driver iteration 1 case 25 (reduced)", 1,
     '[{"body":[{"build":"concat","kind":"bytes","parts":[{"count":32,"part":"zeros"},{"count":0,"part":"zeros"}]},'
     '{"access":{"access":"length"},"constant":3,"fold":"add","kind":"observe","value":"sc_b0"},{"form":"inline",'
     '"index":{"index":"literal","value":0},"kind":"write","target":"sc_b0","value":{"operand":"input"},'
     '"width":"byte"}],"loop":{"form":"single","mask":1}}]'),
    ("driver iteration 3 cases 51, 53, 55, 56, 57, 59 (original)", 6,
     '[{"action":{"build":"to_bytes","kind":"bytes","parts":[{"operand":{"operand":"input"},"part":"word"}]}},'
     '{"body":[{"access":{"access":"hash"},"constant":31,"fold":"add","kind":"observe","value":"sc_b0"},'
     '{"form":"inline","index":{"index":"literal","value":20},"kind":"write","target":"sc_b0",'
     '"value":{"constant":187,"operand":"xor"},"width":"byte"},{"build":"to_bytes","kind":"bytes",'
     '"parts":[{"count":0,"part":"zeros"}]}],"loop":{"form":"single","mask":3}},{"action":{"access":{"access":"byte",'
     '"index":{"index":"literal","value":4}},"constant":31,"fold":"add","kind":"observe","value":"sc_b0"}}]'),
    ("driver iteration 1 cases 27, 29, 31, 32, 33, 34, 35 (original)", 7,
     '[{"body":[{"build":"concat","kind":"bytes","parts":[{"count":32,"part":"zeros"},{"count":0,"part":"zeros"}]},'
     '{"access":{"access":"length"},"constant":3,"fold":"xor","kind":"observe","value":"sc_b0"},{"form":"inline",'
     '"index":{"index":"literal","value":11},"kind":"write","target":"sc_b0","value":{"operand":"counter"},'
     '"width":"byte"}],"loop":{"form":"single","mask":7}}]'),
    ("driver iteration 3 case 50 (reduced)", 1,
     '[{"action":{"build":"to_bytes","kind":"bytes","parts":[{"operand":{"operand":"input"},"part":"word"}]}},'
     '{"body":[{"access":{"access":"hash"},"constant":31,"fold":"add","kind":"observe","value":"sc_b0"},'
     '{"form":"inline","index":{"index":"literal","value":20},"kind":"write","target":"sc_b0",'
     '"value":{"constant":187,"operand":"xor"},"width":"byte"},{"build":"to_bytes","kind":"bytes",'
     '"parts":[{"count":0,"part":"zeros"}]}],"loop":{"form":"single","mask":3}}]'),
    ("driver iteration 1 case 26 (reduced)", 1,
     '[{"body":[{"build":"concat","kind":"bytes","parts":[{"count":32,"part":"zeros"},{"count":0,"part":"zeros"}]},'
     '{"access":{"access":"length"},"constant":3,"fold":"add","kind":"observe","value":"sc_b0"},{"form":"inline",'
     '"index":{"index":"literal","value":11},"kind":"write","target":"sc_b0","value":{"operand":"counter"},'
     '"width":"byte"}],"loop":{"form":"single","mask":3}}]'),
    ("driver iteration 3 case 49 (reduced)", 1,
     '[{"action":{"build":"to_bytes","kind":"bytes","parts":[{"operand":{"operand":"input"},"part":"word"}]}},'
     '{"body":[{"access":{"access":"length"},"constant":3,"fold":"add","kind":"observe","value":"sc_b0"},'
     '{"form":"inline","index":{"index":"literal","value":0},"kind":"write","target":"sc_b0",'
     '"value":{"operand":"input"},"width":"byte"},{"build":"to_bytes","kind":"bytes","parts":[{"count":0,'
     '"part":"zeros"}]}],"loop":{"form":"single","mask":1}}]'),
]


def memory_mismatch(program, steps):
    """A memory-value mismatch with the real fingerprint, on the run's backend, and a final case of these steps."""
    case = {"memoryValuePlan": {"schema": "solcore-lean.memory-value-plan.v1", "steps": steps}}
    return ("semantic-mismatch", "", program, None, {"fingerprint": MEMORY_LOOP_FINGERPRINT, "case": case})


class FakeSuite:
    """Writes a suite-shaped output for each requested (seed, backend)."""

    def __init__(self, scenario, stage=None):
        self.scenario = scenario
        self.stage = stage
        self.calls = []

    def __call__(self, argv, stdout_path, stderr_path, stop, grace=120.0):
        value = lambda name: argv[argv.index(name) + 1]
        output, backend, seed = Path(value("--output")), value("--backend"), int(value("--seed"))
        profiles = [argv[index + 1] for index, item in enumerate(argv) if item == "--profile"]
        self.calls.append({"backend": backend, "seed": seed, "profiles": profiles})
        stdout_path.write_text("")
        stderr_path.write_text("")
        rows = self.scenario(seed, backend)
        if rows is None:
            return 2, False
        output.mkdir(parents=True)
        summary_rows = []
        for index, (profile, findings) in enumerate(rows):
            folder = output / f"{index:02d}-{profile}"
            (folder / "cases").mkdir(parents=True)
            (folder / "cases/0000.json").write_text("{}")
            (folder / "summary.json").write_text("{}")
            (folder / "generation.json").write_text("{}")
            (output / f"{index:02d}-{profile}.stdout.log").write_text("log")
            entries = []
            for case, (category, detail, program, *site) in enumerate(findings):
                real = site[1] if len(site) > 1 else {}
                location = folder / "findings/real" / f"{case:04d}"
                (location / "original").mkdir(parents=True)
                (location / "original/analysis.json").write_text(json.dumps({"comparison": {"category": category, "detail": detail}}))
                if "case" in real:
                    (location / "original/case.json").write_text(json.dumps(real["case"]))
                if site and site[0]:
                    work = output / ".work" / f"run-{case:06d}"
                    (location / "original/case.sol").write_text("contract C {}")
                    (location / "original/report.json").write_text(json.dumps({"processes": [
                        {"stage": "rust-checked-source", "returncode": 0, "command": ["true"]},
                        {"stage": "rust-code-images", "returncode": 2, "command": [
                            sys.executable, str(self.stage), f"{work}/case.sol", "--root", str(work), "--frame",
                            *(site[0] if isinstance(site[0], list) else [site[0]])]}]}))
                (location / "shrink.json").write_text("{}")
                fingerprint = {"backend": backend, "category": category, "stage": "rust-code-images",
                               "disagreeingPairs": ["directCore/rustEvm"] if category == "semantic-mismatch" else [],
                               "synthetic": False}
                entries.append({"caseIndex": case, "synthetic": False, "finalCaseSha256": program,
                                "fingerprint": {**real["fingerprint"], "backend": backend} if "fingerprint" in real else fingerprint,
                                "originalArchive": f"findings/real/{case:04d}/original", "history": f"findings/real/{case:04d}/shrink.json",
                                "finalArchive": f"findings/real/{case:04d}/original"})
            summary_rows.append({"profile": profile, "status": "failed" if findings else "passed", "output": folder.name,
                                 "seed": str(seed), "findings": entries, "secondaryFindings": [], "command": ["campaign"],
                                 "campaign": {"counts": {"executed": 4, "matched": 4 - len(findings), "errors": len(findings)},
                                              "generation": {"requested": 4, "generatorVersions": [f"{profile}-v2"],
                                                             "acceptances": ["exclude-boundary-identity-v1"],
                                                             "transactions": 8},
                                              "compilation": {"policy": "fixture", "distinctSources": 2, "compiled": 2,
                                                              "reused": 2}}})
        status = "failed" if any(row["findings"] for row in summary_rows) else "passed"
        counts = {"executed": 4 * len(rows), "matched": sum(row["campaign"]["counts"]["matched"] for row in summary_rows)}
        fuzz.save(output / "summary.json", {"schema": "solcore-lean.semantic-suite.v1", "status": status,
                                            "profiles": summary_rows, "unexecutedProfiles": [], "counts": counts})
        return (0 if status == "passed" else 1), False


class FuzzTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="semantic-fuzz-test-")
        self.directory = Path(self.temporary.name).resolve()
        self.state = self.directory / "state"
        self.receipt = self.directory / "semantic-tools-build.json"
        self.receipt.write_text('{"tools": 1}')
        patcher = patch.object(fuzz, "verify_tools", lambda config: self.receipt)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.stage = self.directory / "fake_stage.py"
        self.stage.write_text(FAKE_STAGE)

    def tearDown(self):
        self.temporary.cleanup()

    def main(self, *argv, scenario=lambda seed, backend: [("closed-g0", [])]):
        fake = FakeSuite(scenario, self.stage)
        with patch.object(fuzz, "run_suite", fake), contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            code = fuzz.main(list(argv))
        return code, fake

    def start(self, *argv, **kwargs):
        return self.main("run", "--state", str(self.state), "--base-seed", "100", "--backend", "sonatina-o0",
                         "--backend", "sonatina-o2", "--profile", "closed-g0", "--profile", "runtime-primitives",
                         "--examples", "2", *argv, **kwargs)

    def ledger(self):
        return fuzz.State(self.state).ledger()

    def registry(self):
        return fuzz.State(self.state).registry()

    def test_symptoms_ignore_run_detail_and_mismatches_keep_their_program(self):
        first = fuzz.symptom(crash(thread=1, user="a")[1])
        self.assertEqual(first, fuzz.symptom(crash(thread=99, user="b")[1]))
        self.assertEqual(first, {"panic": "primitive-types-0.14.0/src/lib.rs:43:1", "message": "Integer overflow when casting to usize"})
        self.assertNotEqual(first, fuzz.symptom(crash("arithmetic operation overflow")[1]))
        self.assertEqual(fuzz.symptom("note: building\nerror[SC0231]: value 12 at /tmp/x/y.sol differs\n"),
                         {"message": "error[SC0231]: value <n> at <path> differs"})
        fingerprint = {"backend": "sonatina-o0", "category": "semantic-mismatch", "stage": "comparison", "disagreeingPairs": ["a/b"]}
        keys = [fuzz.signature_key("closed-g0", fingerprint, "", program) for program in ("1" * 64, "2" * 64)]
        self.assertNotEqual(fuzz.canonical_id(keys[0]), fuzz.canonical_id(keys[1]))
        crash_fingerprint = {**fingerprint, "category": "compiler-crash"}
        self.assertEqual(fuzz.canonical_id(fuzz.signature_key("closed-g0", crash_fingerprint, crash()[1], "1" * 64)),
                         fuzz.canonical_id(fuzz.signature_key("stateful-logs", crash_fingerprint, crash(user="c")[1], "2" * 64)))

    def test_run_registers_retains_examples_and_prunes(self):
        def scenario(seed, backend):
            if backend == "sonatina-o0":
                return [("closed-g0", []), ("runtime-primitives", [])]
            return [("closed-g0", [mismatch("b" * 64)]), ("runtime-primitives", [crash(), crash(thread=8), crash(thread=9)])]
        code, fake = self.start("--iterations", "1", scenario=scenario)
        self.assertEqual(code, 0)
        self.assertEqual([(call["backend"], call["seed"]) for call in fake.calls], [("sonatina-o0", 100), ("sonatina-o2", 100)])
        rows = self.ledger()
        self.assertEqual([(row["iteration"], row["backend"], row["suiteStatus"]) for row in rows],
                         [(0, "sonatina-o0", "passed"), (0, "sonatina-o2", "failed")])
        signatures = self.registry()["signatures"]
        self.assertEqual(sorted(entry["count"] for entry in signatures.values()), [1, 3])
        crashed = next(entry for entry in signatures.values() if entry["category"] == "compiler-crash")
        self.assertEqual(len(crashed["examples"]), 2)
        for example in crashed["examples"]:
            self.assertTrue((self.state / example / "original/analysis.json").exists())
            self.assertEqual(json.loads((self.state / example / "occurrence.json").read_text())["rootSeed"], "100")
        self.assertEqual([occurrence["new"] for occurrence in rows[1]["occurrences"]], [True, True, False, False])
        self.assertFalse((self.state / "runs/000000/sonatina-o0").exists())
        kept = self.state / "runs/000000/sonatina-o2"
        self.assertTrue((kept / "summary.json").exists())
        self.assertEqual(sorted(path.name for path in (kept / "01-runtime-primitives").iterdir()), ["generation.json", "summary.json"])
        self.assertFalse((kept / "01-runtime-primitives/findings").exists())
        report = (self.state / "report.md").read_text()
        self.assertIn("untriaged (new)", report)
        self.assertIn("Integer overflow when casting to usize", report)

    def test_seed_progression_resumes_and_configuration_is_fixed(self):
        self.start("--iterations", "2")
        code, fake = self.main("run", "--state", str(self.state), "--iterations", "1")
        self.assertEqual(code, 0)
        self.assertEqual([(call["backend"], call["seed"]) for call in fake.calls], [("sonatina-o0", 102), ("sonatina-o2", 102)])
        self.assertEqual([row["rootSeed"] for row in self.ledger()], ["100", "100", "101", "101", "102", "102"])
        # Seeds replay with the generation fields each profile recorded.
        self.assertEqual({json.dumps(entry["generation"], sort_keys=True) for row in self.ledger() for entry in row["profiles"]},
                         {json.dumps({"acceptances": ["exclude-boundary-identity-v1"], "generatorVersions": ["closed-g0-v2"],
                                      "transactions": 8}, sort_keys=True)})
        # So do their shared-compilation counts, without the policy text.
        self.assertEqual({json.dumps(entry["compilation"], sort_keys=True) for row in self.ledger() for entry in row["profiles"]},
                         {json.dumps({"compiled": 2, "distinctSources": 2, "reused": 2}, sort_keys=True)})
        code, fake = self.main("run", "--state", str(self.state), "--cases", "8")
        self.assertEqual((code, fake.calls), (2, []))

    def test_repeated_signatures_count_without_new_examples(self):
        self.start("--iterations", "3", scenario=lambda seed, backend: [("runtime-primitives", [crash(thread=seed)])])
        # The backend is part of a signature: the same panic on O0 and O2 is triaged separately.
        signatures = self.registry()["signatures"].values()
        self.assertEqual(sorted((entry["key"]["backend"], entry["count"], len(entry["examples"])) for entry in signatures),
                         [("sonatina-o0", 3, 2), ("sonatina-o2", 3, 2)])
        entry = next(entry for entry in signatures if entry["key"]["backend"] == "sonatina-o2")
        self.assertEqual(entry["backends"], {"sonatina-o2": 3})
        self.assertEqual((entry["firstSeen"]["iteration"], entry["lastSeen"]["iteration"]), (0, 2))
        self.assertEqual(sum(occurrence["new"] for row in self.ledger() for occurrence in row["occurrences"]), 2)

    def test_finished_unrecorded_run_is_recorded_once(self):
        self.start("--iterations", "1")
        state = fuzz.State(self.state)
        FakeSuite(lambda seed, backend: [("runtime-primitives", [crash()])])(
            ["--output", str(state.run_directory(1, "sonatina-o0")), "--backend", "sonatina-o0", "--seed", "101"],
            self.directory / "out.log", self.directory / "err.log", None)
        registry = state.registry()
        code, fake = self.main("run", "--state", str(self.state), "--iterations", "1")
        self.assertEqual(code, 0)
        self.assertEqual([call["backend"] for call in fake.calls], ["sonatina-o2"])
        self.assertEqual([(row["iteration"], row["backend"]) for row in self.ledger()][2:], [(1, "sonatina-o0"), (1, "sonatina-o2")])
        entry, = state.registry()["signatures"].values()
        self.assertEqual(entry["count"], 1)
        # Processing the same run again must not count it twice.
        fuzz.register(state, json.loads(state.config_path.read_text()), {"id": "e"}, 1, "sonatina-o0",
                      self.directory / "absent", {"profiles": [{"profile": "runtime-primitives", "output": "x",
                                                                "findings": [{"fingerprint": {"category": "compiler-crash"}}]}]})
        self.assertEqual(state.registry()["signatures"][entry["id"]]["count"], 1)
        self.assertEqual(registry["processedRuns"], ["000000-sonatina-o0", "000000-sonatina-o2"])

    def test_interrupted_run_is_set_aside_and_rerun_from_its_seed(self):
        self.start("--iterations", "1")
        run_dir = fuzz.State(self.state).run_directory(1, "sonatina-o0")
        (run_dir / "00-closed-g0/findings/real/0000").mkdir(parents=True)
        fuzz.save(run_dir / "summary.json", {"status": "running", "profiles": []})
        code, fake = self.main("run", "--state", str(self.state), "--iterations", "1")
        self.assertEqual(code, 0)
        self.assertEqual([(call["backend"], call["seed"]) for call in fake.calls], [("sonatina-o0", 101), ("sonatina-o2", 101)])
        kept, = (self.state / "interrupted").iterdir()
        self.assertTrue((kept / "run/00-closed-g0/findings/real/0000").is_dir())
        self.assertIn("interrupted/" + kept.name, (self.state / "report.md").read_text())

    def test_stop_signal_interrupts_the_running_suite(self):
        def interrupting(argv, stdout_path, stderr_path, stop, grace=120.0):
            output = Path(argv[argv.index("--output") + 1])
            (output / "00-closed-g0/findings/real/0000").mkdir(parents=True)
            fuzz.save(output / "summary.json", {"status": "inconclusive-resource", "stop": "interrupted", "profiles": []})
            return 1, True
        with patch.object(fuzz, "run_suite", interrupting), contextlib.redirect_stdout(io.StringIO()):
            code = fuzz.main(["run", "--state", str(self.state), "--base-seed", "5", "--backend", "sonatina-o0", "--profile", "closed-g0"])
        self.assertEqual((code, self.ledger()), (0, []))
        self.assertEqual(len(list((self.state / "interrupted").iterdir())), 1)

    def test_epoch_change_stops_until_accepted(self):
        self.start("--iterations", "1")
        self.receipt.write_text('{"tools": 2}')
        code, fake = self.main("run", "--state", str(self.state), "--iterations", "1")
        self.assertEqual((code, fake.calls), (3, []))
        code, fake = self.main("run", "--state", str(self.state), "--iterations", "1", "--accept-new-epoch")
        self.assertEqual((code, len(fake.calls)), (0, 2))
        epochs = json.loads((self.state / "state.json").read_text())["epochs"]
        self.assertEqual([epoch["firstIteration"] for epoch in epochs], [0, 1])
        self.assertEqual(len({row["epoch"] for row in self.ledger()}), 2)

    def test_labels_mark_signatures_known_without_hiding_them(self):
        self.start("--iterations", "2",
                   scenario=lambda seed, backend: [("runtime-primitives", [crash()] if backend == "sonatina-o2" else [])])
        sid, = self.registry()["signatures"]
        self.assertEqual(self.main("label", "--state", str(self.state), sid, "Q013 constant shift")[0], 0)
        report = json.loads((self.state / "report.json").read_text())
        self.assertEqual([(entry["triage"], entry["label"], entry["count"]) for entry in report["signatures"]],
                         [("known", "Q013 constant shift", 2)])
        self.assertIn("known: Q013 constant shift", (self.state / "report.md").read_text())
        self.assertEqual(self.main("label", "--state", str(self.state), sid, "--clear")[0], 0)
        self.assertEqual(json.loads((self.state / "report.json").read_text())["signatures"][0]["triage"], "untriaged")
        self.assertEqual(self.main("label", "--state", str(self.state), "missing", "text")[0], 2)

    def test_upstream_findings_of_questions_md_are_known_by_their_real_occurrences(self):
        keys = set()
        for source, profile, backend, category, stage, detail, site in UPSTREAM_OCCURRENCES:
            fingerprint = {"backend": backend, "category": category, "stage": stage}
            sid = fuzz.canonical_id(fuzz.signature_key(profile, fingerprint, detail, "a" * 64, site))
            self.assertIn(sid, fuzz.KNOWN, (source, profile, backend))
            keys.add(sid)
        # Every listed suite signature has an occurrence; each is a symptom, never a reduced program.
        self.assertEqual({fuzz.canonical_id(key) for key, _ in fuzz.KNOWN_FINDINGS} - keys,
                         {fuzz.canonical_id(key) for key, _ in fuzz.KNOWN_FINDINGS if key["backend"] == fuzz.FIXTURES})
        self.assertTrue(all("symptom" in key and "program" not in key for key, _ in fuzz.KNOWN_FINDINGS))
        _, profile, backend, category, stage, detail, _ = UPSTREAM_OCCURRENCES[0]
        fingerprint = {"backend": backend, "category": category, "stage": stage}
        for site in (["sonatina_codegen::optim::a", "sonatina_codegen::optim::b"], ["not reproduced"], None):
            self.assertNotIn(fuzz.canonical_id(fuzz.signature_key(profile, fingerprint, detail, None, site)), fuzz.KNOWN)
        mismatched = {**fingerprint, "category": "semantic-mismatch", "stage": "comparison", "disagreeingPairs": ["a/b"]}
        self.assertNotIn(fuzz.canonical_id(fuzz.signature_key(profile, mismatched, "", "a" * 64)), fuzz.KNOWN)

    def test_runs_count_known_upstream_findings_but_never_as_new(self):
        def scenario(seed, backend):
            if backend == "sonatina-o0":
                return [("runtime-primitives", [])]
            return [("runtime-assembly-loops", [crash(site=DEMANDED_BITS), crash(site=SIGNEXTEND_FOLD),
                                                crash("arithmetic operation overflow", site=SIGNEXTEND_FOLD),
                                                mismatch("b" * 64)])]
        code, _ = self.start("--iterations", "1", scenario=scenario)
        self.assertEqual(code, 0)
        row, = [row for row in self.ledger() if row["backend"] == "sonatina-o2"]
        self.assertEqual([occurrence["new"] for occurrence in row["occurrences"]], [False, True, False, True])
        signatures = self.registry()["signatures"]
        known = [sid for sid in signatures if sid in fuzz.KNOWN]
        self.assertEqual(sorted(signatures[sid]["key"]["symptom"]["message"] for sid in known),
                         ["Integer overflow when casting to usize", "arithmetic operation overflow"])
        self.assertTrue(all(signatures[sid]["count"] == 1 for sid in signatures))
        report = (self.state / "report.md").read_text()
        self.assertIn("known: Sonatina O2 demanded-bits overflow", report)
        self.assertIn("known: Sonatina O2 signextend folding overflow", report)

    def final_case(self, steps):
        """A final archive holding a memory-value case of these plan steps."""
        folder = Path(tempfile.mkdtemp(dir=self.directory))
        folder.joinpath("case.json").write_text(json.dumps(
            {"memoryValuePlan": {"schema": "solcore-lean.memory-value-plan.v1", "steps": steps}}))
        return folder

    def test_recorded_mismatch_classes_hold_their_real_occurrences(self):
        (key, _, _, label), = fuzz.MISMATCH_CLASSES
        self.assertEqual(sum(count for _, count, _ in MEMORY_LOOP_PLANS), 37)
        for source, _, steps in MEMORY_LOOP_PLANS:
            final = self.final_case(json.loads(steps))
            self.assertEqual(fuzz.signature_key("runtime-memory-values", MEMORY_LOOP_FINGERPRINT, "", "a" * 64, None, final),
                             key, source)
        self.assertEqual(fuzz.KNOWN[fuzz.canonical_id(key)], label)
        self.assertNotIn("program", key)
        # Without its final case an occurrence keeps the key it had before the classes.
        self.assertEqual(fuzz.signature_key("runtime-memory-values", MEMORY_LOOP_FINGERPRINT, "", "a" * 64)["program"], "a" * 64)

    def test_mismatch_classes_leave_near_misses_new(self):
        steps = json.loads(MEMORY_LOOP_PLANS[3][2])  # MemorySize.len(sc_b1) and then sc_put8(sc_b1, 0, sc_x)
        *before, loop = steps
        observe, write = loop["body"]
        plans = {"a write alone": [*before, {**loop, "body": [write]}],
                 "a write before the observation": [*before, {**loop, "body": [write, observe]}],
                 "an array write": [*before, {**loop, "body": [observe, {**write, "target": "sc_a0"}]}],
                 "an array observation": [*before, {**loop, "body": [{**observe, "value": "sc_a0"}, write]}],
                 "no loop": [*before, {"action": observe}, {"action": write}],
                 "a nested loop": [*before, {**loop, "loop": {"form": "nested", "outer": 1, "bound": "input", "inner": 1}}]}
        reverted = {**MEMORY_LOOP_FINGERPRINT["pathShapes"], "rustEvm": {"payload": "bytes", "status": "reverted"}}
        fingerprints = {"O2": {"backend": "sonatina-o2"}, "Yul": {"backend": "yul"},
                        "Core and Hull disagreeing": {"disagreeingPairs": ["directCore/importedHull", "directCore/rustEvm"]},
                        "a revert": {"pathShapes": reverted}, "a synthetic mismatch": {"synthetic": True}}
        cases = [(name, "runtime-memory-values", {}, plan) for name, plan in plans.items()]
        cases += [(name, "runtime-memory-values", changes, steps) for name, changes in fingerprints.items()]
        cases.append(("another profile on O0", "runtime-assembly-memory", {}, steps))
        for name, profile, changes, plan in cases:
            fingerprint = {**MEMORY_LOOP_FINGERPRINT, **changes}
            key = fuzz.signature_key(profile, fingerprint, "", "b" * 64, None, self.final_case(plan))
            self.assertEqual(key, fuzz.signature_key(profile, fingerprint, "", "b" * 64), name)
            self.assertNotIn(fuzz.canonical_id(key), fuzz.KNOWN, name)
        # A final case that cannot be read stays outside every class.
        self.assertEqual(fuzz.signature_key("runtime-memory-values", MEMORY_LOOP_FINGERPRINT, "", "b" * 64, None,
                                            self.directory / "missing")["program"], "b" * 64)

    def test_runs_count_mismatch_class_occurrences_as_known(self):
        known = [memory_mismatch(str(index) * 64, json.loads(steps)) for index, (_, _, steps) in enumerate(MEMORY_LOOP_PLANS[:3], 1)]
        *before, loop = json.loads(MEMORY_LOOP_PLANS[0][2])
        alone = memory_mismatch("4" * 64, [*before, {**loop, "body": loop["body"][1:]}])

        def scenario(seed, backend):
            return [("runtime-memory-values", known + [alone] if backend == "sonatina-o0" else known)]
        code, _ = self.main("run", "--state", str(self.state), "--base-seed", "100", "--backend", "sonatina-o0",
                            "--backend", "sonatina-o2", "--profile", "runtime-memory-values", "--examples", "2",
                            "--iterations", "1", scenario=scenario)
        self.assertEqual(code, 0)
        rows = {row["backend"]: row for row in self.ledger()}
        self.assertEqual([occurrence["new"] for occurrence in rows["sonatina-o0"]["occurrences"]], [False, False, False, True])
        # The same pattern on O2 is no occurrence of the O0 class.
        self.assertEqual([occurrence["new"] for occurrence in rows["sonatina-o2"]["occurrences"]], [True, True, True])
        entry = self.registry()["signatures"][fuzz.canonical_id(fuzz.MISMATCH_CLASSES[0][0])]
        self.assertEqual((entry["count"], entry["backends"], len(entry["examples"])), (3, {"sonatina-o0": 3}, 2))
        self.assertEqual([brief["program"] for brief in entry["recent"]], ["1" * 64, "2" * 64, "3" * 64])
        report = (self.state / "report.md").read_text()
        self.assertIn("known: Sonatina O0 returns other Words for loops that write std memory values", report)
        self.assertIn("class loop-observes-then-slices-or-writes", report)

    def test_stop_file_lock_and_disk_limit_prevent_runs(self):
        self.start("--iterations", "1")
        (self.state / "STOP").write_text("")
        code, fake = self.main("run", "--state", str(self.state))
        self.assertEqual((code, fake.calls), (0, []))
        (self.state / "STOP").unlink()
        with fuzz.State(self.state).lock():
            code, fake = self.main("run", "--state", str(self.state))
        self.assertEqual((code, fake.calls), (2, []))
        code, fake = self.main("run", "--state", str(self.state), "--max-state-bytes", "1")
        self.assertEqual((code, fake.calls), (4, []))

    def test_missing_summaries_are_problems_notify_and_stop(self):
        notes = self.directory / "notes.txt"
        command = f"{sys.executable} -c \"import os,sys; open(sys.argv[1],'a').write(os.environ['SEMANTIC_FUZZ_PROBLEMS']+'\\n')\" {notes}"
        code, fake = self.start("--notify-command", command, scenario=lambda seed, backend: None)
        self.assertEqual((code, len(fake.calls)), (5, 3))
        self.assertEqual([row["problems"][0]["status"] for row in self.ledger()], ["missing-summary"] * 3)
        self.assertEqual(notes.read_text().split(), ["1", "1", "1"])
        self.assertTrue((self.state / "runs/000000/sonatina-o0.stderr.log").exists())

    def test_notify_reports_new_signatures(self):
        notes = self.directory / "notes.txt"
        command = f"{sys.executable} -c \"import os,sys; open(sys.argv[1],'a').write(os.environ['SEMANTIC_FUZZ_NEW']+'\\n')\" {notes}"
        self.start("--iterations", "2", "--notify-command", command,
                   scenario=lambda seed, backend: [("runtime-primitives", [crash()] if backend == "sonatina-o2" else [])])
        sid, = self.registry()["signatures"]
        self.assertEqual(notes.read_text().split(), [sid])
        log = [json.loads(line) for line in (self.state / "notify.log").read_text().splitlines()]
        self.assertEqual([entry["new"] for entry in log], [[sid]])

    def test_parallel_workers_run_distinct_units_concurrently(self):
        import threading, time
        active, peak, guard = [0], [0], threading.Lock()

        def scenario(seed, backend):
            with guard:
                active[0] += 1
                peak[0] = max(peak[0], active[0])
            time.sleep(.3)
            with guard:
                active[0] -= 1
            return [("runtime-primitives", [crash()] if backend == "sonatina-o2" else [])]
        code, fake = self.start("--iterations", "2", "--jobs", "3", scenario=scenario)
        self.assertEqual(code, 0)
        self.assertGreater(peak[0], 1)
        units = sorted((row["iteration"], row["backend"], row["rootSeed"]) for row in self.ledger())
        self.assertEqual(units, [(0, "sonatina-o0", "100"), (0, "sonatina-o2", "100"),
                                 (1, "sonatina-o0", "101"), (1, "sonatina-o2", "101")])
        entry, = self.registry()["signatures"].values()
        self.assertEqual((entry["count"], len(entry["examples"])), (2, 2))
        self.assertEqual(sum(occurrence["new"] for row in self.ledger() for occurrence in row["occurrences"]), 1)

    def test_size_cycle_scales_node_budgets_by_iteration(self):
        code, fake = self.main("run", "--state", str(self.state), "--base-seed", "3", "--backend", "sonatina-o0",
                               "--profile", "closed-g0", "--size-cycle", "1,1.5,3", "--iterations", "4")
        self.assertEqual(code, 0)
        self.assertEqual([row["nodesScale"] for row in self.ledger()], [1.0, 1.5, 3.0, 1.0])
        config = json.loads((self.state / "config.json").read_text())
        argv = fuzz.suite_command(config, 2, "sonatina-o0", self.directory / "x")
        self.assertEqual(argv[argv.index("--nodes-scale") + 1], "3.0")
        self.assertEqual(fuzz.suite.node_budget(fuzz.suite.parse_args(argv[2:]), "closed-g0"), 72)
        code, fake = self.main("run", "--state", str(self.directory / "bad"), "--size-cycle", "0.5")
        self.assertEqual((code, fake.calls), (2, []))
        self.assertEqual(fuzz.CONFIG_DEFAULTS["size_cycle"], [1.0, 2.0])

    def test_functions_reach_the_suite_and_stay_fixed(self):
        code, fake = self.main("run", "--state", str(self.state), "--base-seed", "5", "--backend", "sonatina-o0",
                               "--profile", "closed-g0", "--profile", "runtime-word", "--functions", "2", "--iterations", "1")
        self.assertEqual(code, 0)
        config = json.loads((self.state / "config.json").read_text())
        self.assertEqual(config["functions"], 2)
        argv = fuzz.suite_command(config, 0, "sonatina-o0", self.directory / "x")
        self.assertEqual(argv[argv.index("--functions") + 1], "2")
        parsed = fuzz.suite.parse_args(argv[2:])
        # Two runtime-word functions of eight inputs each; closed-g0 keeps the sixteen default cases.
        self.assertEqual((fuzz.suite.requested(parsed, "runtime-word"), fuzz.suite.requested(parsed, "closed-g0")), (16, 16))
        self.assertIn("2 whole functions per runtime-input profile and 16 cases per other profile",
                      (self.state / "report.md").read_text())
        self.assertNotIn("--functions", fuzz.suite_command({**config, "functions": None}, 0, "sonatina-o0", self.directory / "y"))
        code, fake = self.main("run", "--state", str(self.state), "--functions", "3")
        self.assertEqual((code, fake.calls), (2, []))
        # A configuration whose profiles have no runtime inputs is rejected before it is stored.
        code, fake = self.main("run", "--state", str(self.directory / "closed"), "--base-seed", "1", "--backend", "sonatina-o0",
                               "--profile", "closed-g0", "--functions", "2", "--iterations", "1")
        self.assertEqual((code, fake.calls, (self.directory / "closed/config.json").exists()), (2, [], False))

    def test_backtrace_frames_name_the_compiler_call_site(self):
        output = ("thread 'x' panicked at y\nstack backtrace:\n   0: __rustc::rust_begin_unwind\n   1: core::panicking::panic_fmt\n"
                  "   2: <primitive_types::U256>::as_usize::h0011223344556677\n   3: sonatina_codegen::bits::propagate::h0011223344556677\n"
                  "             at /a/b.rs:1:1\n   4: <sonatina_ir::Inst as core::fmt::Debug>::fmt\n   5: std::rt::lang_start\n")
        self.assertEqual(fuzz.backtrace_frames(output)[2:4], ["<primitive_types::U256>::as_usize", "sonatina_codegen::bits::propagate"])
        self.assertEqual(fuzz.call_site(output, "primitive-types-0.14.0/src/lib.rs:43:1"),
                         ["sonatina_codegen::bits::propagate", "<sonatina_ir::Inst as core::fmt::Debug>::fmt"])
        self.assertEqual(fuzz.call_site("no panic here", "x"), ["not reproduced"])
        self.assertEqual(fuzz.call_site("panicked at\n   0: core::panicking::panic_fmt\n", None), ["no compiler frame"])

    def test_crash_replay_rewrites_the_archive_root_and_sets_rust_backtrace(self):
        FakeSuite(lambda seed, backend: [("runtime-primitives", [crash(site="sonatina_codegen::bits::propagate")])], self.stage)(
            ["--output", str(self.directory / "run"), "--backend", "sonatina-o2", "--seed", "1"],
            self.directory / "o.log", self.directory / "e.log", None)
        summary = json.loads((self.directory / "run/summary.json").read_text())
        record, = fuzz.finding_records(self.directory / "run", summary["profiles"][0])
        self.assertEqual(fuzz.crash_site(record), ["sonatina_codegen::bits::propagate", "sonatina_codegen::driver::run"])
        self.assertIsNone(fuzz.crash_site({**record, "detail": "error: no panic"}))
        self.assertEqual(fuzz.crash_site(record, timeout=1e-9), ["replay timeout"])

    def test_crash_signatures_split_by_call_site_unless_replay_is_disabled(self):
        def scenario(seed, backend):
            return [("runtime-primitives", [crash(site="sonatina_codegen::bits::propagate"),
                                            crash(site="sonatina_codegen::known::shift"),
                                            crash(site="sonatina_codegen::bits::propagate")])]
        self.main("run", "--state", str(self.state), "--base-seed", "1", "--backend", "sonatina-o2",
                  "--profile", "runtime-primitives", "--iterations", "1", scenario=scenario)
        sites = sorted((entry["symptom"]["site"][0], entry["count"]) for entry in self.registry()["signatures"].values())
        self.assertEqual(sites, [("sonatina_codegen::bits::propagate", 2), ("sonatina_codegen::known::shift", 1)])
        self.assertIn("sonatina_codegen::known::shift", (self.state / "report.md").read_text())
        plain = self.directory / "plain"
        self.main("run", "--state", str(plain), "--base-seed", "1", "--backend", "sonatina-o2", "--profile",
                  "runtime-primitives", "--iterations", "1", "--no-crash-replay", scenario=scenario)
        entry, = fuzz.State(plain).registry()["signatures"].values()
        self.assertEqual((entry["count"], "site" in entry["symptom"]), (3, False))

    def test_next_run_fills_gaps_before_new_iterations(self):
        config = {"backend": ["sonatina-o0", "sonatina-o2"]}
        ledger = [{"iteration": 1, "backend": "sonatina-o0"}, {"iteration": 1, "backend": "sonatina-o2"},
                  {"iteration": 0, "backend": "sonatina-o0"}]
        self.assertEqual(fuzz.next_run(config, ledger), (0, "sonatina-o2"))
        self.assertEqual(fuzz.next_run(config, ledger, {(0, "sonatina-o2")}), (2, "sonatina-o0"))
        self.assertEqual(fuzz.next_run(config, []), (0, "sonatina-o0"))
        self.assertEqual(fuzz.parse_args(["run"]).jobs, 1)
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            fuzz.parse_args(["run", "--jobs", "0"])

    def test_configuration_is_checked_with_the_suite_and_yul_runs_pure_and_storage_family_profiles(self):
        code, fake = self.main("run", "--state", str(self.state), "--cases", "0")
        self.assertEqual((code, fake.calls, (self.state / "config.json").exists()), (2, [], False))
        # The two call profiles whose sources compile both contracts never run on Yul, so a
        # configuration of only them runs nothing there; the call-return profile runs.
        code, fake = self.main("run", "--state", str(self.directory / "yul-calls"), "--base-seed", "1", "--backend", "yul",
                               "--profile", "stateful-calls", "--profile", "stateful-forwarded-value", "--iterations", "1")
        self.assertEqual((code, fake.calls), (2, []))
        code, fake = self.main("run", "--state", str(self.directory / "yul-returns"), "--base-seed", "1", "--backend", "yul",
                               "--profile", "stateful-calls", "--profile", "stateful-call-returns", "--iterations", "1")
        self.assertEqual((code, [call["profiles"] for call in fake.calls]), (0, [["stateful-call-returns"]]))
        code, fake = self.main("run", "--state", str(self.directory / "yul"), "--base-seed", "1", "--backend", "yul",
                               "--profile", "stateful-storage", "--iterations", "1")
        self.assertEqual((code, [call["profiles"] for call in fake.calls]), (0, [["stateful-storage"]]))
        code, fake = self.main("run", "--state", str(self.directory / "mixed"), "--base-seed", "1", "--backend", "sonatina-o0",
                               "--backend", "yul", "--profile", "closed-g0", "--profile", "stateful-storage",
                               "--profile", "stateful-calls", "--iterations", "1")
        self.assertEqual(code, 0)
        self.assertEqual([call["profiles"] for call in fake.calls],
                         [["closed-g0", "stateful-storage", "stateful-calls"], ["closed-g0", "stateful-storage"]])

    def test_default_yul_iterations_select_the_storage_family_beside_the_pure_profiles(self):
        families = {profile: family for profile, (_, family, _) in fuzz.suite.PROFILES.items()}
        code, fake = self.main("run", "--state", str(self.state), "--base-seed", "1", "--backend", "sonatina-o0",
                               "--backend", "yul", "--iterations", "1")
        self.assertEqual(code, 0)
        sonatina, yul = fake.calls
        # Sonatina keeps the suite's own default selection, every profile.
        self.assertEqual((sonatina["backend"], sonatina["profiles"]), ("sonatina-o0", []))
        self.assertEqual(yul["backend"], "yul")
        self.assertEqual(yul["profiles"], [profile for profile, family in families.items()
                                           if family != "call" or profile in ("stateful-call-returns", "stateful-call-sequences",
                                                                              "stateful-call-branches")])
        self.assertEqual(sorted({families[profile] for profile in yul["profiles"]}), ["call", "pure", "storage"])
        self.assertEqual(len([profile for profile in yul["profiles"] if families[profile] == "storage"]), 27)
        # Of the call profiles only the three whose sources the exporter admits.
        self.assertEqual([profile for profile in yul["profiles"] if families[profile] == "call"],
                         ["stateful-call-returns", "stateful-call-sequences", "stateful-call-branches"])
        # The suite parses the explicit selection; its own default for Yul stays the pure profiles.
        config = json.loads((self.state / "config.json").read_text())
        argv = fuzz.suite_command(config, 0, "yul", self.directory / "unused")
        self.assertEqual(fuzz.suite.parse_args(argv[2:]).profile, yul["profiles"])
        self.assertEqual(fuzz.suite.parse_args([*argv[2:argv.index("--profile")], "--output", str(self.directory / "other")]).profile,
                         [profile for profile, family in families.items() if family == "pure"])


FIXTURE_CHECK = fuzz.fixture_check  # the unpatched readiness check
# The Sonatina O2 crash as semantic-fixtures.py records it, with another user's paths and thread.
O2_CRASH = ("\nthread 'code-image-export' (17) panicked at /home/b/.cargo/git/checkouts/sonatina-a154b53739ea70c3/8ee2481/"
            "crates/ir/src/dfg.rs:354:9:\nassertion failed: self.has_inst(inst_id)\nnote: run with `RUST_BACKTRACE=1`\n")


def fixture_findings(seed, fixtures):
    """A known crash, a reduced mismatch with its duplicate and a Lean language failure, on the first three fixtures."""
    crash_fixture, mismatch_fixture, failure_fixture = fixtures[:3]
    mismatch = {"fixture": mismatch_fixture, "step": 3, "category": "path-mismatch",
                "signature": ["path-mismatch", ["output"], [["hull", "sonatina-o0"], ["yul"]]],
                "mutant": {"operator": "word", "word": 0, "recorded": "0x1", "value": "0x5"}}
    return [{"fixture": crash_fixture, "category": "compiler-crash", "paths": ["sonatina-o2"], "stage": "rust-code-images-O2",
             "detail": O2_CRASH},
            {**mismatch, "entry": "3.1", "reduction": {"status": "reduced", "steps": [], "calldata": "0x01", "value": 0}},
            {**mismatch, "entry": "3.2", "reduction": {"status": "duplicate", "of": "3.1"}},
            {"fixture": failure_fixture, "entry": "2.1", "step": 2, "category": "path-failure", "path": "hull",
             "signature": ["path-failure", "hull", "language-failure"], "detail": "Solcore.Core.Value.word 7",
             "reduction": {"status": "not-reproduced", "runs": 1}}]


# ignored-builtin-effects' source mutants at e2eef194 as unit 18's run of all 63 recorded them: the step, the site's
# start, text and replacement, and the words that Hull and Yul, Sonatina O0 and Sonatina O2 return.
WORD = 2 ** 256
ALLOCATION_MUTANTS = {
    "p16": (3, 1869, "0x40", "0x00", ((0x7, 0xc0), (0x7, 0x240), (0x7, 0x180))),
    "p17": (3, 1869, "0x40", "0x01", ((0x7, 0xc0), (0x7, 0x240), (0x7, 0x180))),
    "p58": (4, 2695, "2", "1", ((0x87, 0x40), (0x207, 0x40), (0x147, 0x40))),
    "p62": (4, 2697, "*", "/", ((0x107, 0x40), (0x407, 0x40), (0x287, 0x40))),
    # Outside the class: memory contents read at 0x80, the pointer's slot read one byte early, and 255 pointers.
    "p34": (3, 2096, "0x40", "0x80", ((0x7, -0x77 % WORD), (0x7, -0x200 % WORD), (0x7, -0x140 % WORD))),
    "p39": (4, 2315, "0x40", "0x3f", ((0x107, 0xc0), (0x403, 0x23e), (0x285, 0x17f))),
    "p18": (3, 1869, "0x40", "0x41", ((0x7, -0x7f40 % WORD), (0x7, -0x1fdc0 % WORD), (0x7, -0x13e80 % WORD))),
}


def words_output(words):
    return "0x" + "".join(f"{word:064x}" for word in words)


def allocation_finding(mutant, reduction=None):
    """One of ALLOCATION_MUTANTS' path mismatches as semantic-fixtures.py records it."""
    step, start, text, replacement, (hull, o0, o2) = ALLOCATION_MUTANTS[mutant]
    observations = {path: {"status": "returned", "output": words_output(words), "logs": []}
                    for path, words in (("hull", hull), ("sonatina-o0", o0), ("sonatina-o2", o2), ("yul", hull))}
    return {"fixture": "ignored-builtin-effects", "source": mutant,
            "edit": {"file": "main.sol", "start": start, "end": start + len(text), "replacement": replacement},
            "entry": f"{mutant}@{step}", "step": step, "position": step, "category": "path-mismatch",
            "signature": ["path-mismatch", ["output"], [["hull", "yul"], ["sonatina-o0"], ["sonatina-o2"]]],
            "observations": observations, "reduction": reduction or {"status": "duplicate", "of": "p2@4"}}


class FakeFixtures:
    """Writes a harness-shaped report for each fixtures run, with the findings `scenario(seed, fixtures)` returns."""

    def __init__(self, scenario, stop=None):
        self.scenario, self.stop, self.calls = scenario, stop, []

    def __call__(self, argv, stdout_path, stderr_path, stop, grace=120.0):
        value = lambda name: argv[argv.index(name) + 1]
        output, seed = Path(value("--output")), int(value("--seed"))
        selected = [argv[index + 1] for index, item in enumerate(argv) if item == "--fixture"]
        self.calls.append({"seed": seed, "fixtures": selected, "argv": argv})
        stdout_path.write_text("")
        stderr_path.write_text("")
        findings = self.scenario(seed, selected)
        (output / "fixtures").mkdir(parents=True)
        for fixture in selected:
            fuzz.save(output / "fixtures" / (fixture + ".json"),
                      {"id": fixture, "findings": [item for item in findings if item["fixture"] == fixture]})
        totals = {"fixtures": len(selected), "agree": 3 * len(selected), "disagree": 0, "incomplete": len(selected),
                  "unobserved": 1, "recorded": 2 * len(selected), "mutants": 2 * len(selected) + 1, "budgetStopped": 1,
                  "unexecuted": 0, "exclusions": {"rust-checked-source:compile-failure": 1},
                  "sequence": {"mutants": 2, "steps": 7, "agree": 4, "disagree": 0, "incomplete": 1, "unobserved": 1, "budget": 1},
                  "source": {"mutants": 1, "steps": 3, "agree": 2, "disagree": 0, "incomplete": 1, "unobserved": 0, "budget": 0}}
        fuzz.save(output / "report.json", {"schema": "solcore-lean.semantic-fixtures.v1", "coreReference": False,
                                           "stop": self.stop, "toolsUnchanged": True, "findings": findings, "errors": [],
                                           "totals": totals})
        return (130 if self.stop == "signal" else 1 if findings else 0), False


class FixtureRunTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="semantic-fuzz-fixtures-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name).resolve()
        self.state = self.directory / "state"
        self.receipt = self.directory / "semantic-tools-build.json"
        self.receipt.write_text('{"tools": 1}')
        self.check = {"status": "ready", "tools": {"scripts": 1}, "builds": {}, "manifests": {}, "fixtures": ["a"]}
        for target, replacement in (("verify_tools", lambda config: self.receipt), ("fixture_check", lambda config: self.check)):
            patcher = patch.object(fuzz, target, replacement)
            patcher.start()
            self.addCleanup(patcher.stop)

    def main(self, *argv, fake=None):
        fake = fake or FakeFixtures(lambda seed, fixtures: fixture_findings(seed, fixtures) if seed == 100 else [])
        with patch.object(fuzz, "run_suite", fake), contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            code = fuzz.main(["run", "--state", str(self.state), "--base-seed", "100", "--backend", "fixtures",
                              "--fixture-count", "4", *argv])
        return code, fake

    def test_each_cycle_runs_every_fixture_once_from_the_base_seed(self):
        config = {"base_seed": 7, "shard_index": 0, "shard_count": 1, "fixture_count": 8}
        pool = fuzz.fixture_pool(config)
        self.assertEqual(len(pool), 184)
        self.assertFalse(any(set(name) & set("*?[") for name in pool))  # ids pass to --fixture as exact globs
        cycle = [fuzz.fixture_selection(config, iteration) for iteration in range(23)]
        self.assertEqual(sorted(sum(cycle, [])), pool)
        self.assertEqual([len(selection) for selection in cycle], [8] * 23)
        self.assertEqual(fuzz.fixture_selection(config, 3), cycle[3])
        self.assertNotEqual(fuzz.fixture_selection(config, 23), cycle[0])
        self.assertNotEqual(fuzz.fixture_selection({**config, "base_seed": 8}, 0), cycle[0])
        shard = {**config, "shard_index": 1, "shard_count": 5}
        self.assertEqual(fuzz.fixture_pool(shard), pool[1::5])
        slices = [fuzz.fixture_selection(shard, iteration) for iteration in range(5)]
        self.assertEqual(([len(selection) for selection in slices], sorted(sum(slices, []))), ([8, 8, 8, 8, 5], pool[1::5]))

    def test_the_command_carries_the_root_seed_budgets_selection_and_paths(self):
        config = {**fuzz.CONFIG_DEFAULTS, "base_seed": 10, "bin_dir": "/b", "cast": "/c/cast", "anvil": "/c/anvil"}
        argv = fuzz.fixtures_command(config, 2, Path("/out"))
        value = lambda name: argv[argv.index(name) + 1]
        self.assertEqual([value(name) for name in ("--mode", "--seed", "--fixture-mutants", "--sequence-mutants", "--source-mutants",
                                                   "--fixture-seconds", "--seconds", "--jobs")],
                         ["mutation", "12", "32", "8", "2", "300.0", "1800.0", "2"])
        none = fuzz.fixtures_command({**config, "fixture_sequences": 0}, 2, Path("/out"))
        self.assertEqual(none[none.index("--sequence-mutants") + 1], "0")
        self.assertEqual([argv[index + 1] for index, item in enumerate(argv) if item == "--fixture"], fuzz.fixture_selection(config, 2))
        self.assertEqual((value("--hull-runner"), value("--cast"), value("--anvil")), ("/b/rust-hull-scenario", "/c/cast", "/c/anvil"))
        self.assertIn("--reuse-exports", argv)
        self.assertNotIn("--cast", fuzz.suite_command(config, 2, "yul", Path("/out")))

    def test_runs_register_known_and_new_findings_keep_examples_and_prune(self):
        code, fake = self.main("--iterations", "2", "--examples", "2")
        self.assertEqual(code, 0)
        selections = [fuzz.fixture_selection(json.loads((self.state / "config.json").read_text()), iteration) for iteration in (0, 1)]
        self.assertEqual([(call["seed"], call["fixtures"]) for call in fake.calls], [(100, selections[0]), (101, selections[1])])
        rows = fuzz.State(self.state).ledger()
        self.assertEqual([(row["iteration"], row["backend"], row["suiteStatus"], row["fixtures"]) for row in rows],
                         [(0, "fixtures", "failed", selections[0]), (1, "fixtures", "passed", selections[1])])
        # Sequence and source mutants' compared steps count with the entries; a step a budget left unrun does not.
        self.assertEqual(rows[0]["counts"], {"executed": 26, "matched": 18, "mismatched": 0, "errors": 0, "inconclusive": 8,
                                             "sequences": 2, "sources": 1, "fixtures": 4, "recorded": 8, "mutants": 9,
                                             "budgetStopped": 1, "unexecuted": 0, "findings": 4, "exclusions": 1})
        signatures = fuzz.State(self.state).registry()["signatures"]
        crashed, = [sid for sid, entry in signatures.items() if entry["category"] == "compiler-crash"]
        self.assertIn(crashed, fuzz.KNOWN)
        self.assertEqual([(occurrence["case"], occurrence["new"]) for occurrence in rows[0]["occurrences"]],
                         [("rust-code-images-O2", False), ("3.1", True), ("3.2", False), ("2.1", True)])
        mismatched, = [entry for entry in signatures.values() if entry["category"] == "path-mismatch"]
        self.assertEqual((mismatched["count"], mismatched["profiles"], len(mismatched["examples"])), (2, {selections[0][1]: 2}, 2))
        example = self.state / mismatched["examples"][0]
        self.assertEqual(json.loads((example / "fixture.json").read_text())["id"], selections[0][1])
        replay = json.loads((example / "occurrence.json").read_text())["replay"]
        self.assertEqual((replay[replay.index("--seed") + 1], replay[replay.index("--fixture") + 1:replay.index("--fixture") + 2]),
                         ("100", [selections[0][1]]))
        failed, = [entry for entry in signatures.values() if entry["category"] == "path-failure"]
        self.assertEqual(failed["key"]["symptom"], {"value": "Solcore.Core.Value.word 7"})
        kept = self.state / "runs/000000/fixtures"
        self.assertEqual(sorted(path.name for path in (kept / "fixtures").iterdir()), sorted(name + ".json" for name in selections[0][:3]))
        self.assertTrue((kept / "report.json").is_file())
        self.assertFalse((self.state / "runs/000001").exists())
        report = (self.state / "report.md").read_text()
        self.assertIn("known: Sonatina O2 has_inst assertion", report)
        self.assertIn("Fixtures: 4 pinned end-to-end fixtures per iteration, at most 32 mutants, 8 sequence mutants, "
                      "2 source mutants", report)

    def test_the_epoch_covers_the_harness_check_only_when_fixtures_run(self):
        config = {"backend": list(fuzz.BACKENDS)}
        with patch.object(fuzz, "harness_digest", return_value="h"):
            suite_only = fuzz.current_epoch(config)
            self.assertEqual(suite_only["id"], fuzz.canonical_id({"receipt": fuzz.suite.digest(self.receipt), "harness": "h"}))
            self.assertNotIn("fixturesSha256", suite_only)
            config["backend"] = [*fuzz.BACKENDS, "fixtures"]
            with_fixtures = fuzz.current_epoch(config)
            self.assertNotEqual(with_fixtures["id"], suite_only["id"])
            self.check["manifests"] = {"rust-method-parity.json": "changed"}
            self.assertNotEqual(fuzz.current_epoch(config)["id"], with_fixtures["id"])

    def test_the_harness_check_must_report_ready(self):
        ready = subprocess.CompletedProcess([], 0, json.dumps({"status": "ready", "tools": {}}) + "\n", "")
        with patch.object(fuzz.subprocess, "run", return_value=ready) as run:
            self.assertEqual(FIXTURE_CHECK({"bin_dir": "/b"})["status"], "ready")
        self.assertEqual(run.call_args.args[0][2:], ["--check", "--hull-runner", "/b/rust-hull-scenario"])
        refused = subprocess.CompletedProcess([], 2, "", "semantic-fixtures: directive tool receipt is stale")
        with patch.object(fuzz.subprocess, "run", return_value=refused), self.assertRaisesRegex(fuzz.NotReady, "receipt is stale"):
            FIXTURE_CHECK({})

    def test_unready_harness_or_invalid_budgets_stop_before_any_run(self):
        with patch.object(fuzz, "fixture_check", side_effect=fuzz.NotReady("solc is missing")):
            code, fake = self.main("--iterations", "1")
        self.assertEqual((code, fake.calls, fuzz.State(self.state).ledger()), (2, [], []))
        code, fake = self.main("--iterations", "1", "--fixture-count", "0")
        self.assertEqual((code, fake.calls), (2, []))
        code, fake = self.main("--iterations", "1", "--fixture-sequences", "-1")
        self.assertEqual((code, fake.calls), (2, []))
        code, fake = self.main("--iterations", "1", "--fixture-sources", "4097")
        self.assertEqual((code, fake.calls), (2, []))

    def test_a_source_finding_is_its_edit_and_reduced_steps_and_a_refusal_its_symptom(self):
        edit = {"file": "main.sol", "start": 10, "end": 12, "replacement": "0x00"}
        mismatch = {"fixture": "f", "category": "path-mismatch", "step": 3, "source": "p16", "edit": edit,
                    "signature": ["path-mismatch", ["output"], [["hull", "yul"], ["sonatina-o0"]]]}
        reduced = fuzz.fixture_signature_key({**mismatch, "reduction": {"status": "reduced", "steps": [], "edit": edit}})
        self.assertEqual(reduced["program"], fuzz.canonical_id({"fixture": "f", "edit": edit, "steps": []}))
        unreduced = fuzz.fixture_signature_key({**mismatch, "reduction": {"status": "not-reproduced", "runs": 1}})
        self.assertEqual(unreduced["program"], fuzz.canonical_id({"fixture": "f", "edit": edit, "step": 3}))
        refusal = {"fixture": "f", "category": "compile-mismatch", "source": "p2", "edit": edit, "paths": ["yul"],
                   "stage": "yul-export", "detail": "Error: StackTooDeepError at /tmp/a/x.sol:12"}
        key = fuzz.fixture_signature_key(refusal)
        self.assertEqual((key["stage"], key["paths"], "program" in key), ("yul-export", ["yul"], False))
        self.assertEqual(key, fuzz.fixture_signature_key({**refusal, "source": "p9", "edit": {**edit, "start": 99}}))

    def test_a_source_mutants_hull_memory_range_failure_is_known_by_its_real_occurrences(self):
        # asm-string-escapes p8 and revert p2 store at 2^256 - 1: Hull's range fails, O0 and O2 run out of gas, and
        # solc's Yul returns without the store.
        widest = "115792089237316195423570985008687907853269984665640564039457584007913129639935"
        occurrences = [("asm-string-escapes", "p8", 517, "suite `assembly_string_escapes` test #2"), ("revert", "p2", 208, "fail/1")]
        for fixture, source, start, label in occurrences:
            edit = {"file": "main.sol", "start": start, "end": start + 1, "replacement": widest}
            finding = {"fixture": fixture, "source": source, "edit": edit, "entry": f"{source}@1", "step": 1, "label": label,
                       "position": 1, "category": "path-failure", "path": "hull",
                       "signature": ["path-failure", "hull", "language-failure"], "detail": "Solcore.Core.Value.word 6",
                       "reduction": {"status": "reduced", "runs": 1, "steps": [], "edit": edit}}
            sid = fuzz.canonical_id(fuzz.fixture_signature_key(finding))
            self.assertIn("Hull memory's range", fuzz.KNOWN[sid], fixture)
        # Another Core value, another path or another status stays new.
        for changes in ({"detail": "Solcore.Core.Value.word 7"}, {"path": "yul", "signature": ["path-failure", "yul", "language-failure"]},
                        {"signature": ["path-failure", "hull", "error"]}):
            self.assertNotIn(fuzz.canonical_id(fuzz.fixture_signature_key({**finding, **changes})), fuzz.KNOWN, changes)

    def test_the_first_allocation_class_holds_its_real_occurrences(self):
        key, _, label = fuzz.FIXTURE_MISMATCH_CLASSES[0]
        self.assertEqual(fuzz.KNOWN[fuzz.canonical_id(key)], label)
        for mutant in ("p16", "p17", "p58", "p62"):
            self.assertEqual(fuzz.fixture_mismatch_class(allocation_finding(mutant)), key, mutant)
        # p16 returns `after`, each path's pointer past its first allocation of 64 bytes.
        observations = allocation_finding("p16")["observations"]
        self.assertEqual({path: fuzz.returned_words(observation["output"])[1] - 0x40 for path, observation in observations.items()},
                         fuzz.FIRST_ALLOCATION)
        for mutant in ("p34", "p39", "p18"):
            self.assertIsNone(fuzz.fixture_mismatch_class(allocation_finding(mutant)), mutant)

    def test_the_first_allocation_class_leaves_near_misses_new(self):
        finding = allocation_finding("p16")
        observations, groups = finding["observations"], finding["signature"][2]

        def changed(path, **fields):
            return {**observations, path: {**observations[path], **fields}}
        near_misses = {
            "another difference": {"observations": changed("sonatina-o2", output=words_output((0x7, 0x181)))},
            "another path pair": {"observations": changed("sonatina-o2", output=observations["hull"]["output"]),
                                  "signature": ["path-mismatch", ["output"], [["hull", "sonatina-o2", "yul"], ["sonatina-o0"]]]},
            "another status": {"observations": changed("sonatina-o0", status="reverted"),
                               "signature": ["path-mismatch", ["output", "status"], groups]},
            "five first allocations": {"observations": {path: {**observation, "output": words_output(
                (0x7, 5 * fuzz.FIRST_ALLOCATION[path] + 0x40))} for path, observation in observations.items()}},
            "a partial word": {"observations": changed("sonatina-o0", output=observations["sonatina-o0"]["output"] + "00")},
            "another difference field": {"signature": ["path-mismatch", ["storage"], groups]},
            "no source mutant": {"source": None},
        }
        for name, changes in near_misses.items():
            near_miss = {**finding, **changes}
            self.assertIsNone(fuzz.fixture_mismatch_class(near_miss), name)
            self.assertNotIn(fuzz.canonical_id(fuzz.fixture_signature_key(near_miss)), fuzz.KNOWN, name)

    def test_runs_count_first_allocation_class_occurrences_as_known(self):
        def scenario(seed, fixtures):
            if seed != 100:
                return []
            reduced = allocation_finding("p58", {"status": "reduced", "runs": 3, "steps": []})
            reduced = {**reduced, "fixture": fixtures[0], "reduction": {**reduced["reduction"], "edit": reduced["edit"]}}
            return [reduced, *({**allocation_finding(mutant, {"status": "duplicate", "of": reduced["entry"]}), "fixture": fixtures[0]}
                               for mutant in ("p62", "p34"))]
        code, fake = self.main("--iterations", "1", fake=FakeFixtures(scenario))
        self.assertEqual(code, 0)
        row, = fuzz.State(self.state).ledger()
        self.assertEqual([(occurrence["case"], occurrence["new"]) for occurrence in row["occurrences"]],
                         [("p58@4", False), ("p62@4", False), ("p34@3", True)])
        signatures = fuzz.State(self.state).registry()["signatures"]
        self.assertEqual(signatures[fuzz.canonical_id(fuzz.FIXTURE_MISMATCH_CLASSES[0][0])]["count"], 2)
        # Outside the class of the finding it repeats, p34 is its own edit at its step.
        fixture = fake.calls[0]["fixtures"][0]
        p34 = {**allocation_finding("p34"), "fixture": fixture}
        entry = signatures[fuzz.canonical_id(fuzz.fixture_signature_key(p34))]
        self.assertEqual((entry["count"], entry["key"]["program"]),
                         (1, fuzz.canonical_id({"fixture": fixture, "edit": p34["edit"], "step": 3})))
        report = (self.state / "report.md").read_text()
        self.assertIn("known: the paths' first allocations differ", report)
        self.assertIn("class offset-by-first-allocations", report)

    def test_a_sequence_finding_is_its_reduced_sequence_and_operator(self):
        mismatch = {"fixture": "f", "category": "path-mismatch", "step": 4, "sequence": "s7", "operator": "commit", "change": 3,
                    "signature": ["path-mismatch", ["storage"], [["hull"], ["yul"]]],
                    "mutant": {"operator": "word", "word": 0, "recorded": "0x1", "value": "0x5"}}
        reduced = {"status": "reduced", "operator": "commit", "position": 2,
                   "sequence": [{"step": 0, "persist": True}, {"step": 3, "persist": True, "mutant": mismatch["mutant"]},
                                {"step": 4, "persist": True}]}
        key = fuzz.fixture_signature_key({**mismatch, "reduction": reduced})
        self.assertEqual(key["program"], fuzz.canonical_id({"fixture": "f", "operator": "commit", "sequence": reduced["sequence"]}))
        self.assertEqual(fuzz.fixture_signature_key({**mismatch, "reduction": {**reduced, "position": 9}}), key)
        unreduced = fuzz.fixture_signature_key({**mismatch, "reduction": {"status": "not-reproduced", "runs": 1}})
        self.assertEqual(unreduced["program"], fuzz.canonical_id({"fixture": "f", "operator": "commit", "step": 4, "change": 3,
                                                                  "mutant": mismatch["mutant"]}))
        self.assertNotEqual(unreduced, fuzz.fixture_signature_key({**mismatch, "operator": "drop", "reduction": {"status": "stopped"}}))

    def test_an_interrupted_fixtures_run_is_set_aside_and_rerun(self):
        code, fake = self.main("--iterations", "1", fake=FakeFixtures(fixture_findings, stop="signal"))
        self.assertEqual((code, fuzz.State(self.state).ledger()), (0, []))
        kept, = (self.state / "interrupted").iterdir()
        self.assertTrue((kept / "run/report.json").is_file())
        code, fake = self.main("--iterations", "1")
        self.assertEqual([call["seed"] for call in fake.calls], [100])
        self.assertEqual([row["iteration"] for row in fuzz.State(self.state).ledger()], [0])


NATIVE_CHECK = fuzz.native_check  # the unpatched readiness check
NATIVE_SOURCE = """pragma solcore;
import * from std;

contract SynthesizedFunctions {
    function run(input: uint256) public returns (uint256) {
        return input; // MARK
    }
}
"""
NATIVE_INFERENCE = ("Solcore.Frontend.ProgramCheckError.inference { declaration := { moduleId := { library := "
                    "Solcore.Workspace.LibraryId.main }, declarationIndex := 2 }, error := "
                    "Solcore.Frontend.SourceInference.Error.")
# A stand-in for semantic-native-tool with the native frontend's own error texts: a marked source is refused or reads
# an uninitialized local, and any other source returns each input's word.
NATIVE_STUB = """#!/usr/bin/env python3
import json, sys
request = json.load(open(sys.argv[1]))
source = request["sources"][0]["content"]
refused = [detail for mark, detail in %r.items() if mark in source]
if refused:
    observations = []
elif "UNINITIALIZED" in source:
    observations = [{"status": "failed", "error": "uninitializedLocal", "reason": "1"} for _ in request["inputs"]]
else:
    observations = [{"status": "returned", "word": words[0]} for words in request["inputs"]]
print(json.dumps({"schema": "solcore-lean.semantic-native-result.v1", "status": "rejected" if refused else "compiled",
                  "stage": "inference" if refused else "compiled", "detail": refused[0] if refused else "",
                  "milliseconds": {}, "observations": observations}))
""" % {"NONEXHAUSTIVE": NATIVE_INFERENCE + 'nonExhaustiveMatch { source := { path := "main.sol" }, startByte := 3326 } }',
       "TYPEDEF": NATIVE_INFERENCE + 'operatorNotSupported "Typedef" (Solcore.TypeSystem.Ty.variable { index := 8 }) }'}


def native_case(mark="", word=7, core=None):
    """A pure case that the native admission admits: a functions source whose method returns its input."""
    return {"schema": "solcore-lean.semantic-function-case.v1", "source": NATIVE_SOURCE.replace("MARK", mark),
            "program": {"tag": "apply"}, "provenance": {"emitterVersion": "solcore-source-functions-v2"},
            "contract": {"method": "run", "signature": "run(uint256)", "calldata": f"0xa444f5e9{word:064x}"},
            "directCore": core or {"stage": "execution", "status": "returned", "word": str(word)}}


def native_scenario(seed, profile):
    """At root seed 100: an agreeing case, Lean's unlabelled enum exhaustiveness rejection in both profiles, and the
    known open `Typedef` call and uninitialized local; every later case agrees."""
    if seed != 100:
        return [native_case()]
    if profile == "runtime-functions":
        return [native_case(), native_case("NONEXHAUSTIVE"), native_case("NONEXHAUSTIVE", 5), native_case("TYPEDEF"),
                native_case("UNINITIALIZED")]
    return [native_case("NONEXHAUSTIVE", 9)]


class FakeNative:
    """Runs the native harness's own profile runs, comparisons and report, with the stub tool, on the cases that
    `scenario(seed, profile)` gives: only the case preparation is replaced. `interrupted` stops it as a signal does,
    `missing` writes no report, and `finished` is its tools' identity when it ends."""

    def __init__(self, scenario=native_scenario, interrupted=False, missing=False, finished=None):
        self.scenario, self.interrupted, self.missing, self.finished = scenario, interrupted, missing, finished
        self.calls = []

    def __call__(self, argv, stdout_path, stderr_path, stop, grace=120.0):
        native = fuzz.native_harness()
        args, suite_args = native.parse_args(argv[2:])
        self.calls.append({"seed": args.seed, "profiles": args.profile})
        stdout_path.write_text("")
        stderr_path.write_text("")
        if self.missing:
            return 2, False
        args.output.mkdir(parents=True)
        run = native.NativeRun(args, suite_args)
        for profile in args.profile:
            response = {"cases": self.scenario(args.seed, profile), "excluded": []}
            with patch.object(native, "prepare", return_value=response), \
                    patch.object(native.suite, "command", return_value=["python", "runner"]):
                run.run_profile(profile)
        run.stopped = run.stopped or self.interrupted
        report = run.report({"tools": 1}, self.finished or {"tools": 1}, 0.0)
        (args.output / "report.json").write_text(json.dumps(report, indent=1) + "\n")
        for leftover in (args.output / ".work").glob("*"):
            leftover.unlink()
        (args.output / ".work").rmdir()
        return (130 if self.interrupted else 0 if report["status"] == "passed" else 1), False


class NativeRunTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="semantic-fuzz-native-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name).resolve()
        self.state = self.directory / "state"
        self.receipt = self.directory / "semantic-tools-build.json"
        self.receipt.write_text('{"tools": 1}')
        self.bin = self.directory / "bin"
        self.bin.mkdir()
        self.tool = self.bin / "semantic-native-tool"
        self.tool.write_text(NATIVE_STUB)
        self.tool.chmod(0o755)
        self.check = {"status": "ready", "versions": {"admission": "native-admission-v1"}, "admittedEmitters": ["e"],
                      "tools": {"nativeTool": {"sha256": "1"}}, "scripts": {"semantic-native.py": "2"}}
        for target, replacement in (("verify_tools", lambda config: self.receipt),
                                    ("native_check", lambda config: self.check)):
            patcher = patch.object(fuzz, target, replacement)
            patcher.start()
            self.addCleanup(patcher.stop)

    def main(self, *argv, fake=None):
        fake, output = fake or FakeNative(), io.StringIO()
        with patch.object(fuzz, "run_suite", fake), contextlib.redirect_stdout(output), \
                contextlib.redirect_stderr(io.StringIO()):
            code = fuzz.main(list(argv))
        return code, fake, output.getvalue()

    def start(self, *argv, state=None, fake=None):
        return self.main("run", "--state", str(state or self.state), "--base-seed", "100", "--backend", "native",
                         "--profile", "runtime-functions", "--profile", "runtime-enums", "--bin-dir", str(self.bin),
                         "--examples", "2", *argv, fake=fake)

    def signature(self, category, **fields):
        return fuzz.canonical_id({"backend": "native", "category": category, **fields})

    def test_native_is_opt_in_and_draws_the_programs_of_its_iterations_suite_runs(self):
        self.assertEqual((fuzz.CONFIG_DEFAULTS["backend"], fuzz.parse_args(["run", "--backend", "native"]).backend),
                         (list(fuzz.BACKENDS), ["native"]))
        native = fuzz.native_harness()
        admitted = [profile for profile in native.PURE_PROFILES if native.profile_emitter(profile) in native.EMITTERS]
        base = {**fuzz.CONFIG_DEFAULTS, "base_seed": 41, "shard_index": 1, "shard_count": 3}
        for config in (base, {**base, "functions": 2, "nodes": 40}):
            for iteration in range(3):
                suite_args = fuzz.suite.parse_args(fuzz.suite_command(config, iteration, "sonatina-o0", self.directory)[2:])
                args, native_suite = native.parse_args(fuzz.native_command(config, iteration, self.directory)[2:])
                self.assertEqual((args.profile, args.seconds), (admitted, 1800.0))
                for profile in admitted:
                    ours = native.suite.command(native_suite, profile, self.directory, 1.0, 10**9)
                    theirs = fuzz.suite.command(suite_args, profile, self.directory, 1.0, 10**9)
                    # A profile's draw: its derived seed, node budget, case or function count and attempts.
                    self.assertEqual(ours[ours.index("--seed"):], theirs[theirs.index("--seed"):], (iteration, profile))
        config = {**base, "bin_dir": str(self.bin), "native_seconds": 60.0,
                  "profile": ["closed-g0", "runtime-assembly", "stateful-storage", "runtime-enums"]}
        args, _ = native.parse_args(fuzz.native_command(config, 0, self.directory)[2:])
        self.assertEqual((args.profile, args.seconds, args.native_tool, args.bin_dir),
                         (["closed-g0", "runtime-enums"], 60.0, self.tool, self.bin))
        # No admitted pure profile, or no time, is refused before anything is recorded.
        for options in (["--profile", "runtime-assembly", "--profile", "stateful-storage"], ["--native-seconds", "0"]):
            code, fake, _ = self.main("run", "--state", str(self.directory / "refused"), "--backend", "native", *options)
            self.assertEqual((code, fake.calls, (self.directory / "refused/config.json").exists()), (2, [], False))

    def test_runs_count_the_cases_of_new_and_known_findings_and_record_their_counts(self):
        code, fake, _ = self.start("--iterations", "2")
        self.assertEqual(code, 0)
        self.assertEqual([(call["seed"], call["profiles"]) for call in fake.calls],
                         [(100, ["runtime-functions", "runtime-enums"]), (101, ["runtime-functions", "runtime-enums"])])
        first, second = fuzz.State(self.state).ledger()
        # A run that fails only by its new finding is no problem.
        self.assertEqual((first["suiteStatus"], first["problems"], second["suiteStatus"]), ("failed", [], "passed"))
        self.assertEqual(first["counts"], {"executed": 6, "matched": 1, "mismatched": 1, "errors": 4, "cases": 6,
                                           "generationExcluded": 0, "notAdmitted": 0, "admitted": 6, "programs": 5,
                                           "agree": 1, "mismatch": 1, "rejected": 4, "inconclusive": 0,
                                           "unexecuted": 0, "findings": 3, "newFindings": 1})
        self.assertEqual(first["known"], {"open-typedef-call": 1, "uninitialized-local": 1})
        exhaustive = self.signature("native-rejection", stage="inference", symptom={"message": "nonExhaustiveMatch"})
        typedef = self.signature("native-rejection", stage="inference", **{"class": "open-typedef-call"})
        uninitialized = self.signature("native-mismatch", stage="execution", **{"class": "uninitialized-local"})
        self.assertTrue({typedef, uninitialized} <= set(fuzz.KNOWN) and exhaustive not in fuzz.KNOWN)
        self.assertEqual({(item["signature"], item["profile"]): (item["cases"], item["new"], bool(item["retained"]))
                          for item in first["occurrences"]},
                         {(exhaustive, "runtime-functions"): (2, True, True), (exhaustive, "runtime-enums"): (1, False, False),
                          (typedef, "runtime-functions"): (1, False, True),
                          (uninitialized, "runtime-functions"): (1, False, True)})
        signatures = fuzz.State(self.state).registry()["signatures"]
        entry = signatures[exhaustive]
        self.assertEqual((entry["count"], entry["profiles"], entry["backends"], len(entry["examples"])),
                         (3, {"runtime-functions": 2, "runtime-enums": 1}, {"native": 3}, 1))
        self.assertEqual((signatures[typedef]["count"], signatures[uninitialized]["count"]), (1, 1))
        example = self.state / entry["examples"][0]
        self.assertEqual(sorted(path.name for path in example.iterdir()),
                         ["case.json", "occurrence.json", "request.json", "result.json"])
        occurrence = json.loads((example / "occurrence.json").read_text())
        self.assertEqual((occurrence["case"], occurrence["finding"]["symptom"], "replay" in occurrence["finding"]),
                         ("case-1", "nonExhaustiveMatch", False))
        self.assertEqual(occurrence["replay"][2:], ["replay", "--state", str(self.state), entry["examples"][0]])
        rerun, _ = fuzz.native_harness().parse_args(occurrence["rerun"][2:])
        self.assertEqual((rerun.seed, rerun.profile), (100, ["runtime-functions"]))
        # The failed run keeps only its report; the passed one leaves its ledger row.
        self.assertEqual([path.name for path in (self.state / "runs/000000/native").iterdir()], ["report.json"])
        self.assertFalse((self.state / "runs/000001").exists())
        report = (self.state / "report.md").read_text()
        for text in ("Native: Lean's native frontend on each iteration's draws",
                     "| native | 2 | failed 1, passed 1 | 8 | 3 | 1 | 4 | 0 |",
                     "| 8 | 0 | 0 | 8 | 7 | 3 | 1 | 4 | 0 | 0 |", "- Not admitted, by reason: none.",
                     "- Known differences, by label: open-typedef-call 1, uninitialized-local 1.",
                     "known: Lean rejects a `Typedef` call", "class uninitialized-local", "| nonExhaustiveMatch |"):
            self.assertIn(text, report)

    def test_a_run_that_does_not_pass_without_a_finding_is_a_problem(self):
        invalid = lambda seed, profile: [native_case(core={"stage": "execution", "status": "invalid"})]
        cases = ((["--base-seed", "100"], FakeNative(invalid), "failed", ["inconclusive", "inconclusive"]),
                 (["--native-seconds", "1e-9"], FakeNative(), "failed", ["unexecuted", "unexecuted"]),
                 ([], FakeNative(finished={"tools": 2}), "error", ["tools-changed"]),
                 ([], FakeNative(missing=True), "missing-summary", ["missing-summary"]))
        for index, (options, fake, status, problems) in enumerate(cases):
            state = self.directory / f"state-{index}"
            code, _, _ = self.main("run", "--state", str(state), "--base-seed", "101", "--backend", "native",
                                   "--profile", "runtime-functions", "--profile", "runtime-enums", "--bin-dir",
                                   str(self.bin), "--iterations", "1", *options, fake=fake)
            row, = fuzz.State(state).ledger()
            self.assertEqual((code, row["suiteStatus"], [problem["status"] for problem in row["problems"]]),
                             (0, status, problems), options)
        self.assertEqual(fuzz.State(self.directory / "state-0").ledger()[0]["inconclusiveReasons"],
                         {"direct Core execution/invalid": 2})
        errors = {"status": "failed", "toolsUnchanged": True, "errors": [{"profile": "runtime-word", "detail": "x"}]}
        self.assertEqual((fuzz.native_status(errors), [problem["status"] for problem in fuzz.native_problems(errors)]),
                         ("error", ["harness-error"]))

    def test_the_epoch_covers_the_native_harness_only_when_native_runs(self):
        with patch.object(fuzz, "harness_digest", return_value="h"):
            suite_only = fuzz.current_epoch({"backend": list(fuzz.BACKENDS)})
            self.assertEqual(suite_only["id"], fuzz.canonical_id({"receipt": fuzz.suite.digest(self.receipt), "harness": "h"}))
            self.assertNotIn("nativeSha256", suite_only)
            config = {"backend": [*fuzz.BACKENDS, "native"]}
            with_native = fuzz.current_epoch(config)
            self.assertNotEqual(with_native["id"], suite_only["id"])
            self.check["tools"] = {"nativeTool": {"sha256": "3"}}
            self.assertNotEqual(fuzz.current_epoch(config)["id"], with_native["id"])
        ready = subprocess.CompletedProcess([], 0, json.dumps({"status": "ready", "tools": {}}) + "\n", "")
        with patch.object(fuzz.subprocess, "run", return_value=ready) as run:
            self.assertEqual(NATIVE_CHECK({"bin_dir": str(self.bin)})["status"], "ready")
        self.assertEqual(run.call_args.args[0][2:], ["--check", "--mode", "random", "--bin-dir", str(self.bin),
                                                     "--native-tool", str(self.tool)])
        missing = subprocess.CompletedProcess([], 2, json.dumps({"status": "not-ready", "missing": ["nativeTool"]}), "")
        with patch.object(fuzz.subprocess, "run", return_value=missing), \
                self.assertRaisesRegex(fuzz.NotReady, "native harness is not ready.*nativeTool"):
            NATIVE_CHECK({})

    def test_the_native_classes_are_the_harness_labels_and_other_findings_keep_their_keys(self):
        native = fuzz.native_harness()
        self.assertEqual(({key["class"] for key, _ in fuzz.NATIVE_CLASSES}, fuzz.NATIVE_COUNTS),
                         (set(native.KNOWN), native.NativeRun.COUNTS))
        self.assertTrue(all(fuzz.KNOWN[fuzz.canonical_id(key)] == label for key, label in fuzz.NATIVE_CLASSES))
        # Lean's enum exhaustiveness rejection has no label; nor has one the driver does not list or one on another
        # kind or stage.
        rejection = {"kind": "native-rejection", "stage": "inference", "symptom": "nonExhaustiveMatch", "label": None}
        for changes in ({}, {"label": "another"}, {"label": "open-typedef-call", "stage": "signatures"},
                        {"label": "uninitialized-local"}):
            key = fuzz.native_signature_key({**rejection, **changes})
            self.assertEqual(key.get("symptom"), {"message": "nonExhaustiveMatch"}, changes)
            self.assertNotIn(fuzz.canonical_id(key), fuzz.KNOWN, changes)
        mismatch = {"kind": "native-mismatch", "profile": "runtime-word", "core": "returned", "native": "returned"}
        self.assertEqual(fuzz.native_signature_key(mismatch)["fingerprint"], {"core": "returned", "native": "returned"})

    def test_a_kept_example_replays_through_the_harness_comparison(self):
        self.start("--iterations", "1")
        signatures = fuzz.State(self.state).registry()["signatures"].values()
        exhaustive, = [entry for entry in signatures if entry["symptom"] == {"message": "nonExhaustiveMatch"}]
        known = {entry["key"].get("class"): entry for entry in signatures}
        for entry, verdict in ((exhaustive, "rejected"), (known["open-typedef-call"], "rejected"),
                               (known["uninitialized-local"], "mismatch")):
            code, _, output = self.main("replay", "--state", str(self.state), entry["examples"][0])
            outcome = json.loads(output)
            self.assertEqual((code, outcome["verdicts"], outcome["replayed"], outcome["reproduced"]),
                             (0, [verdict], [entry["id"]], True))
        # A frontend that now accepts the program agrees with direct Core, so its finding does not reproduce.
        self.tool.write_text(NATIVE_STUB.replace("'NONEXHAUSTIVE'", "'ACCEPTED'"))
        code, _, output = self.main("replay", "--state", str(self.state), exhaustive["examples"][0])
        self.assertEqual((code, json.loads(output)["verdicts"], json.loads(output)["reproduced"]), (1, ["agree"], False))
        self.assertEqual(self.main("replay", "--state", str(self.state), "findings/missing")[0], 2)

    def test_an_interrupted_native_run_is_set_aside_and_a_finished_one_recorded_on_resume(self):
        code, fake, _ = self.start("--iterations", "1", fake=FakeNative(interrupted=True))
        self.assertEqual((code, fuzz.State(self.state).ledger()), (0, []))
        kept, = (self.state / "interrupted").iterdir()
        self.assertTrue(any((kept / "run/findings").iterdir()))
        code, fake, _ = self.start("--iterations", "1")
        self.assertEqual([call["seed"] for call in fake.calls], [100])
        config = json.loads((self.state / "config.json").read_text())
        FakeNative()(fuzz.native_command(config, 1, fuzz.State(self.state).run_directory(1, "native")),
                     self.directory / "out.log", self.directory / "err.log", None)
        code, fake, _ = self.start("--iterations", "1")
        recorded = [row["iteration"] for row in fuzz.State(self.state).ledger()]
        self.assertEqual(([call["seed"] for call in fake.calls], recorded), ([102], [0, 1, 2]))


if __name__ == "__main__":
    unittest.main()
