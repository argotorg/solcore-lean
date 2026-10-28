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
    frame = sys.argv[sys.argv.index("--frame") + 1]
    sys.stderr.write("stack backtrace:\\n   0: __rustc::rust_begin_unwind\\n   1: core::panicking::panic_fmt\\n"
                     "   2: primitive_types::U256::as_usize::h0123456789abcdef\\n   3: " + frame + "::h0123456789abcdef\\n"
                     "             at /x/crates/codegen/src/a.rs:1:2\\n   4: sonatina_codegen::driver::run\\n")
sys.exit(101)
"""


def mismatch(program):
    return ("semantic-mismatch", "", program)


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
                location = folder / "findings/real" / f"{case:04d}"
                (location / "original").mkdir(parents=True)
                (location / "original/analysis.json").write_text(json.dumps({"comparison": {"category": category, "detail": detail}}))
                if site and site[0]:
                    work = output / ".work" / f"run-{case:06d}"
                    (location / "original/case.sol").write_text("contract C {}")
                    (location / "original/report.json").write_text(json.dumps({"processes": [
                        {"stage": "rust-checked-source", "returncode": 0, "command": ["true"]},
                        {"stage": "rust-code-images", "returncode": 2, "command": [
                            sys.executable, str(self.stage), f"{work}/case.sol", "--root", str(work), "--frame", site[0]]}]}))
                (location / "shrink.json").write_text("{}")
                entries.append({"caseIndex": case, "synthetic": False, "finalCaseSha256": program,
                                "fingerprint": {"backend": backend, "category": category, "stage": "rust-code-images",
                                                "disagreeingPairs": ["directCore/rustEvm"] if category == "semantic-mismatch" else [],
                                                "synthetic": False},
                                "originalArchive": f"findings/real/{case:04d}/original", "history": f"findings/real/{case:04d}/shrink.json"})
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
        # The call profiles never run on Yul, so a configuration of only them runs nothing there.
        code, fake = self.main("run", "--state", str(self.directory / "yul-calls"), "--base-seed", "1", "--backend", "yul",
                               "--profile", "stateful-calls", "--profile", "stateful-forwarded-value", "--iterations", "1")
        self.assertEqual((code, fake.calls), (2, []))
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
        self.assertEqual(yul["profiles"], [profile for profile, family in families.items() if family != "call"])
        self.assertEqual(sorted({families[profile] for profile in yul["profiles"]}), ["pure", "storage"])
        self.assertEqual(len([profile for profile in yul["profiles"] if families[profile] == "storage"]), 25)
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
                  "unexecuted": 0, "exclusions": {"rust-checked-source:compile-failure": 1}}
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
        self.assertEqual(len(pool), 168)
        self.assertFalse(any(set(name) & set("*?[") for name in pool))  # ids pass to --fixture as exact globs
        cycle = [fuzz.fixture_selection(config, iteration) for iteration in range(21)]
        self.assertEqual(sorted(sum(cycle, [])), pool)
        self.assertEqual({len(selection) for selection in cycle}, {8})
        self.assertEqual(fuzz.fixture_selection(config, 3), cycle[3])
        self.assertNotEqual(fuzz.fixture_selection(config, 21), cycle[0])
        self.assertNotEqual(fuzz.fixture_selection({**config, "base_seed": 8}, 0), cycle[0])
        shard = {**config, "shard_index": 1, "shard_count": 5}
        self.assertEqual(fuzz.fixture_pool(shard), pool[1::5])
        slices = [fuzz.fixture_selection(shard, iteration) for iteration in range(5)]
        self.assertEqual(([len(selection) for selection in slices], sorted(sum(slices, []))), ([8, 8, 8, 8, 2], pool[1::5]))

    def test_the_command_carries_the_root_seed_budgets_selection_and_paths(self):
        config = {**fuzz.CONFIG_DEFAULTS, "base_seed": 10, "bin_dir": "/b", "cast": "/c/cast", "anvil": "/c/anvil"}
        argv = fuzz.fixtures_command(config, 2, Path("/out"))
        value = lambda name: argv[argv.index(name) + 1]
        self.assertEqual([value(name) for name in ("--mode", "--seed", "--fixture-mutants", "--fixture-seconds", "--seconds", "--jobs")],
                         ["mutation", "12", "32", "300.0", "1800.0", "2"])
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
        self.assertEqual(rows[0]["counts"], {"executed": 17, "matched": 12, "mismatched": 0, "errors": 0, "inconclusive": 5,
                                             "fixtures": 4, "recorded": 8, "mutants": 9, "budgetStopped": 1, "unexecuted": 0,
                                             "findings": 4, "exclusions": 1})
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
        self.assertIn("Fixtures: 4 pinned end-to-end fixtures per iteration", report)

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

    def test_an_interrupted_fixtures_run_is_set_aside_and_rerun(self):
        code, fake = self.main("--iterations", "1", fake=FakeFixtures(fixture_findings, stop="signal"))
        self.assertEqual((code, fuzz.State(self.state).ledger()), (0, []))
        kept, = (self.state / "interrupted").iterdir()
        self.assertTrue((kept / "run/report.json").is_file())
        code, fake = self.main("--iterations", "1")
        self.assertEqual([call["seed"] for call in fake.calls], [100])
        self.assertEqual([row["iteration"] for row in fuzz.State(self.state).ledger()], [0])


if __name__ == "__main__":
    unittest.main()
