#!/usr/bin/env python3
"""Verify finding reduction, replay and resource classification using real tools.

The explicit campaign test adapter changes only a copied observation after
actual three-way agreement. Original compiler/runtime reports stay unchanged.
Use a reducible fixed case, such as closed-g0 cases/0006.json (word-add).
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import math
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


suite = load("findings_suite", "semantic-suite.py")
campaign = load("findings_campaign", "semantic-campaign.py")
m2 = campaign.m2
SCHEMA = "solcore-lean.semantic-findings-check.v1"
PHASES = ("synthetic-reduction", "exact-replay", "synthetic-replay", "resource-limit")


class CheckFailure(Exception):
    def __init__(self, detail, category="failed"):
        super().__init__(detail)
        self.category = category


def require(condition, message):
    if not condition:
        raise CheckFailure(message)


def actual_match(report):
    """Check the raw observations too; a saved 'matched' label is insufficient."""
    require(report.get("schema") == m2.REPORT_SCHEMA, "unexpected actual report schema")
    raw, observed = report.get("rawObservations"), report.get("observations")
    require(isinstance(raw, dict) and isinstance(observed, dict), "missing actual observations")
    normalized = {name: m2.normalize_observation(raw.get(name), direct=name == "directCore")
                  for name in campaign.PATHS}
    require(observed == normalized, "actual observations differ from raw execution results")
    comparison = m2.compare(normalized)
    require(comparison.get("category") == "matched" and report.get("comparison") == comparison,
            "actual three-way execution did not match")


def safe_member(directory, relative):
    require(isinstance(relative, str) and bool(relative), "missing retained archive path")
    path = Path(relative)
    require(not path.is_absolute() and all(part not in (".", "..") for part in path.parts),
            "retained archive path is not relative and contained")
    current = directory
    for part in path.parts:
        current /= part
        require(not current.is_symlink(), "retained archive contains a symlink")
    require(current.resolve().is_relative_to(directory.resolve()) and current.exists(),
            "retained archive is missing or outside its campaign")
    return current


def verify_synthetic(directory, code, require_reduction):
    summary = m2.read_json(directory / "summary.json")
    require(code == 1 and summary.get("schema") == campaign.SCHEMA and
            summary.get("status") == "complete" and summary.get("synthetic") is True,
            "synthetic campaign did not complete with a nonzero finding result")
    require(summary.get("testAdapter") == {"name": campaign.TEST_ADAPTER, "path": "rustEvm"},
            "unexpected synthetic adapter")
    counts = summary.get("counts", {})
    for name in ("generated", "executed", "completed", "mismatched", "syntheticMismatches"):
        require(type(counts.get(name)) is int and counts[name] == 1, "unexpected synthetic count: " + name)
    for name in ("matched", "unexecuted", "inconclusive", "errors", "sourceRejected", "compilationRejected"):
        require(type(counts.get(name)) is int and counts[name] == 0, "unexpected non-success count: " + name)
    require(summary.get("secondaryFindings") == [], "a genuine secondary finding needs investigation")
    findings = summary.get("findings")
    require(isinstance(findings, list) and len(findings) == 1, "expected exactly one synthetic finding")
    finding = findings[0]
    require(finding.get("synthetic") is True, "finding is not explicitly synthetic")
    expected = finding.get("fingerprint")
    for key in ("originalArchive", "finalArchive"):
        folder = safe_member(directory, finding.get(key))
        report = m2.read_json(folder / "report.json")
        actual_match(report)
        analysis = m2.read_json(folder / "analysis.json")
        require(analysis == campaign.analyze(report, "rustEvm"), "copied synthetic analysis was changed")
        require(campaign.fingerprint(analysis) == expected, "retained finding fingerprint changed")
    history = m2.read_json(safe_member(directory, finding.get("history")))
    steps = history.get("steps")
    require(isinstance(steps, list) and len(steps) <= 4 and summary.get("shrinkAttempts") == len(steps),
            "shrink history exceeded its bound or lost attempts")
    require(history.get("status") in ("attempt-limit", "no-preserving-candidate", "no-attempts"),
            "shrink stopped incompletely")
    require(history.get("fingerprint") == expected and history.get("finalArchive") == finding.get("finalArchive") and
            history.get("finalProgramSha256") == finding.get("finalProgramSha256"), "shrink history differs from finding")
    accepted = 0
    for index, step in enumerate(steps, 1):
        require(step.get("attempt") == index and type(step.get("accepted")) is bool,
                "invalid shrink attempt inventory")
        require(step.get("actualComparison", {}).get("category") == "matched",
                "a reduction's actual execution did not match")
        require(step.get("fingerprint") == expected and step.get("comparison", {}).get("category") == "semantic-mismatch",
                "a reduction lost the synthetic fingerprint")
        accepted += int(step["accepted"])
    if require_reduction:
        require(accepted > 0 and finding.get("finalProgramSha256") != finding.get("originalProgramSha256"),
                "case has no accepted smaller candidate; supply a reducible fixed case")
    else:
        require(not steps, "synthetic replay unexpectedly performed reduction")
    return {"fingerprint": expected, "acceptedReductions": accepted, "attempts": len(steps),
            "finalArchive": finding["finalArchive"], "finalProgramSha256": finding["finalProgramSha256"]}


def verify_resource(report, code):
    require(code == 1 and report.get("schema") == m2.REPORT_SCHEMA and
            report.get("comparison", {}).get("category") == "inconclusive-resource",
            "fuel-one execution was not a nonzero inconclusive resource result")
    require(report.get("budgets", {}).get("direct_fuel") == 1 and
            report.get("rawObservations", {}).get("directCore", {}).get("status") == "out-of-fuel" and
            report.get("observations", {}).get("directCore", {}).get("status") == "out-of-fuel",
            "resource result did not come from actual direct Core fuel exhaustion")
    require(set(report.get("rawObservations", {})) == {"directCore"},
            "fuel-exhausted case unexpectedly executed later comparison paths")


class Verification:
    def __init__(self, args):
        self.args = args
        self.started = time.monotonic()
        self.deadline = self.started + args.seconds
        self.report = {"schema": SCHEMA, "status": "running", "checks": [], "unexecuted": list(PHASES),
                       "caseSha256": suite.digest(args.case), "validatorSha256": suite.digest(Path(__file__)),
                       "limits": {key: getattr(args, key) for key in ("seconds", "disk_bytes", "case_timeout", "cleanup_seconds")},
                       "scope": "real executions; synthetic copied observation only; not an upstream bug or opcode coverage"}
        self.checkpoint()

    def checkpoint(self):
        self.report["elapsedSeconds"] = round(time.monotonic() - self.started, 3)
        suite.save(self.args.output / "verification.json", self.report)

    def shared(self):
        return [part for key in ("anvil", "upstream", "target_dir", "case_tool", "core_runner")
                for part in ("--" + key.replace("_", "-"), str(getattr(self.args, key)))]

    def process(self, phase, command):
        if time.monotonic() >= self.deadline:
            raise CheckFailure("verification time limit exhausted", "inconclusive-resource")
        row = {"phase": phase, "status": "running", "command": command}
        self.report["checks"].append(row)
        self.report["unexecuted"].remove(phase)
        self.checkpoint()
        code, stopped = suite.run_process(command, self.args, self.deadline,
            self.args.output / (phase + ".stdout.log"), self.args.output / (phase + ".stderr.log"))
        row.update(exitCode=code, stopped=stopped)
        if stopped:
            raise CheckFailure(phase + " stopped: " + stopped, "inconclusive-resource")
        return row, code

    def campaign_command(self, case, output, attempts):
        remaining = max(.001, self.deadline - time.monotonic())
        return [sys.executable, str(ROOT / "scripts/semantic-campaign.py"), "--case", str(case),
                "--output", str(output), "--test-perturb-path", "rustEvm", "--shrink-attempts", str(attempts),
                "--shrink-candidates", "4", "--seconds", str(remaining), "--case-timeout", str(self.args.case_timeout),
                "--disk-bytes", str(self.args.disk_bytes - self.args.reserve_bytes), *self.shared()]

    def run(self):
        first = self.args.output / "synthetic"
        row, code = self.process(PHASES[0], self.campaign_command(self.args.case, first, 4))
        result = verify_synthetic(first, code, True)
        row.update(status="passed", **result)
        self.checkpoint()
        archive = safe_member(first, result["finalArchive"])

        replay = self.args.output / "exact-replay"
        row, code = self.process(PHASES[1], [sys.executable, str(ROOT / "scripts/semantic-differential.py"),
            "--replay", str(archive), "--output", str(replay), *self.shared()])
        require(code == 0, "exact archive replay exited unsuccessfully")
        actual_match(m2.read_json(replay / "report.json"))
        row.update(status="passed", reportSha256=suite.digest(replay / "report.json"))
        self.checkpoint()

        synthetic_replay = self.args.output / "synthetic-replay"
        row, code = self.process(PHASES[2], self.campaign_command(archive / "case.json", synthetic_replay, 0))
        repeated = verify_synthetic(synthetic_replay, code, False)
        require(repeated["fingerprint"] == result["fingerprint"] and
                repeated["finalProgramSha256"] == result["finalProgramSha256"],
                "synthetic replay changed the reduced program or failure fingerprint")
        row.update(status="passed", **repeated)
        self.checkpoint()

        resource = self.args.output / "resource-limit"
        row, code = self.process(PHASES[3], [sys.executable, str(ROOT / "scripts/semantic-differential.py"),
            "--case", str(self.args.case), "--output", str(resource), "--direct-fuel", "1", *self.shared()])
        verify_resource(m2.read_json(resource / "report.json"), code)
        row.update(status="passed", reportSha256=suite.digest(resource / "report.json"))
        self.report["status"] = "passed"
        self.checkpoint()


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", required=True, type=Path, help="reducible saved case; use fixed closed-g0 cases/0006.json")
    parser.add_argument("--output", required=True, type=Path, help="new validation directory")
    for key, default in {"anvil": Path(shutil.which("anvil") or "anvil"),
                         "upstream": ROOT / ".upstream/solcore-rs-20261023", "target-dir": ROOT / ".upstream/rust-parity-target",
                         "case-tool": ROOT / ".lake/build/bin/semantic-case-tool", "core-runner": ROOT / ".lake/build/bin/rust-hull-scenario"}.items():
        parser.add_argument("--" + key, type=Path, default=default)
    parser.add_argument("--seconds", type=float, default=600)
    parser.add_argument("--case-timeout", type=float, default=90)
    parser.add_argument("--disk-bytes", type=int, default=512 * 1024**2)
    parser.add_argument("--cleanup-seconds", type=float, default=10)
    args = parser.parse_args(argv)
    for key, low, high in (("seconds", .001, 86400), ("case_timeout", .001, 3600),
                           ("disk_bytes", 32 * 1024**2, 10**10), ("cleanup_seconds", .1, 30)):
        require(math.isfinite(getattr(args, key)) and low <= getattr(args, key) <= high, "invalid limit: " + key)
    for key in ("case", "output", "anvil", "upstream", "target_dir", "case_tool", "core_runner"):
        setattr(args, key, getattr(args, key).resolve())
    args.reserve_bytes = min(8 * 1024**2, args.disk_bytes // 8)
    args.output_limit = 2 * 1024**2
    return args


def main(argv=None):
    args = parse_args(argv)
    case = m2.read_json(args.case, 2 * 1024**2)
    m2.validate_case(case)
    args.output.mkdir(parents=True, exist_ok=False)
    verification = Verification(args)
    previous = signal.getsignal(signal.SIGTERM)

    def interrupt(_signal, _frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupt)
    try:
        verification.run()
    except KeyboardInterrupt:
        verification.report.update(status="inconclusive-resource", detail="interrupted")
    except CheckFailure as error:
        verification.report.update(status=error.category, detail=str(error))
    except (ValueError, OSError, KeyError, TypeError, subprocess.SubprocessError, m2.Finding) as error:
        verification.report.update(status="adapter-error", detail=str(error))
    finally:
        try:
            if verification.report["checks"] and verification.report["checks"][-1]["status"] == "running":
                verification.report["checks"][-1]["status"] = verification.report["status"]
            verification.checkpoint()
        finally:
            signal.signal(signal.SIGTERM, previous)
    print(json.dumps({"status": verification.report["status"], "record": str(args.output / "verification.json")}))
    return 0 if verification.report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
