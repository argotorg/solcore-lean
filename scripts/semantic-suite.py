#!/usr/bin/env python3
"""Run the existing differential campaigns sequentially with shared limits.

Build the native tools and pinned Rust exporters beforehand. Fixed mode runs
complete manifests; random mode derives reproducible profile/shard seeds and
keeps generation exclusions visible. A resource limit or an unexecuted profile
never passes. Existing campaigns retain genuine findings and reduced archives.
The suite adds orchestration, not another execution oracle or reducer.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
_adapter_spec = importlib.util.spec_from_file_location("semantic_suite_adapter", ROOT / "scripts/semantic-differential.py")
assert _adapter_spec and _adapter_spec.loader
adapter = importlib.util.module_from_spec(_adapter_spec)
_adapter_spec.loader.exec_module(adapter)
SCHEMA = "solcore-lean.semantic-suite.v1"
SEED_VERSION = "sha256-profile-shard-v1"
MIN_CAMPAIGN_BYTES = 16 * 1024 * 1024
PROFILES = {
    # manifest stem, campaign family, default random node budget
    "closed-g0": ("semantic", "pure", 24),
    "runtime-word": ("semantic-input", "pure", 32),
    "runtime-functions": ("semantic-function", "pure", 64),
    "runtime-mutation": ("semantic-mutation", "pure", 192),
    "runtime-aggregates": ("semantic-aggregate", "pure", 256),
    "runtime-loops": ("semantic-loop", "pure", 384),
    "runtime-generics": ("semantic-generic", "pure", 384),
    "runtime-closures": ("semantic-closure", "pure", 384),
    "runtime-comptime": ("semantic-comptime", "pure", 384),
    "runtime-modules": ("semantic-module", "pure", 384),
    "runtime-primitives": ("semantic-primitive", "pure", 96),
    "runtime-call-graphs": ("semantic-call-graph", "pure", 192),
    "runtime-call-graph-loops": ("semantic-call-graph-loop", "pure", 256),
    "runtime-aggregate-call-graphs": ("semantic-aggregate-call-graph", "pure", 192),
    "stateful-storage": ("semantic-storage", "storage", 384),
    "stateful-storage-rollback": ("semantic-storage-rollback", "storage", 384),
    "stateful-calls": ("semantic-call", "call", 384),
    "stateful-keyed-storage": ("semantic-keyed-storage", "storage", 384),
    "stateful-dynamic-array": ("semantic-dynamic-array", "storage", 384),
}
# Profiles that declare their observed slots share the declared-slot Hull runner.
DECLARED_SLOT_PROFILES = ("stateful-keyed-storage", "stateful-dynamic-array")
CAMPAIGNS = {"pure": "semantic-campaign.py", "storage": "semantic-storage-campaign.py", "call": "semantic-call-campaign.py"}
CAMPAIGN_SCHEMAS = {"pure": "solcore-lean.semantic-campaign.v1", "storage": "solcore-lean.semantic-storage-campaign.v1", "call": "solcore-lean.semantic-call-campaign.v1"}


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(65536), b""):
            result.update(chunk)
    return result.hexdigest()


def save(path, value):
    temporary = path.with_suffix(".writing")
    temporary.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")
    temporary.replace(path)


def directory_bytes(directory):
    total = 0
    for path in directory.rglob("*"):
        try:
            if path.is_file() and not path.is_symlink():
                total += path.stat().st_size
        except FileNotFoundError:
            pass  # A campaign may remove a completed export during this scan.
    return total


def derived_seed(root_seed, profile, shard_index, shard_count, attempts):
    payload = json.dumps([SEED_VERSION, str(root_seed), profile, shard_index, shard_count], separators=(",", ":"))
    # Consecutive attempts must not wrap the uint64 seed boundary.
    return int.from_bytes(hashlib.sha256(payload.encode()).digest()[:8], "big") % ((1 << 64) - max(1, attempts) + 1)


def manifest(profile):
    return ROOT / "scripts" / (PROFILES[profile][0] + "-corpus.json")


def requested(args, profile):
    if args.mode == "random":
        return args.cases
    data = json.loads(manifest(profile).read_text())
    if data.get("profile", "closed-g0") != profile or not isinstance(data.get("cases"), list) or not data["cases"]:
        raise ValueError("fixed manifest profile or cases changed: " + profile)
    return len(data["cases"])


def profile_attempts(args, profile):
    if profile == "runtime-call-graphs" and not getattr(args, "attempts_explicit", True):
        return 1024
    return args.attempts


def command(args, profile, output, seconds, disk_bytes):
    _, family, nodes = PROFILES[profile]
    attempts = profile_attempts(args, profile)
    if args.backend == "yul" and family != "pure":
        raise ValueError("Yul is restricted to pure profiles")
    storage_tools = {"stateful-keyed-storage": args.keyed_case_tool, "stateful-dynamic-array": args.array_case_tool}
    tool = {"pure": args.case_tool, "storage": args.rollback_case_tool if profile.endswith("-rollback") else
            storage_tools.get(profile, args.storage_case_tool), "call": args.call_case_tool}[family]
    runner = {"pure": args.core_runner, "storage": args.keyed_core_runner if profile in DECLARED_SLOT_PROFILES else
              args.storage_core_runner, "call": args.call_core_runner}[family]
    result = [sys.executable, str(ROOT / "scripts" / CAMPAIGNS[family]), "--output", str(output), "--profile", profile,
              "--seconds", str(seconds), "--disk-bytes", str(disk_bytes), "--case-tool", str(tool), "--core-runner", str(runner)]
    for key in ("backend", "anvil", "upstream", "target_dir", "direct_fuel", "core_fuel", "gas", "case_timeout", "shrink_attempts", "shrink_candidates"):
        result += ["--" + key.replace("_", "-"), str(getattr(args, key))]
    if args.backend == "yul":
        result += ["--solc", str(args.solc)]
    if args.mode == "fixed":
        # Never truncate a fixed corpus and call its missing coverage complete.
        result += ["--corpus", str(manifest(profile)), "--attempts", str(max(attempts, requested(args, profile)))]
    else:
        seed = derived_seed(args.seed, profile, args.shard_index, args.shard_count, profile_attempts(args, profile))
        result += ["--seed", str(seed), "--nodes", str(args.nodes or nodes), "--cases", str(args.cases), "--attempts", str(attempts)]
    return result


def missing_coverage(summary):
    return {group: {key: value for key, value in values.items() if key.startswith("missing") and value}
            for group, values in summary.items() if isinstance(values, dict)
            and (group == "coverage" or group.endswith("Coverage"))
            and any(key.startswith("missing") and value for key, value in values.items())}


def classify(summary, profile, count, exit_code, stopped=None, backend="sonatina-o0"):
    """Use both process completion and the campaign's observed completion counts."""
    if not isinstance(summary, dict) or summary.get("schema") != CAMPAIGN_SCHEMAS[PROFILES[profile][1]]:
        return "inconclusive-resource" if stopped else "adapter-error"
    counts = summary.get("counts", {})
    configuration = summary.get("configuration")
    if not isinstance(counts, dict) or not isinstance(configuration, dict) or configuration.get("profile") != profile:
        return "adapter-error"
    try:
        adapter.resolve_backend(backend, summary)
        if "backend" in configuration:
            adapter.resolve_backend(backend, configuration)
    except ValueError:
        return "adapter-error"
    if summary.get("synthetic") is not False:
        return "adapter-error"
    if any(type(value) is not int or value < 0 for value in counts.values()) or counts.get("syntheticMismatches", 0):
        return "adapter-error"
    categories = set()
    for key in ("findings", "secondaryFindings"):
        findings = summary.get(key, [])
        if not isinstance(findings, list):
            return "adapter-error"
        for finding in findings:
            fingerprint = finding.get("fingerprint") if isinstance(finding, dict) else None
            if not isinstance(fingerprint, dict) or fingerprint.get("synthetic") is not False:
                return "adapter-error"
            try:
                adapter.resolve_backend(backend, fingerprint)
            except ValueError:
                return "adapter-error"
            categories.add(fingerprint.get("category"))
    # A real finding survives a later timeout/interruption in another case.
    failures = {"semantic-mismatch", "source-rejected", "compilation-rejected", "compiler-crash", "execution-error", "adapter-error"}
    if any(counts.get(key, 0) > 0 for key in ("mismatched", "errors", "sourceRejected", "compilationRejected")) or categories & failures:
        return "failed"
    if categories - failures - {"inconclusive-resource"}:
        return "adapter-error"
    if stopped or summary.get("status") in {"budget-exhausted", "interrupted"} or counts.get("inconclusive", 0) > 0 or "inconclusive-resource" in categories:
        return "inconclusive-resource"
    if summary.get("status") != "complete" or missing_coverage(summary):
        return "incomplete" if summary.get("status") in {"generation-exhausted", "coverage-incomplete"} or missing_coverage(summary) else "adapter-error"
    required = ("generated", "executed", "completed", "matched")
    if exit_code != 0 or any(type(counts.get(key)) is not int or counts[key] != count for key in required) or counts.get("unexecuted") != 0:
        return "incomplete"
    return "passed"


def process_table():
    """Record identities so forced cleanup cannot target a reused PID."""
    result = subprocess.run(["ps", "-axo", "pid=,ppid=,pgid=,lstart="], capture_output=True, text=True, timeout=5, check=True)
    table = {}
    for line in result.stdout.splitlines():
        fields = line.split(maxsplit=3)
        if len(fields) == 4:
            table[int(fields[0])] = (int(fields[1]), int(fields[2]), fields[3])
    return table


def remember_children(root_pid, owned, table):
    parents = {root_pid} | {pid for pid, identity in owned.items() if pid in table and table[pid][2] == identity}
    while True:
        children = {pid for pid, (parent, _, _) in table.items() if parent in parents}
        if children <= parents:
            break
        parents |= children
    for pid in parents:
        if pid in table:
            owned[pid] = table[pid][2]


def signal_owned(owned, signum):
    table = process_table()
    for pid, identity in owned.items():
        if pid in table and table[pid][2] == identity:
            try:
                if table[pid][1] == pid:
                    try:
                        os.killpg(pid, signum)
                    except PermissionError:
                        # On macOS a group becoming empty can reject killpg
                        # while its owned leader is still awaiting reaping.
                        os.kill(pid, signum)
                else:
                    os.kill(pid, signum)
            except ProcessLookupError:
                pass


def stop_owned(process, owned, grace):
    # First let the campaign stop its separate-session compiler/Anvil children
    # and flush its own summary. Track escaped-session descendants as a fallback.
    try:
        remember_children(process.pid, owned, process_table())
        if process.poll() is None:
            process.send_signal(signal.SIGTERM)
        deadline = time.monotonic() + grace
        while process.poll() is None and time.monotonic() < deadline:
            remember_children(process.pid, owned, process_table())
            time.sleep(.05)
        signal_owned(owned, signal.SIGTERM)
        time.sleep(.05)
        signal_owned(owned, signal.SIGKILL)
    finally:
        # Inspection errors must not bypass cleanup of the known child group.
        if process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except PermissionError:
                process.kill()
            except ProcessLookupError:
                pass
        process.wait(timeout=5)


def run_process(argv, args, deadline, stdout_path, stderr_path):
    # Fail closed before spawning if descendant cleanup is unavailable.
    process_table()
    owned, stopped = {}, None
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        process = subprocess.Popen(argv, cwd=ROOT, stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr, start_new_session=True)
        try:
            while process.poll() is None:
                remember_children(process.pid, owned, process_table())
                if time.monotonic() >= deadline:
                    stopped = "time-limit"
                elif directory_bytes(args.output) >= args.disk_bytes - args.reserve_bytes:
                    stopped = "disk-limit"
                elif stdout.tell() + stderr.tell() > args.output_limit:
                    stopped = "output-limit"
                if stopped:
                    break
                time.sleep(.1)
        except KeyboardInterrupt:
            stopped = "interrupted"
        finally:
            stop_owned(process, owned, args.cleanup_seconds)
    for path in (stdout_path, stderr_path):
        if path.stat().st_size > args.output_limit:
            with path.open("r+b") as stream:
                stream.truncate(args.output_limit)
    return process.returncode, stopped


class Suite:
    def __init__(self, args):
        self.args = args
        self.started = time.monotonic()
        self.deadline = self.started + args.seconds
        self.report = {"schema": SCHEMA, "status": "running", "backend": args.backend, "mode": args.mode, "seedVersion": SEED_VERSION,
            "rootSeed": str(args.seed), "shardIndex": args.shard_index, "shardCount": args.shard_count,
            "selectedProfiles": args.profile, "profiles": [], "unexecutedProfiles": args.profile[:],
            "limits": {key: getattr(args, key) for key in ("seconds", "profile_seconds", "disk_bytes", "profile_disk_bytes", "output_limit", "cleanup_seconds")},
            "suiteSha256": digest(Path(__file__)), "executionOrder": "sequential",
            "coverageScope": "existing campaign gates; no additional runtime opcode coverage claim"}
        self.checkpoint()

    def checkpoint(self):
        self.report["elapsedSeconds"] = round(time.monotonic() - self.started, 3)
        self.report["retainedBytes"] = directory_bytes(self.args.output)
        save(self.args.output / "summary.json", self.report)

    def run(self):
        args = self.args
        for index, profile in enumerate(args.profile):
            remaining = self.deadline - time.monotonic()
            free = args.disk_bytes - directory_bytes(args.output) - args.reserve_bytes
            if remaining < .001 or free < MIN_CAMPAIGN_BYTES:
                self.report["stop"] = "time-limit" if remaining < .001 else "disk-limit"
                break
            seconds = min(args.profile_seconds, remaining)
            count = requested(args, profile)
            folder = args.output / f"{index:02d}-{profile}"
            argv = command(args, profile, folder, seconds, min(args.profile_disk_bytes, free))
            row = {"profile": profile, "backend": args.backend, "status": "running", "requested": count, "output": folder.name,
                   "command": argv, "campaignSha256": digest(Path(argv[1]))}
            if args.mode == "fixed":
                row.update(manifest=str(manifest(profile).relative_to(ROOT)), manifestSha256=digest(manifest(profile)))
            else:
                row.update(seed=str(derived_seed(args.seed, profile, args.shard_index, args.shard_count, profile_attempts(args, profile))), attempts=profile_attempts(args, profile))
            self.report["profiles"].append(row)
            self.report["unexecutedProfiles"] = args.profile[index + 1:]
            self.checkpoint()
            profile_started = time.monotonic()
            exit_code, stopped = run_process(argv, args, min(self.deadline, time.monotonic() + seconds),
                args.output / f"{index:02d}-{profile}.stdout.log", args.output / f"{index:02d}-{profile}.stderr.log")
            row.update(exitCode=exit_code, stop=stopped, elapsedSeconds=round(time.monotonic() - profile_started, 3))
            summary_path = folder / "summary.json"
            summary = None
            try:
                if summary_path.stat().st_size > args.output_limit:
                    raise ValueError("campaign summary exceeds report limit")
                summary = json.loads(summary_path.read_text())
            except (OSError, ValueError) as error:
                row["summaryError"] = str(error)
            row["status"] = classify(summary, profile, count, exit_code, stopped, args.backend)
            if isinstance(summary, dict):
                row["campaign"] = {key: summary[key] for key in ("backend", "status", "counts", "transactionCounts", "stop", "generation") if key in summary}
                row["missingCoverage"] = missing_coverage(summary)
                row["summary"] = str(summary_path.relative_to(args.output))
                row["summarySha256"] = digest(summary_path)
                row["findings"] = summary.get("findings", [])
                row["secondaryFindings"] = summary.get("secondaryFindings", [])
                counts = summary.get("counts", {})
                row["casesPerSecond"] = round(counts.get("executed", 0) / max(row["elapsedSeconds"], .001), 3) if type(counts.get("executed")) is int else None
            self.checkpoint()
            print(json.dumps({"profile": profile, "status": row["status"]}), flush=True)
            if stopped == "interrupted":
                self.report["stop"] = stopped
                break
        statuses = [row["status"] for row in self.report["profiles"]]
        self.report["counts"] = {key: sum(row.get("campaign", {}).get("counts", {}).get(key, 0)
            for row in self.report["profiles"] if type(row.get("campaign", {}).get("counts", {}).get(key, 0)) is int)
            for key in ("generated", "excluded", "generationResourceExclusions", "executed", "completed", "matched", "mismatched", "unexecuted", "errors", "inconclusive")}
        self.report["casesPerSecond"] = round(self.report["counts"]["executed"] / max(time.monotonic() - self.started, .001), 3)
        if any(status in {"failed", "adapter-error"} for status in statuses):
            self.report["status"] = "failed"
        elif self.report.get("stop") or "inconclusive-resource" in statuses:
            self.report["status"] = "inconclusive-resource"
        elif self.report["unexecutedProfiles"] or any(status != "passed" for status in statuses):
            self.report["status"] = "incomplete"
        else:
            self.report["status"] = "passed"
        self.checkpoint()


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", choices=adapter.BACKENDS, default="sonatina-o0")
    parser.add_argument("--mode", choices=("fixed", "random"), default="fixed")
    parser.add_argument("--output", type=Path, required=True, help="fresh suite directory; existing output is never overwritten")
    parser.add_argument("--profile", action="append", choices=tuple(PROFILES), help="repeat to select profiles; default nineteen for Sonatina, fourteen pure profiles for Yul")
    parser.add_argument("--seed", type=int, default=1, help="root seed for reproducible random profile/shard seeds")
    parser.add_argument("--shard-index", type=int, default=0)
    parser.add_argument("--shard-count", type=int, default=1, help="seed shard count; every shard still runs all selected profiles")
    parser.add_argument("--cases", type=int, help="random cases per profile (default 4); fixed mode always uses the entire manifest")
    parser.add_argument("--nodes", type=int, help="override random node budget; otherwise profile-specific defaults")
    parser.add_argument("--attempts", type=int, help="generation attempts; default 1024 for call graphs, 512 for other profiles")
    defaults = {"seconds": 7200., "profile_seconds": 900., "disk_bytes": 1024**3,
                "profile_disk_bytes": 256 * 1024**2, "output_limit": 8 * 1024**2, "cleanup_seconds": 10.,
                "case_timeout": 90., "direct_fuel": 1000000, "core_fuel": 10000000, "gas": 10000000,
                "shrink_attempts": 16, "shrink_candidates": 64}
    for key, default in defaults.items():
        parser.add_argument("--" + key.replace("_", "-"), type=float if isinstance(default, float) else int, default=default)
    parser.add_argument("--bin-dir", type=Path, default=ROOT / ".lake/build/bin", help="directory of prebuilt native tools; suite performs no builds")
    binaries = {"case_tool": "semantic-case-tool", "storage_case_tool": "semantic-storage-tool", "rollback_case_tool": "semantic-storage-rollback-tool", "call_case_tool": "semantic-call-tool",
                "core_runner": "rust-hull-scenario", "storage_core_runner": "rust-hull-storage-scenario", "call_core_runner": "rust-hull-call-scenario",
                "keyed_case_tool": "semantic-keyed-storage-tool", "keyed_core_runner": "rust-hull-keyed-storage-scenario",
                "array_case_tool": "semantic-dynamic-array-tool"}
    for key in binaries:
        parser.add_argument("--" + key.replace("_", "-"), type=Path)
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--solc", type=Path, default=Path(shutil.which("solc") or "solc"), help="pinned solc; forwarded only to pure Yul campaigns")
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    args = parser.parse_args(argv)
    args.attempts_explicit = args.attempts is not None
    args.attempts = 512 if args.attempts is None else args.attempts
    if args.mode == "fixed" and (args.cases is not None or args.nodes is not None):
        parser.error("--cases and --nodes apply only to random mode; fixed corpora must remain complete")
    args.cases = args.cases if args.cases is not None else 4
    if args.backend == "yul":
        if args.profile and any(PROFILES[profile][1] != "pure" for profile in args.profile):
            parser.error("--backend yul supports only pure profiles; stateful profiles must use Sonatina")
        args.profile = args.profile or [profile for profile, (_, family, _) in PROFILES.items() if family == "pure"]
    else:
        args.profile = args.profile or list(PROFILES)
    if len(args.profile) != len(set(args.profile)):
        parser.error("duplicate profile selection")
    limits = {"seed": (0, 2**64-1), "shard_count": (1, 1000000), "shard_index": (0, 999999), "cases": (1, 1024),
              "attempts": (0, 10000), "seconds": (.001, 86400), "profile_seconds": (.001, 86400),
              "disk_bytes": (MIN_CAMPAIGN_BYTES * 2, 10**10), "profile_disk_bytes": (MIN_CAMPAIGN_BYTES, 10**10),
              "output_limit": (1024, 64 * 1024**2), "cleanup_seconds": (.1, 30), "case_timeout": (.001, 3600),
              "direct_fuel": (1, 10000000), "core_fuel": (1, 1000000000), "gas": (1, 1000000000),
              "shrink_attempts": (0, 10000), "shrink_candidates": (1, 4096)}
    if args.nodes is not None:
        limits["nodes"] = (3, 512)
    for key, (low, high) in limits.items():
        value = getattr(args, key)
        if not math.isfinite(value) or not low <= value <= high:
            parser.error(f"{key} must be between {low} and {high}")
    if args.shard_index >= args.shard_count:
        parser.error("--shard-index must be less than --shard-count")
    for key, binary in binaries.items():
        setattr(args, key, (getattr(args, key) or args.bin_dir / binary).resolve())
    for key in ("output", "bin_dir", "anvil", "upstream", "target_dir", "solc"):
        setattr(args, key, getattr(args, key).resolve())
    args.reserve_bytes = min(8 * 1024**2, args.disk_bytes // 8)
    return args


def main(argv=None):
    args = parse_args(argv)
    args.output.mkdir(parents=True, exist_ok=False)
    suite = Suite(args)
    previous = signal.getsignal(signal.SIGTERM)

    def interrupted(_signal, _frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupted)
    try:
        suite.run()
    except KeyboardInterrupt:
        previous_failure = any(row.get("status") in {"failed", "adapter-error"} for row in suite.report["profiles"])
        suite.report.update(status="failed" if previous_failure else "inconclusive-resource", stop="interrupted")
    except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as error:
        suite.report.update(status="failed", stop={"category": "adapter-error", "detail": str(error)})
    finally:
        suite.checkpoint()
        signal.signal(signal.SIGTERM, previous)
    print(json.dumps({"status": suite.report["status"], "summary": str(args.output / "summary.json"), "unexecutedProfiles": suite.report["unexecutedProfiles"]}))
    return 0 if suite.report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
