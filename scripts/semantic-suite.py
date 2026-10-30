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
# The pure campaign's runtime-input profiles and the inputs each of their functions yields.
_pure_spec = importlib.util.spec_from_file_location("semantic_suite_pure_campaign", ROOT / "scripts/semantic-campaign.py")
assert _pure_spec and _pure_spec.loader
pure_campaign = importlib.util.module_from_spec(_pure_spec)
_pure_spec.loader.exec_module(pure_campaign)
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
    "runtime-nested-loops": ("semantic-nested-loop", "pure", 384),
    "runtime-recursion": ("semantic-recursion", "pure", 384),
    "runtime-recursive-loops": ("semantic-recursive-loop", "pure", 384),
    "runtime-loop-closures": ("semantic-loop-closure", "pure", 384),
    "runtime-generics": ("semantic-generic", "pure", 384),
    "runtime-closures": ("semantic-closure", "pure", 384),
    "runtime-comptime": ("semantic-comptime", "pure", 384),
    "runtime-modules": ("semantic-module", "pure", 384),
    "runtime-primitives": ("semantic-primitive", "pure", 96),
    "runtime-assembly": ("semantic-assembly", "pure", 96),
    "runtime-assembly-memory": ("semantic-assembly-memory", "pure", 96),
    "runtime-enums": ("semantic-enum", "pure", 2048),
    "runtime-traits": ("semantic-trait", "pure", 2048),
    "runtime-trait-hierarchies": ("semantic-trait-hierarchy", "pure", 2048),
    "runtime-memory-values": ("semantic-memory-value", "pure", 1024),
    "runtime-memory-calls": ("semantic-memory-call", "pure", 1024),
    "runtime-call-graphs": ("semantic-call-graph", "pure", 192),
    "runtime-call-graph-loops": ("semantic-call-graph-loop", "pure", 256),
    "runtime-assembly-loops": ("semantic-assembly-loop", "pure", 256),
    "runtime-aggregate-call-graphs": ("semantic-aggregate-call-graph", "pure", 192),
    "stateful-storage": ("semantic-storage", "storage", 384),
    "stateful-storage-rollback": ("semantic-storage-rollback", "storage", 384),
    "stateful-calls": ("semantic-call", "call", 384),
    "stateful-keyed-storage": ("semantic-keyed-storage", "storage", 384),
    "stateful-dynamic-array": ("semantic-dynamic-array", "storage", 384),
    "stateful-logs": ("semantic-log", "storage", 384),
    "stateful-call-value": ("semantic-call-value", "storage", 384),
    "stateful-bytes": ("semantic-bytes", "storage", 384),
    "stateful-forwarded-value": ("semantic-forward", "call", 384),
    "stateful-mapping": ("semantic-mapping", "storage", 384),
    "stateful-ledger": ("semantic-ledger", "storage", 384),
    "stateful-long-bytes": ("semantic-long-bytes", "storage", 384),
    "stateful-nested-array": ("semantic-nested-array", "storage", 384),
    # Its std-modeling wrapper takes 273 nodes, so the step keeps 175 of 448.
    "stateful-malformed-calldata": ("semantic-malformed-calldata", "storage", 448),
    # Its std-modeling wrapper keeps 197 nodes inside the budget, so the step keeps 251 of 448.
    "stateful-malformed-nested-array": ("semantic-malformed-nested-array", "storage", 448),
    # Its std-modeling wrapper keeps 211 nodes inside the budget, so the step keeps 237 of 448.
    "stateful-malformed-bytes": ("semantic-malformed-bytes", "storage", 448),
    # The dispatch shell takes 58 nodes of 448; two to four methods share the rest.
    "stateful-methods": ("semantic-methods", "storage", 448),
    # The loop shell takes 57 nodes of 384; its guards lie outside the budget.
    "stateful-storage-loops": ("semantic-storage-loop", "storage", 384),
    # The Keccak-loop shell takes 38 nodes of 384; the Keccak closure and the
    # guards lie outside the budget.
    "stateful-keccak-loops": ("semantic-keccak-loop", "storage", 384),
    # The inline Yul forms of the two loop plans keep their parents' budgets.
    "stateful-assembly-storage-loops": ("semantic-assembly-storage-loop", "storage", 384),
    "stateful-assembly-keccak-loops": ("semantic-assembly-keccak-loop", "storage", 384),
    # The enum and struct storage shell takes 52 nodes of 384; the Keccak
    # closure, the enum closures and the methods lie outside the budget.
    "stateful-adt-storage": ("semantic-adt-storage", "storage", 384),
    # The tuple-return shell takes 79, 85 or 91 nodes of 384, by arity.
    "stateful-tuple-returns": ("semantic-tuple-return", "storage", 384),
    # The bytes-return shell takes 125 nodes of 384.
    "stateful-bytes-returns": ("semantic-bytes-return", "storage", 384),
    # The enum-return shell takes 130 to 291 nodes of 384, by shape.
    "stateful-enum-returns": ("semantic-enum-return", "storage", 384),
    # The enum-argument wrapper's fixed 168 nodes lie inside the budget; the
    # shape's decoder, 33 to 500 nodes, lies outside it.
    "stateful-enum-arguments": ("semantic-enum-argument", "storage", 384),
    # The enum-array reservation of 168 nodes lies inside the budget; the rest
    # of the array wrapper, 190 or 229 nodes, and the shape's decoder, 26 to 452
    # nodes, lie outside it.
    "stateful-enum-array-arguments": ("semantic-enum-array", "storage", 384),
    # The array-return shell takes 89 to 175 nodes of 384, by shape.
    "stateful-array-returns": ("semantic-array-return", "storage", 384),
    # The constructor-argument runtime shell takes 69 nodes of 384; the
    # initializer, 76 to 611 nodes, lies outside the budget.
    "stateful-constructor-arguments": ("semantic-constructor-argument", "storage", 384),
}
# Profiles that declare their observed slots share the declared-slot Hull runner.
DECLARED_SLOT_PROFILES = ("stateful-keyed-storage", "stateful-dynamic-array", "stateful-logs", "stateful-bytes", "stateful-mapping",
                          "stateful-long-bytes", "stateful-nested-array", "stateful-malformed-calldata",
                          "stateful-malformed-nested-array", "stateful-malformed-bytes", "stateful-methods",
                          "stateful-assembly-storage-loops", "stateful-assembly-keccak-loops",
                          "stateful-adt-storage",
                          "stateful-storage-loops", "stateful-keccak-loops", "stateful-tuple-returns",
                          "stateful-bytes-returns", "stateful-enum-returns", "stateful-enum-arguments",
                          "stateful-enum-array-arguments", "stateful-array-returns", "stateful-constructor-arguments")
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


def function_count(args, profile):
    """Whole functions a random runtime-input campaign generates under --functions, else None."""
    if args.mode == "random" and args.functions is not None and profile in pure_campaign.RUNTIME_INPUT_PROFILES:
        return args.functions
    return None


def inputs_per_function(profile):
    """The cases one function yields under the campaign's default random input selection."""
    return pure_campaign.inputs_per_function(profile, pure_campaign.RANDOM_INPUT_SELECTION)


def requested(args, profile):
    if args.mode == "random":
        functions = function_count(args, profile)
        return args.cases if functions is None else functions * inputs_per_function(profile)
    data = json.loads(manifest(profile).read_text())
    if data.get("profile", "closed-g0") != profile or not isinstance(data.get("cases"), list) or not data["cases"]:
        raise ValueError("fixed manifest profile or cases changed: " + profile)
    return len(data["cases"])


def profile_attempts(args, profile):
    """An explicit budget wins. Otherwise 1024 for call graphs and 512 elsewhere,
    raised under --functions to the campaign's attempts per function, within the
    case tool's limit; the derived seed keeps that many attempts below 2^64."""
    if getattr(args, "attempts_explicit", True):
        return args.attempts
    default = 1024 if profile == "runtime-call-graphs" else args.attempts
    functions = function_count(args, profile)
    if functions is None:
        return default
    return min(pure_campaign.MAX_ATTEMPTS, max(default, pure_campaign.ATTEMPTS_PER_FUNCTION * functions))


def node_budget(args, profile):
    """An explicit budget wins; otherwise the profile default, scaled and capped like the campaigns:
    at 512 nodes, at the enum, trait and trait hierarchy profiles' 4,096-node case limit, or at the
    memory value and memory call profiles' 2,048 nodes without their hash closure."""
    cap = pure_campaign.maximum_nodes(profile) if PROFILES[profile][1] == "pure" else 512
    return args.nodes or min(cap, round(PROFILES[profile][2] * args.nodes_scale))


def command(args, profile, output, seconds, disk_bytes):
    _, family, nodes = PROFILES[profile]
    attempts = profile_attempts(args, profile)
    if args.backend == "yul" and family == "call":
        raise ValueError("Yul is restricted to the pure and storage-family profiles")
    storage_tools = {"stateful-keyed-storage": args.keyed_case_tool, "stateful-dynamic-array": args.array_case_tool,
                     "stateful-logs": args.log_case_tool, "stateful-call-value": args.value_case_tool,
                     "stateful-bytes": args.bytes_case_tool, "stateful-mapping": args.mapping_case_tool,
                     "stateful-ledger": args.ledger_case_tool, "stateful-long-bytes": args.long_bytes_case_tool,
                     "stateful-nested-array": args.nested_array_case_tool,
                     "stateful-malformed-calldata": args.malformed_case_tool,
                     "stateful-malformed-nested-array": args.malformed_nested_case_tool,
                     "stateful-malformed-bytes": args.malformed_bytes_case_tool,
                     "stateful-methods": args.methods_case_tool,
                     "stateful-storage-loops": args.storage_loop_case_tool,
                     "stateful-keccak-loops": args.keccak_loop_case_tool,
                     "stateful-assembly-storage-loops": args.assembly_storage_loop_case_tool,
                     "stateful-assembly-keccak-loops": args.assembly_keccak_loop_case_tool,
                     "stateful-adt-storage": args.adt_storage_case_tool,
                     "stateful-tuple-returns": args.tuple_return_case_tool,
                     "stateful-bytes-returns": args.bytes_return_case_tool,
                     "stateful-enum-returns": args.enum_return_case_tool,
                     "stateful-enum-arguments": args.enum_argument_case_tool,
                     "stateful-enum-array-arguments": args.enum_array_case_tool,
                     "stateful-array-returns": args.array_return_case_tool,
                     "stateful-constructor-arguments": args.constructor_argument_case_tool}
    forwarded = profile == "stateful-forwarded-value"
    tool = {"pure": args.case_tool, "storage": args.rollback_case_tool if profile.endswith("-rollback") else
            storage_tools.get(profile, args.storage_case_tool), "call": args.forward_case_tool if forwarded else args.call_case_tool}[family]
    runner = {"pure": args.core_runner, "storage": args.value_core_runner if profile == "stateful-call-value" else
              args.ledger_core_runner if profile == "stateful-ledger" else
              args.keyed_core_runner if profile in DECLARED_SLOT_PROFILES else args.storage_core_runner,
              "call": args.forward_core_runner if forwarded else args.call_core_runner}[family]
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
        functions = function_count(args, profile)
        count = ["--cases", str(args.cases)] if functions is None else ["--functions", str(functions)]
        result += ["--seed", str(seed), "--nodes", str(node_budget(args, profile)), *count, "--attempts", str(attempts)]
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
            "rootSeed": str(args.seed), "shardIndex": args.shard_index, "shardCount": args.shard_count, "nodesScale": args.nodes_scale,
            "functions": args.functions,
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
                row.update(seed=str(derived_seed(args.seed, profile, args.shard_index, args.shard_count, profile_attempts(args, profile))), attempts=profile_attempts(args, profile), nodes=node_budget(args, profile))
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
                row["campaign"] = {key: summary[key] for key in ("backend", "status", "counts", "transactionCounts", "stop", "generation", "compilation") if key in summary}
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
    parser.add_argument("--profile", action="append", choices=tuple(PROFILES), help="repeat to select profiles; default all fifty-four for Sonatina, the twenty-five pure profiles for Yul, "
                             "which also runs the twenty-seven storage-family profiles when they are selected")
    parser.add_argument("--seed", type=int, default=1, help="root seed for reproducible random profile/shard seeds")
    parser.add_argument("--shard-index", type=int, default=0)
    parser.add_argument("--shard-count", type=int, default=1, help="seed shard count; every shard still runs all selected profiles")
    parser.add_argument("--cases", type=int, help="random cases per profile (default 4); fixed mode always uses the entire manifest")
    parser.add_argument("--functions", type=int,
                        help="random runtime-input pure profiles generate this many whole functions, each with all of its "
                             "inputs, instead of --cases; closed-g0 and the stateful profiles keep --cases")
    parser.add_argument("--nodes", type=int, help="override random node budget; otherwise profile-specific defaults")
    parser.add_argument("--nodes-scale", type=float, default=1.0, help="multiply each profile's default random node budget (1 to 4), capped at 512, or 4096 for enums, traits and trait hierarchies, or 2048 for memory values and memory calls")
    parser.add_argument("--attempts", type=int, help="generation attempts; default 1024 for call graphs, 512 for other profiles, "
                                                      "and with --functions at least 16 per function, up to 10000")
    # Hull fuel is only a bound: deploying the larger enum and struct storage
    # contracts from Sonatina O0 images takes up to 15,000,000.
    defaults = {"seconds": 7200., "profile_seconds": 900., "disk_bytes": 1024**3,
                "profile_disk_bytes": 256 * 1024**2, "output_limit": 8 * 1024**2, "cleanup_seconds": 10.,
                "case_timeout": 90., "direct_fuel": 1000000, "core_fuel": 40000000, "gas": 10000000,
                "shrink_attempts": 16, "shrink_candidates": 64}
    for key, default in defaults.items():
        parser.add_argument("--" + key.replace("_", "-"), type=float if isinstance(default, float) else int, default=default)
    parser.add_argument("--bin-dir", type=Path, default=ROOT / ".lake/build/bin", help="directory of prebuilt native tools; suite performs no builds")
    binaries = {"case_tool": "semantic-case-tool", "storage_case_tool": "semantic-storage-tool", "rollback_case_tool": "semantic-storage-rollback-tool", "call_case_tool": "semantic-call-tool",
                "core_runner": "rust-hull-scenario", "storage_core_runner": "rust-hull-storage-scenario", "call_core_runner": "rust-hull-call-scenario",
                "keyed_case_tool": "semantic-keyed-storage-tool", "keyed_core_runner": "rust-hull-keyed-storage-scenario",
                "array_case_tool": "semantic-dynamic-array-tool", "log_case_tool": "semantic-log-tool",
                "value_case_tool": "semantic-call-value-tool", "value_core_runner": "rust-hull-value-scenario",
                "bytes_case_tool": "semantic-bytes-tool", "forward_case_tool": "semantic-forward-tool",
                "forward_core_runner": "rust-hull-forward-scenario", "mapping_case_tool": "semantic-mapping-tool",
                "ledger_case_tool": "semantic-ledger-tool", "ledger_core_runner": "rust-hull-ledger-scenario",
                "long_bytes_case_tool": "semantic-long-bytes-tool", "nested_array_case_tool": "semantic-nested-array-tool",
                "malformed_case_tool": "semantic-malformed-calldata-tool",
                "malformed_nested_case_tool": "semantic-malformed-nested-array-tool",
                "malformed_bytes_case_tool": "semantic-malformed-bytes-tool",
                "methods_case_tool": "semantic-methods-tool",
                "storage_loop_case_tool": "semantic-storage-loop-tool",
                "keccak_loop_case_tool": "semantic-keccak-loop-tool",
                "assembly_storage_loop_case_tool": "semantic-assembly-storage-loop-tool",
                "assembly_keccak_loop_case_tool": "semantic-assembly-keccak-loop-tool",
                "adt_storage_case_tool": "semantic-adt-storage-tool",
                "tuple_return_case_tool": "semantic-tuple-return-tool",
                "bytes_return_case_tool": "semantic-bytes-return-tool",
                "enum_return_case_tool": "semantic-enum-return-tool",
                "enum_argument_case_tool": "semantic-enum-argument-tool",
                "enum_array_case_tool": "semantic-enum-array-tool",
                "array_return_case_tool": "semantic-array-return-tool",
                "constructor_argument_case_tool": "semantic-constructor-argument-tool"}
    for key in binaries:
        parser.add_argument("--" + key.replace("_", "-"), type=Path)
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--solc", type=Path, default=Path(shutil.which("solc") or "solc"), help="pinned solc; forwarded only to Yul campaigns")
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    args = parser.parse_args(argv)
    args.attempts_explicit = args.attempts is not None
    args.attempts = 512 if args.attempts is None else args.attempts
    if args.mode == "fixed" and (args.cases is not None or args.functions is not None or args.nodes is not None or args.nodes_scale != 1):
        parser.error("--cases, --functions, --nodes and --nodes-scale apply only to random mode; fixed corpora must remain complete")
    args.cases = args.cases if args.cases is not None else 4
    if args.backend == "yul":
        if args.profile and any(PROFILES[profile][1] == "call" for profile in args.profile):
            parser.error("--backend yul supports the pure and storage-family profiles; call profiles must use Sonatina")
        args.profile = args.profile or [profile for profile, (_, family, _) in PROFILES.items() if family == "pure"]
    else:
        args.profile = args.profile or list(PROFILES)
    if len(args.profile) != len(set(args.profile)):
        parser.error("duplicate profile selection")
    if args.functions is not None:
        counted = [profile for profile in args.profile if profile in pure_campaign.RUNTIME_INPUT_PROFILES]
        if not counted:
            parser.error("--functions needs a selected runtime-input profile")
        # Each campaign returns at most MAX_CASES cases, so the profile with the most inputs bounds N.
        bound, binding = min((pure_campaign.MAX_CASES // inputs_per_function(profile), profile) for profile in counted)
        if not 1 <= args.functions <= bound:
            parser.error(f"--functions must be between 1 and {bound}, the most {binding} allows")
    limits = {"seed": (0, 2**64-1), "shard_count": (1, 1000000), "shard_index": (0, 999999), "cases": (1, 1024),
              "attempts": (0, 10000), "seconds": (.001, 86400), "profile_seconds": (.001, 86400),
              "disk_bytes": (MIN_CAMPAIGN_BYTES * 2, 10**10), "profile_disk_bytes": (MIN_CAMPAIGN_BYTES, 10**10),
              "output_limit": (1024, 64 * 1024**2), "cleanup_seconds": (.1, 30), "case_timeout": (.001, 3600),
              "direct_fuel": (1, 10000000), "core_fuel": (1, 1000000000), "gas": (1, 1000000000),
              "shrink_attempts": (0, 10000), "shrink_candidates": (1, 4096), "nodes_scale": (1, 4)}
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
