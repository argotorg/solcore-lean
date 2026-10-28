#!/usr/bin/env python3
"""Run random semantic campaigns continuously and register their findings.

Each iteration runs scripts/semantic-suite.py in random mode once per selected
backend, with root seed base + iteration on a fixed shard, so every backend
compares the same generated programs. The prepared tools are verified before
each run; their readiness receipt and the harness scripts form an epoch that
may change only when a new epoch is accepted explicitly. Every finding
occurrence is counted in a registry under a signature. The first examples of a
signature keep their archives, and runs are pruned to compact records, since
random cases replay from their recorded seeds. A label records triage only:
labelled signatures stay counted and listed. The driver compares no
observations itself.
"""
from __future__ import annotations

import argparse
import contextlib
import datetime
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import traceback

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
_suite_spec = importlib.util.spec_from_file_location("semantic_fuzz_suite", ROOT / "scripts/semantic-suite.py")
assert _suite_spec and _suite_spec.loader
suite = importlib.util.module_from_spec(_suite_spec)
_suite_spec.loader.exec_module(suite)
SCHEMA = "solcore-lean.semantic-fuzz.v1"
BACKENDS = ("sonatina-o0", "sonatina-o2", "yul")
INCONCLUSIVE = {"inconclusive-resource"}
# Categories identified by the failing tool's message rather than by the program.
SYMPTOM_CATEGORIES = {"compiler-crash", "source-rejected", "compilation-rejected", "execution-error", "adapter-error",
                      "unsupported-scope", "inconclusive-resource"}
PROGRAM_KEYS = ("finalCaseSha256", "finalProgramSha256", "caseSha256", "programSha256", "originalCaseSha256",
                "originalProgramSha256")
RECENT = 20
MISSING_SUMMARY_LIMIT = 3
# Campaign generation fields besides the seed that decide what a random case regenerates.
REPLAY_FIELDS = ("generatorVersions", "inputSelections", "acceptances", "transactions")
# A pure campaign's shared-compilation counts, kept per profile beside them.
COMPILATION_FIELDS = ("distinctSources", "compiled", "reused")
CONFIG_DEFAULTS = {"base_seed": None, "shard_index": 0, "shard_count": 1, "backend": list(BACKENDS), "profile": None,
                   "cases": 16, "functions": None, "attempts": 2048, "nodes": None, "size_cycle": [1.0, 2.0],
                   "seconds": 14400.0, "profile_seconds": 900.0,
                   "disk_bytes": 1024**3, "examples": 3, "crash_replay": True, "bin_dir": None, "upstream": None,
                   "target_dir": None,
                   "anvil": None, "solc": None}
PATH_OPTIONS = ("bin_dir", "upstream", "target_dir", "anvil", "solc")


class NotReady(Exception):
    pass


class EpochChanged(Exception):
    pass


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")


def save(path, value):
    temporary = path.with_name(path.name + ".writing")
    temporary.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")
    temporary.replace(path)


def load(path, default=None):
    try:
        return json.loads(path.read_text())
    except FileNotFoundError:
        return default


def remove(path):
    if path.is_dir() and not path.is_symlink():
        shutil.rmtree(path, ignore_errors=True)
    else:
        path.unlink(missing_ok=True)


def canonical_id(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()[:12]


def normalize(text):
    """Remove run-specific detail so that repeated failures share a symptom."""
    text = re.sub(r"\S*?index\.crates\.io-[0-9a-f]+/", "", text)
    text = re.sub(r"\S*?/(crates/[^\s:]+)", r"\1", text)
    text = re.sub(r"(?<![\w.])/[^\s:]+", "<path>", text)
    text = re.sub(r"thread '([^']*)' \(\d+\)", r"thread '\1'", text)
    text = re.sub(r"0x[0-9a-fA-F]+", "<hex>", text)
    return re.sub(r"(?<![\w.:<])\d+(?![\w.])", "<n>", text).strip()


def symptom(detail):
    """The first panic location and message, else the first error line."""
    detail = detail if isinstance(detail, str) else json.dumps(detail, sort_keys=True)
    panic = re.search(r"panicked at ([^\n]+?):?\n([^\n]+)", detail)
    if panic:
        location = re.sub(r"\S*?index\.crates\.io-[0-9a-f]+/", "", panic.group(1))
        return {"panic": re.sub(r"\S*?/(crates/\S+)", r"\1", location), "message": normalize(panic.group(2))}
    lines = [line.strip() for line in detail.splitlines() if line.strip()]
    errors = [line for line in lines if re.search(r"error", line, re.I)]
    return {"message": normalize((errors or lines or [""])[0])[:400]}


# Frames of the panic machinery and of the standard library never identify a compiler call site.
MACHINERY = re.compile(r"^<?(std|core|alloc|__rustc|backtrace|panic_unwind|rust_begin_unwind)(::|\b)")


def backtrace_frames(text):
    """Function names of a Rust backtrace, without hash suffixes, in order."""
    names = []
    for line in text.splitlines():
        match = re.match(r"\s*\d+:\s+(\S.*?)\s*$", line)
        if match and not match.group(1).startswith("0x"):
            names.append(re.sub(r"::h[0-9a-f]{16}$", "", match.group(1)))
    return names


def call_site(output, panic):
    """The first two frames outside the panic machinery and the panicking library itself."""
    if "panicked at" not in output:
        return ["not reproduced"]
    library = re.sub(r"-\d+(\.\d+)*(-[^/]*)?$", "", panic.split("/")[0]).replace("-", "_") if panic else None
    frames = [name for name in backtrace_frames(output) if not MACHINERY.match(name)
              and not (library and re.match(rf"^<?{re.escape(library)}(::|\b)", name))]
    return frames[:2] or ["no compiler frame"]


def crash_site(record, timeout=180):
    """Replay a panicking Rust stage of a retained archive with RUST_BACKTRACE=1 and name its call site.

    The replay runs in a scratch copy of the archive and only adds detail to the
    signature; the run's own classification is never revisited.
    """
    archive, detail = record["archive"], record["detail"]
    if not archive or not isinstance(detail, str) or "panicked at" not in detail:
        return None
    original = archive / "original" if (archive / "original").is_dir() else archive
    report = load(original / "report.json") or {}
    failing = [process for process in report.get("processes", [])
               if process.get("returncode") and str(process.get("stage", "")).startswith("rust-")]
    if not failing:
        return None
    command = [str(part) for part in failing[-1].get("command", [])]
    root = command[command.index("--root") + 1] if "--root" in command[:-1] else \
        next((str(Path(part).parent) for part in command if part.endswith(".sol")), None)
    if not root:
        return None
    with tempfile.TemporaryDirectory(prefix="semantic-fuzz-replay-") as scratch:
        shutil.copytree(original, scratch, dirs_exist_ok=True)
        replay = [scratch + part[len(root):] if part.startswith(root) else part for part in command]
        if Path(replay[0]).name.startswith("python"):
            replay[0] = sys.executable
        try:
            result = subprocess.run(replay, cwd=ROOT, env={**os.environ, "RUST_BACKTRACE": "1"}, capture_output=True,
                                    text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return ["replay timeout"]
        except OSError as error:
            return [f"replay failed: {error.__class__.__name__}"]
    return call_site(result.stderr + result.stdout, symptom(detail).get("panic"))


def signature_key(profile, fingerprint, detail, program, site=None):
    key = {"backend": fingerprint.get("backend"), "category": fingerprint.get("category"), "stage": fingerprint.get("stage")}
    if key["category"] in SYMPTOM_CATEGORIES:
        key["symptom"] = symptom(detail)
        if site:
            key["symptom"]["site"] = site
    else:
        # Coarse mismatch fingerprints are shared by unrelated miscompilations;
        # only the same reduced program counts as the same finding.
        key.update(profile=profile, program=program, fingerprint={name: value for name, value in fingerprint.items()
                                                                     if name not in ("backend", "category", "stage")})
    return key


class StopFlag:
    def __init__(self):
        self.reason = None

    def __call__(self, signum, _frame):
        self.reason = self.reason or signal.Signals(signum).name


class State:
    def __init__(self, directory):
        self.directory = Path(directory).resolve()
        self.config_path = self.directory / "config.json"
        self.state_path = self.directory / "state.json"
        self.ledger_path = self.directory / "ledger.jsonl"
        self.registry_path = self.directory / "registry.json"
        self.labels_path = self.directory / "labels.json"
        self.stop_path = self.directory / "STOP"

    @contextlib.contextmanager
    def lock(self):
        self.directory.mkdir(parents=True, exist_ok=True)
        with (self.directory / "lock").open("a+") as handle:
            try:
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                raise NotReady(f"another driver holds {self.directory / 'lock'}") from None
            handle.truncate(0)
            handle.write(str(os.getpid()))
            handle.flush()
            yield

    def ledger(self):
        try:
            lines = self.ledger_path.read_text().splitlines()
        except FileNotFoundError:
            return []
        rows = []
        for number, line in enumerate(lines):
            try:
                rows.append(json.loads(line))
            except ValueError:
                if number != len(lines) - 1:
                    raise  # Only an interrupted final write may be partial.
        return rows

    def append_ledger(self, row):
        with self.ledger_path.open("a") as ledger:
            ledger.write(json.dumps(row, sort_keys=True) + "\n")
            ledger.flush()
            os.fsync(ledger.fileno())

    def registry(self):
        return load(self.registry_path, {"schema": SCHEMA + "/registry", "signatures": {}, "processedRuns": []})

    def run_directory(self, iteration, backend):
        return self.directory / "runs" / f"{iteration:06d}" / backend


def profiles_for(config, backend):
    """Yul runs the pure and storage-family profiles, configured or not, and never
    the call profiles. The suite's own Yul default is only the pure profiles, so the
    storage family is selected explicitly."""
    if backend == "yul":
        selected = list(suite.PROFILES) if config["profile"] is None else config["profile"]
        return [profile for profile in selected if suite.PROFILES[profile][1] != "call"]
    if config["profile"] is None:
        return None  # The suite's own default selection for this backend.
    return list(config["profile"])


def root_seed(config, iteration):
    return (config["base_seed"] + iteration) % 2**64


def nodes_scale(config, iteration):
    """Every backend of an iteration uses the same scale, so they compare the same programs."""
    cycle = config.get("size_cycle") or [1.0]
    return cycle[iteration % len(cycle)]


def suite_command(config, iteration, backend, output):
    argv = [sys.executable, str(ROOT / "scripts/semantic-suite.py"), "--mode", "random", "--backend", backend,
            "--seed", str(root_seed(config, iteration)), "--shard-index", str(config["shard_index"]),
            "--shard-count", str(config["shard_count"]), "--cases", str(config["cases"]),
            "--seconds", str(config["seconds"]), "--profile-seconds", str(config["profile_seconds"]),
            "--disk-bytes", str(config["disk_bytes"]), "--nodes-scale", str(nodes_scale(config, iteration)),
            "--output", str(output)]
    for key in ("functions", "attempts", "nodes"):
        if config.get(key) is not None:
            argv += ["--" + key, str(config[key])]
    for profile in profiles_for(config, backend) or []:
        argv += ["--profile", profile]
    for key in PATH_OPTIONS:
        if config.get(key) and (key != "solc" or backend == "yul"):
            argv += ["--" + key.replace("_", "-"), config[key]]
    return argv


def configure(state, args):
    """Create the configuration once; later invocations may only repeat it."""
    stored = load(state.config_path)
    given = {key: getattr(args, key) for key in CONFIG_DEFAULTS if getattr(args, key, None) is not None}
    for key in PATH_OPTIONS:
        if key in given:
            given[key] = str(Path(given[key]).resolve())
    if stored is not None:
        different = {key: (stored.get(key), value) for key, value in given.items() if stored.get(key) != value}
        if different:
            raise NotReady(f"configuration differs from {state.config_path}: {different}; use a new state directory")
        return stored
    config = {**CONFIG_DEFAULTS, **given, "schema": SCHEMA + "/config", "created": now()}
    if config["base_seed"] is None:
        config["base_seed"] = int(time.time())
    if not 0 <= config["base_seed"] < 2**64:
        raise NotReady("--base-seed must be an unsigned 64-bit integer")
    if not config["backend"] or len(config["backend"]) != len(set(config["backend"])):
        raise NotReady("select each backend at most once")
    if config["examples"] < 1:
        raise NotReady("--examples must be at least 1")
    if not config["size_cycle"] or any(not 1 <= scale <= 4 for scale in config["size_cycle"]):
        raise NotReady("--size-cycle needs scales between 1 and 4")
    for backend in config["backend"]:
        if config["profile"] is not None and not profiles_for(config, backend):
            raise NotReady(f"no selected profile runs on {backend}")
        # Reject what the suite would reject before any run is recorded.
        try:
            with open(os.devnull, "w") as sink, contextlib.redirect_stderr(sink):
                suite.parse_args(suite_command(config, 0, backend, state.directory / "unused")[2:])
        except SystemExit:
            raise NotReady(f"the suite rejects this configuration for {backend}: {suite_command(config, 0, backend, 'OUTPUT')[2:]}") from None
    save(state.config_path, config)
    return config


def next_run(config, ledger, claimed=frozenset()):
    """The earliest run neither recorded nor in progress; gaps left by parallel workers come first."""
    taken = {(row["iteration"], row["backend"]) for row in ledger} | set(claimed)
    iteration = 0
    while True:
        for backend in config["backend"]:
            if (iteration, backend) not in taken:
                return iteration, backend
        iteration += 1


def harness_digest():
    result = hashlib.sha256()
    for path in sorted((ROOT / "scripts").glob("*.py")):
        if not path.name.startswith("test-") and path.name != "semantic-fuzz.py":
            result.update(path.name.encode() + b"\0" + suite.digest(path).encode() + b"\n")
    return result.hexdigest()


def verify_tools(config):
    argv = [sys.executable, str(ROOT / "scripts/prepare-semantic-tools.py"), "--verify"]
    for key in ("upstream", "target_dir", "anvil"):
        if config.get(key):
            argv += ["--" + key.replace("_", "-"), config[key]]
    result = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=1800)
    lines = result.stdout.strip().splitlines()
    report = None
    with contextlib.suppress(ValueError):
        report = json.loads(lines[-1]) if result.returncode == 0 and lines else None
    if not isinstance(report, dict) or report.get("status") != "ready":
        raise NotReady("prepared tools are not ready: " + (result.stderr.strip() or result.stdout.strip())[-2000:])
    return Path(report["receipt"])


def current_epoch(config):
    receipt = verify_tools(config)
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip() or None
    epoch = {"receiptSha256": suite.digest(receipt), "harnessSha256": harness_digest(), "gitHead": head}
    epoch["id"] = canonical_id({"receipt": epoch["receiptSha256"], "harness": epoch["harnessSha256"]})
    return epoch


def check_epoch(state, epoch, iteration, accept):
    record = load(state.state_path, {"schema": SCHEMA + "/state", "epochs": []})
    epochs = record["epochs"]
    if epochs and epochs[-1]["id"] == epoch["id"]:
        return
    if epochs and not accept:
        raise EpochChanged(f"prepared tools or harness scripts changed (epoch {epochs[-1]['id']} -> {epoch['id']}); "
                           "rerun with --accept-new-epoch to continue under the new epoch")
    epochs.append({**epoch, "firstIteration": iteration, "accepted": now()})
    save(state.state_path, record)


def run_suite(argv, stdout_path, stderr_path, stop, grace=120.0):
    """Run one suite; forward a stop request so that it records unfinished work."""
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        process = subprocess.Popen(argv, cwd=ROOT, stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr,
                                   start_new_session=True)
        forwarded = None
        while process.poll() is None:
            if stop.reason and forwarded is None:
                forwarded = time.monotonic()
                with contextlib.suppress(ProcessLookupError):
                    process.send_signal(signal.SIGTERM)
            if forwarded is not None and time.monotonic() - forwarded > grace:
                with contextlib.suppress(ProcessLookupError, PermissionError):
                    os.killpg(process.pid, signal.SIGKILL)
                break
            time.sleep(.5)
        return process.wait(), forwarded is not None


def finding_records(output, row):
    """Each finding of a suite profile row with its archive, failure detail and program identity."""
    folder = output / row["output"]
    records = []
    # Secondary archives may sit inside a primary archive, so take them out first.
    for kind, key in (("secondary", "secondaryFindings"), ("primary", "findings")):
        for finding in row.get(key) or []:
            if not isinstance(finding, dict) or not isinstance(finding.get("fingerprint"), dict):
                continue
            if kind == "primary":
                archive = (folder / finding["history"]).parent if finding.get("history") else None
                analysis = folder / finding.get("originalArchive", "missing") / "analysis.json"
                ident = f"case-{finding.get('caseIndex')}"
            else:
                archive = folder / finding["archive"] if finding.get("archive") else None
                analysis = archive / "analysis.json" if archive else folder / "missing"
                ident = "secondary-" + finding.get("archive", "unknown").replace("/", "-")
            detail = ""
            with contextlib.suppress(OSError, ValueError, AttributeError):
                detail = json.loads(analysis.read_text()).get("comparison", {}).get("detail", "")
            program = next((finding[name] for name in PROGRAM_KEYS if finding.get(name)), None)
            records.append({"kind": kind, "ident": ident, "finding": finding, "archive": archive, "detail": detail,
                            "program": program})
    return records


def crash_sites(config, output, summary):
    """Call sites of the run's panicking findings, computed before the archives move."""
    if not config.get("crash_replay"):
        return {}
    sites = {}
    for row in summary.get("profiles", []):
        for record in finding_records(output, row):
            site = crash_site(record)
            if site:
                sites[(row["profile"], record["ident"])] = site
    return sites


def register(state, config, epoch, iteration, backend, output, summary, sites=None):
    """Count every finding occurrence once and keep the first examples of each signature."""
    sites = sites or {}
    registry = state.registry()
    run_id = f"{iteration:06d}-{backend}"
    first_time = run_id not in registry["processedRuns"]
    occurrences = []
    for row in summary.get("profiles", []):
        for record in finding_records(output, row):
            key = signature_key(row["profile"], record["finding"]["fingerprint"], record["detail"], record["program"],
                                sites.get((row["profile"], record["ident"])))
            sid = canonical_id(key)
            brief = {"iteration": iteration, "backend": backend, "rootSeed": str(root_seed(config, iteration)),
                     "profile": row["profile"], "profileSeed": row.get("seed"), "kind": record["kind"],
                     "case": record["ident"], "epoch": epoch["id"], "program": record["program"]}
            entry = registry["signatures"].get(sid)
            new = entry is None
            if new:
                entry = registry["signatures"][sid] = {
                    "id": sid, "key": key, "kind": "inconclusive" if key["category"] in INCONCLUSIVE else "failure",
                    "category": key["category"], "stage": key["stage"], "symptom": key.get("symptom"), "count": 0,
                    "backends": {}, "profiles": {}, "firstSeen": brief, "lastSeen": brief, "examples": [], "recent": []}
            destination = state.directory / "findings" / sid / f"{iteration:06d}-{backend}-{row['profile']}-{record['ident']}"
            retained = None
            if destination.exists():
                retained = str(destination.relative_to(state.directory))
            elif len(entry["examples"]) < config["examples"] and record["archive"] and record["archive"].is_dir():
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.move(str(record["archive"]), str(destination))
                save(destination / "occurrence.json", {**brief, "signature": sid, "finding": record["finding"],
                                                       "suiteCommand": row.get("command")})
                retained = str(destination.relative_to(state.directory))
            if first_time:
                entry["count"] += 1
                entry["backends"][backend] = entry["backends"].get(backend, 0) + 1
                entry["profiles"][row["profile"]] = entry["profiles"].get(row["profile"], 0) + 1
                entry["lastSeen"] = brief
                entry["recent"] = (entry["recent"] + [brief])[-RECENT:]
                if retained and retained not in entry["examples"]:
                    entry["examples"].append(retained)
            occurrences.append({"signature": sid, "new": new and first_time, "profile": row["profile"],
                                "kind": record["kind"], "case": record["ident"], "retained": retained})
    if first_time:
        registry["processedRuns"].append(run_id)
    save(state.registry_path, registry)
    return occurrences


def problems_of(summary):
    """Runs and profiles that did not pass without a finding that explains them."""
    problems = []
    for row in summary.get("profiles", []):
        explained = row.get("status") == "failed" and bool(row.get("findings") or row.get("secondaryFindings"))
        if row.get("status") != "passed" and not explained:
            problems.append({"profile": row.get("profile"), "status": row.get("status"), "stop": row.get("stop"),
                             "counts": row.get("campaign", {}).get("counts"), "summaryError": row.get("summaryError")})
    for profile in summary.get("unexecutedProfiles", []):
        problems.append({"profile": profile, "status": "unexecuted", "stop": summary.get("stop")})
    if not summary.get("profiles") and summary.get("status") != "passed":
        problems.append({"profile": None, "status": summary.get("status", "missing-summary"), "stop": summary.get("stop")})
    return problems


def prune(run_dir, summary, keep):
    """Reduce a recorded run to compact records; random cases replay from their recorded seeds."""
    if keep or not run_dir.exists():
        return
    logs = [run_dir.with_name(run_dir.name + suffix) for suffix in (".stdout.log", ".stderr.log")]
    if summary.get("status") == "passed":
        for path in [run_dir, *logs]:
            remove(path)
        with contextlib.suppress(OSError):
            run_dir.parent.rmdir()
        return
    statuses = {row["output"]: row.get("status") for row in summary.get("profiles", []) if "output" in row}
    for path in list(run_dir.iterdir()):
        name = path.name.split(".")[0]
        if path.name == "summary.json":
            continue
        if statuses.get(name) == "passed" or (path.is_dir() and name not in statuses):
            remove(path)
        elif path.is_dir():
            for inner in list(path.iterdir()):
                if inner.name not in ("summary.json", "generation.json"):
                    remove(inner)


def retain_interrupted(state, run_dir):
    """An interrupted run is rerun from its seed; partial findings stay for inspection only."""
    logs = [run_dir.with_name(run_dir.name + suffix) for suffix in (".stdout.log", ".stderr.log")]
    if run_dir.exists() and any(run_dir.glob("*/findings/*/*")):
        destination = state.directory / "interrupted" / f"{run_dir.parent.name}-{run_dir.name}-{int(time.time())}"
        destination.mkdir(parents=True)
        shutil.move(str(run_dir), str(destination / "run"))
        for log in logs:
            if log.exists():
                shutil.move(str(log), str(destination / log.name))
        return str(destination.relative_to(state.directory))
    remove(run_dir)
    return None


def unrecorded_runs(state, ledger):
    """Finished but unrecorded runs; an interrupted one is set aside and rerun."""
    done = {(row["iteration"], row["backend"]) for row in ledger}
    runs = state.directory / "runs"
    found = []
    for run_dir in sorted(runs.glob("*/*")) if runs.exists() else []:
        if not run_dir.is_dir() or run_dir.name not in BACKENDS or not run_dir.parent.name.isdigit():
            continue
        if (int(run_dir.parent.name), run_dir.name) in done:
            continue
        summary = load(run_dir / "summary.json")
        if isinstance(summary, dict) and summary.get("status") not in (None, "running") and summary.get("stop") != "interrupted":
            found.append((int(run_dir.parent.name), run_dir.name, run_dir, summary))
        else:
            retain_interrupted(state, run_dir)
    return found


def replay_fields(row):
    generation = (row.get("campaign") or {}).get("generation") or {}
    return {key: generation[key] for key in REPLAY_FIELDS if key in generation}


def compilation_counts(row):
    """A pure campaign's shared-compilation counts; distinct sources measure its program diversity."""
    compilation = (row.get("campaign") or {}).get("compilation") or {}
    return {key: compilation[key] for key in COMPILATION_FIELDS if type(compilation.get(key)) is int}


def record_run(state, config, epoch, iteration, backend, run_dir, summary, exit_code, started, elapsed, keep, sites=None):
    occurrences = register(state, config, epoch, iteration, backend, run_dir, summary, sites)
    row = {"schema": SCHEMA + "/run", "iteration": iteration, "backend": backend,
           "rootSeed": str(root_seed(config, iteration)), "nodesScale": nodes_scale(config, iteration),
           "shardIndex": config["shard_index"],
           "shardCount": config["shard_count"], "epoch": epoch["id"], "started": started, "finished": now(),
           "elapsedSeconds": elapsed, "exitCode": exit_code, "suiteStatus": summary.get("status", "missing-summary"),
           "stop": summary.get("stop"), "counts": summary.get("counts", {}),
           "profiles": [{"profile": row.get("profile"), "status": row.get("status"), "seed": row.get("seed"),
                         "generation": replay_fields(row), "compilation": compilation_counts(row),
                         "findings": len(row.get("findings") or []),
                         "secondaryFindings": len(row.get("secondaryFindings") or [])}
                        for row in summary.get("profiles", [])],
           "occurrences": occurrences, "problems": problems_of(summary),
           "retainedRun": None if summary.get("status") == "passed" and not keep or not run_dir.exists()
           else str(run_dir.relative_to(state.directory))}
    state.append_ledger(row)
    prune(run_dir, summary, keep)
    return row


def report(state):
    """Write report.json and report.md from the configuration, ledger, registry and labels."""
    if not state.config_path.exists():
        raise NotReady(f"no fuzzing state in {state.directory}")
    config = load(state.config_path)
    ledger = state.ledger()
    registry = state.registry()
    labels = load(state.labels_path, {})
    runs = {}
    for row in ledger:
        totals = runs.setdefault(row["backend"], {"runs": 0, "iterations": set(), "statuses": {}, "counts": {},
                                                  "elapsedSeconds": 0.0})
        totals["runs"] += 1
        totals["iterations"].add(row["iteration"])
        totals["statuses"][row["suiteStatus"]] = totals["statuses"].get(row["suiteStatus"], 0) + 1
        totals["elapsedSeconds"] += row.get("elapsedSeconds") or 0
        for key, value in (row.get("counts") or {}).items():
            if type(value) is int:
                totals["counts"][key] = totals["counts"].get(key, 0) + value
    for totals in runs.values():
        totals["iterations"] = len(totals["iterations"])
        totals["elapsedSeconds"] = round(totals["elapsedSeconds"], 3)
    latest = max((row["iteration"] for row in ledger), default=None)
    newest = {occurrence["signature"] for row in ledger if row["iteration"] == latest
              for occurrence in row.get("occurrences", []) if occurrence.get("new")}
    signatures = []
    for sid, entry in registry["signatures"].items():
        text = labels.get(sid, {}).get("label")
        signatures.append({**{key: entry.get(key) for key in ("id", "kind", "category", "stage", "symptom", "count",
                                                                "backends", "profiles", "firstSeen", "lastSeen", "examples")},
                           "label": text, "triage": "known" if text else "untriaged", "newInLatestIteration": sid in newest})
    signatures.sort(key=lambda entry: (entry["triage"] == "known", entry["kind"] != "failure",
                                       -entry["lastSeen"]["iteration"], entry["id"]))
    problems = [{"iteration": row["iteration"], "backend": row["backend"], **problem}
                for row in ledger for problem in row.get("problems", [])]
    interrupted = state.directory / "interrupted"
    data = {"schema": SCHEMA + "/report", "generated": now(), "state": str(state.directory), "config": config,
            "epochs": load(state.state_path, {"epochs": []})["epochs"], "runs": runs, "latestIteration": latest,
            "signatures": signatures, "problemCount": len(problems), "problems": problems[-200:],
            "interrupted": sorted(path.name for path in interrupted.iterdir()) if interrupted.exists() else []}
    save(state.directory / "report.json", data)
    (state.directory / "report.md").write_text(markdown(data))
    return data


def seen(brief):
    return f"it {brief['iteration']} {brief['backend']} {brief['profile']} {brief['case']}" if brief else ""


def markdown(data):
    config = data["config"]
    # Configurations created before --functions existed have no such key.
    functions = config.get("functions")
    counts = (f"{config['cases']} cases per profile" if functions is None else
              f"{functions} whole functions per runtime-input profile and {config['cases']} cases per other profile")
    lines = ["# Semantic fuzzing report", "", f"Generated {data['generated']} from `{data['state']}`.", "",
             f"Base seed {config['base_seed']}, shard {config['shard_index']} of {config['shard_count']}, "
             f"backends {', '.join(config['backend'])}, {counts}, node-budget scales "
             f"{', '.join(str(scale) for scale in config.get('size_cycle') or [1.0])} by iteration, profiles: "
             f"{'suite default' if config['profile'] is None else ', '.join(config['profile'])}.", ""]
    if data["epochs"]:
        epoch = data["epochs"][-1]
        lines += [f"Epoch `{epoch['id']}` since iteration {epoch['firstIteration']} (readiness receipt "
                  f"{epoch['receiptSha256'][:12]}, harness {epoch['harnessSha256'][:12]}, git {str(epoch['gitHead'])[:12]}).", ""]
    lines += ["## Runs", "",
              "| Backend | Iterations | Suite statuses | Executed | Matched | Mismatched | Errors | Inconclusive | Hours |",
              "| --- | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for backend, totals in sorted(data["runs"].items()):
        counts = totals["counts"]
        statuses = ", ".join(f"{name} {count}" for name, count in sorted(totals["statuses"].items()))
        lines.append(f"| {backend} | {totals['iterations']} | {statuses} | {counts.get('executed', 0)} | "
                     f"{counts.get('matched', 0)} | {counts.get('mismatched', 0)} | {counts.get('errors', 0)} | "
                     f"{counts.get('inconclusive', 0)} | {totals['elapsedSeconds'] / 3600:.2f} |")
    lines += ["", "## Findings by signature", "",
              "Untriaged signatures come first. A label marks a signature as known; it stays counted.", "",
              "| Signature | Triage | Category | Stage | Symptom or program | Count | Backends | Profiles | First seen | Last seen | Kept |",
              "| --- | --- | --- | --- | --- | ---: | --- | --- | --- | --- | ---: |"]
    for entry in data["signatures"]:
        described = " ".join(str(value) for value in (entry["symptom"] or {}).values()) or str(entry["firstSeen"].get("program"))
        triage = ("known: " + entry["label"]) if entry["label"] else "untriaged"
        triage += " (new)" if entry["newInLatestIteration"] else ""
        lines.append("| `{}` | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |".format(
            entry["id"], triage.replace("|", "\\|"), entry["category"], entry["stage"],
            described.replace("|", "\\|")[:160], entry["count"],
            ", ".join(f"{name} {count}" for name, count in sorted(entry["backends"].items())),
            ", ".join(f"{name} {count}" for name, count in sorted(entry["profiles"].items())),
            seen(entry["firstSeen"]), seen(entry["lastSeen"]), len(entry["examples"])))
    if not data["signatures"]:
        lines.append("| none | | | | | | | | | | |")
    lines += ["", "## Problems", "", f"{data['problemCount']} profile runs ended without passing and without a finding "
              "that explains them. The latest:", ""]
    lines += [f"- iteration {problem['iteration']} {problem['backend']} {problem.get('profile')}: {problem.get('status')} "
              f"(stop {problem.get('stop')})" for problem in data["problems"][-20:]] or ["- none"]
    if data["interrupted"]:
        lines += ["", "## Interrupted runs kept for inspection", ""] + [f"- `interrupted/{name}`" for name in data["interrupted"]]
    return "\n".join(lines) + "\n"


def notify(command, state, row, new):
    if not command:
        return
    environment = {**os.environ, "SEMANTIC_FUZZ_STATE": str(state.directory),
                   "SEMANTIC_FUZZ_REPORT": str(state.directory / "report.md"), "SEMANTIC_FUZZ_NEW": ",".join(new),
                   "SEMANTIC_FUZZ_PROBLEMS": str(len(row["problems"])), "SEMANTIC_FUZZ_ITERATION": str(row["iteration"]),
                   "SEMANTIC_FUZZ_BACKEND": row["backend"]}
    try:
        result = subprocess.run(shlex.split(command), cwd=ROOT, env=environment, capture_output=True, text=True, timeout=120)
        outcome = f"exit {result.returncode}: {(result.stderr or result.stdout)[-500:]}"
    except (OSError, subprocess.SubprocessError) as error:
        outcome = f"failed: {error}"
    with (state.directory / "notify.log").open("a") as log:
        log.write(json.dumps({"time": now(), "iteration": row["iteration"], "backend": row["backend"], "new": new,
                              "outcome": outcome}) + "\n")


def finish(state, reason, code=0, kept=None):
    report(state)
    print(json.dumps({"stopped": reason, "report": str(state.directory / "report.md"), "interruptedArchive": kept}), flush=True)
    return code


class Driver:
    """Parallel workers claim (iteration, backend) runs; results are recorded one at a time."""

    def __init__(self, state, config, args, stop):
        self.state, self.config, self.args, self.stop = state, config, args, stop
        self.lock = threading.Lock()
        self.claimed = set()
        self.first = None
        self.missing = 0
        self.ending = None

    def end(self, reason, code=0, kept=None):
        """The first reason to stop wins; runs in progress still finish and are recorded."""
        if self.ending is None:
            self.ending = (reason, code, kept)

    def claim(self):
        with self.lock:
            if self.ending is None and self.stop.reason:
                self.end("signal " + self.stop.reason)
            elif self.ending is None and self.state.stop_path.exists():
                self.end("stop file")
            elif self.ending is None and self.args.max_state_bytes and \
                    suite.directory_bytes(self.state.directory) >= self.args.max_state_bytes:
                self.end("state disk limit", 4)
            if self.ending is not None:
                return None
            unit = next_run(self.config, self.state.ledger(), self.claimed)
            self.first = unit[0] if self.first is None else self.first
            if self.args.iterations and unit[0] >= self.first + self.args.iterations:
                self.end("iteration limit")
                return None
            self.claimed.add(unit)
            return unit

    def work(self):
        while (unit := self.claim()) is not None:
            try:
                self.run(*unit)
            except EpochChanged as error:
                with self.lock:
                    self.end("epoch changed: " + str(error), 3)
            except NotReady as error:
                with self.lock:
                    self.end(("signal " + self.stop.reason) if self.stop.reason else "not ready: " + str(error),
                             0 if self.stop.reason else 2)
            except Exception as error:  # noqa: BLE001 - stop every worker and keep the traceback visible.
                traceback.print_exc()
                with self.lock:
                    self.end(f"driver error in iteration {unit[0]} ({unit[1]}): {error!r}", 6)
            finally:
                with self.lock:
                    self.claimed.discard(unit)

    def run(self, iteration, backend):
        state, config, args = self.state, self.config, self.args
        epoch = current_epoch(config)
        with self.lock:
            check_epoch(state, epoch, iteration, args.accept_new_epoch)
            args.accept_new_epoch = False  # One acceptance covers only the epoch it was given for.
        run_dir = state.run_directory(iteration, backend)
        run_dir.parent.mkdir(parents=True, exist_ok=True)
        started, began = now(), time.monotonic()
        exit_code, interrupted = run_suite(suite_command(config, iteration, backend, run_dir),
                                           run_dir.with_name(backend + ".stdout.log"),
                                           run_dir.with_name(backend + ".stderr.log"), self.stop)
        summary = load(run_dir / "summary.json")
        if interrupted or isinstance(summary, dict) and summary.get("stop") == "interrupted":
            with self.lock:
                kept = retain_interrupted(state, run_dir)
                self.end(f"interrupted in iteration {iteration} ({backend}); it reruns on resume", kept=kept)
            return
        summary = summary if isinstance(summary, dict) else None
        sites = crash_sites(config, run_dir, summary) if summary else {}  # Replays run outside the lock.
        with self.lock:
            self.missing = self.missing + 1 if summary is None else 0
            summary = summary or {"status": "missing-summary", "profiles": []}
            row = record_run(state, config, epoch, iteration, backend, run_dir, summary, exit_code, started,
                             round(time.monotonic() - began, 3), args.keep_runs, sites)
            report(state)
            if self.missing >= MISSING_SUMMARY_LIMIT:
                self.end(f"{self.missing} consecutive runs produced no suite summary; see their logs", 5)
        new = [occurrence["signature"] for occurrence in row["occurrences"] if occurrence["new"]]
        print(json.dumps({"iteration": iteration, "backend": backend, "rootSeed": row["rootSeed"], "status": row["suiteStatus"],
                          "occurrences": len(row["occurrences"]), "new": new, "problems": len(row["problems"])}), flush=True)
        if new or any(problem.get("status") in ("adapter-error", "missing-summary") for problem in row["problems"]):
            notify(args.notify_command, state, row, new)


def run(args):
    state = State(args.state)
    with state.lock():
        config = configure(state, args)
        stop = StopFlag()
        previous = {signum: signal.signal(signum, stop) for signum in (signal.SIGTERM, signal.SIGINT)}
        try:
            for iteration, backend, run_dir, summary in unrecorded_runs(state, state.ledger()):
                record_run(state, config, current_epoch(config), iteration, backend, run_dir, summary, None, None, None,
                           args.keep_runs, crash_sites(config, run_dir, summary))
            driver = Driver(state, config, args, stop)
            workers = [threading.Thread(target=driver.work, name=f"fuzz-worker-{index}", daemon=True)
                       for index in range(args.jobs)]
            for worker in workers:
                worker.start()
            for worker in workers:
                while worker.is_alive():
                    worker.join(.5)  # Short joins keep signal handling in the main thread prompt.
            reason, code, kept = driver.ending or ("workers finished", 0, None)
            return finish(state, reason, code, kept)
        finally:
            for signum, handler in previous.items():
                signal.signal(signum, handler)


def label(args):
    state = State(args.state)
    if args.signature not in state.registry()["signatures"]:
        raise NotReady(f"unknown signature {args.signature}")
    labels = load(state.labels_path, {})
    if args.clear:
        labels.pop(args.signature, None)
    elif args.text:
        labels[args.signature] = {"label": args.text, "updated": now()}
    else:
        raise NotReady("give a label text or --clear")
    save(state.labels_path, labels)
    report(state)
    return 0


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    runner = commands.add_parser("run", help="run iterations until stopped")
    shown = commands.add_parser("report", help="regenerate report.md and report.json and print the Markdown")
    labeller = commands.add_parser("label", help="record or clear the triage label of a signature")
    for command in (runner, shown, labeller):
        command.add_argument("--state", type=Path, default=ROOT / ".upstream/semantic-fuzz", help="state directory")
    runner.add_argument("--base-seed", type=int, help="root seed of iteration zero (default: the creation time)")
    runner.add_argument("--shard-index", type=int)
    runner.add_argument("--shard-count", type=int)
    runner.add_argument("--backend", action="append", choices=BACKENDS, help="repeat; default all three")
    runner.add_argument("--profile", action="append", choices=tuple(suite.PROFILES), help="repeat; default the suite's selection")
    runner.add_argument("--size-cycle", type=lambda text: [float(part) for part in text.split(",")],
                        help="comma-separated node-budget scales used by successive iterations (default 1,2)")
    for name, kind in (("cases", int), ("functions", int), ("attempts", int), ("nodes", int), ("seconds", float),
                       ("profile-seconds", float), ("disk-bytes", int), ("examples", int)):
        runner.add_argument("--" + name, type=kind)
    for name in ("bin-dir", "upstream", "target-dir", "anvil", "solc"):
        runner.add_argument("--" + name, type=Path)
    runner.add_argument("--iterations", type=int, default=0, help="stop after this many iterations (default: until stopped)")
    runner.add_argument("--jobs", type=int, default=1, help="runs in parallel; each run is one suite on one backend")
    runner.add_argument("--max-state-bytes", type=int, default=50 * 1024**3, help="stop before a run once the state uses this much disk")
    runner.add_argument("--accept-new-epoch", action="store_true", help="continue after the tools or harness scripts changed")
    runner.add_argument("--keep-runs", action="store_true", help="keep complete run directories instead of pruning them")
    runner.add_argument("--notify-command", help="command run after a run with new signatures or missing summaries")
    runner.add_argument("--no-crash-replay", dest="crash_replay", action="store_const", const=False,
                        help="do not replay panics with RUST_BACKTRACE=1 to split crash signatures by call site")
    labeller.add_argument("signature")
    labeller.add_argument("text", nargs="?")
    labeller.add_argument("--clear", action="store_true")
    args = parser.parse_args(argv)
    if args.command == "run" and args.iterations < 0:
        parser.error("--iterations must not be negative")
    if args.command == "run" and not 1 <= args.jobs <= 256:
        parser.error("--jobs must be between 1 and 256")
    return args


def main(argv=None):
    args = parse_args(argv)
    try:
        if args.command == "run":
            return run(args)
        if args.command == "label":
            return label(args)
        state = State(args.state)
        report(state)
        print((state.directory / "report.md").read_text(), end="")
        return 0
    except EpochChanged as error:
        print(json.dumps({"stopped": "epoch changed", "detail": str(error)}), file=sys.stderr)
        return 3
    except NotReady as error:
        print(json.dumps({"stopped": "not ready", "detail": str(error)}), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
