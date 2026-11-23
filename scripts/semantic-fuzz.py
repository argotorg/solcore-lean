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

The opt-in run kind `fixtures` runs scripts/semantic-fixtures.py in mutation
mode on a seeded slice of the pinned end-to-end fixtures per iteration, within
per-fixture mutant, sequence mutant, source mutant and time budgets and an
iteration time budget. That
harness compares compiled paths with each other and with upstream's recorded
expectations, never with original Core.

The opt-in run kind `native` runs scripts/semantic-native.py in random mode on
each iteration's draws: the suite's root seed, shard, case counts, attempts and
node-budget scale, on the pure profiles whose emitter the native admission
admits, within a run time budget. That harness compares Lean's native frontend
with each admitted case's direct Core result, never with a compiled path, and
its labels of Lean's known differences from upstream count as known. `replay`
reruns a kept native example through the harness's own comparison.
"""
from __future__ import annotations

import argparse
import contextlib
import datetime
import fcntl
import functools
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
# A fixtures run compares every compiled path of the pinned end-to-end fixtures at once.
FIXTURES = "fixtures"
# A native run compares Lean's native frontend with original Core on the admitted pure cases.
NATIVE = "native"
RUN_KINDS = BACKENDS + (FIXTURES, NATIVE)
# The native harness's counts of a run, in its order, and its time budget for one program (its default).
NATIVE_COUNTS = ("cases", "generationExcluded", "notAdmitted", "admitted", "programs", "agree", "mismatch", "rejected",
                 "inconclusive", "unexecuted")
NATIVE_PROGRAM_SECONDS = 120.0
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
                   "anvil": None, "solc": None, "fixture_count": 8, "fixture_mutants": 32, "fixture_sequences": 8, "fixture_sources": 2,
                   "fixture_seconds": 300.0,
                   "fixture_run_seconds": 1800.0, "fixture_jobs": 2, "cast": None, "native_seconds": 1800.0}
PATH_OPTIONS = ("bin_dir", "upstream", "target_dir", "anvil", "solc")
# Paths only a fixtures run reads; the suite takes none of them.
FIXTURE_PATH_OPTIONS = ("cast",)


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


# Upstream findings recorded in questions.md: they count, but never as new. Each
# key is a stable symptom taken from a real occurrence through the driver, a crash
# by its panic and call site, a rejection by its first error line and a path
# failure by its path and Core value; mismatches, whose keys are reduced programs,
# are never listed here but in MISMATCH_CLASSES and FIXTURE_MISMATCH_CLASSES.
PRIMITIVE_TYPES = "primitive-types-0.14.0/src/lib.rs:43:1"
DEMANDED_BITS = ["<sonatina_codegen::analysis::demanded_bits::DemandedBitsQuery>::propagate_binary",
                 "<sonatina_codegen::analysis::demanded_bits::DemandedBitsQuery>::propagate_from_value"]
SIGNEXTEND_FOLD = ["sonatina_codegen::optim::simplify_expr::fold_evm_signextend_raw",
                   "sonatina_codegen::optim::simplify_expr::fold_evm_signextend"]
NOT_CONCRETE = "error[SC0401]: cannot specialize expression: type is not concrete"
KNOWN_FINDINGS = (
    ({"backend": FIXTURES, "category": "compiler-crash", "stage": "rust-code-images-O2", "paths": ["sonatina-o2"],
      "symptom": {"panic": "crates/ir/src/dfg.rs:354:9", "message": "assertion failed: self.has_inst(inst_id)"}},
     "Sonatina O2 has_inst assertion on ignored-builtin-effects (questions.md, 2026-10-29)"),
    ({"backend": FIXTURES, "category": "path-failure", "stage": "execution", "path": "hull", "status": "language-failure",
      "symptom": {"value": "Solcore.Core.Value.word 6"}},
     "Hull memory's range on a source mutant's store at 2^256 - 1 that solc's Yul removes (questions.md, 2026-10-31)"),
    *(({"backend": backend, "category": "compiler-crash", "stage": "rust-code-images",
        "symptom": {"panic": PRIMITIVE_TYPES, "message": "Integer overflow when casting to usize", "site": DEMANDED_BITS}}, label)
      for backend, label in (
          ("sonatina-o2", "Sonatina O2 demanded-bits overflow on a constant shift count, Q013 (questions.md, 2026-10-26 to "
                          "2026-10-28)"),
          ("sonatina-o0", "Sonatina O0 demanded-bits overflow on a constant shift count in inline Yul (questions.md, "
                          "2026-10-28)"),
          ("yul", "Sonatina O0 demanded-bits overflow in the Yul runs' code images (questions.md, 2026-10-28)"))),
    ({"backend": "sonatina-o2", "category": "compiler-crash", "stage": "rust-code-images",
      "symptom": {"panic": PRIMITIVE_TYPES, "message": "arithmetic operation overflow", "site": SIGNEXTEND_FOLD}},
     "Sonatina O2 signextend folding overflow (questions.md, 2026-10-27)"),
    *(({"backend": backend, "category": "source-rejected", "stage": "rust-checked-source",
        "symptom": {"message": NOT_CONCRETE}},
       "checked frontend SC0406 for a base method through two superclass bounds (questions.md, 2026-10-29)")
      for backend in BACKENDS),
    ({"backend": "yul", "category": "compilation-rejected", "stage": "rust-yul-evm",
      "symptom": {"message": "Dynamic exception type: boost::wrapexcept<solidity::yul::StackTooDeepError>"}},
     "solc StackTooDeepError on specialized trait methods (questions.md, 2026-10-29)"),
)


def memory_value(ref):
    """A bytes value `sc_b<n>` or a slice `sc_s<n>` of a memory-value plan; arrays are `sc_a<n>`."""
    return isinstance(ref, str) and re.fullmatch(r"sc_[bs]\d+", ref) is not None


def loop_observes_then_slices_or_writes(case):
    """A single loop whose body observes a bytes value or slice and later takes a slice or writes to one."""
    for step in (case.get("memoryValuePlan") or {}).get("steps") or []:
        if (step.get("loop") or {}).get("form") != "single":
            continue
        observed = False
        for action in step.get("body") or []:
            kind = action.get("kind")
            if observed and (kind == "slice" or kind == "write" and memory_value(action.get("target"))):
                return True
            observed = observed or kind == "observe" and memory_value(action.get("value"))
    return False


# Recorded semantic defects of questions.md whose occurrences differ only in their
# programs: a mismatch counts under a class, never as new, when its profile, its
# fingerprint's backend, category, stage, disagreeing paths and path shapes, and its
# final case (the reduced one, else the original) have the class's properties, each
# taken from the recorded reductions. Every other mismatch keeps its reduced program.
RETURNED_WORDS = {path: {"payload": "word", "status": "returned"} for path in ("directCore", "importedHull", "rustEvm")}
MISMATCH_CLASSES = (
    ({"backend": "sonatina-o0", "category": "semantic-mismatch", "stage": None, "profile": "runtime-memory-values",
      "class": "loop-observes-then-slices-or-writes"},
     {"disagreeingPairs": ["directCore/rustEvm", "importedHull/rustEvm"], "pathShapes": RETURNED_WORDS, "synthetic": False},
     loop_observes_then_slices_or_writes,
     "Sonatina O0 returns other Words for loops that write std memory values (questions.md, 2026-10-29)"),
)

# Each fixture path's first allocation at the pin (questions.md, 2026-10-31; Sonatina O2's since e2eef194). A
# differing word may carry at most ALLOCATION_MULTIPLE of them, as `result - 2 / before` carries two.
FIRST_ALLOCATION = {"hull": 0x80, "yul": 0x80, "sonatina-o0": 0x200, "sonatina-o2": 0x140}
ALLOCATION_MULTIPLE = 4


def returned_words(output):
    """The 32-byte words of a hex output, else None."""
    if not isinstance(output, str) or not output.startswith("0x") or (len(output) - 2) % 64:
        return None
    with contextlib.suppress(ValueError):
        return [int(output[index:index + 64], 16) for index in range(2, len(output), 64)]
    return None


def offset_by_first_allocations(finding):
    """The paths differ only in their returned words, they disagree exactly where their first allocations differ,
    and each differing word is `k` times the path's first allocation plus one constant on every path, for one
    `k` with 0 < |k| <= ALLOCATION_MULTIPLE."""
    _, fields, groups = finding["signature"]
    observations = finding["observations"]
    if fields != ["output"] or any(path not in FIRST_ALLOCATION for path in observations):
        return False
    by_allocation = {}
    for path in observations:
        by_allocation.setdefault(FIRST_ALLOCATION[path], []).append(path)
    if sorted(map(sorted, groups)) != sorted(map(sorted, by_allocation.values())):
        return False
    words = {path: returned_words(observation.get("output")) for path, observation in observations.items()}
    if any(value is None for value in words.values()) or len({len(value) for value in words.values()}) != 1:
        return False
    differing = [index for index in range(len(next(iter(words.values()))))
                 if len({value[index] for value in words.values()}) > 1]
    return bool(differing) and all(
        any(len({(value[index] - k * FIRST_ALLOCATION[path]) % 2 ** 256 for path, value in words.items()}) == 1
            for k in range(-ALLOCATION_MULTIPLE, ALLOCATION_MULTIPLE + 1) if k)
        for index in differing)


# Recorded differences of the fixtures' paths whose occurrences differ only in their
# source mutants: a source mutant's step finding counts under a class, never as new,
# when its own recorded observations have the class's property. Every other fixture
# finding keeps its key.
FIXTURE_MISMATCH_CLASSES = (
    ({"backend": FIXTURES, "category": "path-mismatch", "stage": "execution", "kind": "source-mutant",
      "class": "offset-by-first-allocations"},
     offset_by_first_allocations,
     "the paths' first allocations differ, Hull and solc at 0x80, Sonatina O2 at 0x140 and O0 at 0x200, in source "
     "mutants that return addresses (questions.md, 2026-10-31)"),
)
# Lean's known differences from upstream, by the labels semantic-native.py gives them (its KNOWN): a native rejection
# or mismatch with one of these labels counts under its label's class, never as new. Every other native finding,
# one with a label not listed here included, keeps its own key.
NATIVE_CLASSES = tuple(({"backend": NATIVE, "category": category, "stage": stage, "class": name}, label)
                       for category, stage, name, label in (
    ("native-rejection", "inference", "open-typedef-call",
     "Lean rejects a `Typedef` call whose type is still open at the call (integer note, differences from upstream), "
     "and so an unannotated `let m = [];` (memory-array note, difference 8)"),
    ("native-rejection", "inference", "open-array-base",
     "Lean rejects a length, a slice, `toArray`, `lidx` or `CanStore` whose base's type is still open there "
     "(memory-array note, differences 14, 18, 19 and 22 to 24)"),
    ("native-rejection", "inference", "generalized-lambda-parameter",
     "Lean generalizes a local lambda, so an operator on a parameter that nothing types is rejected (integer note, "
     "differences from upstream)"),
    ("native-rejection", "inference", "bool-equality", "Lean has no `==` on `bool` (semantic-native.py)"),
    ("native-rejection", "inference", "not-equal",
     "Lean has no `!=` at a type without a builtin one, which upstream takes from std's `ne` (semantic-native.py)"),
    ("native-mismatch", "execution", "uninitialized-local",
     "Lean faults on a read of an uninitialized local, which upstream reads as zero (source semantics, uninitialized "
     "locals)"),
    ("native-mismatch", "execution", "dirty-conversion",
     "Lean's conversion to one of the twelve fixed-width types reverts with `DirtyHigherBitsForInteger()` on a word "
     "that is not canonical for the type, where upstream keeps the raw word (integer note, accepted difference 1)")))
KNOWN = {canonical_id(key): label for key, label in KNOWN_FINDINGS} | \
    {canonical_id(key): label for key, _, _, label in MISMATCH_CLASSES} | \
    {canonical_id(key): label for key, _, label in FIXTURE_MISMATCH_CLASSES} | \
    {canonical_id(key): label for key, label in NATIVE_CLASSES}


def mismatch_class(profile, fingerprint, final):
    """The key of the class a mismatch falls in, else None; `final` is the archive of its final case."""
    for key, paths, shares, _ in MISMATCH_CLASSES:
        if profile != key["profile"] or any(fingerprint.get(name) != key[name] for name in ("backend", "category", "stage")) \
                or any(fingerprint.get(name) != value for name, value in paths.items()):
            continue
        # An unreadable or malformed case stays outside every class.
        with contextlib.suppress(OSError, ValueError, AttributeError, TypeError):
            if final and shares(json.loads((final / "case.json").read_text())):
                return key
    return None


def fixture_mismatch_class(finding):
    """The key of the class a source mutant's step finding falls in by its own observations, else None."""
    for key, shares, _ in FIXTURE_MISMATCH_CLASSES:
        if finding.get("category") != key["category"] or not finding.get("source"):
            continue
        # A finding without well-formed observations stays outside every class.
        with contextlib.suppress(KeyError, ValueError, TypeError, AttributeError):
            if shares(finding):
                return dict(key)
    return None


def native_signature_key(finding):
    """A native finding of the harness's report: its label's class, else a rejection's stage and symptom or a
    mismatch's profile and observation classes, as the harness signs it."""
    category = finding.get("kind")
    for key, _ in NATIVE_CLASSES:
        if finding.get("label") == key["class"] and category == key["category"] and \
                (category != "native-rejection" or finding.get("stage") == key["stage"]):
            return dict(key)
    if category == "native-rejection":
        return {"backend": NATIVE, "category": category, "stage": finding.get("stage"),
                "symptom": {"message": finding.get("symptom")}}
    return {"backend": NATIVE, "category": category, "stage": "execution", "profile": finding.get("profile"),
            "fingerprint": {"core": finding.get("core"), "native": finding.get("native")}}


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


def signature_key(profile, fingerprint, detail, program, site=None, final=None):
    key = {"backend": fingerprint.get("backend"), "category": fingerprint.get("category"), "stage": fingerprint.get("stage")}
    if key["category"] in SYMPTOM_CATEGORIES:
        key["symptom"] = symptom(detail)
        if site:
            key["symptom"]["site"] = site
    elif known := mismatch_class(profile, fingerprint, final):
        return dict(known)
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
    """Yul runs the pure and storage-family profiles and, of the call profiles, only
    the two-source ones, configured or not. The suite's own Yul default is only the
    pure profiles, so the others are selected explicitly. A native run takes the
    pure profiles whose emitter the native admission admits."""
    if backend == NATIVE:
        if config["profile"] is None:
            return None  # The native harness's own random selection, which is the same.
        native = native_harness()
        return [profile for profile in config["profile"]
                if profile in native.PURE_PROFILES and native.profile_emitter(profile) in native.EMITTERS]
    if backend == "yul":
        selected = list(suite.PROFILES) if config["profile"] is None else config["profile"]
        return [profile for profile in selected if suite.PROFILES[profile][1] != "call" or profile in suite.YUL_CALL_PROFILES]
    if config["profile"] is None:
        return None  # The suite's own default selection for this backend.
    return list(config["profile"])


def root_seed(config, iteration):
    return (config["base_seed"] + iteration) % 2**64


def nodes_scale(config, iteration):
    """Every backend of an iteration uses the same scale, so they compare the same programs."""
    cycle = config.get("size_cycle") or [1.0]
    return cycle[iteration % len(cycle)]


def setting(config, key):
    """A configured value; configurations created before a setting existed use its default."""
    value = config.get(key)
    return CONFIG_DEFAULTS[key] if value is None else value


def script_module(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@functools.cache
def harness():
    """The fixture harness, loaded only for its inventory and seeded streams."""
    return script_module("semantic_fuzz_fixtures", "semantic-fixtures.py")


@functools.cache
def native_harness():
    """The native harness, loaded only for its profile selection, its argument checks and its replays."""
    return script_module("semantic_fuzz_native", "semantic-native.py")


def fixture_pool(config):
    """The pinned fixtures of this shard, in id order."""
    return [item["id"] for item in harness().inventory()][config["shard_index"]::config["shard_count"]]


def fixture_selection(config, iteration):
    """Each cycle runs every fixture of the pool once: consecutive slices of a permutation seeded by the base
    seed and the cycle number."""
    pool = fixture_pool(config)
    count = min(setting(config, "fixture_count"), len(pool))
    cycle, slot = divmod(iteration, -(-len(pool) // count))
    stream = harness().Stream(harness().derive(config["base_seed"], "fixture-cycle", cycle))
    for index in range(len(pool) - 1, 0, -1):
        other = stream.below(index + 1)
        pool[index], pool[other] = pool[other], pool[index]
    return sorted(pool[slot * count:(slot + 1) * count])


def fixture_paths(config):
    argv = []
    for key in ("upstream", "target_dir", "solc", "anvil", *FIXTURE_PATH_OPTIONS):
        if config.get(key):
            argv += ["--" + key.replace("_", "-"), config[key]]
    if config.get("bin_dir"):
        argv += ["--hull-runner", str(Path(config["bin_dir"]) / "rust-hull-scenario")]
    return argv


def fixtures_command(config, iteration, output, fixtures=None):
    """A mutation run of the iteration's fixtures, or of `fixtures`, within the configured budgets."""
    argv = [sys.executable, str(ROOT / "scripts/semantic-fixtures.py"), "--mode", "mutation",
            "--seed", str(root_seed(config, iteration)), "--output", str(output), "--reuse-exports",
            "--jobs", str(setting(config, "fixture_jobs")), "--fixture-mutants", str(setting(config, "fixture_mutants")),
            "--sequence-mutants", str(setting(config, "fixture_sequences")),
            "--source-mutants", str(setting(config, "fixture_sources")),
            "--fixture-seconds", str(setting(config, "fixture_seconds")),
            "--seconds", str(setting(config, "fixture_run_seconds"))]
    for fixture in fixture_selection(config, iteration) if fixtures is None else fixtures:
        argv += ["--fixture", fixture]
    return argv + fixture_paths(config)


def native_tool(config):
    """The native tool beside the configured tools, else where `lake build semanticNativeTool` puts it."""
    return Path(config["bin_dir"]) / "semantic-native-tool" if config.get("bin_dir") else \
        ROOT / ".lake/build/bin/semantic-native-tool"


def native_paths(config):
    return ["--bin-dir", config["bin_dir"], "--native-tool", str(native_tool(config))] if config.get("bin_dir") else []


def native_command(config, iteration, output, profiles=None):
    """A native run of the iteration's draws, the root seed, shard, sizes and scale its suite runs take, on the
    admitted pure profiles, or on `profiles`, within the configured budget."""
    argv = [sys.executable, str(ROOT / "scripts/semantic-native.py"), "--mode", "random",
            "--seed", str(root_seed(config, iteration)), "--shard-index", str(config["shard_index"]),
            "--shard-count", str(config["shard_count"]), "--cases", str(config["cases"]),
            "--nodes-scale", str(nodes_scale(config, iteration)), "--seconds", str(setting(config, "native_seconds")),
            "--output", str(output)]
    for key in ("functions", "attempts", "nodes"):
        if config.get(key) is not None:
            argv += ["--" + key, str(config[key])]
    for profile in (profiles_for(config, NATIVE) or []) if profiles is None else profiles:
        argv += ["--profile", profile]
    return argv + native_paths(config)


def run_command(config, iteration, backend, output):
    if backend == FIXTURES:
        return fixtures_command(config, iteration, output)
    if backend == NATIVE:
        return native_command(config, iteration, output)
    return suite_command(config, iteration, backend, output)


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
    for key in PATH_OPTIONS + FIXTURE_PATH_OPTIONS:
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
        if backend == FIXTURES:
            if min(config["fixture_count"], config["fixture_mutants"]) < 1 or \
                    min(config["fixture_seconds"], config["fixture_run_seconds"]) <= 0 or not 1 <= config["fixture_jobs"] <= 16:
                raise NotReady("fixture counts, budgets and jobs must be positive, with at most 16 jobs")
            if not 0 <= config["fixture_sequences"] <= 4096:
                raise NotReady("--fixture-sequences must be between 0 and 4096")
            if not 0 <= config["fixture_sources"] <= 4096:
                raise NotReady("--fixture-sources must be between 0 and 4096")
            if not fixture_pool(config):
                raise NotReady("no pinned fixture falls on this shard")
            continue
        if backend == NATIVE:
            if config["native_seconds"] <= 0:
                raise NotReady("--native-seconds must be positive")
            if config["profile"] is not None and not profiles_for(config, NATIVE):
                raise NotReady("no selected profile is a pure profile whose emitter the native harness admits")
            try:
                with open(os.devnull, "w") as sink, contextlib.redirect_stderr(sink):
                    native_harness().parse_args(native_command(config, 0, state.directory / "unused")[2:])
            except SystemExit:
                raise NotReady("the native harness rejects this configuration: "
                               f"{native_command(config, 0, 'OUTPUT')[2:]}") from None
            continue
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


def ready_check(argv, name):
    """A harness's `--check` report, which must say it is ready."""
    result = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=1800)
    lines = result.stdout.strip().splitlines()
    check = None
    with contextlib.suppress(ValueError):
        check = json.loads(lines[-1]) if result.returncode == 0 and lines else None
    if not isinstance(check, dict) or check.get("status") != "ready":
        raise NotReady(f"the {name} harness is not ready: " + (result.stderr.strip() or result.stdout.strip())[-2000:])
    return check


def fixture_check(config):
    """The fixture harness's readiness: the receipts of the compilers and directive tools, solc, and the identity of
    every script, binary and tool a fixtures run reads, with the parity manifests and the inventory."""
    return ready_check([sys.executable, str(ROOT / "scripts/semantic-fixtures.py"), "--check", *fixture_paths(config)],
                       "fixture")


def native_check(config):
    """The native harness's readiness: its admission, adapter and comparison versions, its admitted emitters, and the
    identity of the native tool, which no receipt covers, of the case tool and of the scripts a native run reads."""
    return ready_check([sys.executable, str(ROOT / "scripts/semantic-native.py"), "--check", "--mode", "random",
                        *native_paths(config)], "native")


def current_epoch(config):
    receipt = verify_tools(config)
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip() or None
    epoch = {"receiptSha256": suite.digest(receipt), "harnessSha256": harness_digest(), "gitHead": head}
    identity = {"receipt": epoch["receiptSha256"], "harness": epoch["harnessSha256"]}
    if FIXTURES in config["backend"]:
        # A state without fixtures keeps its epoch formula.
        check = fixture_check(config)
        epoch["fixturesSha256"] = hashlib.sha256(json.dumps({key: check.get(key) for key in (
            "tools", "builds", "manifests", "fixtures")}, sort_keys=True).encode()).hexdigest()
        identity["fixtures"] = epoch["fixturesSha256"]
    if NATIVE in config["backend"]:
        # Likewise a state without native runs keeps its epoch formula.
        check = native_check(config)
        epoch["nativeSha256"] = hashlib.sha256(json.dumps({key: check.get(key) for key in (
            "versions", "admittedEmitters", "tools", "scripts")}, sort_keys=True).encode()).hexdigest()
        identity["native"] = epoch["nativeSha256"]
    epoch["id"] = canonical_id(identity)
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


def signalled(backend, summary, exit_code):
    """Whether a run stopped on a signal: the suite and the fixture harness record it, the native harness exits 130."""
    if backend == NATIVE:
        return exit_code == 130
    return isinstance(summary, dict) and summary.get("stop") == ("signal" if backend == FIXTURES else "interrupted")


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
                final = folder / (finding.get("finalArchive") or finding.get("originalArchive") or "missing")
                ident = f"case-{finding.get('caseIndex')}"
            else:
                archive = folder / finding["archive"] if finding.get("archive") else None
                analysis = archive / "analysis.json" if archive else folder / "missing"
                final = archive
                ident = "secondary-" + finding.get("archive", "unknown").replace("/", "-")
            detail = ""
            with contextlib.suppress(OSError, ValueError, AttributeError):
                detail = json.loads(analysis.read_text()).get("comparison", {}).get("detail", "")
            program = next((finding[name] for name in PROGRAM_KEYS if finding.get(name)), None)
            records.append({"kind": kind, "ident": ident, "finding": finding, "archive": archive, "detail": detail,
                            "program": program, "final": final})
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


def note_occurrence(state, config, registry, sid, key, brief, destination, keep, first_time, cases=1):
    """Count one occurrence of a signature, of `cases` cases. While it has fewer than --examples kept,
    `keep(destination)` keeps the occurrence's archive there and says whether it did. A known finding is counted but
    never new."""
    entry = registry["signatures"].get(sid)
    new = entry is None and sid not in KNOWN
    if entry is None:
        entry = registry["signatures"][sid] = {
            "id": sid, "key": key, "kind": "inconclusive" if key["category"] in INCONCLUSIVE else "failure",
            "category": key["category"], "stage": key["stage"], "symptom": key.get("symptom"), "count": 0,
            "backends": {}, "profiles": {}, "firstSeen": brief, "lastSeen": brief, "examples": [], "recent": []}
    retained = None
    if destination.exists() or len(entry["examples"]) < config["examples"] and keep(destination):
        retained = str(destination.relative_to(state.directory))
    if first_time:
        entry["count"] += cases
        entry["backends"][brief["backend"]] = entry["backends"].get(brief["backend"], 0) + cases
        entry["profiles"][brief["profile"]] = entry["profiles"].get(brief["profile"], 0) + cases
        entry["lastSeen"] = brief
        entry["recent"] = (entry["recent"] + [brief])[-RECENT:]
        if retained and retained not in entry["examples"]:
            entry["examples"].append(retained)
    return {"signature": sid, "new": new and first_time, "profile": brief["profile"], "kind": brief["kind"],
            "case": brief["case"], "retained": retained}


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
                                sites.get((row["profile"], record["ident"])), record["final"])
            sid = canonical_id(key)
            brief = {"iteration": iteration, "backend": backend, "rootSeed": str(root_seed(config, iteration)),
                     "profile": row["profile"], "profileSeed": row.get("seed"), "kind": record["kind"],
                     "case": record["ident"], "epoch": epoch["id"], "program": record["program"]}

            def keep(destination, record=record, row=row, brief=brief, sid=sid):
                if not (record["archive"] and record["archive"].is_dir()):
                    return False
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.move(str(record["archive"]), str(destination))
                save(destination / "occurrence.json", {**brief, "signature": sid, "finding": record["finding"],
                                                       "suiteCommand": row.get("command")})
                return True
            destination = state.directory / "findings" / sid / f"{iteration:06d}-{backend}-{row['profile']}-{record['ident']}"
            occurrences.append(note_occurrence(state, config, registry, sid, key, brief, destination, keep, first_time))
    if first_time:
        registry["processedRuns"].append(run_id)
    save(state.registry_path, registry)
    return occurrences


def fixture_signature_key(finding):
    """A crash or path failure is its symptom on its path; a mismatch is its fixture and reduced input."""
    key = {"backend": FIXTURES, "category": finding["category"]}
    # A source mutant's refusal on some paths is, like a crash, its symptom at its stage.
    if finding["category"] in ("compiler-crash", "compile-mismatch"):
        return {**key, "stage": finding.get("stage"), "paths": finding.get("paths"), "symptom": symptom(finding.get("detail") or "")}
    if finding["category"] == "path-failure":
        status, detail = finding["signature"][2], finding.get("detail") or ""
        # A language failure's Core value is exact; normalizing would merge its distinct reasons.
        return {**key, "stage": "execution", "path": finding.get("path"), "status": status,
                "symptom": {"value": detail} if status == "language-failure" else symptom(detail)}
    reduction = finding.get("reduction") or {}
    names = ("operator", "sequence") if finding.get("sequence") else ("edit", "steps") if finding.get("source") else \
        ("steps", "calldata", "value")
    if reduction.get("status") in ("reduced", "budget-exhausted"):
        reduced = {name: reduction.get(name) for name in names}
    elif finding.get("source"):
        # An unreduced source finding is its edit at its step.
        reduced = {"edit": finding.get("edit"), "step": finding.get("step")}
    elif finding.get("sequence"):
        # An unreduced sequence finding is its operator at its step, with the mutant it commits.
        reduced = {"operator": finding.get("operator"), "step": finding.get("step"), "change": finding.get("change"),
                   "mutant": finding.get("mutant")}
    else:
        reduced = {"step": finding.get("step"), "mutant": finding.get("mutant")}
    return {**key, "stage": "execution", "profile": finding["fixture"], "fingerprint": finding.get("signature"),
            "program": canonical_id({"fixture": finding["fixture"], **reduced})}


def register_fixture_findings(state, config, epoch, iteration, run_dir, outcome):
    """Count each fixture finding once; a duplicate within a fixture shares the signature of the finding it repeats."""
    registry = state.registry()
    run_id = f"{iteration:06d}-{FIXTURES}"
    first_time = run_id not in registry["processedRuns"]
    findings = outcome.get("findings") or []
    entries = {(finding["fixture"], finding.get("entry")): finding for finding in findings}
    occurrences = []
    for finding in findings:
        reduction = finding.get("reduction") or {}
        base = entries.get((finding["fixture"], reduction.get("of")), finding) if reduction.get("status") == "duplicate" else finding
        # A class holds a finding by its own observations, a duplicate's included; a duplicate outside the
        # class of the finding it repeats is its own edit at its step.
        known = fixture_mismatch_class(finding)
        own = fixture_signature_key(finding if not known and base is not finding and fixture_mismatch_class(base) else base)
        key = known or own
        sid = canonical_id(key)
        case = finding.get("entry") or finding.get("stage") or "fixture"
        brief = {"iteration": iteration, "backend": FIXTURES, "rootSeed": str(root_seed(config, iteration)),
                 "profile": finding["fixture"], "profileSeed": None, "kind": "primary", "case": case, "epoch": epoch["id"],
                 "program": own.get("program")}

        def keep(destination, finding=finding, brief=brief, sid=sid):
            destination.mkdir(parents=True)
            record = run_dir / "fixtures" / (finding["fixture"] + ".json")
            if record.is_file():
                shutil.copy2(record, destination / "fixture.json")
            save(destination / "occurrence.json", {**brief, "signature": sid, "finding": finding,
                                                   "replay": fixtures_command(config, iteration, "OUTPUT", [finding["fixture"]])})
            return True
        destination = state.directory / "findings" / sid / f"{iteration:06d}-{FIXTURES}-{finding['fixture']}-{case}"
        occurrences.append(note_occurrence(state, config, registry, sid, key, brief, destination, keep, first_time))
    if first_time:
        registry["processedRuns"].append(run_id)
    save(state.registry_path, registry)
    return occurrences


def register_native_findings(state, config, epoch, iteration, run_dir, outcome):
    """Count each native finding's cases once per profile. The harness lists a finding's profiles in the order of
    their first cases and archives its first case, so the first profile's occurrence keeps that archive."""
    registry = state.registry()
    run_id = f"{iteration:06d}-{NATIVE}"
    first_time = run_id not in registry["processedRuns"]
    occurrences = []
    for finding in outcome.get("findings") or []:
        key = native_signature_key(finding)
        sid = canonical_id(key)
        archive = run_dir / "findings" / str(finding.get("signature"))[:16]
        for profile, cases in (finding.get("profiles") or {}).items():
            example = next((item for item in finding.get("examples") or [] if item.get("profile") == profile), {})
            brief = {"iteration": iteration, "backend": NATIVE, "rootSeed": str(root_seed(config, iteration)),
                     "profile": profile, "profileSeed": None, "kind": "primary",
                     "case": f"case-{example['case']}" if "case" in example else f"{cases} cases",
                     "epoch": epoch["id"], "program": example.get("programSha256")}

            def keep(destination, finding=finding, brief=brief, sid=sid, archive=archive, profile=profile):
                if not archive.is_dir():
                    return False
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.move(str(archive), str(destination))
                place = str(destination.relative_to(state.directory))
                # The harness's own replay path pointed into the run directory.
                recorded = {name: value for name, value in finding.items() if name != "replay"}
                save(destination / "occurrence.json", {
                    **brief, "signature": sid, "finding": recorded,
                    "replay": [sys.executable, str(ROOT / "scripts/semantic-fuzz.py"), "replay", "--state",
                               str(state.directory), place],
                    "rerun": native_command(config, iteration, "OUTPUT", [profile])})
                return True
            destination = state.directory / "findings" / sid / f"{iteration:06d}-{NATIVE}-{profile}-{archive.name}"
            occurrence = note_occurrence(state, config, registry, sid, key, brief, destination, keep, first_time, cases)
            occurrences.append({**occurrence, "cases": cases})
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


def remove_run(run_dir):
    """A run's directory and logs, and its iteration's directory once that is empty."""
    for path in [run_dir, *(run_dir.with_name(run_dir.name + suffix) for suffix in (".stdout.log", ".stderr.log"))]:
        remove(path)
    with contextlib.suppress(OSError):
        run_dir.parent.rmdir()


def prune(run_dir, summary, keep):
    """Reduce a recorded run to compact records; random cases replay from their recorded seeds."""
    if keep or not run_dir.exists():
        return
    if summary.get("status") == "passed":
        remove_run(run_dir)
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
    if run_dir.exists() and (any(run_dir.glob("*/findings/*/*")) or any(run_dir.glob("findings/*/*")) or
                             any((load(path) or {}).get("findings") for path in run_dir.glob("fixtures/*.json"))):
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
        if not run_dir.is_dir() or run_dir.name not in RUN_KINDS or not run_dir.parent.name.isdigit():
            continue
        if (int(run_dir.parent.name), run_dir.name) in done:
            continue
        if run_dir.name in (FIXTURES, NATIVE):
            # The harnesses write their reports only when the run ends. The native one says only that it stopped, on
            # a signal or at its time budget, so such a run reruns as an interrupted one does.
            outcome = load(run_dir / "report.json")
            finished = isinstance(outcome, dict) and (outcome.get("stop") != "signal" if run_dir.name == FIXTURES
                                                      else not outcome.get("stopped"))
            if finished:
                found.append((int(run_dir.parent.name), run_dir.name, run_dir, outcome))
            else:
                retain_interrupted(state, run_dir)
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


def fixture_status(outcome):
    if not isinstance(outcome, dict):
        return "missing-summary"
    if outcome.get("errors") or not outcome.get("toolsUnchanged"):
        return "error"
    return "failed" if outcome.get("findings") else "passed"


def fixture_counts(outcome):
    """A fixtures run's entries in the suite's terms, and its own counts."""
    totals = (outcome or {}).get("totals") or {}
    # A sequence mutant's steps from its change on, and a source mutant's steps, are compared entries too.
    sequence, source = totals.get("sequence") or {}, totals.get("source") or {}

    def both(key):
        return totals.get(key, 0) + sequence.get(key, 0) + source.get(key, 0)
    return {"executed": sum(both(key) for key in ("agree", "disagree", "incomplete", "unobserved")),
            "matched": both("agree"), "mismatched": both("disagree"),
            "errors": len((outcome or {}).get("errors") or []),
            "inconclusive": both("incomplete") + both("unobserved"), "sequences": sequence.get("mutants", 0),
            "sources": source.get("mutants", 0),
            **{key: totals.get(key, 0) for key in ("fixtures", "recorded", "mutants", "budgetStopped", "unexecuted")},
            "findings": len((outcome or {}).get("findings") or []), "exclusions": sum((totals.get("exclusions") or {}).values())}


def fixture_problems(outcome):
    """A missing report, harness errors and changed tools; budget stops are counted, not problems."""
    if not isinstance(outcome, dict):
        return [{"profile": None, "status": "missing-summary", "stop": None}]
    problems = [{"profile": error["fixture"], "status": "harness-error", "stop": outcome.get("stop"),
                 "detail": str(error["detail"])[-500:]} for error in outcome.get("errors") or []]
    if not outcome.get("toolsUnchanged"):
        problems.append({"profile": None, "status": "tools-changed", "stop": outcome.get("stop")})
    return problems


def prune_fixture_run(run_dir, outcome, status, keep):
    """A passed run leaves its ledger row, since its mutants replay from the root seed. Otherwise the report and
    the records of fixtures with findings or errors stay, or everything when the report is missing."""
    if keep or not run_dir.exists() or not isinstance(outcome, dict):
        return
    if status == "passed":
        remove_run(run_dir)
        return
    kept = {finding["fixture"] for finding in outcome.get("findings") or []} | \
        {error["fixture"] for error in outcome.get("errors") or []}
    for path in list((run_dir / "fixtures").glob("*.json")):
        if path.stem not in kept:
            remove(path)


def record_fixture_run(state, config, epoch, iteration, run_dir, outcome, exit_code, started, elapsed, keep):
    status = fixture_status(outcome)
    occurrences = register_fixture_findings(state, config, epoch, iteration, run_dir, outcome) if isinstance(outcome, dict) else []
    row = {"schema": SCHEMA + "/run", "iteration": iteration, "backend": FIXTURES,
           "rootSeed": str(root_seed(config, iteration)), "fixtures": fixture_selection(config, iteration),
           "shardIndex": config["shard_index"], "shardCount": config["shard_count"], "epoch": epoch["id"],
           "started": started, "finished": now(), "elapsedSeconds": elapsed, "exitCode": exit_code,
           "suiteStatus": status, "stop": (outcome or {}).get("stop"), "counts": fixture_counts(outcome),
           "occurrences": occurrences, "problems": fixture_problems(outcome),
           "retainedRun": None if status == "passed" and not keep or not run_dir.exists()
           else str(run_dir.relative_to(state.directory))}
    state.append_ledger(row)
    prune_fixture_run(run_dir, outcome, status, keep)
    return row


def native_status(outcome):
    if not isinstance(outcome, dict):
        return "missing-summary"
    if outcome.get("errors") or not outcome.get("toolsUnchanged"):
        return "error"
    return "passed" if outcome.get("status") == "passed" else "failed"


def native_counts(outcome):
    """A native run's admitted cases in the suite's terms, a native rejection as an error, and the harness's counts."""
    totals = (outcome or {}).get("totals") or {}
    counts, findings = totals.get("counts") or {}, totals.get("findings") or {}
    own = {key: counts.get(key, 0) for key in NATIVE_COUNTS}
    return {"executed": own["agree"] + own["mismatch"] + own["rejected"] + own["inconclusive"], "matched": own["agree"],
            "mismatched": own["mismatch"], "errors": own["rejected"], **own,
            "findings": findings.get("signatures", 0), "newFindings": findings.get("new", 0)}


def native_problems(outcome):
    """What kept a native run from passing besides its new findings: a missing report, harness errors, changed tools,
    and the profiles with inconclusive or unexecuted cases."""
    if not isinstance(outcome, dict):
        return [{"profile": None, "status": "missing-summary", "stop": None}]
    stop = "time budget" if outcome.get("stopped") else None
    problems = [{"profile": error.get("profile"), "status": "harness-error", "stop": stop,
                 "detail": str(error.get("detail"))[-500:]} for error in outcome.get("errors") or []]
    if not outcome.get("toolsUnchanged"):
        problems.append({"profile": None, "status": "tools-changed", "stop": stop})
    for profile, totals in (outcome.get("profiles") or {}).items():
        counts = totals.get("counts") or {}
        problems += [{"profile": profile, "status": status, "stop": stop, "counts": counts,
                      "reasons": totals.get("inconclusive") or {}}
                     for status in ("inconclusive", "unexecuted") if counts.get(status)]
    if outcome.get("status") != "passed" and not problems and \
            not ((outcome.get("totals") or {}).get("findings") or {}).get("new"):
        problems.append({"profile": None, "status": outcome.get("status"), "stop": stop})
    return problems


def prune_native_run(run_dir, outcome, status, keep):
    """A passed run leaves its ledger row, since its cases replay from the root seed. Otherwise only the report stays,
    or everything when the report is missing; the kept examples have already moved to their signatures."""
    if keep or not run_dir.exists() or not isinstance(outcome, dict):
        return
    if status == "passed":
        remove_run(run_dir)
        return
    for path in list(run_dir.iterdir()):
        if path.name != "report.json":
            remove(path)


def record_native_run(state, config, epoch, iteration, run_dir, outcome, exit_code, started, elapsed, keep):
    status = native_status(outcome)
    occurrences = register_native_findings(state, config, epoch, iteration, run_dir, outcome) \
        if isinstance(outcome, dict) else []
    totals = (outcome or {}).get("totals") or {}
    row = {"schema": SCHEMA + "/run", "iteration": iteration, "backend": NATIVE,
           "rootSeed": str(root_seed(config, iteration)), "nodesScale": nodes_scale(config, iteration),
           "shardIndex": config["shard_index"], "shardCount": config["shard_count"], "epoch": epoch["id"],
           "started": started, "finished": now(), "elapsedSeconds": elapsed, "exitCode": exit_code,
           "suiteStatus": status, "stop": "time budget" if (outcome or {}).get("stopped") else None,
           "counts": native_counts(outcome), "notAdmitted": totals.get("reasons") or {},
           "known": totals.get("known") or {}, "inconclusiveReasons": totals.get("inconclusive") or {},
           "profiles": [{"profile": profile, "counts": item.get("counts"), "seconds": item.get("seconds")}
                        for profile, item in ((outcome or {}).get("profiles") or {}).items()],
           "occurrences": occurrences, "problems": native_problems(outcome),
           "retainedRun": None if status == "passed" and not keep or not run_dir.exists()
           else str(run_dir.relative_to(state.directory))}
    state.append_ledger(row)
    prune_native_run(run_dir, outcome, status, keep)
    return row


def record_finished_run(state, config, epoch, iteration, backend, run_dir, summary, exit_code, started, elapsed, keep,
                        sites=None):
    """Record a finished run of any kind from its suite summary or harness report, None when it wrote none."""
    if backend == FIXTURES:
        return record_fixture_run(state, config, epoch, iteration, run_dir, summary, exit_code, started, elapsed, keep)
    if backend == NATIVE:
        return record_native_run(state, config, epoch, iteration, run_dir, summary, exit_code, started, elapsed, keep)
    return record_run(state, config, epoch, iteration, backend, run_dir,
                      summary or {"status": "missing-summary", "profiles": []}, exit_code, started, elapsed, keep, sites)


def report(state):
    """Write report.json and report.md from the configuration, ledger, registry and labels."""
    if not state.config_path.exists():
        raise NotReady(f"no fuzzing state in {state.directory}")
    config = load(state.config_path)
    ledger = state.ledger()
    registry = state.registry()
    labels = load(state.labels_path, {})
    runs = {}
    # A native run's reasons not to admit a case, its known differences and its reasons for inconclusive cases.
    native = {"notAdmitted": {}, "known": {}, "inconclusive": {}}
    for row in ledger:
        if row["backend"] == NATIVE:
            for section, field in (("notAdmitted", "notAdmitted"), ("known", "known"),
                                   ("inconclusive", "inconclusiveReasons")):
                for key, value in (row.get(field) or {}).items():
                    native[section][key] = native[section].get(key, 0) + value
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
        text = labels.get(sid, {}).get("label") or KNOWN.get(sid)
        signatures.append({**{key: entry.get(key) for key in ("id", "kind", "category", "stage", "symptom", "count",
                                                                "backends", "profiles", "firstSeen", "lastSeen", "examples")},
                           "class": (entry.get("key") or {}).get("class"), "label": text,
                           "triage": "known" if text else "untriaged", "newInLatestIteration": sid in newest})
    signatures.sort(key=lambda entry: (entry["triage"] == "known", entry["kind"] != "failure",
                                       -entry["lastSeen"]["iteration"], entry["id"]))
    problems = [{"iteration": row["iteration"], "backend": row["backend"], **problem}
                for row in ledger for problem in row.get("problems", [])]
    interrupted = state.directory / "interrupted"
    data = {"schema": SCHEMA + "/report", "generated": now(), "state": str(state.directory), "config": config,
            "epochs": load(state.state_path, {"epochs": []})["epochs"], "runs": runs, "latestIteration": latest,
            "native": native if NATIVE in runs else None,
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
    suites = ("" if config["backend"] == [FIXTURES] else
              f", {counts}, node-budget scales {', '.join(str(scale) for scale in config.get('size_cycle') or [1.0])} "
              f"by iteration, profiles: {'suite default' if config['profile'] is None else ', '.join(config['profile'])}")
    lines = ["# Semantic fuzzing report", "", f"Generated {data['generated']} from `{data['state']}`.", "",
             f"Base seed {config['base_seed']}, shard {config['shard_index']} of {config['shard_count']}, "
             f"backends {', '.join(config['backend'])}{suites}.", ""]
    if FIXTURES in config["backend"]:
        lines += [f"Fixtures: {setting(config, 'fixture_count')} pinned end-to-end fixtures per iteration, at most "
                  f"{setting(config, 'fixture_mutants')} mutants, {setting(config, 'fixture_sequences')} sequence mutants, "
                  f"{setting(config, 'fixture_sources')} source mutants and "
                  f"{setting(config, 'fixture_seconds'):g} seconds per fixture, "
                  f"{setting(config, 'fixture_run_seconds'):g} seconds per run, {setting(config, 'fixture_jobs')} at a time; "
                  "compiled paths compared with each other and with upstream's recorded expectations, not with original Core.", ""]
    if NATIVE in config["backend"]:
        lines += ["Native: Lean's native frontend on each iteration's draws of the pure profiles whose emitter the "
                  f"native admission admits, within {setting(config, 'native_seconds'):g} seconds per run; each "
                  "admitted case compared with its direct Core result, not with a compiled path.", ""]
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
    if data.get("native"):
        counts, native = data["runs"][NATIVE]["counts"], data["native"]
        lines += ["", "## Native runs", "",
                  "Rejected cases are the Errors above; a known difference is a rejection or mismatch under its "
                  "label.", "",
                  "| Cases | Generation exclusions | Not admitted | Admitted | Programs | Agree | Mismatch | Rejected | "
                  "Inconclusive | Unexecuted |", "|" + " ---: |" * len(NATIVE_COUNTS),
                  "| " + " | ".join(str(counts.get(name, 0)) for name in NATIVE_COUNTS) + " |", ""]
        sections = (("Not admitted, by reason", "notAdmitted"), ("Known differences, by label", "known"),
                    ("Inconclusive, by reason", "inconclusive"))
        lines += [f"- {title}: " + (", ".join(f"{name} {count}" for name, count in sorted(native[section].items()))
                                    or "none") + "." for title, section in sections]
    lines += ["", "## Findings by signature", "",
              "Untriaged signatures come first. A label marks a signature as known; it stays counted.", "",
              "| Signature | Triage | Category | Stage | Symptom or program | Count | Backends | Profiles | First seen | Last seen | Kept |",
              "| --- | --- | --- | --- | --- | ---: | --- | --- | --- | --- | ---: |"]
    for entry in data["signatures"]:
        described = " ".join(str(value) for value in (entry["symptom"] or {}).values()) or \
            (f"class {entry['class']}" if entry.get("class") else str(entry["firstSeen"].get("program")))
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
        suite_run = backend in BACKENDS
        exit_code, interrupted = run_suite(run_command(config, iteration, backend, run_dir),
                                           run_dir.with_name(backend + ".stdout.log"),
                                           run_dir.with_name(backend + ".stderr.log"), self.stop)
        summary = load(run_dir / ("summary.json" if suite_run else "report.json"))
        if interrupted or signalled(backend, summary, exit_code):
            with self.lock:
                kept = retain_interrupted(state, run_dir)
                self.end(f"interrupted in iteration {iteration} ({backend}); it reruns on resume", kept=kept)
            return
        summary = summary if isinstance(summary, dict) else None
        sites = crash_sites(config, run_dir, summary) if summary and suite_run else {}  # Replays run outside the lock.
        with self.lock:
            self.missing = self.missing + 1 if summary is None else 0
            row = record_finished_run(state, config, epoch, iteration, backend, run_dir, summary, exit_code, started,
                                      round(time.monotonic() - began, 3), args.keep_runs, sites)
            report(state)
            if self.missing >= MISSING_SUMMARY_LIMIT:
                self.end(f"{self.missing} consecutive runs produced no suite summary; see their logs", 5)
        new = [occurrence["signature"] for occurrence in row["occurrences"] if occurrence["new"]]
        print(json.dumps({"iteration": iteration, "backend": backend, "rootSeed": row["rootSeed"], "status": row["suiteStatus"],
                          "occurrences": len(row["occurrences"]), "new": new, "problems": len(row["problems"])}), flush=True)
        if new or any(problem.get("status") in ("adapter-error", "missing-summary", "harness-error", "tools-changed")
                      for problem in row["problems"]):
            notify(args.notify_command, state, row, new)


def run(args):
    state = State(args.state)
    with state.lock():
        config = configure(state, args)
        stop = StopFlag()
        previous = {signum: signal.signal(signum, stop) for signum in (signal.SIGTERM, signal.SIGINT)}
        try:
            for iteration, backend, run_dir, summary in unrecorded_runs(state, state.ledger()):
                sites = crash_sites(config, run_dir, summary) if backend in BACKENDS else None
                record_finished_run(state, config, current_epoch(config), iteration, backend, run_dir, summary, None,
                                    None, None, args.keep_runs, sites)
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


def replay(args):
    """Rerun a kept native example: the native tool on its archived program with its archived case's arguments, and
    the harness's own verdict on the case against its direct Core result. It reproduces when the harness finds the
    finding's signature again."""
    state = State(args.state)
    config = load(state.config_path)
    if config is None:
        raise NotReady(f"no fuzzing state in {state.directory}")
    example = args.example if args.example.is_absolute() else state.directory / args.example
    occurrence, request, case = (load(example / name) for name in ("occurrence.json", "request.json", "case.json"))
    if not all(isinstance(value, dict) for value in (occurrence, request, case)) or occurrence.get("backend") != NATIVE:
        raise NotReady(f"{example} is no kept native example")
    tool = native_tool(config)
    if not tool.is_file():
        raise NotReady(f"the native tool is missing: {tool}")
    native = native_harness()
    first = ((occurrence.get("finding") or {}).get("examples") or [{}])[0]  # The archived case's own record.
    group = {"programSha256": first.get("programSha256"), "source": request["sources"][0]["content"],
             "function": request["function"], "cases": [(first.get("case"), case, first.get("arguments"))]}
    with tempfile.TemporaryDirectory(prefix="semantic-fuzz-native-replay-") as scratch:
        options = argparse.Namespace(native_tool=tool, program_seconds=NATIVE_PROGRAM_SECONDS,
                                     seconds=NATIVE_PROGRAM_SECONDS, output=Path(scratch))
        run = native.NativeRun(options, None)
        totals = {"counts": dict.fromkeys(NATIVE_COUNTS, 0), "reasons": {}, "inconclusive": {}, "known": {}}
        try:
            run.run_program(occurrence.get("profile"), group, totals, Path(scratch))
        except ValueError as error:
            raise NotReady(f"the native tool's result is unexpected: {error}") from None
    replayed = sorted(canonical_id(native_signature_key(finding)) for finding in run.findings.values())
    outcome = {"example": str(example), "tool": str(tool), "signature": occurrence.get("signature"),
               "verdicts": run.programs[0]["verdicts"], "replayed": replayed,
               "reproduced": occurrence.get("signature") in replayed}
    print(json.dumps(outcome, sort_keys=True), flush=True)
    return 0 if outcome["reproduced"] else 1


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    runner = commands.add_parser("run", help="run iterations until stopped")
    shown = commands.add_parser("report", help="regenerate report.md and report.json and print the Markdown")
    labeller = commands.add_parser("label", help="record or clear the triage label of a signature")
    replayer = commands.add_parser("replay", help="rerun a kept native example through the native harness's comparison")
    for command in (runner, shown, labeller, replayer):
        command.add_argument("--state", type=Path, default=ROOT / ".upstream/semantic-fuzz", help="state directory")
    runner.add_argument("--base-seed", type=int, help="root seed of iteration zero (default: the creation time)")
    runner.add_argument("--shard-index", type=int)
    runner.add_argument("--shard-count", type=int)
    runner.add_argument("--backend", action="append", choices=RUN_KINDS,
                        help="repeat; default the three suite backends; fixtures adds a mutation run of the pinned "
                             "end-to-end fixtures on Hull, O0, O2 and Yul; native adds a run of Lean's native frontend "
                             "on the iteration's admitted pure cases, compared with direct Core")
    runner.add_argument("--profile", action="append", choices=tuple(suite.PROFILES), help="repeat; default the suite's selection, and on Yul also the storage-family, call-return, "
                             "call-sequence and call-branch profiles; the other call profiles never run on Yul")
    runner.add_argument("--size-cycle", type=lambda text: [float(part) for part in text.split(",")],
                        help="comma-separated node-budget scales used by successive iterations (default 1,2)")
    for name, kind in (("cases", int), ("functions", int), ("attempts", int), ("nodes", int), ("seconds", float),
                       ("profile-seconds", float), ("disk-bytes", int), ("examples", int)):
        runner.add_argument("--" + name, type=kind)
    for name, kind, text in (("fixture-count", int, "fixtures per iteration (default 8)"),
                             ("fixture-mutants", int, "mutants per fixture at most (default 32)"),
                             ("fixture-sequences", int, "sequence mutants per fixture at most (default 8; 0 runs none)"),
                             ("fixture-sources", int, "source mutants per fixture at most (default 2; 0 runs none)"),
                             ("fixture-seconds", float, "wall time per fixture (default 300)"),
                             ("fixture-run-seconds", float, "wall time per fixtures run (default 1800)"),
                             ("fixture-jobs", int, "fixtures run at a time (default 2)"),
                             ("native-seconds", float, "wall time per native run (default 1800)")):
        runner.add_argument("--" + name, type=kind, help=text)
    for name in ("bin-dir", "upstream", "target-dir", "anvil", "solc", "cast"):
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
    replayer.add_argument("example", type=Path, help="a kept native example, as the registry lists it")
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
        if args.command == "replay":
            return replay(args)
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
