#!/usr/bin/env python3
"""Compare Lean's native frontend with original Core on the pure cases it is admitted to read.

The native path reads the source a case's emitter wrote, lifted out of its contract by a versioned
adapter, through `semantic-native-tool`: loading, checking and compiling a Word entry of the
contract's method once, then one run per input. Each input's observation is compared with the
case's own direct Core result: a returned Word with the Word, and a native panic, which the native
session decodes to upstream's revert data, with the revert's output.

Admission is a versioned predicate decided before the native tool runs. It reads the case's
provenance (its emitter and the Core operations of its program), the adapter's reading of the source
(one contract with functions only, no storage field, `uint256` parameters) and, for memory arrays,
the source's array forms (std's array traits are not admitted). The adapter keeps the source's
imports of `std.opcodes`, whose pure functions the native frontend provides, and adds std's own
`tobool` where the source calls it and defines none. Cases that are not admitted are counted by
reason. A native rejection, crash or different observation of an admitted case is a finding, never
an exclusion; the known differences from upstream are findings under their own labels. Out of fuel
and timeouts are inconclusive.

Cases come from the pure runner's own preparation (`semantic-campaign.py`, with the arguments
`semantic-suite.py` gives each profile), for the fixed corpora or a seeded random draw; preparation
compiles and executes nothing. The native tool is not in the shared tools receipt: `--check` prints
the identity of every tool, script and corpus a run reads, and a run whose identity changes while it
runs does not pass.
"""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


suite = load("semantic_native_suite", "semantic-suite.py")
runner = suite.pure_campaign
SCHEMA = "solcore-lean.semantic-native.v1"
REQUEST_SCHEMA = "solcore-lean.semantic-native-request.v1"
RESULT_SCHEMA = "solcore-lean.semantic-native-result.v1"
ADMISSION = "native-admission-v6"
ADAPTER = "native-lift-v3"
COMPARISON = "native-compare-v1"
TOOL = ROOT / ".lake/build/bin/semantic-native-tool"
SCRIPTS = ("semantic-native.py", "semantic-suite.py", "semantic-campaign.py", "semantic-differential.py",
           "semantic-source-bundle.py")
PURE_PROFILES = tuple(profile for profile, (_, family, _) in suite.PROFILES.items() if family == "pure")
FUEL = {"checkingFuel": 4096, "compilationFuel": 4096, "specializationBudget": 1024, "executionFuel": 10_000_000}
WRAPPER = "sc_native_"
PROFILE_SECONDS = 900.0
PROFILE_DISK_BYTES = 256 * 1024**2

# Core sums, which the G0-derived emitters write as upstream's builtin `sum<a, b>` with unqualified `inl` and `inr`:
# the native frontend has neither. Their std.opcodes aliases (`sc_div`, ...) and the plans' `signextend` for signed
# narrow types come from the import the adapter keeps.
SUMS = frozenset(("inLeft", "inRight", "case"))
# Each admitted emitter, with the Core operations that exclude a case.
EMITTERS = {
    **{version: SUMS for version in (
        "solcore-source-g0-v2", "solcore-source-input-v2", "solcore-source-functions-v2",
        "solcore-source-mutation-v2", "solcore-source-aggregates-v3", "solcore-source-aggregate-call-graphs-v2",
        "solcore-source-call-graphs-v2", "solcore-source-call-graph-loops-v2", "solcore-source-closures-v3",
        "solcore-source-generics-v3", "solcore-source-loops-v3", "solcore-source-nested-loops-v2",
        "solcore-source-recursion-v2", "solcore-source-recursive-loops-v2", "solcore-source-loop-closures-v2",
        "solcore-source-primitives-v2")},
    "solcore-source-shifts-v2": frozenset(),
    "solcore-source-checked-arithmetic-v2": frozenset(),
    "solcore-source-enums-v2": frozenset(),
    "solcore-source-closure-captures-v2": frozenset(),
    "solcore-source-closure-factories-v2": frozenset(),
    "solcore-source-memory-arrays-v2": frozenset(),
}
# A call of std's `tobool(x: word) returns (bool)`, which the G0-derived emitters wrap around `sgt`'s word: std is not
# a module of the native load, so where a source calls it and does not define it, the adapter adds std's own
# definition, as `std/std.sol` has it at the pin (`d1b5ac28`).
TOBOOL_CALL = re.compile(r"\btobool\s*\(")
TOBOOL_DEFINITION = re.compile(r"\bfunction\s+tobool\b")
STD_TOBOOL = ("function tobool(x: word) returns (bool) {\n    match (x) {\n        case 0 {\n"
              "            return false;\n        }\n        default {\n            return true;\n"
              "        }\n    }\n}\n")
# The array form of the array emitters' sources that this version does not admit: std's array traits, which row 4's
# Lean side leaves out (its lengths are compiler forms, and it declares no std trait). A `lidx` call whose index is an
# integer literal is admitted since v5: Lean gives the index `uint256` at finalization, as upstream does.
STD_ARRAY_TRAITS = re.compile(r"\b(?:RValueIdxAccess|LValueIdxAccess|ridx)\b|\bLength\b(?!\s*\.\s*length\b)")
ARRAY_REASONS = ("std's array trait",)
ARRAY_EMITTERS = frozenset(("solcore-source-memory-arrays-v2",))
# The native errors of row 4's array operations on a base whose type is still open where they are: Lean decides a
# slice, a length, `toArray`, `lidx` and `CanStore` there (differences 18, 14, 19 and 22 to 24).
OPEN_ARRAY_BASE = frozenset(('unsupportedExpression "slice"', *(f'operatorNotSupported "{name}" at variable'
                                                              for name in ("Length", "toArray", "lidx", "CanStore"))))
# What the other pure emitters' sources need that the native frontend lacks or reads differently.
NOT_ADMITTED = {
    "solcore-source-assembly-v2": "inline Yul",
    "solcore-source-assembly-loops-v2": "inline Yul",
    "solcore-source-assembly-memory-v2": "inline Yul",
    "solcore-source-halt-v2": "std's Error type and invalid halts",
    "solcore-source-revert-data-v2": "std's Error type and revert data",
    "solcore-source-memory-values-v2": "std's memory traits and bytes",
    "solcore-source-memory-calls-v2": "std's memory traits and bytes",
    "solcore-source-traits-v2": "std's sum in instance types",
    "solcore-source-trait-hierarchies-v2": "std's sum in instance types",
    "solcore-source-comptime-v3": "comptime constant functions",
    "solcore-source-modules-v3": "comptime constant functions and module bundles",
    "solcore-source-array-abi-v2": "array parameters",
}
# Known differences from upstream, each recognized by the native error it gives.
KNOWN = {
    "open-typedef-call": "row 1's waiting `Typedef` call: Lean resolves `Typedef` where the call is and rejects "
                         "one whose type is still open there, as it rejects row 4's unannotated `let m = [];` "
                         "(difference 8)",
    "open-array-base": "row 4's array operations on an open base (differences 14, 18, 19 and 22 to 24): Lean decides "
                       "a length, a slice, `toArray`, `lidx` or `CanStore` on its base's type where it is and rejects "
                       "one whose base is still open there, while upstream's constraints wait for later uses",
    "generalized-lambda-parameter": "local lambda generalization: Lean quantifies an unannotated lambda parameter that "
                                    "upstream keeps monomorphic, so an operator on it is rejected",
    "bool-equality": "`==` on `bool`, which Lean does not provide",
    "not-equal": "`!=` at a type with no builtin `!=`, which upstream takes from std's `ne`",
    "uninitialized-local": "a read of an uninitialized local, which Lean faults on and upstream reads as zero",
}

STD_IMPORT = re.compile(r"^[ \t]*import\b[^;\n]*\bstd\b[^;\n]*;[ \t]*$", re.M)
# An import of `std.opcodes`, which the native load resolves, so the adapter keeps it.
STD_OPCODES_IMPORT = re.compile(r"\bstd\s*\.\s*opcodes\s*;[ \t]*$")
CONTRACT = re.compile(r"^[ \t]*contract\s+([A-Za-z_]\w*)\s*(?:<[^>{]*>)?\s*\{", re.M)
FUNCTION = re.compile(r"function\s+([A-Za-z_]\w*)\s*(?:<[^>(]*>)?\s*\(")
FIELD = re.compile(r"[A-Za-z_]\w*\s*:[^;{}]*;", re.S)
MODIFIERS = re.compile(r"\b(?:public|external|internal|private|payable|view|pure|nonpayable)\b")
HEADER = r"function\s+{name}\s*\(([^()]*)\)\s*(?:returns\s*\(\s*([^()]*?)\s*\))?\s*\{{"
ERROR = re.compile(r'([A-Za-z]*Error)\.([a-zA-Z]+)(?: "((?:[^"\\]|\\.)*)")?'
                   r"(?: \(Solcore\.TypeSystem\.Ty\.(variable|constructor)"
                   r"(?: \(Solcore\.TypeSystem\.TypeConstructorId\.builtin"
                   r" \(Solcore\.TypeSystem\.BuiltinType\.(\w+))?)?")
WRAPPING_ERRORS = ("ProgramCheckError", "ProgramLoadError", "CompileError")
RESOURCE = re.compile(r"[Ff]uel|[Bb]udget")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def key_digest(value) -> str:
    return digest(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def operations(program) -> set[str]:
    """The Core operations of a program: its node tags, each unary, binary or ternary node with its operator."""
    found, pending = set(), [program]
    while pending:
        node = pending.pop()
        if isinstance(node, dict):
            tag, operator = node.get("tag"), node.get("op")
            if isinstance(tag, str):
                lifted = tag in ("unary", "binary", "ternary") and isinstance(operator, str)
                found.add(f"{tag}:{operator}" if lifted else tag)
            pending.extend(node.values())
        elif isinstance(node, list):
            pending.extend(node)
    return found


def skip(text: str, index: int) -> int:
    """The index after a comment or string literal that starts at `index`, else `index` itself."""
    if text.startswith("//", index):
        end = text.find("\n", index)
        return len(text) if end < 0 else end
    if text.startswith("/*", index):
        end = text.find("*/", index + 2)
        return len(text) if end < 0 else end + 2
    if text[index] == '"':
        position = index + 1
        while position < len(text) and text[position] != '"':
            position += 2 if text[position] == "\\" else 1
        return position + 1
    return index


def matching_brace(text: str, opening: int) -> int:
    depth, position = 0, opening
    while position < len(text):
        after = skip(text, position)
        if after != position:
            position = after
            continue
        if text[position] == "{":
            depth += 1
        elif text[position] == "}":
            depth -= 1
            if depth == 0:
                return position
        position += 1
    raise ValueError("unbalanced braces")


def members(body: str) -> list[str]:
    """A contract body's members at its own depth: each ends with `;` or with its closing brace."""
    result, start, depth, position = [], 0, 0, 0
    while position < len(body):
        after = skip(body, position)
        if after != position:
            position = after
            continue
        character = body[position]
        if character == "{":
            depth += 1
        elif character == "}":
            depth -= 1
            if depth == 0:
                result.append(body[start:position + 1])
                start = position + 1
        elif character == ";" and depth == 0:
            result.append(body[start:position + 1])
            start = position + 1
        position += 1
    if body[start:].strip():
        result.append(body[start:])
    return result


def first_brace(text: str) -> int:
    """The index of the first `{` outside comments and string literals, else the text's length."""
    position = 0
    while position < len(text):
        after = skip(text, position)
        if after != position:
            position = after
            continue
        if text[position] == "{":
            return position
        position += 1
    return len(text)


def code_only(text: str) -> str:
    """The text without its comments; string literals stay."""
    kept, position = [], 0
    while position < len(text):
        after = skip(text, position)
        if after != position and text[position] != '"':
            position = after
            continue
        kept.append(text[position])
        position += 1
    return "".join(kept)


def array_forms(source: str) -> dict[str, list[str]]:
    """The array forms of a source's code that the native path does not read, by reason, each with what was found."""
    code, found = code_only(source), {}
    traits = sorted({match.group(0) for match in STD_ARRAY_TRAITS.finditer(code)})
    if traits:
        found["std's array trait"] = traits
    return found


def lift(source: str, method: str) -> dict:
    """native-lift-v3 on a case's source: its std imports other than those of `std.opcodes` dropped, each line kept
    as an empty line, and its one contract's functions moved to the top level without their visibility and
    mutability words; std's own `tobool` appended where the code calls it and defines none; then a Word entry of
    `method` appended. Gives the lifted source and the entry's name, or the reason it cannot."""
    text = STD_IMPORT.sub(lambda match: match.group(0) if STD_OPCODES_IMPORT.search(match.group(0)) else "", source)
    contracts = list(CONTRACT.finditer(text))
    if len(contracts) != 1:
        return {"reason": "contract shape", "detail": f"{len(contracts)} contracts"}
    match = contracts[0]
    opening = match.end() - 1
    closing = matching_brace(text, opening)
    functions, fields, others = [], 0, 0
    for member in members(text[opening + 1:closing]):
        code = code_only(member).strip()
        if not code:
            continue
        if FUNCTION.match(code):
            header_end = first_brace(member)
            functions.append(MODIFIERS.sub("", member[:header_end]) + member[header_end:])
        elif FIELD.fullmatch(code):
            fields += 1
        else:
            others += 1
    if fields:
        return {"reason": "storage field", "detail": f"{fields} fields"}
    if others:
        return {"reason": "contract member", "detail": f"{others} members"}
    lifted = text[:match.start()] + "\n".join(functions) + text[closing + 1:]
    code = code_only(lifted)
    if TOBOOL_CALL.search(code) and not TOBOOL_DEFINITION.search(code):
        lifted = lifted + "\n" + STD_TOBOOL
    header = re.search(HEADER.format(name=re.escape(method)), "\n".join(functions))
    if not header:
        return {"reason": "parameters or result", "detail": "no method header"}
    parameters = [item.strip() for item in header.group(1).split(",") if item.strip()]
    types = [item.split(":", 1)[1].strip() if ":" in item else "" for item in parameters]
    result = header.group(2)
    if any(item != "uint256" for item in types) or result not in ("uint256", "word"):
        return {"reason": "parameters or result", "detail": f"({', '.join(types)}) -> {result}"}
    entry = WRAPPER + method
    if re.search(r"\b" + re.escape(entry) + r"\b", source):
        return {"reason": "contract shape", "detail": f"the source already names {entry}"}
    names = [f"{WRAPPER}a{index}" for index in range(len(types))]
    call = f"{method}({', '.join(f'uint256({name})' for name in names)})"
    body = f"return Typedef.rep({call});" if result == "uint256" else f"return {call};"
    entry_text = (f"\nfunction {entry}({', '.join(f'{name}: word' for name in names)}) returns (word) {{\n"
                  f"    {body}\n}}\n")
    return {"reason": None, "source": lifted + entry_text, "function": entry, "parameters": len(types)}


def arguments(contract: dict, count: int) -> list[str] | None:
    """The method's Word arguments from the case's calldata: the selector, then one word each."""
    calldata = contract.get("calldata")
    if not isinstance(calldata, str) or not calldata.startswith("0x"):
        return None
    try:
        data = bytes.fromhex(calldata[2:])
    except ValueError:
        return None
    if len(data) != 4 + 32 * count:
        return None
    return [str(int.from_bytes(data[4 + 32 * index:36 + 32 * index], "big")) for index in range(count)]


def admission(case: dict) -> dict:
    """native-admission-v6, decided from the case alone before any native run: the program the native tool reads
    with the case's arguments, or the first reason in a fixed order that the case is not admitted."""
    def refuse(reason: str, detail=None) -> dict:
        return {"admitted": False, "reason": reason, "detail": detail}

    provenance = case.get("provenance") if isinstance(case.get("provenance"), dict) else {}
    emitter = provenance.get("emitterVersion")
    if emitter not in EMITTERS:
        return refuse("emitter", emitter)
    found = sorted(operations(case.get("program")) & EMITTERS[emitter])
    if found:
        return refuse("sum", ", ".join(found))
    if not isinstance(case.get("source"), str) or "sourceBundle" in case or "sources" in case:
        return refuse("sources")
    contract = case.get("contract") if isinstance(case.get("contract"), dict) else {}
    method = contract.get("method")
    if not isinstance(method, str) or not re.fullmatch(r"[A-Za-z_]\w*", method):
        return refuse("contract shape", "no method")
    lifted = lift(case["source"], method)
    if lifted["reason"]:
        return refuse(lifted["reason"], lifted.get("detail"))
    if contract.get("signature") != f"{method}({','.join(['uint256'] * lifted['parameters'])})":
        return refuse("parameters or result", contract.get("signature"))
    words = arguments(contract, lifted["parameters"])
    if words is None:
        return refuse("calldata")
    forms = array_forms(case["source"]) if emitter in ARRAY_EMITTERS else {}
    for reason in ARRAY_REASONS:
        if reason in forms:
            return refuse(reason, ", ".join(forms[reason]))
    return {"admitted": True, "source": lifted["source"], "function": lifted["function"], "arguments": words}


def symptom(detail: str) -> str:
    """A rejection's error, stable across programs: its innermost named error constructor, the constructor's quoted
    name argument and, for an operator, whether its type was open (`variable`) or a builtin."""
    matches = list(ERROR.finditer(detail or ""))
    chosen = next((item for item in matches if item.group(1) not in WRAPPING_ERRORS), matches[0] if matches else None)
    if chosen is None:
        return (detail or "").split(" ", 1)[0][:80]
    _, name, argument, kind, builtin = chosen.groups()
    return name + (f' "{argument}"' if argument is not None else "") + (f" at {builtin or kind}" if kind else "")


def rejection_label(stage: str, found: str) -> str | None:
    if stage != "inference":
        return None
    if found == 'operatorNotSupported "Typedef" at variable':
        return "open-typedef-call"
    if found in OPEN_ARRAY_BASE:
        return "open-array-base"
    if re.fullmatch(r'operatorNotSupported "\w+" at variable', found):
        return "generalized-lambda-parameter"
    if found == 'operatorNotSupported "Eq" at bool':
        return "bool-equality"
    if found == 'unknownVariable "ne"':
        return "not-equal"
    return None


def observed(observation: dict) -> str:
    """An observation's class: `returned`, `reverted:` and the revert data's selector, or `failed:` and its error."""
    status = observation.get("status")
    if status == "reverted":
        return "reverted:" + str(observation.get("output", ""))[:10].lower()
    if status == "failed":
        return "failed:" + str(observation.get("error"))
    return str(status)


def compare(core: dict, observation: dict) -> dict:
    """native-compare-v1: one input's verdict, `agree`, `mismatch`, `rejected` or `inconclusive`, with its reason."""
    status = observation.get("status")
    if status == "out-of-fuel":
        return {"verdict": "inconclusive", "reason": "out-of-fuel"}
    if status == "rejected":
        return {"verdict": "rejected", "stage": observation.get("stage"), "symptom": symptom(observation.get("detail"))}
    if core.get("stage") != "execution" or core.get("status") not in ("returned", "reverted"):
        return {"verdict": "inconclusive", "reason": f"direct Core {core.get('stage')}/{core.get('status')}"}
    if core["status"] == "returned" and not isinstance(core.get("word"), str):
        return {"verdict": "inconclusive", "reason": "direct Core output"}
    if core["status"] == "returned" and status == "returned" and observation.get("word") == core["word"]:
        return {"verdict": "agree"}
    if core["status"] == "reverted" and status == "reverted" and \
            str(observation.get("output", "")).lower() == str(core.get("output", "")).lower():
        return {"verdict": "agree"}
    core_class = "returned" if core["status"] == "returned" else "reverted:" + str(core.get("output", ""))[:10].lower()
    return {"verdict": "mismatch", "core": core_class, "native": observed(observation),
            "label": "uninitialized-local" if observation.get("error") == "uninitializedLocal" else None}


def run_tool(tool: Path, program: dict, inputs: list[list[str]], work: Path, timeout: float) -> dict:
    """One native tool run of a program with all of its inputs: the tool's result, or a timeout or crash."""
    request = {"schema": REQUEST_SCHEMA, "entry": "main.sol",
               "sources": [{"path": "main.sol", "content": program["source"]}],
               "function": program["function"], "inputs": inputs, **FUEL}
    path = work / "request.json"
    path.write_text(json.dumps(request))
    started = time.monotonic()
    try:
        completed = subprocess.run([str(tool), str(path)], stdin=subprocess.DEVNULL, capture_output=True, text=True,
                                   timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "seconds": round(time.monotonic() - started, 3), "request": request}
    seconds = round(time.monotonic() - started, 3)
    if completed.returncode:
        return {"status": "crash", "seconds": seconds, "request": request,
                "detail": f"exit {completed.returncode}: " + (completed.stderr or completed.stdout)[-2000:]}
    result = json.loads(completed.stdout)
    if result.get("schema") != RESULT_SCHEMA or not isinstance(result.get("observations"), list) or \
            (result.get("status") == "compiled" and len(result["observations"]) != len(inputs)):
        raise ValueError(f"the native tool returned an unexpected result: {completed.stdout[:300]}")
    return {**result, "seconds": seconds, "request": request}


def prepare(arguments_: list[str]) -> dict:
    """The pure runner's own case preparation for one profile: its argument checks and its generation, or its
    corpus emission and validation, through the case tool; its `run` is replaced for this call only, so nothing
    is compiled or executed."""
    captured = {}

    class Preparation(runner.Campaign):
        def run(self):
            captured["response"] = self.prepare_cases()
            self.summary["status"] = "complete"

    saved = runner.Campaign, sys.argv
    runner.Campaign, sys.argv = Preparation, ["semantic-campaign.py", *arguments_]
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            runner.main()
    except SystemExit as stop:
        raise ValueError(f"the pure runner refused its arguments (exit {stop.code})") from None
    finally:
        runner.Campaign, sys.argv = saved
    if "response" not in captured:
        output = Path(arguments_[arguments_.index("--output") + 1])
        summary = json.loads((output / "summary.json").read_text()) if (output / "summary.json").is_file() else {}
        if summary.get("status") == "interrupted":
            raise KeyboardInterrupt
        raise ValueError(f"case preparation stopped: {summary.get('stop') or summary.get('status')}")
    return captured["response"]


def profile_emitter(profile: str) -> str | None:
    return json.loads(suite.manifest(profile).read_text()).get("emitterVersion")


def identity(args) -> dict:
    """Everything a run reads: the native and case tools, the scripts and, in fixed mode, the selected corpora."""
    tools = {name: {"path": str(path), "sha256": runner.m2.file_digest(path) if path.is_file() else None}
             for name, path in (("nativeTool", args.native_tool), ("caseTool", args.bin_dir / "semantic-case-tool"))}
    return {"versions": {"admission": ADMISSION, "adapter": ADAPTER, "comparison": COMPARISON},
            "admittedEmitters": sorted(EMITTERS), "tools": tools,
            "scripts": {name: runner.m2.file_digest(ROOT / "scripts" / name) for name in SCRIPTS},
            "corpora": {profile: runner.m2.file_digest(suite.manifest(profile)) for profile in args.profile}
            if args.mode == "fixed" else {}}


def counter(table: dict, key: str, amount: int = 1) -> None:
    table[key] = table.get(key, 0) + amount


class NativeRun:
    COUNTS = ("cases", "generationExcluded", "notAdmitted", "admitted", "programs", "agree", "mismatch", "rejected",
              "inconclusive", "unexecuted")

    def __init__(self, args, suite_args):
        self.args, self.suite_args = args, suite_args
        self.deadline = time.monotonic() + args.seconds
        self.findings: dict[str, dict] = {}
        self.programs: list[dict] = []
        self.profiles: dict[str, dict] = {}
        self.errors: list[dict] = []
        self.stopped = False

    def finding(self, kind: str, key: dict, label: str | None, profile: str, example: dict, saved: dict) -> None:
        signature = key_digest([kind, key])
        record = self.findings.get(signature)
        if record is None:
            record = self.findings[signature] = {"signature": signature, "kind": kind, **key, "label": label,
                                                 "known": label is not None, "count": 0, "profiles": {}, "examples": []}
            folder = self.args.output / "findings" / signature[:16]
            folder.mkdir(parents=True, exist_ok=True)
            for name, value in saved.items():
                (folder / f"{name}.json").write_text(json.dumps(value, indent=1) + "\n")
            record["replay"] = str(folder / "request.json")
        record["count"] += 1
        counter(record["profiles"], profile)
        if len(record["examples"]) < 3:
            record["examples"].append(example)

    def run_profile(self, profile: str) -> None:
        counts = {key: 0 for key in self.COUNTS}
        totals = {"counts": counts, "reasons": {}, "inconclusive": {}, "known": {}, "seconds": 0.0}
        self.profiles[profile] = totals
        started = time.monotonic()
        prepared = self.args.output / "prepared" / profile
        seconds = max(1.0, min(PROFILE_SECONDS, self.deadline - time.monotonic()))
        command = suite.command(self.suite_args, profile, prepared, seconds, PROFILE_DISK_BYTES)[2:]
        response = prepare(command)
        cases = response.get("cases") or []
        counts["cases"] = len(cases)
        counts["generationExcluded"] = len(response.get("excluded") or [])
        groups: dict[str, dict] = {}
        for index, case in enumerate(cases):
            decided = admission(case)
            if not decided["admitted"]:
                counts["notAdmitted"] += 1
                counter(totals["reasons"], decided["reason"])
                continue
            counts["admitted"] += 1
            key = digest((decided["function"] + "\0" + decided["source"]).encode())
            group = groups.setdefault(key, {"programSha256": key, "source": decided["source"],
                                            "function": decided["function"], "cases": []})
            group["cases"].append((index, case, decided["arguments"]))
        counts["programs"] = len(groups)
        work = self.args.output / ".work"
        work.mkdir(exist_ok=True)
        for group in groups.values():
            if self.stopped or time.monotonic() >= self.deadline:
                self.stopped = True
                counts["unexecuted"] += len(group["cases"])
                continue
            try:
                self.run_program(profile, group, totals, work)
            except ValueError as error:
                self.errors.append({"profile": profile, "programSha256": group["programSha256"], "detail": str(error)})
                counts["unexecuted"] += len(group["cases"])
        totals["seconds"] = round(time.monotonic() - started, 3)

    def run_program(self, profile: str, group: dict, totals: dict, work: Path) -> None:
        counts = totals["counts"]
        inputs = [words for _, _, words in group["cases"]]
        result = run_tool(self.args.native_tool, group, inputs, work, self.args.program_seconds)
        record = {"profile": profile, "programSha256": group["programSha256"],
                  "cases": [index for index, _, _ in group["cases"]], "status": result["status"],
                  "stage": result.get("stage"), "seconds": result["seconds"],
                  "milliseconds": result.get("milliseconds"), "verdicts": []}
        self.programs.append(record)
        program_level = None
        if result["status"] in ("timeout", "out-of-fuel"):
            program_level = {"verdict": "inconclusive", "reason": result["status"]}
        elif result["status"] == "crash":
            last = result["detail"].strip().splitlines()[-1][:200]
            program_level = {"verdict": "rejected", "stage": "tool", "symptom": last}
        elif result["status"] == "rejected":
            found = symptom(result.get("detail"))
            if RESOURCE.search(found):
                program_level = {"verdict": "inconclusive", "reason": "native resource: " + found}
            else:
                program_level = {"verdict": "rejected", "stage": result.get("stage"), "symptom": found}
        observations = result.get("observations") or []
        for position, (index, case, words) in enumerate(group["cases"]):
            observation = observations[position] if program_level is None else None
            verdict = program_level or compare(case.get("directCore") or {}, observation)
            record["verdicts"].append(verdict["verdict"])
            counts[verdict["verdict"]] += 1
            if verdict["verdict"] == "inconclusive":
                counter(totals["inconclusive"], verdict["reason"])
            if verdict["verdict"] not in ("rejected", "mismatch"):
                continue
            if verdict["verdict"] == "rejected":
                kind, key = "native-rejection", {"stage": verdict["stage"], "symptom": verdict["symptom"]}
                label = rejection_label(verdict["stage"], verdict["symptom"])
            else:
                kind = "native-mismatch"
                key = {"profile": profile, "core": verdict["core"], "native": verdict["native"]}
                label = verdict["label"]
            if label:
                counter(totals["known"], label)
            example = {"profile": profile, "case": index, "programSha256": group["programSha256"], "arguments": words,
                       "directCore": case.get("directCore"), "native": observation,
                       "detail": (result.get("detail") or "")[:600] if program_level else None}
            saved = {"request": result["request"], "result": {k: v for k, v in result.items() if k != "request"},
                     "case": case}
            self.finding(kind, key, label, profile, example, saved)

    def report(self, started_identity: dict, finished_identity: dict, started: float) -> dict:
        totals = {"counts": {key: 0 for key in self.COUNTS}, "reasons": {}, "inconclusive": {}, "known": {}}
        for profile in self.profiles.values():
            for section in ("counts", "reasons", "inconclusive", "known"):
                for key, value in profile[section].items():
                    counter(totals[section], key, value)
        findings = sorted(self.findings.values(), key=lambda item: (item["known"], -item["count"], item["signature"]))
        totals["findings"] = {"signatures": len(findings), "known": sum(item["known"] for item in findings),
                              "new": sum(not item["known"] for item in findings)}
        unchanged = started_identity == finished_identity
        passed = unchanged and not self.errors and not self.stopped and totals["findings"]["new"] == 0 and \
            totals["counts"]["inconclusive"] == 0 and totals["counts"]["unexecuted"] == 0
        return {"schema": SCHEMA, "status": "passed" if passed else "failed", "mode": self.args.mode,
                "seed": self.args.seed if self.args.mode == "random" else None,
                "shard": [self.args.shard_index, self.args.shard_count] if self.args.mode == "random" else None,
                "comparison": "the native frontend's observation of each admitted pure case, lifted by "
                              f"{ADAPTER}, against the case's direct Core result",
                "fuel": FUEL, "programSeconds": self.args.program_seconds, "identity": started_identity,
                "toolsUnchanged": unchanged, "stopped": self.stopped, "known": KNOWN,
                "notAdmittedEmitters": NOT_ADMITTED,
                "seconds": round(time.monotonic() - started, 3), "totals": totals, "profiles": self.profiles,
                "findings": findings, "errors": self.errors, "programs": self.programs}


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--mode", choices=("fixed", "random"), default="fixed")
    parser.add_argument("--output", type=Path, help="fresh directory for the report; required unless --check")
    parser.add_argument("--profile", action="append", choices=PURE_PROFILES,
                        help="repeat to select pure profiles; default every pure profile in fixed mode, and every "
                             "profile whose emitter is admitted in random mode")
    parser.add_argument("--seed", type=int, default=1, help="random mode's root seed, derived per profile and shard "
                                                            "as semantic-suite.py derives it")
    parser.add_argument("--shard-index", type=int, default=0)
    parser.add_argument("--shard-count", type=int, default=1)
    for name in ("cases", "functions", "nodes", "attempts"):
        parser.add_argument("--" + name, type=int, help="random mode, as semantic-suite.py takes it")
    parser.add_argument("--nodes-scale", type=float, default=1.0, help="random mode, as semantic-suite.py takes it")
    parser.add_argument("--native-tool", type=Path, default=TOOL)
    parser.add_argument("--bin-dir", type=Path, default=ROOT / ".lake/build/bin", help="the case tool's directory")
    parser.add_argument("--seconds", type=float, default=3600, help="wall time of the run; later programs do not run")
    parser.add_argument("--program-seconds", type=float, default=120, help="wall time of one native tool run")
    parser.add_argument("--check", action="store_true", help="print the identity of what a run reads and exit")
    args = parser.parse_args(argv)
    if args.output is None and not args.check:
        parser.error("--output is required unless --check is given")
    if min(args.seconds, args.program_seconds) <= 0:
        parser.error("time budgets must be positive")
    if args.profile is None:
        args.profile = list(PURE_PROFILES) if args.mode == "fixed" else \
            [profile for profile in PURE_PROFILES if profile_emitter(profile) in EMITTERS]
    suite_argv = ["--mode", args.mode, "--output", str(args.output or ROOT / ".upstream/semantic-native-check"),
                  "--bin-dir", str(args.bin_dir)]
    suite_argv += [item for profile in args.profile for item in ("--profile", profile)]
    if args.mode == "random":
        suite_argv += ["--seed", str(args.seed), "--shard-index", str(args.shard_index),
                       "--shard-count", str(args.shard_count), "--nodes-scale", str(args.nodes_scale)]
    for name in ("cases", "functions", "nodes", "attempts"):
        if getattr(args, name) is not None:
            suite_argv += ["--" + name, str(getattr(args, name))]
    suite_args = suite.parse_args(suite_argv)
    for key in ("native_tool", "bin_dir"):
        setattr(args, key, getattr(args, key).resolve())
    if args.output is not None:
        args.output = args.output.resolve()
    return args, suite_args


def main(argv=None) -> int:
    args, suite_args = parse_args(argv)
    if args.check:
        found = identity(args)
        missing = [name for name, tool in found["tools"].items() if tool["sha256"] is None]
        status = "not-ready" if missing else "ready"
        print(json.dumps({"schema": SCHEMA + "/check", "status": status, "missing": missing, **found}, sort_keys=True))
        return 2 if missing else 0
    if args.output.exists() and any(args.output.iterdir()):
        raise ValueError("the output directory must be fresh")
    args.output.mkdir(parents=True, exist_ok=True)
    started, started_identity = time.monotonic(), identity(args)
    if any(tool["sha256"] is None for tool in started_identity["tools"].values()):
        raise ValueError("a tool is missing: " + json.dumps(started_identity["tools"]))
    run = NativeRun(args, suite_args)
    previous = signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    interrupted = False
    try:
        for profile in args.profile:
            try:
                run.run_profile(profile)
            except (ValueError, OSError, KeyError, TypeError, runner.m2.Finding) as error:
                run.errors.append({"profile": profile, "detail": f"{type(error).__name__}: {error}"})
            print(f"{profile}: {json.dumps(run.profiles.get(profile, {}).get('counts'))}", flush=True)
    except KeyboardInterrupt:
        interrupted = run.stopped = True
    finally:
        signal.signal(signal.SIGTERM, previous)
        with contextlib.suppress(OSError):
            for leftover in (args.output / ".work").glob("*"):
                leftover.unlink()
            (args.output / ".work").rmdir()
    report = run.report(started_identity, identity(args), started)
    (args.output / "report.json").write_text(json.dumps(report, indent=1) + "\n")
    totals = report["totals"]
    print(json.dumps({"status": report["status"], "counts": totals["counts"], "known": totals["known"],
                      "findings": totals["findings"], "inconclusive": totals["inconclusive"],
                      "toolsUnchanged": report["toolsUnchanged"], "errors": len(report["errors"]),
                      "report": str(args.output / "report.json")}))
    if interrupted:
        return 130
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError) as error:
        print(f"semantic-native: {error}", file=sys.stderr)
        raise SystemExit(2)
