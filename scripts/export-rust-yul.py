#!/usr/bin/env python3
"""Export Yul EVM bytes for the bounded, pure generated contract wrappers.

This is a separate EVM artifact, not a Hull CodeImage or a linker map. One real
solc compilation supplies both deployment and runtime bytes. The checked Hull,
original Yul and exact standard-JSON request/response remain available for replay.
The pinned compiler tools must already be built; this exporter never builds them.
Wrapper names and object shape do not prove purity: the differential adapter
must replay a canonical pure case before using this exporter as its EVM path.
"""
from __future__ import annotations

import argparse
import copy
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


hull = load("yul_checked_hull", "export-rust-hull.py")
common = load("yul_differential", "semantic-differential.py")
SCHEMA = "solcore-rs.yul-evm.v1"
SOLC_VERSION = "0.8.35+commit.47b9dedd"
BACKEND = {"name": "solc-yul", "version": SOLC_VERSION,
           "optimizer": {"enabled": True}, "evmVersion": "osaka"}
CONTRACTS = tuple(common.CASE_CONTRACTS.values())
YUL_SOURCE = "checked.yul"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate_contract(contract):
    require(contract in CONTRACTS, "only the ten generated pure contract wrappers are supported")


def validate_artifact(document, contract):
    validate_contract(contract)
    require(isinstance(document, dict) and set(document) == {
        "schema", "upstreamCommit", "selectedObject", "runtimeObject", "backend", "initCode", "runtimeCode"},
        "unexpected Yul EVM artifact fields")
    require(document["schema"] == SCHEMA and document["upstreamCommit"] == hull.COMMIT and
            document["selectedObject"] == contract + "Deploy" and document["runtimeObject"] == contract and
            document["backend"] == BACKEND, "unexpected Yul EVM schema, wrapper, revision or backend")
    require(type(document["backend"]["optimizer"]["enabled"]) is bool, "invalid optimizer configuration")
    for key, bound in (("initCode", 49152), ("runtimeCode", 24576)):
        code = document[key]
        require(isinstance(code, str) and re.fullmatch(r"0x(?:[0-9a-f]{2})+", code),
                "invalid or empty Yul EVM bytecode: " + key)
        require((len(code) - 2) // 2 <= bound, "export EVM code size limit exceeded: " + key)


def validate_version(stdout):
    lines = [line.removeprefix("Version: ") for line in stdout.splitlines() if line.startswith("Version: ")]
    require(len(lines) == 1 and re.fullmatch(re.escape(SOLC_VERSION) + r"(?:\.[A-Za-z0-9_.+-]+)?", lines[0]),
            "solc must report the pinned version " + SOLC_VERSION)


def validate_hull(document, contract):
    validate_contract(contract)
    require(isinstance(document, dict) and document.get("schema") == hull.SCHEMA and
            document.get("upstreamCommit") == hull.COMMIT, "unexpected checked Hull schema or revision")
    program = document.get("program")
    require(isinstance(program, dict), "malformed checked Hull program")
    objects = program.get("objects")
    require(isinstance(objects, list) and len(objects) == 1 and isinstance(objects[0], dict),
            "Yul profile requires exactly one checked Hull deployment object")
    root = objects[0]
    children = root.get("inners")
    require(root.get("name") == contract + "Deploy" and isinstance(children, list) and len(children) == 1 and
            isinstance(children[0], dict) and children[0].get("name") == contract and children[0].get("inners") == [],
            "Yul profile requires the selected deployment object and one leaf runtime object")


def standard_input(source):
    return {"language": "Yul", "sources": {YUL_SOURCE: {"content": source}},
        "settings": {"optimizer": {"enabled": True}, "evmVersion": "osaka", "outputSelection": {
            "*": {"*": ["ast", "evm.bytecode.object", "evm.bytecode.linkReferences", "evm.deployedBytecode.object",
                         "evm.deployedBytecode.linkReferences", "evm.deployedBytecode.immutableReferences"], "": ["ast"]}}}}


def artifact_from_output(document, contract):
    validate_contract(contract)
    require(isinstance(document, dict) and set(document) <= {"contracts", "sources", "errors"},
            "unknown solc standard-JSON output fields")
    diagnostics = document.get("errors", [])
    require(isinstance(diagnostics, list) and all(isinstance(row, dict) for row in diagnostics),
            "malformed solc diagnostics")
    errors = [row for row in diagnostics if row.get("severity") == "error"]
    require(not errors, "Yul compilation rejected: " + "\n".join(
        str(row.get("formattedMessage", row.get("message", row))) for row in errors))
    require(all(row.get("severity") == "warning" for row in diagnostics), "unknown solc diagnostic severity")
    contracts, sources = document.get("contracts"), document.get("sources")
    selected = contract + "Deploy"
    require(isinstance(contracts, dict) and set(contracts) == {YUL_SOURCE} and
            isinstance(contracts[YUL_SOURCE], dict) and set(contracts[YUL_SOURCE]) == {selected},
            "unexpected solc contract output inventory")
    require(isinstance(sources, dict) and set(sources) == {YUL_SOURCE} and
            isinstance(sources[YUL_SOURCE], dict) and set(sources[YUL_SOURCE]) == {"ast", "id"} and
            type(sources[YUL_SOURCE]["id"]) is int and sources[YUL_SOURCE]["id"] == 0,
            "unexpected solc source output inventory")
    ast = sources[YUL_SOURCE]["ast"]
    require(isinstance(ast, dict) and ast.get("nodeType") == "YulObject" and ast.get("name") == selected,
            "solc AST does not describe the selected deployment object")
    children = ast.get("subObjects")
    require(isinstance(children, list) and len(children) == 1 and isinstance(children[0], dict) and
            children[0].get("nodeType") == "YulObject" and children[0].get("name") == contract and
            children[0].get("subObjects") == [], "solc AST runtime object differs from the checked Hull wrapper")
    result = contracts[YUL_SOURCE][selected]
    require(isinstance(result, dict) and set(result) == {"evm"} and isinstance(result["evm"], dict) and
            set(result["evm"]) == {"bytecode", "deployedBytecode"}, "missing runtime bytes or unknown solc EVM output")
    bytecode, runtime = result["evm"]["bytecode"], result["evm"]["deployedBytecode"]
    require(isinstance(bytecode, dict) and set(bytecode) == {"object", "linkReferences"} and
            bytecode["linkReferences"] == {} and isinstance(runtime, dict) and
            set(runtime) == {"object", "linkReferences", "immutableReferences"} and
            runtime["linkReferences"] == {} and runtime["immutableReferences"] == {},
            "unsupported solc link references, immutables or bytecode fields")
    require(isinstance(bytecode["object"], str) and isinstance(runtime["object"], str), "non-text solc bytecode")
    artifact = {"schema": SCHEMA, "upstreamCommit": hull.COMMIT, "selectedObject": selected,
        "runtimeObject": contract, "backend": copy.deepcopy(BACKEND),
        "initCode": "0x" + bytecode["object"], "runtimeCode": "0x" + runtime["object"]}
    validate_artifact(artifact, contract)
    return artifact


def stop_owned_process(process):
    # The outer runner allows two seconds to stop this exporter. Finish killing
    # the compiler's separate session within that grace period, even if it
    # ignores TERM, rather than leaving it alive when the exporter is killed.
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=.25)
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait(timeout=.5)


def run_process(command, args, *, cwd=ROOT, stdin=None, watched=()):
    """Bound captured output and time, stopping the command's owned process group."""
    started = time.monotonic()
    with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr, tempfile.TemporaryFile() as input_file:
        if stdin is not None:
            require(len(stdin) <= args.output_limit, "export standard-JSON input size limit exceeded")
            input_file.write(stdin)
            input_file.seek(0)
        process = subprocess.Popen(command, cwd=cwd, stdin=input_file if stdin is not None else subprocess.DEVNULL,
                                   stdout=stdout, stderr=stderr, start_new_session=True)
        reason = None

        def oversized():
            return stdout.tell() + stderr.tell() > args.output_limit or any(
                path.exists() and path.stat().st_size > args.output_limit for path in watched)

        try:
            while process.poll() is None:
                if time.monotonic() - started >= args.timeout:
                    reason = "export time limit exhausted: timeout"
                    break
                if oversized():
                    reason = "export output limit exceeded"
                    break
                time.sleep(.02)
        finally:
            stop_owned_process(process)
        if oversized():
            reason = "export output limit exceeded"
        stdout.seek(0)
        stderr.seek(0)
        out, err = stdout.read(args.output_limit), stderr.read(args.output_limit)
    if reason:
        raise ValueError(reason)
    if process.returncode:
        detail = (err + out).decode(errors="replace")
        if process.returncode < 0:
            raise ValueError(f"internal compiler error: process terminated by signal {-process.returncode}:\n{detail}")
        raise ValueError(f"compiler command failed with status {process.returncode}:\n{detail}")
    if err:
        sys.stderr.write(err.decode(errors="replace"))
    return out


def checked_build(upstream, target, args):
    """Check installed exporter patches read-only before invoking its normal CLI."""
    require(upstream.is_relative_to((ROOT / ".upstream").resolve()) and
            target.is_relative_to((ROOT / ".upstream").resolve()), "compiler checkout and target must stay inside .upstream")

    def git(*command):
        return run_process(["git", "-C", str(upstream), *command], args).decode()

    require(git("rev-parse", "HEAD").strip() == hull.COMMIT, "unexpected checked Rust compiler revision")
    replacements = {"crates/driver/src/main.rs": ("mod emit;", "mod emit;\nmod lean_export;"),
        "crates/driver/src/emit.rs": ("&hull::pretty_program(db, &program)", "&crate::lean_export::export(db, &program)")}
    require(set(git("diff", "--name-only", "HEAD").splitlines()) <= set(replacements),
            "checked Rust compiler has unrelated tracked changes")
    patches = {}
    for path, (old, new) in replacements.items():
        original = git("show", hull.COMMIT + ":" + path)
        require(original.count(old) == 1, "checked Hull injection point changed")
        expected = original.replace(old, new).encode()
        require((upstream / path).read_bytes() == expected, "checked Hull exporter is not prepared; build it separately")
        patches[path] = hull.digest(expected)
    serializer = "crates/driver/src/lean_export.rs"
    expected = (ROOT / "scripts/rust-hull-export.rs").read_bytes()
    require((upstream / serializer).read_bytes() == expected, "checked Hull serializer changed; build it separately")
    patches[serializer] = hull.digest(expected)
    driver = target / "debug/solcore-driver"
    receipt = common.read_json(target / "lean-export-build.json", args.output_limit)
    require(receipt.get("upstreamCommit") == hull.COMMIT and receipt.get("patches") == patches and
            receipt.get("binarySha256") == common.file_digest(driver), "checked Hull build receipt is stale")
    return driver, receipt


def export(args):
    source, output, upstream, target = args.source, args.output, args.upstream, args.target_dir
    require(source.is_file() and source.stat().st_size <= args.output_limit, "export source size limit exceeded or source missing")
    driver, build = checked_build(upstream, target, args)
    version = run_process([str(args.solc), "--version"], args).decode()
    validate_version(version)
    compiler_hash = common.file_digest(args.solc)
    stem = output.with_suffix("")
    hull_output = args.hull_output or Path(str(stem) + ".hull.json")
    paths = {"hull": hull_output, "hullProvenance": hull_output.with_suffix(hull_output.suffix + ".provenance.json"),
             "yul": Path(str(stem) + ".yul"), "solcInput": Path(str(stem) + ".solc-input.json"),
             "solcOutput": Path(str(stem) + ".solc-output.json")}
    sidecar = output.with_suffix(output.suffix + ".provenance.json")
    all_paths = [output, sidecar, *paths.values()]
    require(len(set(all_paths)) == len(all_paths) and source not in all_paths,
            "source, artifact and evidence output paths must differ")
    require(all(path.parent == output.parent and not path.exists() for path in all_paths),
            "Yul outputs must be fresh sibling files")
    output.parent.mkdir(parents=True, exist_ok=True)
    hull_command = [sys.executable, str(ROOT / "scripts/export-rust-hull.py"), str(source),
        "--upstream", str(upstream), "--target-dir", str(target), "--output", str(hull_output)]
    yul_command = [str(driver), str(source), "--std-root", str(upstream / "std"),
                   "--emit-yul", "--emit-yul-object", args.contract + "Deploy"]
    if args.root:
        hull_command += ["--root", str(args.root)]
        yul_command += ["--root", str(args.root)]
    source_before = common.file_digest(source)
    run_process(hull_command, args, watched=(hull_output, paths["hullProvenance"]))
    checked = common.read_json(hull_output, args.output_limit)
    validate_hull(checked, args.contract)
    receipt = common.read_json(paths["hullProvenance"], args.output_limit)
    require(receipt.get("outputSha256") == common.file_digest(hull_output) and
            receipt.get("binarySha256") == build["binarySha256"] and
            receipt.get("sources", {}).get(source.as_uri()) == source_before,
            "checked Hull provenance differs from source or compiler")
    yul = run_process(yul_command, args, cwd=upstream)
    paths["yul"].write_bytes(yul)
    request = common.json_bytes(standard_input(yul.decode()))
    paths["solcInput"].write_bytes(request)
    solc_command = [str(args.solc), "--standard-json"]
    response = run_process(solc_command, args, stdin=request)
    paths["solcOutput"].write_bytes(response)
    artifact = artifact_from_output(json.loads(response), args.contract)
    sources = hull.source_hashes(checked)
    sources[source.as_uri()] = common.file_digest(source)
    require(sources == receipt["sources"], "source files changed between checked Hull and Yul compilation")
    require(common.file_digest(driver) == build["binarySha256"] and common.file_digest(args.solc) == compiler_hash,
            "compiler binary changed during Yul export")
    contents = common.json_bytes(artifact)
    output.write_bytes(contents)
    record = {"schema": SCHEMA, "upstreamCommit": hull.COMMIT, "backend": copy.deepcopy(BACKEND),
        "selectedObject": args.contract + "Deploy", "runtimeObject": args.contract,
        "exporterSha256": common.file_digest(Path(__file__)), "outputSha256": hull.digest(contents),
        "compiler": {"path": str(args.solc), "sha256": compiler_hash, "versionOutput": version},
        "toolBuild": build, "hullProvenance": receipt, "sources": sources,
        "commands": {"hull": hull_command, "yul": yul_command, "solc": solc_command},
        "artifacts": {key: {"file": path.name, "sha256": common.file_digest(path)} for key, path in paths.items()},
        "scope": "generated two-object wrapper shape; caller validates canonical pure case; EVM bytes only; no Hull linker map"}
    sidecar.write_bytes(common.json_bytes(record))
    return output


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--contract", choices=CONTRACTS, required=True)
    parser.add_argument("--solc", type=Path, required=True, help="preinstalled solc " + SOLC_VERSION)
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--root", type=Path)
    parser.add_argument("--hull-output", type=Path, help="fresh checked Hull sibling; default OUTPUT.hull.json")
    parser.add_argument("--timeout", type=float, default=90, help="per-process time limit")
    parser.add_argument("--output-limit", type=int, default=8 * 1024**2, help="per-process output and artifact size limit")
    args = parser.parse_args(argv)
    if not math.isfinite(args.timeout) or not .001 <= args.timeout <= 3600 or not 1024 <= args.output_limit <= 64 * 1024**2:
        parser.error("invalid export resource limits")
    for key in ("source", "output", "contract", "solc", "upstream", "target_dir", "root", "hull_output"):
        value = getattr(args, key)
        if isinstance(value, Path):
            setattr(args, key, value.resolve())
    return args


def main(argv=None):
    args = parse_args(argv)
    previous = signal.getsignal(signal.SIGTERM)

    def interrupt(_signal, _frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupt)
    try:
        print("Exported actual Yul EVM bytes: " + str(export(args)))
        return 0
    finally:
        signal.signal(signal.SIGTERM, previous)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print("export-rust-yul: interrupted", file=sys.stderr)
        raise SystemExit(130)
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print("export-rust-yul: " + str(error), file=sys.stderr)
        raise SystemExit(2)
