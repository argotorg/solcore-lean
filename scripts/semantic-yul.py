#!/usr/bin/env python3
"""Validate and execute the separate Yul EVM export boundary.

The caller first validates a canonical pure or storage-family case with the
native replay tool; this module validates the case again with its adapter.
Imported Hull continues to use its independently exported Sonatina O0 images.
This module provides no execution oracle, source purity proof or Yul linker map.
Its dynamically loaded common.Finding class is local to this module. The calling
adapter must translate those exceptions to its own Finding at the lazy boundary
so resource, compiler and replay classifications remain intact. A case with
several contracts, the call-return profile's, keeps each contract's export and
main checked Hull under its own file prefix; its adapter validates the case and
each export.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


exporter = load("yul_transport_exporter", "export-rust-yul.py")
common = exporter.common
BACKEND = exporter.BACKEND
ARTIFACT = "yul.json"
PROVENANCE = "yul.json.provenance.json"
EVIDENCE = {"hull": "yul.hull.json", "hullProvenance": "yul.hull.json.provenance.json",
            "yul": "yul.yul", "solcInput": "yul.solc-input.json", "solcOutput": "yul.solc-output.json"}
FILES = (ARTIFACT, PROVENANCE, *EVIDENCE.values())
MAIN_FILES = ("hull.json", "hull.json.provenance.json")
PATH_BACKENDS = {"directCore": "original-core", "importedHull": "sonatina-o0", "rustEvm": "yul"}
STORAGE_SCHEMAS = frozenset(value["caseSchema"] for value in exporter.storage.PROFILES.values())


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate_case(case):
    """A storage-family case is validated by the storage adapter, keeping its
    structured failures; every other case by the pure adapter."""
    if isinstance(case, dict) and case.get("schema") in STORAGE_SCHEMAS:
        try:
            exporter.storage.validate_case(case)
        except exporter.storage.common.Finding as error:
            raise common.Finding(error.category, error.stage, error.detail) from error
    else:
        common.validate_case(case)


def valid_hash(value):
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def evidence(prefix=""):
    """One export's files and its main checked Hull, under the contract's prefix."""
    return tuple(prefix + name for name in FILES + MAIN_FILES)


def file_path(directory, name, limit, prefix=""):
    require(name in FILES + MAIN_FILES, "unknown Yul evidence filename")
    path = directory / (prefix + name)
    require(not path.is_symlink() and path.is_file(), "missing or nonregular Yul evidence: " + prefix + name)
    if path.stat().st_size > limit:
        raise common.Finding("inconclusive-resource", "yul-evidence", "Yul evidence exceeds artifact limit: " + prefix + name)
    return path


def validate_export(directory, contract, expected_hull_provenance, limit, prefix=""):
    """Bind saved EVM bytes to both the exact solc response and checked Hull."""
    paths = {name: file_path(directory, name, limit, prefix) for name in FILES}
    artifact = common.read_json(paths[ARTIFACT], limit)
    exporter.validate_artifact(artifact, contract)
    record = common.read_json(paths[PROVENANCE], limit)
    require(isinstance(record, dict) and set(record) == {"schema", "upstreamCommit", "backend", "selectedObject",
        "runtimeObject", "exporterSha256", "outputSha256", "compiler", "toolBuild", "hullProvenance", "sources",
        "commands", "artifacts", "scope"}, "unexpected Yul provenance fields")
    require(record["schema"] == exporter.SCHEMA and record["upstreamCommit"] == common.UPSTREAM_COMMIT and
            record["backend"] == BACKEND and record["selectedObject"] == artifact["selectedObject"] and
            record["runtimeObject"] == contract and valid_hash(record["exporterSha256"]) and
            record["outputSha256"] == common.file_digest(paths[ARTIFACT]), "Yul provenance differs from its artifact")
    require(type(record["backend"]["optimizer"]["enabled"]) is bool, "invalid Yul optimizer setting")
    inventory = record["artifacts"]
    require(isinstance(inventory, dict) and set(inventory) == set(EVIDENCE), "Yul evidence inventory is incomplete or unknown")
    for key, name in EVIDENCE.items():
        entry = inventory[key]
        require(isinstance(entry, dict) and set(entry) == {"file", "sha256"} and entry["file"] == prefix + name and
                valid_hash(entry["sha256"]) and entry["sha256"] == common.file_digest(paths[name]),
                "Yul evidence filename or hash differs: " + key)
    expected = expected_hull_provenance
    require(isinstance(expected, dict) and expected.get("schema") == exporter.hull.SCHEMA and
            expected.get("upstreamCommit") == common.UPSTREAM_COMMIT and valid_hash(expected.get("outputSha256")) and
            valid_hash(expected.get("binarySha256")) and isinstance(expected.get("patches"), dict) and
            expected["patches"] and all(valid_hash(value) for value in expected["patches"].values()) and
            isinstance(expected.get("sources"), dict) and expected["sources"] and
            all(valid_hash(value) for value in expected["sources"].values()), "invalid main checked Hull provenance")
    main_hull = file_path(directory, MAIN_FILES[0], limit, prefix)
    main_receipt = file_path(directory, MAIN_FILES[1], limit, prefix)
    require(common.file_digest(main_hull) == expected["outputSha256"] and
            common.read_json(main_receipt, limit) == expected, "main Hull bytes or on-disk provenance changed")
    hp = common.read_json(paths[EVIDENCE["hullProvenance"]], limit)
    require(hp == expected and record["hullProvenance"] == expected and record["sources"] == expected["sources"] and
            common.file_digest(paths[EVIDENCE["hull"]]) == expected["outputSha256"],
            "Yul checked Hull, sources or compiler provenance differs from the main Hull export")
    exporter.validate_hull(common.read_json(paths[EVIDENCE["hull"]], limit), contract)
    require(record["toolBuild"] == {"upstreamCommit": common.UPSTREAM_COMMIT, "patches": expected["patches"],
            "binarySha256": expected["binarySha256"]}, "Yul Rust compiler build differs from checked Hull")
    compiler = record["compiler"]
    require(isinstance(compiler, dict) and set(compiler) == {"path", "sha256", "versionOutput"} and
            isinstance(compiler["path"], str) and Path(compiler["path"]).is_absolute() and
            valid_hash(compiler["sha256"]) and isinstance(compiler["versionOutput"], str), "invalid solc identity")
    exporter.validate_version(compiler["versionOutput"])
    commands = record["commands"]
    require(isinstance(commands, dict) and set(commands) == {"hull", "yul", "solc"} and
            all(isinstance(command, list) and command and all(isinstance(item, str) for item in command)
                for command in commands.values()) and commands["solc"] == [compiler["path"], "--standard-json"],
            "invalid Yul compiler commands")
    checked_command = expected.get("command")
    require(isinstance(checked_command, list) and checked_command.count("--emit-hull") == 1,
            "missing checked Hull driver command")
    position = checked_command.index("--emit-hull")
    expected_command = checked_command[:position] + ["--emit-yul", "--emit-yul-object", contract + "Deploy"] + checked_command[position + 1:]
    require(commands["yul"] == expected_command, "Yul driver command differs from checked Hull compilation")
    yul = paths[EVIDENCE["yul"]].read_text()
    request = common.read_json(paths[EVIDENCE["solcInput"]], limit)
    require(common.json_bytes(request) == common.json_bytes(exporter.standard_input(yul)),
            "saved solc request changed its Yul, compiler settings or output selection")
    response = common.read_json(paths[EVIDENCE["solcOutput"]], limit)
    require(exporter.artifact_from_output(response, contract) == artifact,
            "Yul EVM bytes differ from the saved solc output")
    return record


def validate_tool_record(record, tools):
    require(isinstance(tools, dict) and tools.get("yulExporterSha256") == record["exporterSha256"] and
            valid_hash(tools.get("yulTransportSha256")), "Yul exporter or transport identity differs from report")
    compiler = tools.get("solc")
    require(isinstance(compiler, dict) and compiler.get("sha256") == record["compiler"]["sha256"] and
            isinstance(compiler.get("version"), str) and compiler["version"] == record["compiler"]["versionOutput"].strip(),
            "solc binary or full version differs from report")


def used_yul_execution(report):
    require(isinstance(report.get("rawObservations", {}), dict) and isinstance(report.get("observations", {}), dict) and
            isinstance(report.get("histories", {}), dict), "malformed saved execution observations")
    return ("rustEvm" in report.get("rawObservations", {}) or "rustEvm" in report.get("observations", {}) or
            "rustEvm" in report.get("histories", {}) or "evmDeployment" in report or "executionContext" in report)


def validate_archive(directory, report, limit):
    """Validate accepted exports without resolving a relocated archive's old URLs."""
    require(isinstance(report, dict) and report.get("backend") == "yul", "not a Yul execution archive")
    saved = report.get("yulExportProvenance")
    if saved is None:
        require("yulExportProvenance" not in report and not used_yul_execution(report),
                "Yul execution archive is missing its accepted export provenance")
        return None  # Compilation or an earlier resource failure can leave partial files.
    require(report.get("pathBackends") == PATH_BACKENDS, "Yul archive relabelled an execution path")
    inventory = report.get("artifacts")
    require(isinstance(inventory, dict), "missing Yul archive artifact inventory")
    for name in FILES + MAIN_FILES:
        path = file_path(directory, name, limit)
        require(valid_hash(inventory.get(name)) and inventory[name] == common.file_digest(path),
                "archive omits or changes Yul evidence: " + name)
    case = common.read_json(directory / "case.json", limit)
    validate_case(case)
    provenance = report.get("exportProvenance", {})
    require(isinstance(provenance, dict), "missing main Hull export provenance")
    record = validate_export(directory, case["contract"]["name"], provenance.get("hull"), limit)
    require(record == saved, "saved Yul provenance differs from its sidecar")
    validate_tool_record(record, report.get("tools"))
    return record


def execute(args, runner, case, source, hull_path, report, previous=None):
    """Export the replay-checked case; the caller executes the returned bytes."""
    validate_case(case)
    require(report.get("backend") == "yul" and report.get("pathBackends") == PATH_BACKENDS,
            "Yul EVM export requires explicitly separated execution paths")
    contract = case["contract"]["name"]
    exporter.validate_contract(contract)
    runner.guard()
    require(hull_path == args.output / MAIN_FILES[0], "Yul export requires the main hull.json artifact")
    hp = common.read_json(hull_path.with_suffix(hull_path.suffix + ".provenance.json"), args.artifact_limit)
    require(hp == report.get("exportProvenance", {}).get("hull"), "main Hull receipt changed before Yul export")
    require(hp.get("sources", {}).get(source.as_uri()) == common.file_digest(source), "entry source changed before Yul export")
    command = [sys.executable, str(ROOT / "scripts/export-rust-yul.py"), str(source), "--output", str(args.output / ARTIFACT),
        "--contract", contract, "--solc", str(args.solc), "--root", str(args.output), "--upstream", str(args.upstream),
        "--target-dir", str(args.target_dir), "--timeout", str(args.timeout), "--output-limit", str(min(args.artifact_limit, 64 * 1024**2))]
    common.checked_process(runner, "rust-yul-evm", command, args.timeout * 3)
    runner.guard()
    record = validate_export(args.output, contract, hp, args.artifact_limit)
    validate_tool_record(record, report.get("tools"))
    require(record["exporterSha256"] == common.file_digest(ROOT / "scripts/export-rust-yul.py") and
            report["tools"]["yulTransportSha256"] == common.file_digest(Path(__file__)), "Yul tools changed during export")
    report["yulExportProvenance"] = record
    if previous is not None:
        old = previous.get("yulExportProvenance")
        if old is None:
            require("yulExportProvenance" not in previous and not used_yul_execution(previous),
                    "saved Yul execution is missing provenance")
        else:
            require(isinstance(old, dict) and isinstance(old.get("compiler"), dict), "malformed saved Yul compiler provenance")
            for key in ("backend", "exporterSha256", "toolBuild", "outputSha256"):
                if old.get(key) != record[key]:
                    raise common.Finding("adapter-error", "replay", "Yul " + key + " changed since the saved run")
            if (old.get("compiler", {}).get("sha256") != record["compiler"]["sha256"] or
                    old.get("compiler", {}).get("versionOutput", "").strip() != record["compiler"]["versionOutput"].strip()):
                raise common.Finding("adapter-error", "replay", "solc binary or full version changed since the saved run")
    artifact = common.read_json(args.output / ARTIFACT, args.artifact_limit)
    return common.hex_bytes(artifact["initCode"], "Yul init code"), common.hex_bytes(artifact["runtimeCode"], "Yul runtime code")
