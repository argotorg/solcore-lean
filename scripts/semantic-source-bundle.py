#!/usr/bin/env python3
"""Integrity and relocation of the fixed four-file semantic source bundle.

Hull span provenance is not a complete import inventory. All generated files
and the pinned standard-library sources are therefore checked independently.
This module validates transport only; native case replay authenticates the
source contents and their fixed import/export graph against the original Core.
"""
from __future__ import annotations

import hashlib
from pathlib import Path
import re
from urllib.parse import unquote, urlparse

SCHEMA = "solcore-lean.source-bundle.v1"
RECEIPT_SCHEMA = "solcore-lean.source-bundle-receipt.v1"
FILES = ("case.sol", "common.sol", "left.sol", "right.sol")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def valid_hash(value) -> bool:
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def validate(case: dict) -> dict[str, str]:
    bundle = case.get("sourceBundle")
    if (not isinstance(bundle, dict) or set(bundle) != {"schema", "entry", "files"}
            or bundle.get("schema") != SCHEMA or bundle.get("entry") != "case.sol"):
        raise ValueError("unsupported source bundle schema or entry")
    rows = bundle.get("files")
    if (not isinstance(rows, list) or len(rows) != len(FILES)
            or any(not isinstance(row, dict) or set(row) != {"path", "source"}
                   or not isinstance(row["source"], str) for row in rows)
            or tuple(row["path"] for row in rows) != FILES):
        raise ValueError("source bundle requires the four canonical sorted file names")
    files = {row["path"]: row["source"] for row in rows}
    if case.get("source") != files["case.sol"]:
        raise ValueError("source bundle entry differs from its source alias")
    return files


def hashes(case: dict) -> dict[str, str]:
    return {name: digest(source.encode()) for name, source in validate(case).items()}


def audit_files(directory: Path, expected: dict[str, str]) -> None:
    """The exporter root is flat and contains exactly the admitted .sol files."""
    for path in directory.iterdir():
        if path.is_symlink() or path.is_dir():
            raise ValueError("source bundle root cannot contain symlinks or directories")
        if path.suffix.lower() == ".sol" and path.name not in FILES:
            raise ValueError("source bundle root contains an unlisted source file")
    for name in FILES:
        path = directory / name
        if not path.is_file() or path.is_symlink() or digest(path.read_bytes()) != expected[name]:
            raise ValueError("source bundle file changed or is missing: " + name)


def write(directory: Path, case: dict) -> dict:
    files = validate(case)
    for path in directory.iterdir():
        if path.is_symlink() or path.is_dir() or path.suffix.lower() == ".sol":
            raise ValueError("source bundle must be written into a fresh flat source root")
    for name, source in files.items():
        with (directory / name).open("xb") as target:
            target.write(source.encode())
    expected = hashes(case)
    audit_files(directory, expected)
    return {"schema": RECEIPT_SCHEMA, "files": expected,
            "generatedUris": {(directory / name).resolve().as_uri(): name for name in FILES}}


def canonical_uri(url: str) -> Path:
    if not isinstance(url, str):
        raise ValueError("source provenance requires a canonical file URI")
    parsed = urlparse(url)
    path = Path(unquote(parsed.path))
    if (parsed.scheme != "file" or parsed.netloc or parsed.query or parsed.fragment
            or not path.is_absolute() or ".." in path.parts or "\x00" in str(path) or path.as_uri() != url):
        raise ValueError("source provenance requires a canonical file URI")
    return path


def library_files(upstream: Path, tracked: list[str]) -> dict[str, str]:
    """Only canonical tracked .sol files below the pinned std root are admitted."""
    root = upstream / "std"
    if root.is_symlink() or root.resolve() != root:
        raise ValueError("standard-library root must be canonical")
    names = set(tracked)
    if len(names) != len(tracked) or not names:
        raise ValueError("missing or duplicated tracked standard-library sources")
    paths = set()
    result = {}
    for name in sorted(names):
        path = upstream / name
        if (not name.startswith("std/") or path.suffix != ".sol" or not path.is_file()
                or path.is_symlink() or path.resolve() != path or not path.is_relative_to(root)):
            raise ValueError("invalid tracked standard-library source")
        paths.add(path)
        result[path.as_uri()] = digest(path.read_bytes())
    actual = set(root.rglob("*.sol"))
    if actual != paths or any(path.is_symlink() for path in root.rglob("*")):
        raise ValueError("standard-library sources differ from the tracked source inventory")
    return result


def validate_receipt(receipt: dict, case: dict) -> None:
    if (not isinstance(receipt, dict) or set(receipt) != {"schema", "files", "generatedUris", "libraries"}
            or receipt.get("schema") != RECEIPT_SCHEMA or receipt.get("files") != hashes(case)):
        raise ValueError("saved source bundle receipt differs from its canonical case")
    uris = receipt.get("generatedUris")
    if (not isinstance(uris, dict) or len(uris) != len(FILES)
            or any(not isinstance(name, str) for name in uris.values())
            or sorted(uris.values()) != list(FILES)):
        raise ValueError("saved source bundle URI inventory is incomplete or duplicated")
    parents = set()
    for uri, name in uris.items():
        path = canonical_uri(uri)
        if path.name != name:
            raise ValueError("saved generated URI does not name its canonical file")
        parents.add(path.parent)
    if len(parents) != 1:
        raise ValueError("saved generated URIs must share one source root")
    libraries = receipt.get("libraries")
    if not isinstance(libraries, dict) or not libraries or set(libraries) & set(uris):
        raise ValueError("saved standard-library inventory is missing or overlaps generated sources")
    for uri, expected in libraries.items():
        canonical_uri(uri)
        if not valid_hash(expected):
            raise ValueError("invalid standard-library source hash")


def normalized_sources(sources: dict, receipt: dict, case: dict) -> dict:
    """Do not resolve saved generated URLs: their former directory may be gone."""
    validate_receipt(receipt, case)
    if not isinstance(sources, dict):
        raise ValueError("source provenance must be an object")
    generated, libraries = {}, {}
    for uri, expected in sources.items():
        canonical_uri(uri)
        if not valid_hash(expected):
            raise ValueError("invalid source provenance hash")
        if uri in receipt["generatedUris"]:
            name = receipt["generatedUris"][uri]
            if name in generated or receipt["files"][name] != expected:
                raise ValueError("generated source provenance changed or collided")
            generated[name] = expected
        elif uri in receipt["libraries"]:
            if receipt["libraries"][uri] != expected:
                raise ValueError("standard-library provenance changed")
            libraries[uri] = expected
        else:
            raise ValueError("export contains a source outside the generated bundle and pinned library")
    if generated.get("case.sol") != receipt["files"]["case.sol"]:
        raise ValueError("export is missing the bundle entry provenance")
    return {"files": receipt["files"], "libraries": receipt["libraries"],
            "observedGenerated": generated, "observedLibraries": libraries}


def verify_archive(directory: Path, case: dict, report: dict) -> None:
    receipt = report.get("sourceBundleReceipt")
    validate_receipt(receipt, case)
    audit_files(directory, hashes(case))
    artifacts = report.get("artifacts", {})
    for name, expected in receipt["files"].items():
        if artifacts.get(name) != expected:
            raise ValueError("saved archive omits a canonical source bundle file: " + name)
    sources = report.get("exportProvenance", {}).get("hull", {}).get("sources")
    if sources is not None:
        normalized_sources(sources, receipt, case)
