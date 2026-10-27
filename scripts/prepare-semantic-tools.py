#!/usr/bin/env python3
"""Prepare the pinned semantic-comparison tools, or verify them without writes.

System prerequisites are installed separately: Python >=3.11, Git, rustup with
Rust 1.97.0, elan with Lean 4.33.1, and Anvil 1.5.1. Nothing here installs
system tools. Network access is enabled only by --prepare --allow-network.
The exporter-owned crate and Cargo target live under this checkout's .upstream.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
COMMIT = "2a745e12974c373c3799fec81b48a53c7dce2ab4"
REPOSITORY = "https://github.com/argotorg/solcore-rs.git"
RUST = "1.97.0"
LEAN = "leanprover/lean4:v4.33.1"
SCHEMA = "solcore-lean.semantic-tools.v1"
TARGETS = {
    "semanticCaseTool": "semantic-case-tool",
    "semanticStorageTool": "semantic-storage-tool",
    "semanticStorageRollbackTool": "semantic-storage-rollback-tool",
    "semanticCallTool": "semantic-call-tool",
    "rustHullScenario": "rust-hull-scenario",
    "rustHullContract": "rust-hull-contract",
    "rustHullStorageScenario": "rust-hull-storage-scenario",
    "rustHullCallScenario": "rust-hull-call-scenario",
    "semanticKeyedStorageTool": "semantic-keyed-storage-tool",
    "rustHullKeyedStorageScenario": "rust-hull-keyed-storage-scenario",
    "semanticDynamicArrayTool": "semantic-dynamic-array-tool",
    "semanticMalformedCalldataTool": "semantic-malformed-calldata-tool",
    "semanticEventLogTool": "semantic-log-tool",
    "semanticCallValueTool": "semantic-call-value-tool",
    "rustHullValueScenario": "rust-hull-value-scenario",
    "semanticBytesTool": "semantic-bytes-tool",
    "semanticForwardTool": "semantic-forward-tool",
    "rustHullForwardScenario": "rust-hull-forward-scenario",
    "semanticMappingTool": "semantic-mapping-tool",
    "semanticLedgerTool": "semantic-ledger-tool",
    "rustHullLedgerScenario": "rust-hull-ledger-scenario",
    "semanticLongBytesTool": "semantic-long-bytes-tool",
    "semanticNestedArrayTool": "semantic-nested-array-tool",
}
PATCHES = {
    "crates/driver/src/main.rs": ("mod emit;", "mod emit;\nmod lean_export;"),
    "crates/driver/src/emit.rs": ("&hull::pretty_program(db, &program)", "&crate::lean_export::export(db, &program)"),
}
SERIALIZER = "crates/driver/src/lean_export.rs"


class NotReady(ValueError):
    pass


def digest(path: Path) -> str:
    if not path.is_file() or path.is_symlink():
        raise NotReady(f"missing or symlinked file: {path}")
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def bytes_digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def no_symlinks(path: Path) -> Path:
    path = Path(os.path.abspath(path))
    if any(part.is_symlink() for part in [path, *path.parents]):
        raise NotReady(f"symlinked managed path: {path}")
    return path


def managed(path: Path, root: Path) -> Path:
    path = no_symlinks(path)
    base = no_symlinks(root / ".upstream")
    if not path.is_relative_to(base) or path == base:
        raise NotReady(f"managed path must be strictly inside {base}: {path}")
    return path


def load_exporter(root: Path):
    spec = importlib.util.spec_from_file_location("semantic_prepare_images", root / "scripts/export-rust-code-image.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    if module.hull.COMMIT != COMMIT:
        raise NotReady("bootstrap/exporter revision mismatch")
    return module


def cleanup_process_group(process: subprocess.Popen) -> None:
    """Reap our leader and stop surviving descendants, without an unbounded wait.

    macOS can report EPERM after an empty group disappears. Never broaden the
    target in response: signal only this session's group and its owned leader.
    """
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(process.pid, sig)
        except (ProcessLookupError, PermissionError):
            if process.poll() is None:
                try:
                    process.send_signal(sig)
                except (ProcessLookupError, PermissionError):
                    pass
        try:
            process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            pass
    if process.poll() is None:
        raise NotReady("could not terminate the owned subprocess within the cleanup deadline")


def cargo_cache_empty(target: Path) -> bool:
    """Only a truly empty destination can omit Cargo's own cache marker."""
    if not target.exists() or not any(target.iterdir()):
        return True
    marker = no_symlinks(target / "CACHEDIR.TAG")
    if not marker.is_file():
        raise NotReady(f"nonempty Cargo target has no cache marker; refusing cleanup: {target}")
    with marker.open("rb") as stream:
        signature = stream.read(43)
    if signature != b"Signature: 8a477f597d28d172789f06886806bc55":
        raise NotReady(f"nonempty Cargo target has an invalid cache marker; refusing cleanup: {target}")
    return False


class Runner:
    def __init__(self, timeout: float):
        self.deadline = time.monotonic() + timeout
        self.env = os.environ.copy()
        self.env.update({"RUSTUP_TOOLCHAIN": RUST, "RUSTUP_AUTO_INSTALL": "0",
                         "ELAN_TOOLCHAIN": LEAN, "GIT_TERMINAL_PROMPT": "0",
                         "CARGO_NET_OFFLINE": "true"})
        self.env.setdefault("CARGO_INCREMENTAL", "0")
        self.env.setdefault("CARGO_PROFILE_DEV_DEBUG", "0")

    def run(self, command, cwd: Path, *, network=False, capture=True, limit=None):
        remaining = self.deadline - time.monotonic()
        if remaining <= 0:
            raise NotReady("preparation time budget exhausted")
        timeout = min(remaining, limit) if limit else remaining
        env = dict(self.env, CARGO_NET_OFFLINE="false" if network else "true")
        # Temporary streams bound memory and disappear even after interruption.
        with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
            process = subprocess.Popen(list(map(str, command)), cwd=cwd, env=env,
                                       stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr,
                                       start_new_session=True)
            try:
                process.wait(timeout=timeout)
                if process.returncode:
                    stderr.seek(0, os.SEEK_END)
                    stderr.seek(max(0, stderr.tell() - 8000))
                    raise NotReady(f"command failed ({process.returncode}): {command}\n{stderr.read().decode(errors='replace')}")
                if not capture:
                    return ""
                stdout.seek(0)
                result = stdout.read(4 * 1024 * 1024 + 1)
                if len(result) > 4 * 1024 * 1024:
                    raise NotReady(f"command output exceeds 4 MiB: {command}")
                return result.decode()
            except subprocess.TimeoutExpired as error:
                raise NotReady(f"command exceeded the preparation time budget: {command}") from error
            finally:
                # Also run after a failed leader has exited: descendants may remain.
                cleanup_process_group(process)



def tool_versions(runner: Runner, root: Path, anvil: Path) -> dict:
    if (root / "lean-toolchain").read_text().strip() != LEAN:
        raise NotReady(f"repository requires a different Lean toolchain than {LEAN}")
    # These queries do not install a missing toolchain. Check elan's inventory
    # before asking its proxy to resolve an executable.
    installed = runner.run(["elan", "toolchain", "list"], root, limit=30)
    if LEAN not in [row.split()[0] for row in installed.splitlines() if row.split()]:
        raise NotReady(f"install {LEAN} separately before preparation")
    paths = {}
    for name in ("cargo", "rustc"):
        paths[name] = Path(runner.run(["rustup", "which", "--toolchain", RUST, name], root, limit=30).strip())
    for name in ("lean", "lake"):
        paths[name] = Path(runner.run(["elan", "which", name], root, limit=30).strip())
    paths["anvil"] = anvil.resolve()
    versions = {name: runner.run([path, "--version"], root, limit=30).strip() for name, path in paths.items()}
    for name in ("cargo", "rustc"):
        if not re.match(rf"^{name} {re.escape(RUST)}(?:\s|$)", versions[name]):
            raise NotReady(f"expected {name} {RUST}: {versions[name]}")
    if not re.search(r"\bversion 4\.33\.1(?:[,\s]|$)", versions["lean"], re.I):
        raise NotReady(f"expected Lean 4.33.1: {versions['lean']}")
    # The stable channel and the v1.5.1 tag build report different suffixes for
    # the same release; foundry-toolchain installs the latter.
    if not re.search(r"^anvil Version: 1\.5\.1(?:-stable|-v1\.5\.1)?(?:\s|$)", versions["anvil"]):
        raise NotReady(f"expected Anvil 1.5.1: {versions['anvil']}")
    runner.env["PATH"] = os.pathsep.join([str(paths["cargo"].parent), str(paths["lean"].parent), runner.env.get("PATH", "")])
    result = {name: {"version": versions[name], "sha256": digest(path)} for name, path in paths.items()}
    result["buildEnvironment"] = {name: runner.env.get(name, "") for name in (
        "CARGO_INCREMENTAL", "CARGO_PROFILE_DEV_DEBUG", "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CC", "CFLAGS")}
    return result


def git(runner: Runner, upstream: Path, *args: str) -> str:
    return runner.run(["git", "-C", upstream, *args], upstream.parent, limit=60)


def checkout(runner: Runner, upstream: Path, allow_network: bool) -> None:
    if (upstream / ".git").exists():
        if git(runner, upstream, "rev-parse", "HEAD").strip() != COMMIT:
            raise NotReady("existing upstream checkout has a different revision; refusing to reset it")
        return
    if upstream.exists() and (not upstream.is_dir() or any(upstream.iterdir())):
        raise NotReady("new upstream destination must be absent or empty")
    if not allow_network:
        raise NotReady("pinned checkout is missing; explicit --prepare --allow-network is required to fetch it")
    upstream.mkdir(parents=True, exist_ok=True)
    runner.run(["git", "init", upstream], upstream.parent)
    runner.run(["git", "-C", upstream, "remote", "add", "origin", REPOSITORY], upstream.parent)
    runner.run(["git", "-C", upstream, "fetch", "--depth", "1", "origin", COMMIT], upstream.parent, network=True)
    runner.run(["git", "-C", upstream, "checkout", "--detach", COMMIT], upstream.parent)
    if git(runner, upstream, "rev-parse", "HEAD").strip() != COMMIT:
        raise NotReady("fetched checkout does not have the required exact revision")


def inspect_checkout(runner: Runner, root: Path, upstream: Path, *, patched: bool, old_serializer: str | None = None) -> dict:
    if git(runner, upstream, "rev-parse", "HEAD").strip() != COMMIT:
        raise NotReady("upstream revision mismatch")
    changed = set(git(runner, upstream, "diff", "--name-only", "HEAD").splitlines())
    untracked = set(git(runner, upstream, "ls-files", "--others", "--exclude-standard").splitlines())
    if changed - PATCHES.keys() or untracked - {SERIALIZER}:
        raise NotReady(f"unrelated upstream changes: {sorted((changed - PATCHES.keys()) | (untracked - {SERIALIZER}))}")
    hashes = {}
    for name, (old, new) in PATCHES.items():
        original = git(runner, upstream, "show", f"{COMMIT}:{name}")
        if original.count(old) != 1:
            raise NotReady(f"exporter injection point changed: {name}")
        expected = original.replace(old, new)
        actual = no_symlinks(upstream / name).read_text()
        if actual != expected and (patched or actual != original):
            raise NotReady(f"unexpected upstream patch: {name}")
        hashes[name] = bytes_digest(expected.encode())
    expected = digest(root / "scripts/rust-hull-export.rs")
    if (upstream / SERIALIZER).exists() or patched:
        actual = digest(upstream / SERIALIZER)
        if actual != expected and (patched or actual != old_serializer):
            raise NotReady("upstream serializer differs from the current exporter and its prior receipt")
    hashes[SERIALIZER] = expected
    return hashes


def materialize_image_tool(root: Path, upstream: Path, exporter) -> None:
    tool = managed(exporter.TOOL, root)
    if tool.exists():
        allowed = {"Cargo.toml", "Cargo.lock", "src", "src/main.rs"}
        for path in tool.rglob("*"):
            if path.is_symlink() or path.relative_to(tool).as_posix() not in allowed:
                raise NotReady(f"unrelated file in exporter-owned crate: {path}")
    (tool / "src").mkdir(parents=True, exist_ok=True)
    # Only these generated files are replaced; no cache directory is deleted.
    (tool / "Cargo.toml").write_text(exporter.MANIFEST)
    (tool / "src/main.rs").write_bytes(exporter.SOURCE.read_bytes())
    (tool / "Cargo.lock").write_bytes((upstream / "Cargo.lock").read_bytes())


def native_input_hash(root: Path) -> str:
    paths = [root / name for name in ("Solcore.lean", "lakefile.lean", "lean-toolchain", "lake-manifest.json")]
    for directory in ("Solcore", "Tests"):
        paths.extend((root / directory).rglob("*.lean"))
    value = hashlib.sha256()
    for path in sorted(paths):
        value.update(path.relative_to(root).as_posix().encode() + b"\0" + digest(path).encode() + b"\n")
    return value.hexdigest()


def inventory(root: Path, upstream: Path, target: Path, versions: dict, patches: dict, exporter) -> dict:
    cargo_cache_empty(target)
    driver = json.loads((target / "lean-export-build.json").read_text())
    if driver != {"upstreamCommit": COMMIT, "patches": patches,
                  "binarySha256": digest(target / "debug/solcore-driver")}:
        raise NotReady("checked Hull build receipt is stale")
    if (exporter.TOOL / "Cargo.toml").read_text() != exporter.MANIFEST or digest(exporter.TOOL / "src/main.rs") != digest(exporter.SOURCE):
        raise NotReady("generated code-image crate differs from its exporter")
    exporter.check_pins(upstream)
    image = json.loads((target / "code-image-export-build.json").read_text())
    expected = {"upstreamCommit": COMMIT, "backendRevision": exporter.BACKEND,
                **exporter.tool_hashes(), "binarySha256": digest(target / "debug/solcore-code-image-export")}
    if image != expected:
        raise NotReady("code-image build receipt is stale")
    binaries = {name: digest(root / ".lake/build/bin" / binary) for name, binary in TARGETS.items()}
    scripts = {name: digest(root / "scripts" / name) for name in (
        "prepare-semantic-tools.py", "export-rust-hull.py", "rust-hull-export.rs",
        "export-rust-code-image.py", "rust-code-image-export.rs")}
    return {"schema": SCHEMA, "upstreamCommit": COMMIT, "backendRevision": exporter.BACKEND,
            "upstreamLockSha256": digest(upstream / "Cargo.lock"), "hardfork": "osaka",
            "tools": versions, "exporterInputs": scripts, "driverBuild": driver,
            "imageBuild": image, "nativeInputsSha256": native_input_hash(root), "nativeBinaries": binaries}


def verify(runner: Runner, root: Path, upstream: Path, target: Path, versions: dict, exporter) -> dict:
    patches = inspect_checkout(runner, root, upstream, patched=True)
    actual = inventory(root, upstream, target, versions, patches, exporter)
    recorded = json.loads((target / "semantic-tools-build.json").read_text())
    if recorded != actual:
        raise NotReady("semantic tools cache receipt is stale; run --prepare to rebuild authorized outputs")
    return actual


def build(runner: Runner, root: Path, upstream: Path, target: Path, versions: dict, exporter, network: bool) -> dict:
    checkout(runner, upstream, network)
    try:
        previous = json.loads((target / "lean-export-build.json").read_text())
        old_serializer = previous.get("patches", {}).get(SERIALIZER)
    except (ValueError, OSError, AttributeError):
        old_serializer = None
    inspect_checkout(runner, root, upstream, patched=False, old_serializer=old_serializer)
    if cargo_cache_empty(target):
        # Cargo 1.97 writes CACHEDIR.TAG only when it creates the target itself.
        # rmdir is atomic and refuses a directory that gained any contents.
        if target.exists():
            target.rmdir()
        target.parent.mkdir(parents=True, exist_ok=True)
    # First fetch the upstream's immutable lock. The generated crate initially
    # has a copied workspace lock without its own root package. Resolve that
    # root OFFLINE, validate all external pins, then fetch the resulting lock.
    command = ["cargo", "fetch", "--locked", "--manifest-path", upstream / "Cargo.toml"]
    runner.run(command + ([] if network else ["--offline"]), root, network=network, capture=False)
    materialize_image_tool(root, upstream, exporter)
    manifest = exporter.TOOL / "Cargo.toml"
    runner.run(["cargo", "metadata", "--offline", "--format-version", "1", "--manifest-path", manifest], root, capture=False)
    exporter.check_pins(upstream)
    command = ["cargo", "fetch", "--locked", "--manifest-path", manifest]
    runner.run(command + ([] if network else ["--offline"]), root, network=network, capture=False)
    # Cargo may otherwise reuse a modified binary whose fingerprint is fresh.
    # Invalidate only our two executable packages when their old receipt cannot
    # authenticate them; never clean all dependencies or an upstream checkout.
    for package, receipt, package_manifest in (
            ("solcore-driver", "lean-export-build.json", upstream / "Cargo.toml"),
            ("solcore-code-image-export", "code-image-export-build.json", manifest)):
        try:
            recorded = json.loads((target / receipt).read_text())
            valid = isinstance(recorded, dict) and recorded.get("binarySha256") == digest(target / "debug" / package)
        except (ValueError, OSError):
            valid = False
        if not valid and not cargo_cache_empty(target):
            runner.run(["cargo", "clean", "--frozen", "--manifest-path", package_manifest,
                        "--target-dir", target, "-p", package], root, capture=False)
    for script in ("export-rust-hull.py", "export-rust-code-image.py"):
        runner.run([sys.executable, root / "scripts" / script, "--build", "--upstream", upstream,
                    "--target-dir", target], root, capture=False)
    runner.run(["lake", "--no-cache", "--rehash", "build", *TARGETS], root, capture=False)
    actual = inventory(root, upstream, target, versions,
                       inspect_checkout(runner, root, upstream, patched=True), exporter)
    receipt = target / "semantic-tools-build.json"
    no_symlinks(receipt)
    with tempfile.NamedTemporaryFile(mode="w", dir=target, prefix="semantic-tools-", suffix=".tmp", delete=False) as stream:
        temporary = Path(stream.name)
        try:
            stream.write(json.dumps(actual, indent=2, sort_keys=True) + "\n")
            stream.flush()
            os.replace(temporary, receipt)
        finally:
            temporary.unlink(missing_ok=True)
    return actual


def configuration(args, root: Path, exporter):
    upstream, target = managed(args.upstream, root), managed(args.target_dir, root)
    tool = managed(exporter.TOOL, root)
    for first, second in ((upstream, target), (upstream, tool), (target, tool)):
        if first.is_relative_to(second) or second.is_relative_to(first):
            raise NotReady("upstream checkout, Cargo target and generated crate must be separate directories")
    for name in ("debug", "debug/solcore-driver", "debug/solcore-code-image-export",
                 "lean-export-build.json", "code-image-export-build.json", "semantic-tools-build.json"):
        no_symlinks(target / name)
    for name in ("Cargo.toml", "Cargo.lock", "src/main.rs"):
        no_symlinks(tool / name)
    return upstream, target


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--prepare", action="store_true", help="rebuild stale authorized outputs, fetching only with --allow-network")
    modes.add_argument("--verify", action="store_true", help="read-only readiness check (default)")
    modes.add_argument("--plan", action="store_true", help="print required versions and ordered operations without running tools")
    parser.add_argument("--allow-network", action="store_true")
    parser.add_argument("--upstream", type=Path, default=ROOT / ".upstream/solcore-rs-20261023")
    parser.add_argument("--target-dir", type=Path, default=ROOT / ".upstream/rust-parity-target")
    parser.add_argument("--anvil", type=Path, default=Path(shutil.which("anvil") or "anvil"))
    parser.add_argument("--timeout", type=float, default=3600, help="total preparation deadline in seconds")
    args = parser.parse_args(argv)
    if args.allow_network and not args.prepare:
        parser.error("--allow-network requires --prepare")
    if not 0 < args.timeout <= 14400:
        parser.error("--timeout must be positive and at most 14400 seconds")
    previous = signal.getsignal(signal.SIGTERM)
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    try:
        exporter = load_exporter(ROOT)
        upstream, target = configuration(args, ROOT, exporter)
        if args.plan:
            print(json.dumps({"schema": SCHEMA, "mode": "plan", "network": False,
                "required": {"rust": RUST, "lean": LEAN, "anvil": "1.5.1", "hardfork": "osaka"},
                "upstream": str(upstream), "commit": COMMIT, "target": str(target),
                "generatedCrate": str(exporter.TOOL), "lakeTargets": list(TARGETS),
                "operations": ["validate installed tools", "fetch exact commit into empty destination when explicitly enabled",
                    "cargo fetch --locked (upstream)", "materialize generated exporter crate",
                    "cargo metadata --offline (normalize generated lock)", "check all dependency pins against upstream",
                    "cargo fetch --locked (generated crate)", "offline exporter builds", "one Lake build", "hash readiness receipt"]}, indent=2))
            return 0
        runner = Runner(args.timeout)
        versions = tool_versions(runner, ROOT, args.anvil)
        cache_hit = True
        try:
            verify(runner, ROOT, upstream, target, versions, exporter)
        except (ValueError, OSError, subprocess.SubprocessError) as error:
            if not args.prepare:
                raise NotReady(str(error)) from error
            cache_hit = False
            build(runner, ROOT, upstream, target, versions, exporter, args.allow_network)
        print(json.dumps({"schema": SCHEMA, "status": "ready", "cacheHit": cache_hit,
                          "receipt": str(target / "semantic-tools-build.json"), "nativeTools": len(TARGETS)}))
        return 0
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(json.dumps({"schema": SCHEMA, "status": "not-ready", "detail": str(error)}), file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print(json.dumps({"schema": SCHEMA, "status": "interrupted"}), file=sys.stderr)
        return 130
    finally:
        signal.signal(signal.SIGTERM, previous)


if __name__ == "__main__":
    raise SystemExit(main())
