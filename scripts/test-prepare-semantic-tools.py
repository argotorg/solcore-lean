#!/usr/bin/env python3
"""Filesystem and orchestration policy tests; these do not validate real compiler builds."""
from __future__ import annotations
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import types
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("prepare_semantic_tools", ROOT / "scripts/prepare-semantic-tools.py")
prep = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prep)


class FakeRunner:
    def __init__(self, fixture=None):
        self.fixture = fixture
        self.calls = []
        self.env = {"PATH": "/bin", "CARGO_INCREMENTAL": "0", "CARGO_PROFILE_DEV_DEBUG": "0"}
        self.version_override = {}

    def run(self, command, cwd, **options):
        command = list(map(str, command))
        self.calls.append((command, Path(cwd), options))
        fixture = self.fixture
        if command[:3] == ["elan", "toolchain", "list"]:
            return self.version_override.get("installed", prep.LEAN + "\n")
        if command[:2] == ["rustup", "which"] or command[:2] == ["elan", "which"]:
            return str(fixture.root / "installed" / command[-1]) + "\n"
        if command[-1:] == ["--version"]:
            name = Path(command[0]).name
            return self.version_override.get(name, {
                "cargo": "cargo 1.97.0 (test)", "rustc": "rustc 1.97.0 (test)",
                "lean": "Lean (version 4.33.1, test)", "lake": "Lake version 5.0.0 (Lean version 4.33.1)",
                "anvil": "anvil Version: 1.5.1-stable\nCommit SHA: test"}[name])
        if command[0] == "git":
            if command[-2:] == ["rev-parse", "HEAD"]:
                return fixture.head + "\n"
            if "--name-only" in command:
                return "\n".join(fixture.changed)
            if "ls-files" in command:
                return "\n".join(fixture.untracked)
            if "show" in command:
                return fixture.original[command[-1].split(":", 1)[1]]
        return ""


class Fixture:
    def __init__(self, root):
        self.root = root
        self.upstream = root / ".upstream/upstream"
        self.target = root / ".upstream/target"
        self.tool = root / ".upstream/rust-code-image-tool"
        self.head = prep.COMMIT
        self.changed = list(prep.PATCHES)
        self.untracked = [prep.SERIALIZER]
        self.original = {name: "// original\n" + old + "\n" for name, (old, _) in prep.PATCHES.items()}
        for path in (self.upstream / ".git", self.target / "debug", self.tool / "src", root / "installed", root / "Solcore", root / "Tests", root / "scripts", root / ".lake/build/bin"):
            path.mkdir(parents=True, exist_ok=True)
        for name in ("cargo", "rustc", "lean", "lake", "anvil"):
            (root / "installed" / name).write_text("test executable " + name)
        (self.target / "CACHEDIR.TAG").write_text("Signature: 8a477f597d28d172789f06886806bc55\n# Cargo cache fixture\n")
        (root / "lean-toolchain").write_text(prep.LEAN + "\n")
        (root / "Solcore.lean").write_text("-- test umbrella\n")
        (root / "lakefile.lean").write_text("-- test configuration\n")
        (root / "lake-manifest.json").write_text('{}')
        (root / "Solcore/A.lean").write_text("-- test source\n")
        for name in ("prepare-semantic-tools.py", "export-rust-hull.py", "rust-hull-export.rs", "export-rust-code-image.py", "rust-code-image-export.rs"):
            (root / "scripts" / name).write_text("fixture " + name)
        for name, (old, new) in prep.PATCHES.items():
            path = self.upstream / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(self.original[name].replace(old, new))
        (self.upstream / prep.SERIALIZER).write_bytes((root / "scripts/rust-hull-export.rs").read_bytes())
        (self.upstream / "Cargo.lock").write_text("test pinned lock")
        (self.upstream / "Cargo.toml").write_text("test upstream manifest")
        (self.tool / "Cargo.toml").write_text("test generated manifest")
        (self.tool / "Cargo.lock").write_text("test generated lock")
        (self.tool / "src/main.rs").write_bytes((root / "scripts/rust-code-image-export.rs").read_bytes())
        for binary in prep.TARGETS.values():
            (root / ".lake/build/bin" / binary).write_text("fixture native " + binary)
        for binary in ("solcore-driver", "solcore-code-image-export"):
            (self.target / "debug" / binary).write_text("fixture exporter " + binary)
        self.exporter = types.SimpleNamespace(TOOL=self.tool, SOURCE=root / "scripts/rust-code-image-export.rs",
            MANIFEST="test generated manifest", BACKEND="test backend", check_pins=lambda upstream: None)
        self.exporter.tool_hashes = lambda: {"sourceSha256": prep.digest(self.exporter.SOURCE),
            "manifestSha256": prep.bytes_digest(self.exporter.MANIFEST.encode()), "lockSha256": prep.digest(self.tool / "Cargo.lock")}
        self.runner = FakeRunner(self)
        self.versions = prep.tool_versions(self.runner, root, root / "installed/anvil")
        self.patches = prep.inspect_checkout(self.runner, root, self.upstream, patched=True)
        self.write_exporter_receipts()
        self.record = prep.inventory(root, self.upstream, self.target, self.versions, self.patches, self.exporter)
        (self.target / "semantic-tools-build.json").write_text(json.dumps(self.record))
        self.runner.calls.clear()

    def write_exporter_receipts(self):
        (self.target / "lean-export-build.json").write_text(json.dumps({"upstreamCommit": prep.COMMIT,
            "patches": self.patches, "binarySha256": prep.digest(self.target / "debug/solcore-driver")}))
        (self.target / "code-image-export-build.json").write_text(json.dumps({"upstreamCommit": prep.COMMIT,
            "backendRevision": self.exporter.BACKEND, **self.exporter.tool_hashes(),
            "binarySha256": prep.digest(self.target / "debug/solcore-code-image-export")}))

    def verify(self):
        return prep.verify(self.runner, self.root, self.upstream, self.target, self.versions, self.exporter)


class BootstrapTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        self.f = Fixture(self.root)

    def tearDown(self):
        self.temp.cleanup()

    def test_verify_is_read_only_and_invokes_only_local_git_queries(self):
        before = {p.relative_to(self.root): (p.read_bytes(), p.stat().st_mtime_ns) for p in self.root.rglob('*') if p.is_file()}
        self.assertEqual(self.f.verify(), self.f.record)
        self.assertTrue(all(call[0][0] == 'git' and not call[2].get('network') for call in self.f.runner.calls))
        after = {p.relative_to(self.root): (p.read_bytes(), p.stat().st_mtime_ns) for p in self.root.rglob('*') if p.is_file()}
        self.assertEqual(before, after)

    def test_native_and_exporter_tamper_are_not_ready(self):
        for path in [self.root / '.lake/build/bin/semantic-case-tool', self.f.target / 'debug/solcore-driver', self.f.target / 'debug/solcore-code-image-export']:
            original = path.read_bytes()
            path.write_bytes(original + b'changed')
            with self.assertRaises(prep.NotReady): self.f.verify()
            path.write_bytes(original)

    def test_source_toolchain_lock_and_script_changes_invalidate_receipt(self):
        for path in [self.root / 'Solcore.lean', self.root / 'Solcore/A.lean', self.f.upstream / 'Cargo.lock', self.root / 'scripts/export-rust-hull.py']:
            original = path.read_bytes()
            path.write_bytes(original + b'changed')
            with self.assertRaises(prep.NotReady): self.f.verify()
            path.write_bytes(original)
        self.f.versions['rustc']['version'] = 'changed compiler'
        with self.assertRaises(prep.NotReady): self.f.verify()

    def test_missing_native_or_readiness_receipt_is_not_ready(self):
        for path in [self.root / '.lake/build/bin/rust-hull-contract', self.f.target / 'semantic-tools-build.json']:
            original = path.read_bytes(); path.unlink()
            with self.assertRaises((OSError, prep.NotReady)): self.f.verify()
            path.write_bytes(original)

    def test_wrong_installed_versions_never_install(self):
        for name, value in [('installed', 'some-other-toolchain'), ('rustc', 'rustc 1.98.0'), ('cargo', 'cargo 1.96.0'), ('lean', 'Lean (version 4.33.0)'), ('anvil', 'anvil Version: 1.5.1-nightly')]:
            runner = FakeRunner(self.f); runner.version_override[name] = value
            with self.assertRaises(prep.NotReady): prep.tool_versions(runner, self.root, self.root / 'installed/anvil')
            self.assertFalse(any('install' in call[0] for call in runner.calls))

    def test_checkout_refuses_wrong_revision_and_unrelated_modifications(self):
        self.f.head = 'wrong'
        with self.assertRaises(prep.NotReady): prep.checkout(self.f.runner, self.f.upstream, True)
        self.f.head = prep.COMMIT
        for field in ['changed', 'untracked']:
            old = getattr(self.f, field); setattr(self.f, field, old + ['unrelated.rs'])
            with self.assertRaises(prep.NotReady): prep.inspect_checkout(self.f.runner, self.root, self.f.upstream, patched=False)
            setattr(self.f, field, old)
        self.assertFalse(any('reset' in c[0] or 'clean' in c[0] for c in self.f.runner.calls))

    def test_serializer_update_requires_its_prior_receipt(self):
        path = self.f.upstream / prep.SERIALIZER
        path.write_text('old generated serializer')
        with self.assertRaises(prep.NotReady): prep.inspect_checkout(self.f.runner, self.root, self.f.upstream, patched=False)
        prep.inspect_checkout(self.f.runner, self.root, self.f.upstream, patched=False, old_serializer=prep.digest(path))
        with self.assertRaises(prep.NotReady): prep.inspect_checkout(self.f.runner, self.root, self.f.upstream, patched=True, old_serializer=prep.digest(path))

    def test_fresh_fetch_is_explicit_exact_and_only_into_empty_directory(self):
        destination = self.root / '.upstream/new'
        with self.assertRaises(prep.NotReady): prep.checkout(self.f.runner, destination, False)
        self.assertFalse(destination.exists())
        prep.checkout(self.f.runner, destination, True)
        calls = self.f.runner.calls
        fetch = [c for c in calls if 'fetch' in c[0]]
        self.assertEqual(len(fetch), 1)
        self.assertEqual(fetch[0][0][-4:], ['--depth', '1', 'origin', prep.COMMIT])
        self.assertTrue(fetch[0][2]['network'])
        (destination / 'user.txt').write_text('do not overwrite')
        with self.assertRaises(prep.NotReady): prep.checkout(self.f.runner, destination, True)
        self.assertEqual((destination / 'user.txt').read_text(), 'do not overwrite')

    def test_paths_must_be_separate_inside_upstream_and_not_symlinked(self):
        for upstream, target in [(self.root / 'outside', self.f.target), (self.f.upstream, self.f.upstream / 'target'), (self.f.upstream, self.f.tool)]:
            with self.assertRaises(prep.NotReady): prep.configuration(types.SimpleNamespace(upstream=upstream, target_dir=target), self.root, self.f.exporter)
        (self.f.target / 'semantic-tools-build.json').unlink()
        (self.f.target / 'semantic-tools-build.json').symlink_to(self.root / 'foreign.json')
        with self.assertRaises(prep.NotReady): prep.configuration(types.SimpleNamespace(upstream=self.f.upstream, target_dir=self.f.target), self.root, self.f.exporter)

    def test_generated_crate_only_replaces_owned_files(self):
        path = self.f.tool / 'notes.txt'; path.write_text('keep')
        with self.assertRaises(prep.NotReady): prep.materialize_image_tool(self.root, self.f.upstream, self.f.exporter)
        self.assertEqual(path.read_text(), 'keep'); path.unlink()
        prep.materialize_image_tool(self.root, self.f.upstream, self.f.exporter)
        self.assertEqual((self.f.tool / 'Cargo.lock').read_bytes(), (self.f.upstream / 'Cargo.lock').read_bytes())
        self.assertEqual((self.f.tool / 'src/main.rs').read_bytes(), self.f.exporter.SOURCE.read_bytes())

    def test_build_plan_normalizes_offline_then_checks_pins_before_locked_fetch(self):
        events = []
        original_run = self.f.runner.run
        def run(command, cwd, **kwargs):
            events.append(('command', list(map(str, command)), kwargs))
            return original_run(command, cwd, **kwargs)
        self.f.runner.run = run
        self.f.exporter.check_pins = lambda upstream: events.append(('pins',))
        # This tests orchestration only. Inventory is a fixture, not a compiler success claim.
        with patch.object(prep, 'inventory', return_value=self.f.record):
            prep.build(self.f.runner, self.root, self.f.upstream, self.f.target, self.f.versions, self.f.exporter, True)
        metadata = next(i for i,e in enumerate(events) if len(e)>1 and e[1][:2]==['cargo','metadata'])
        self.assertIn('--offline', events[metadata][1])
        pins = next(i for i,e in enumerate(events) if e[0]=='pins')
        self.assertGreater(pins, metadata)
        fetch = [e for e in events if len(e)>1 and e[1][:2]==['cargo','fetch']]
        self.assertEqual(len(fetch),2)
        self.assertTrue(all('--locked' in e[1] and e[2]['network'] for e in fetch))
        self.assertLess(pins, next(i for i,e in enumerate(events) if e is fetch[1]))
        builders = [e for e in events if len(e)>1 and '--build' in e[1]]
        self.assertEqual(len(builders),2)
        self.assertTrue(all('--allow-network' not in e[1] and not e[2].get('network') for e in builders))
        lakes = [e[1] for e in events if len(e)>1 and e[1][0]=='lake']
        self.assertEqual(lakes, [['lake','--no-cache','--rehash','build',*prep.TARGETS]])

    def test_offline_prepare_never_fetches_network(self):
        with patch.object(prep, 'inventory', return_value=self.f.record):
            prep.build(self.f.runner, self.root, self.f.upstream, self.f.target, self.f.versions, self.f.exporter, False)
        self.assertFalse(any(c[2].get('network') for c in self.f.runner.calls))
        self.assertTrue(all('--offline' in c[0] for c in self.f.runner.calls if c[0][:2]==['cargo','fetch']))

    def test_corrupt_root_binary_cleans_only_its_owned_package(self):
        (self.f.target / 'debug/solcore-driver').write_text('corrupted')
        with patch.object(prep, 'inventory', return_value=self.f.record):
            prep.build(self.f.runner, self.root, self.f.upstream, self.f.target, self.f.versions, self.f.exporter, False)
        cleaned = [c[0] for c in self.f.runner.calls if c[0][:2]==['cargo','clean']]
        self.assertEqual(len(cleaned),1)
        self.assertEqual(cleaned[0][-2:], ['-p','solcore-driver'])
        self.assertIn('--frozen',cleaned[0])
        self.assertTrue((self.root / 'Solcore/A.lean').exists())

    def test_pin_mismatch_aborts_before_exporter_build(self):
        def mismatch(_): raise prep.NotReady('dependency pin changed')
        self.f.exporter.check_pins = mismatch
        with self.assertRaisesRegex(prep.NotReady,'pin changed'):
            prep.build(self.f.runner, self.root, self.f.upstream, self.f.target, self.f.versions, self.f.exporter, True)
        self.assertFalse(any('--build' in c[0] for c in self.f.runner.calls))

    def test_plan_performs_no_subprocess_and_network_requires_prepare(self):
        with patch.object(prep, 'ROOT', self.root), patch.object(prep, 'load_exporter', return_value=self.f.exporter), patch.object(prep.Runner,'run',side_effect=AssertionError('unexpected tool execution')), contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(prep.main(['--plan','--upstream',str(self.f.upstream),'--target-dir',str(self.f.target)]),0)
            self.assertEqual(json.loads(output.getvalue())['mode'],'plan')
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit): prep.main(['--allow-network','--verify'])

    def test_main_cache_hit_does_not_prepare_or_fetch(self):
        with patch.object(prep, 'ROOT', self.root), patch.object(prep, 'load_exporter', return_value=self.f.exporter), patch.object(prep, 'tool_versions', return_value=self.f.versions), patch.object(prep, 'verify', return_value=self.f.record), patch.object(prep, 'build', side_effect=AssertionError('cache hit rebuilt')), contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(prep.main(['--prepare','--allow-network','--upstream',str(self.f.upstream),'--target-dir',str(self.f.target)]),0)
            self.assertTrue(json.loads(output.getvalue())['cacheHit'])

    def test_main_stale_cache_rebuilds_only_with_explicit_prepare(self):
        args=['--upstream',str(self.f.upstream),'--target-dir',str(self.f.target)]
        with patch.object(prep, 'ROOT', self.root), patch.object(prep, 'load_exporter', return_value=self.f.exporter), patch.object(prep, 'tool_versions', return_value=self.f.versions), patch.object(prep, 'verify', side_effect=prep.NotReady('stale')), patch.object(prep, 'build', return_value=self.f.record) as builder, contextlib.redirect_stdout(io.StringIO()) as output, contextlib.redirect_stderr(io.StringIO()) as errors:
            self.assertEqual(prep.main(['--verify',*args]),2)
            builder.assert_not_called()
            self.assertEqual(json.loads(errors.getvalue())['status'],'not-ready')
            self.assertEqual(prep.main(['--prepare',*args]),0)
            builder.assert_called_once()
            self.assertFalse(builder.call_args.args[-1])
            self.assertFalse(json.loads(output.getvalue())['cacheHit'])

    def test_failed_build_does_not_issue_a_new_ready_receipt(self):
        receipt=self.f.target/'semantic-tools-build.json'
        original=receipt.read_bytes()
        with patch.object(prep,'inventory',side_effect=prep.NotReady('post-build verification failed')):
            with self.assertRaises(prep.NotReady):
                prep.build(self.f.runner,self.root,self.f.upstream,self.f.target,self.f.versions,self.f.exporter,False)
        self.assertEqual(receipt.read_bytes(),original)
        self.assertEqual(list(self.f.target.glob('semantic-tools-*.tmp')),[])

    def test_malformed_exporter_receipt_cleans_only_the_owned_binary_package(self):
        (self.f.target/'lean-export-build.json').write_text('[]')
        with patch.object(prep,'inventory',return_value=self.f.record):
            prep.build(self.f.runner,self.root,self.f.upstream,self.f.target,self.f.versions,self.f.exporter,False)
        clean=[c[0] for c in self.f.runner.calls if c[0][:2]==['cargo','clean']]
        self.assertEqual([c[-1] for c in clean],['solcore-driver'])

    def test_absent_and_empty_targets_are_created_by_cargo_not_bootstrap(self):
        for precreated in (False,True):
            target=self.root/('.upstream/fresh-'+str(precreated))
            if precreated: target.mkdir()
            runner=FakeRunner(self.f)
            original_run=runner.run
            export_calls=[]
            def run(command,cwd,**options):
                if '--build' in command:
                    export_calls.append(command)
                    if len(export_calls)==1:
                        self.assertFalse(target.exists(),'bootstrap precreated Cargo target')
                        # Simulate the exporter/Cargo creating its directory;
                        # this test does not claim compilation was performed.
                        target.mkdir()
                        (target/'CACHEDIR.TAG').write_text('created by simulated Cargo')
                return original_run(command,cwd,**options)
            runner.run=run
            with patch.object(prep,'inventory',return_value=self.f.record):
                prep.build(runner,self.root,self.f.upstream,target,self.f.versions,self.f.exporter,False)
            self.assertFalse(any(c[0][:2]==['cargo','clean'] for c in runner.calls))
            self.assertEqual((target/'CACHEDIR.TAG').read_text(),'created by simulated Cargo')
            self.assertEqual(len(export_calls),2)

    def test_nonempty_target_requires_a_real_cargo_cache_marker(self):
        marker=self.f.target/'CACHEDIR.TAG'
        for invalid in (None,b'not a Cargo cache',b'Signature: invalid'):
            if invalid is None: marker.unlink(missing_ok=True)
            else: marker.write_bytes(invalid)
            self.f.runner.calls.clear()
            with self.assertRaisesRegex(prep.NotReady,'cache marker'):
                prep.build(self.f.runner,self.root,self.f.upstream,self.f.target,self.f.versions,self.f.exporter,False)
            self.assertFalse(any(c[0][0]=='cargo' for c in self.f.runner.calls))
            self.assertTrue((self.f.target/'debug/solcore-driver').is_file())

    def test_empty_group_permission_race_does_not_replace_success(self):
        with patch.object(prep.os,'killpg',side_effect=PermissionError('empty macOS group')):
            output=prep.Runner(5).run([sys.executable,'-c','print("ready")'],self.root)
        self.assertEqual(output,'ready\n')

    def test_group_permission_race_preserves_primary_failure(self):
        with patch.object(prep.os,'killpg',side_effect=PermissionError('empty macOS group')):
            with self.assertRaisesRegex(prep.NotReady,r'command failed \(7\)'):
                prep.Runner(5).run([sys.executable,'-c','raise SystemExit(7)'],self.root)

    def test_group_denial_falls_back_to_bounded_owned_leader_signals(self):
        from unittest.mock import Mock
        leader=Mock(pid=12345)
        leader.poll.side_effect=[None,None,0]
        leader.wait.side_effect=[subprocess.TimeoutExpired('child',2),0]
        with patch.object(prep.os,'killpg',side_effect=PermissionError('denied')):
            prep.cleanup_process_group(leader)
        self.assertEqual([c.args[0] for c in leader.send_signal.call_args_list],[signal.SIGTERM,signal.SIGKILL])
        self.assertTrue(all(c.kwargs=={'timeout':2} for c in leader.wait.call_args_list))

    def test_real_failed_leader_stops_its_surviving_descendant(self):
        pidfile=self.root/'descendant.pid'
        fifo=self.root/'descendant.pipe'
        os.mkfifo(fifo)
        descriptor=os.open(fifo,os.O_RDONLY|os.O_NONBLOCK)
        child='import os,time;from pathlib import Path;fd=os.open('+repr(str(fifo))+',os.O_WRONLY);Path('+repr(str(pidfile))+').write_text(str(os.getpid()));time.sleep(60)'
        leader='import subprocess,sys,time;from pathlib import Path;p=subprocess.Popen([sys.executable,"-c",'+repr(child)+']);deadline=time.monotonic()+3\nwhile not Path('+repr(str(pidfile))+').exists() and time.monotonic()<deadline:time.sleep(.01)\nraise SystemExit(7)'
        try:
            with self.assertRaisesRegex(prep.NotReady,r'command failed \(7\)'):
                prep.Runner(5).run([sys.executable,'-c',leader],self.root)
            self.assertTrue(pidfile.exists())
            # EOF proves the descendant closed its own writer, even if it is
            # briefly a zombie. No process enumeration or unrelated signals.
            eof=False
            deadline=time.monotonic()+3
            while time.monotonic()<deadline:
                try:
                    eof=os.read(descriptor,1)==b''
                    break
                except BlockingIOError:
                    time.sleep(.02)
            self.assertTrue(eof,'descendant still holds its writer after leader failure')
        finally:
            os.close(descriptor)
            if pidfile.exists():
                try: os.kill(int(pidfile.read_text()),signal.SIGKILL)
                except ProcessLookupError: pass

    def test_real_timed_out_child_is_terminated_and_logs_removed(self):
        pidfile=self.root/'child.pid'
        code='import os,time; from pathlib import Path; Path('+repr(str(pidfile))+').write_text(str(os.getpid())); time.sleep(60)'
        with self.assertRaisesRegex(prep.NotReady,'time budget'):
            prep.Runner(0.3).run([sys.executable,'-c',code],self.root)
        pid=int(pidfile.read_text())
        with self.assertRaises(ProcessLookupError): os.kill(pid,0)
        self.assertEqual(list(self.root.glob('*.log')),[])

    def test_real_sigterm_unwinds_active_child(self):
        child_pid=self.root/'child.pid'
        harness=self.root/'interrupt.py'
        harness.write_text('import importlib.util,sys\n' +
            'spec=importlib.util.spec_from_file_location("prep",'+repr(str(ROOT/'scripts/prepare-semantic-tools.py'))+')\n'+
            'p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)\n'+
            'p.load_exporter=lambda _: object()\np.configuration=lambda *args:(p.ROOT,p.ROOT)\n'+
            'def active(runner,*args):\n'+
            ' runner.run([sys.executable,"-c",'+repr('import os,time;from pathlib import Path;Path('+repr(str(child_pid))+').write_text(str(os.getpid()));time.sleep(60)')+'],p.ROOT)\n'+
            'p.tool_versions=active\nraise SystemExit(p.main(["--verify"]))\n')
        process=subprocess.Popen([sys.executable,str(harness)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                                 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
        try:
            deadline=time.monotonic()+5
            while not child_pid.exists() and time.monotonic()<deadline: time.sleep(.02)
            self.assertTrue(child_pid.exists())
            process.send_signal(signal.SIGTERM)
            stdout,stderr=process.communicate(timeout=5)
            self.assertEqual(process.returncode,130,stderr)
            self.assertEqual(json.loads(stderr)['status'],'interrupted')
            with self.assertRaises(ProcessLookupError): os.kill(int(child_pid.read_text()),0)
        finally:
            if process.poll() is None: process.kill();process.wait()


if __name__ == '__main__':
    unittest.main()
