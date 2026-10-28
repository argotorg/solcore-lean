#!/usr/bin/env python3
"""Yul artifact protocol tests; policy JSON fixtures are not compiler executions."""
import copy
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
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("yul_export_policy", ROOT / "scripts/export-rust-yul.py")
exporter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exporter)
CONTRACT = "SynthesizedG0"


def solc_output(contract=CONTRACT):
    return {"contracts": {"checked.yul": {contract + "Deploy": {"evm": {
        "bytecode": {"object": "600000", "linkReferences": {}},
        "deployedBytecode": {"object": "00", "linkReferences": {}, "immutableReferences": {}}}}}},
        "sources": {"checked.yul": {"id": 0, "ast": {"nodeType": "YulObject", "name": contract + "Deploy",
            "subObjects": [{"nodeType": "YulObject", "name": contract, "subObjects": []}]}}}}


def hull_output(contract=CONTRACT):
    return {"schema": exporter.hull.SCHEMA, "upstreamCommit": exporter.hull.COMMIT,
            "program": {"objects": [{"name": contract + "Deploy", "inners": [{"name": contract, "inners": []}]}]}}


class YulProtocolTests(unittest.TestCase):
    def test_pure_and_storage_family_wrappers_are_admitted_but_call_wrappers_are_not(self):
        self.assertEqual(len(exporter.PURE_CONTRACTS), 23)
        self.assertEqual(len(exporter.STORAGE_CONTRACTS), 21)
        self.assertEqual(len(set(exporter.CONTRACTS)), 44)
        self.assertEqual(exporter.CONTRACTS, exporter.PURE_CONTRACTS + exporter.STORAGE_CONTRACTS)
        self.assertIn("SynthesizedAssembly", exporter.PURE_CONTRACTS)
        self.assertIn("SynthesizedRecursiveLoops", exporter.PURE_CONTRACTS)
        self.assertIn("SynthesizedLoopClosures", exporter.PURE_CONTRACTS)
        self.assertIn("SynthesizedAssemblyLoops", exporter.PURE_CONTRACTS)
        self.assertIn("SynthesizedAssemblyMemory", exporter.PURE_CONTRACTS)
        self.assertIn("SynthesizedEnums", exporter.PURE_CONTRACTS)
        self.assertIn("SynthesizedTraits", exporter.PURE_CONTRACTS)
        self.assertIn("SynthesizedRecursion", exporter.CONTRACTS)
        self.assertIn("SynthesizedNestedLoops", exporter.CONTRACTS)
        self.assertIn("SynthesizedPrimitives", exporter.CONTRACTS)
        self.assertIn("SynthesizedCallGraphs", exporter.CONTRACTS)
        self.assertIn("SynthesizedCallGraphLoops", exporter.CONTRACTS)
        self.assertIn("SynthesizedAggregateCallGraphs", exporter.CONTRACTS)
        # Both allow-lists are derived from the case profiles, not maintained separately.
        self.assertEqual(exporter.PURE_CONTRACTS, tuple(exporter.common.CASE_CONTRACTS.values()))
        self.assertEqual(len(exporter.storage.PROFILES), 24)
        self.assertEqual(set(exporter.STORAGE_CONTRACTS), {value["contract"] for value in exporter.storage.PROFILES.values()})
        # The three malformed-calldata profiles reuse the dynamic-array, nested-array and long-bytes wrappers.
        self.assertEqual({value["contract"] for name, value in exporter.storage.PROFILES.items() if "malformed" in name},
                         {"SynthesizedDynamicArray", "SynthesizedNestedArray", "SynthesizedLongBytes"})
        for contract in ("SynthesizedStorage", "SynthesizedRollback", "SynthesizedLedger", "SynthesizedMethods",
                         "SynthesizedAssemblyStorageLoops", "SynthesizedAssemblyKeccakLoops",
                         "SynthesizedStorageLoops", "SynthesizedTupleReturns", "SynthesizedBytesReturns",
                         "SynthesizedAdtStorage", "SynthesizedEnumReturns", "SynthesizedEnumArguments"):
            self.assertIn(contract, exporter.STORAGE_CONTRACTS)
        for contract in exporter.CONTRACTS:
            exporter.validate_contract(contract)
        # The call profiles' parent and child contracts are not admitted.
        for contract in ("Root", "SynthesizedCaller", "SynthesizedCallee", "SynthesizedForwarder", "SynthesizedRecipient",
                         "SynthesizedStorageDeploy", "synthesizedstorage", None):
            with self.assertRaises(ValueError):
                exporter.validate_contract(contract)
        # Near misses of the new wrapper name are not admitted either.
        for contract in ("SynthesizedAggregateCallGraph", "SynthesizedAggregateCallGraphsDeploy",
                         "synthesizedaggregatecallgraphs", "SynthesizedAggregateCallGraphs ", ""):
            with self.assertRaises(ValueError):
                exporter.validate_contract(contract)

    def test_aggregate_call_graph_wrapper_has_its_own_checked_objects_and_cli_choice(self):
        contract = "SynthesizedAggregateCallGraphs"
        artifact = exporter.artifact_from_output(solc_output(contract), contract)
        self.assertEqual((artifact["selectedObject"], artifact["runtimeObject"]), (contract + "Deploy", contract))
        exporter.validate_artifact(artifact, contract)
        exporter.validate_hull(hull_output(contract), contract)
        # A neighbouring wrapper's objects, artifact or checked Hull cannot be exported under this name, nor the reverse.
        for other in (CONTRACT, "SynthesizedCallGraphs", "SynthesizedCallGraphLoops", "SynthesizedAggregates"):
            with self.subTest(other=other):
                with self.assertRaises(ValueError):
                    exporter.artifact_from_output(solc_output(other), contract)
                with self.assertRaises(ValueError):
                    exporter.artifact_from_output(solc_output(contract), other)
                with self.assertRaises(ValueError):
                    exporter.validate_artifact(exporter.artifact_from_output(solc_output(other), other), contract)
                with self.assertRaises(ValueError):
                    exporter.validate_artifact(artifact, other)
                with self.assertRaises(ValueError):
                    exporter.validate_hull(hull_output(other), contract)
                with self.assertRaises(ValueError):
                    exporter.validate_hull(hull_output(contract), other)
        arguments = ["policy.sol", "--output", "policy.json", "--solc", "/policy/solc"]
        self.assertEqual(exporter.parse_args([*arguments, "--contract", contract]).contract, contract)
        for rejected in ("SynthesizedCaller", "SynthesizedAggregateCallGraph"):
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                exporter.parse_args([*arguments, "--contract", rejected])

    def test_storage_family_wrappers_keep_one_creation_runtime_pair_and_record_their_scope(self):
        arguments = ["policy.sol", "--output", "policy.json", "--solc", "/policy/solc"]
        for contract in exporter.STORAGE_CONTRACTS:
            with self.subTest(contract=contract):
                artifact = exporter.artifact_from_output(solc_output(contract), contract)
                self.assertEqual((artifact["selectedObject"], artifact["runtimeObject"]), (contract + "Deploy", contract))
                exporter.validate_artifact(artifact, contract)
                exporter.validate_hull(hull_output(contract), contract)
                self.assertEqual(exporter.parse_args([*arguments, "--contract", contract]).contract, contract)
                self.assertEqual(exporter.scope(contract), "generated two-object wrapper shape; caller validates canonical "
                                 "storage-family case; EVM bytes only; no Hull linker map")
                # A nested child object, a second runtime object or a second deployment object is still refused.
                nested = solc_output(contract)
                nested["sources"]["checked.yul"]["ast"]["subObjects"][0]["subObjects"] = [
                    {"nodeType": "YulObject", "name": "Child", "subObjects": []}]
                second = solc_output(contract)
                second["sources"]["checked.yul"]["ast"]["subObjects"].append({"nodeType": "YulObject", "name": "Other", "subObjects": []})
                for output in (nested, second):
                    with self.assertRaises(ValueError):
                        exporter.artifact_from_output(output, contract)
                two = hull_output(contract)
                two["program"]["objects"].append({"name": "SynthesizedCalleeDeploy", "inners": [{"name": "SynthesizedCallee", "inners": []}]})
                inner = hull_output(contract)
                inner["program"]["objects"][0]["inners"][0]["inners"] = [{"name": "Child", "inners": []}]
                for document in (two, inner):
                    with self.assertRaises(ValueError):
                        exporter.validate_hull(document, contract)
                linked = solc_output(contract)
                linked["contracts"]["checked.yul"][contract + "Deploy"]["evm"]["deployedBytecode"]["immutableReferences"] = {"1": []}
                with self.assertRaises(ValueError):
                    exporter.artifact_from_output(linked, contract)
        self.assertEqual(exporter.scope(CONTRACT), "generated two-object wrapper shape; caller validates canonical pure case; "
                         "EVM bytes only; no Hull linker map")
        with self.assertRaises(ValueError):
            exporter.scope("SynthesizedCaller")

    def test_only_pinned_release_accepts_linux_and_macos_suffixes(self):
        for suffix in ('', '.Linux.g++', '.Darwin.appleclang'):
            exporter.validate_version('solc, the solidity compiler commandline interface\nVersion: ' + exporter.SOLC_VERSION + suffix + '\n')
        for version in ('0.8.34+commit.47b9dedd.Linux.g++', '0.8.35+commit.deadbeef',
                        '0.8.35+commit.47b9dedd0', '0.8.35+commit.47b9dedd-develop', ''):
            with self.assertRaises(ValueError):
                exporter.validate_version('Version: ' + version)
        with self.assertRaises(ValueError):
            exporter.validate_version(('Version: ' + exporter.SOLC_VERSION + '\n') * 2)

    def test_one_compilation_supplies_both_artifact_bytecodes(self):
        artifact = exporter.artifact_from_output(solc_output(), CONTRACT)
        self.assertEqual(artifact['initCode'], '0x600000')
        self.assertEqual(artifact['runtimeCode'], '0x00')
        self.assertEqual(artifact['backend'], exporter.BACKEND)
        self.assertNotIn('images', artifact)
        self.assertNotIn('offset', json.dumps(artifact))
        exporter.validate_artifact(artifact, CONTRACT)
        self.assertEqual(exporter.standard_input('policy Yul')['settings']['optimizer'], {'enabled': True})
        self.assertEqual(exporter.standard_input('policy Yul')['settings']['evmVersion'], 'osaka')
        # solc's Yul output-selection path requires ast in the contract selector.
        self.assertIn('ast', exporter.standard_input('policy Yul')['settings']['outputSelection']['*']['*'])

    def test_artifact_requires_exact_backend_and_bytecode_encoding(self):
        artifact = exporter.artifact_from_output(solc_output(), CONTRACT)
        for key, value in (('schema', 'other'), ('upstreamCommit', 'other'), ('selectedObject', 'Root'),
                           ('runtimeObject', 'Other'), ('extra', None), ('backend', {}),
                           ('initCode', '0x'), ('runtimeCode', '0x0'), ('runtimeCode', '0xAB'),
                           ('runtimeCode', '0x__$link$__'), ('runtimeCode', '0x00' * 24577)):
            with self.assertRaises(ValueError):
                exporter.validate_artifact({**artifact, key: value}, CONTRACT)
        for key in artifact:
            document = copy.deepcopy(artifact)
            del document[key]
            with self.assertRaises(ValueError):
                exporter.validate_artifact(document, CONTRACT)
        for value in (False, 1, 'true'):
            document = copy.deepcopy(artifact)
            document['backend']['optimizer']['enabled'] = value
            with self.assertRaises(ValueError):
                exporter.validate_artifact(document, CONTRACT)
        document = copy.deepcopy(artifact)
        document['runtimeCode'] = '0x' + '00' * 24577
        with self.assertRaisesRegex(ValueError, 'size limit'):
            exporter.validate_artifact(document, CONTRACT)

    def test_rejects_missing_runtime_or_external_references(self):
        for section, field in (('bytecode', 'linkReferences'), ('deployedBytecode', 'linkReferences'),
                               ('deployedBytecode', 'immutableReferences')):
            output = solc_output()
            output['contracts']['checked.yul'][CONTRACT + 'Deploy']['evm'][section][field] = {'reference': []}
            with self.assertRaises(ValueError):
                exporter.artifact_from_output(output, CONTRACT)
        for field in ('deployedBytecode', 'bytecode'):
            output = solc_output()
            del output['contracts']['checked.yul'][CONTRACT + 'Deploy']['evm'][field]
            with self.assertRaises(ValueError):
                exporter.artifact_from_output(output, CONTRACT)

    def test_unknown_output_inventory_or_diagnostics_rejected(self):
        for key, value in (('contracts', {}), ('sources', {}), ('unknown', None), ('errors', {}),
                           ('errors', [{'severity': 'info'}])):
            with self.assertRaises(ValueError):
                exporter.artifact_from_output({**solc_output(), key: value}, CONTRACT)
        output = solc_output()
        output['contracts']['foreign.yul'] = {}
        with self.assertRaises(ValueError):
            exporter.artifact_from_output(output, CONTRACT)
        output = solc_output()
        output['contracts']['checked.yul']['Foreign'] = {}
        with self.assertRaises(ValueError):
            exporter.artifact_from_output(output, CONTRACT)
        with self.assertRaisesRegex(ValueError, 'preserved diagnostic'):
            exporter.artifact_from_output({**solc_output(), 'errors': [{'severity': 'error', 'formattedMessage': 'preserved diagnostic'}]}, CONTRACT)
        exporter.artifact_from_output({**solc_output(), 'errors': [{'severity': 'warning', 'message': 'policy warning'}]}, CONTRACT)

    def test_checked_and_solc_object_shapes_reject_nested_or_other_children(self):
        exporter.validate_hull(hull_output(), CONTRACT)
        for child in ([], [{'name': 'Other', 'inners': []}], [{'name': CONTRACT, 'inners': [{}]}]):
            output = hull_output()
            output['program']['objects'][0]['inners'] = child
            with self.assertRaises(ValueError):
                exporter.validate_hull(output, CONTRACT)
        for program in (None, [], {}, {'objects': []}):
            with self.assertRaises(ValueError):
                exporter.validate_hull({**hull_output(), 'program': program}, CONTRACT)
        for field, value in (('subObjects', []), ('name', 'Other'), ('nodeType', 'YulData')):
            output = solc_output()
            output['sources']['checked.yul']['ast'][field] = value
            with self.assertRaises(ValueError):
                exporter.artifact_from_output(output, CONTRACT)
        output = solc_output()
        output['sources']['checked.yul']['ast']['subObjects'][0]['subObjects'] = [{}]
        with self.assertRaises(ValueError):
            exporter.artifact_from_output(output, CONTRACT)

    def test_real_process_helper_bounds_output_time_and_preserves_error_text(self):
        args = SimpleNamespace(timeout=2, output_limit=1024)
        command = [sys.executable, '-c', "import sys;sys.stdout.buffer.write(sys.stdin.buffer.read())"]
        self.assertEqual(exporter.run_process(command, args, stdin=b'actual bytes'), b'actual bytes')
        with self.assertRaisesRegex(ValueError, 'output limit'):
            exporter.run_process([sys.executable, '-c', "print('x'*2048)"], args)
        with self.assertRaisesRegex(ValueError, 'panicked at policy-process'):
            exporter.run_process([sys.executable, '-c', "import sys;sys.stderr.write('panicked at policy-process');sys.exit(3)"], args)
        with self.assertRaisesRegex(ValueError, 'internal compiler error: process terminated by signal'):
            exporter.run_process([sys.executable, '-c', 'import os,signal;os.kill(os.getpid(),signal.SIGKILL)'], args)
        args.timeout = .05
        started = time.monotonic()
        with self.assertRaisesRegex(ValueError, 'timeout'):
            exporter.run_process([sys.executable, '-c', 'import time;time.sleep(30)'], args)
        self.assertLess(time.monotonic() - started, 5)

    def test_owned_process_cleanup_tolerates_macos_group_permission_error(self):
        process = subprocess.Popen([sys.executable, '-c', 'pass'], start_new_session=True)
        process.wait(timeout=10)
        with patch.object(os, 'killpg', side_effect=PermissionError(1, 'Operation not permitted')) as killpg:
            exporter.stop_owned_process(process)
        self.assertEqual(killpg.call_count, 2)
        running = subprocess.Popen([sys.executable, '-c', 'import time;time.sleep(30)'], start_new_session=True)
        try:
            with patch.object(os, 'killpg', side_effect=PermissionError(1, 'Operation not permitted')):
                exporter.stop_owned_process(running)
            self.assertEqual(running.returncode, -signal.SIGTERM)
        finally:
            if running.poll() is None:
                running.kill()
                running.wait(timeout=10)

    def test_real_process_helper_stops_watched_artifact_growth(self):
        with tempfile.TemporaryDirectory() as directory:
            artifact = Path(directory) / 'large.json'
            with self.assertRaisesRegex(ValueError, 'output limit'):
                exporter.run_process([sys.executable, '-c', "from pathlib import Path;import sys;Path(sys.argv[1]).write_bytes(b'x'*2048)", str(artifact)],
                    SimpleNamespace(timeout=2, output_limit=1024), watched=(artifact,))

    def test_nested_cancellation_stops_term_ignoring_child_within_outer_grace(self):
        # Real child processes exercise cleanup, not a simulated compiler result.
        with tempfile.TemporaryDirectory() as directory:
            pidfile = Path(directory) / 'child.pid'
            child = ("import os,signal,time;from pathlib import Path;"
                     "signal.signal(signal.SIGTERM,signal.SIG_IGN);"
                     f"Path({str(pidfile)!r}).write_text(str(os.getpid()));time.sleep(30)")
            arguments = ['policy.sol', '--output', 'policy.json', '--solc', '/policy/solc', '--contract', CONTRACT]
            driver = ("import importlib.util,sys;sys.dont_write_bytecode=True;"
                      f"s=importlib.util.spec_from_file_location('cleanup_policy',{str(ROOT / 'scripts/export-rust-yul.py')!r});"
                      "m=importlib.util.module_from_spec(s);s.loader.exec_module(m);"
                      f"m.export=lambda args:m.run_process([sys.executable,'-c',{child!r}],args);"
                      f"m.main({arguments!r})")
            process = subprocess.Popen([sys.executable, '-B', '-c', driver], stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE, start_new_session=True)
            try:
                deadline = time.monotonic() + 5
                while not pidfile.exists() and process.poll() is None and time.monotonic() < deadline:
                    time.sleep(.02)
                self.assertTrue(pidfile.exists())
                started = time.monotonic()
                exporter.common.stop_process(process)  # The actual outer adapter's two-second grace.
                process.communicate(timeout=2)
                self.assertLess(time.monotonic() - started, 1.8)
                state = subprocess.run(['ps', '-o', 'stat=', '-p', pidfile.read_text()],
                                       capture_output=True, text=True, check=False).stdout.strip()
                self.assertTrue(not state or state.startswith('Z'))
            finally:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGKILL)
                process.communicate()
                if pidfile.exists():
                    with contextlib.suppress(ProcessLookupError):
                        os.kill(int(pidfile.read_text()), signal.SIGKILL)

    def test_source_limit_rejects_before_compiler_preparation_or_hashing(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'large.sol'
            source.write_bytes(b'x' * 1025)
            args = exporter.parse_args([str(source), '--output', str(Path(directory) / 'out.json'),
                '--solc', '/policy/solc', '--contract', CONTRACT, '--output-limit', '1024'])
            with patch.object(exporter, 'checked_build') as prepare, self.assertRaisesRegex(ValueError, 'source size limit'):
                exporter.export(args)
            prepare.assert_not_called()

    def test_cli_requires_pinned_compiler_and_rejects_bad_scope_before_execution(self):
        command = [sys.executable, str(ROOT / 'scripts/export-rust-yul.py'), 'policy.sol', '--output', 'policy.json',
                   '--solc', '/not/executed', '--contract', 'SynthesizedCaller']
        result = subprocess.run(command, capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 2)
        self.assertIn('invalid choice', result.stderr)

    def test_sigterm_handler_restored_after_export_exception(self):
        before = signal.getsignal(signal.SIGTERM)
        with patch.object(exporter, 'export', side_effect=KeyboardInterrupt), self.assertRaises(KeyboardInterrupt):
            exporter.main(['policy.sol', '--output', 'policy.json', '--solc', '/policy/solc', '--contract', CONTRACT])
        self.assertEqual(signal.getsignal(signal.SIGTERM), before)


class FixtureAdmissionTests(unittest.TestCase):
    def test_a_pinned_fixture_admits_only_its_own_contract_under_the_same_object_checks(self):
        pins = exporter.fixture_pins()
        self.assertEqual((len(pins), pins['00answer']['contract']), (168, 'Answer'))
        exporter.validate_contract('Answer', '00answer')
        for contract, fixture in (('Answer', '01id'), ('Other', '00answer'), ('Answer', 'missing'), (CONTRACT, '00answer')):
            with self.assertRaises(ValueError):
                exporter.validate_contract(contract, fixture)
        with self.assertRaises(ValueError):
            exporter.validate_contract('Answer')
        exporter.validate_hull(hull_output('Answer'), 'Answer', '00answer')
        nested, two = hull_output('Answer'), hull_output('Answer')
        nested['program']['objects'][0]['inners'][0]['inners'] = [{'name': 'Child', 'inners': []}]
        two['program']['objects'].append({'name': 'OtherDeploy', 'inners': []})
        for output in (nested, two):
            with self.assertRaises(ValueError):
                exporter.validate_hull(output, 'Answer', '00answer')
        artifact = exporter.artifact_from_output(solc_output('Answer'), 'Answer', '00answer')
        self.assertEqual((artifact['selectedObject'], artifact['runtimeObject']), ('AnswerDeploy', 'Answer'))
        exporter.validate_artifact(artifact, 'Answer', '00answer')
        with self.assertRaises(ValueError):
            exporter.validate_artifact(artifact, 'Answer')
        for section, field in (('bytecode', 'linkReferences'), ('deployedBytecode', 'linkReferences'),
                               ('deployedBytecode', 'immutableReferences')):
            output = solc_output('Answer')
            output['contracts']['checked.yul']['AnswerDeploy']['evm'][section][field] = {'x': [{'start': 0, 'length': 20}]}
            with self.assertRaises(ValueError):
                exporter.artifact_from_output(output, 'Answer', '00answer')
        self.assertTrue(exporter.scope('Answer', '00answer').startswith('pinned end-to-end fixture 00answer;'))
        self.assertTrue(exporter.scope(CONTRACT).startswith('generated two-object wrapper shape'))

    def test_cli_takes_the_contract_from_the_pin_and_needs_exactly_one_selection(self):
        base = ['policy.sol', '--output', 'policy.json', '--solc', '/policy/solc']
        self.assertEqual(exporter.parse_args(base + ['--fixture', '00answer']).contract, 'Answer')
        self.assertEqual(exporter.parse_args(base + ['--contract', CONTRACT]).fixture, None)
        for extra in ([], ['--fixture', '00answer', '--contract', CONTRACT], ['--fixture', 'missing'],
                      ['--contract', 'Answer']):
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                exporter.parse_args(base + extra)

    def test_fixture_export_refuses_another_source_before_compiling(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'main.sol'
            source.write_text('contract Answer {}\n')
            args = exporter.parse_args([str(source), '--output', str(Path(directory) / 'out.json'),
                                        '--solc', '/policy/solc', '--fixture', '00answer'])
            with patch.object(exporter, 'checked_build') as prepare, \
                    self.assertRaisesRegex(ValueError, 'fixture source differs from its pin'):
                exporter.export(args)
            prepare.assert_not_called()


if __name__ == '__main__':
    unittest.main()
