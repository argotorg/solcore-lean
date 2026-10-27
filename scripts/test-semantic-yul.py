#!/usr/bin/env python3
"""Yul evidence/replay policy fixtures; no compiler or EVM is simulated."""
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('semantic_yul_policy', ROOT / 'scripts/semantic-yul.py')
yul = importlib.util.module_from_spec(spec)
spec.loader.exec_module(yul)
CONTRACT = 'SynthesizedG0'
LIMIT = 1024 * 1024


def save(path, data):
    path.write_bytes(yul.common.json_bytes(data))


def policy_case():
    return {'schema': yul.common.CASE_SCHEMA, 'program': {}, 'source': 'policy fixture only',
        'provenance': {key: 'policy' for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion')},
        'contract': {'name': CONTRACT, 'method': 'run', 'signature': 'run()',
            'deployPath': [CONTRACT + 'Deploy'], 'runtimePath': [CONTRACT + 'Deploy', CONTRACT],
            'calldata': '0xc0406226', 'constructorCalldata': '0x'}}


def storage_case(contract='SynthesizedLedger'):
    """Envelope only; the storage adapter's validator is replaced where it is used."""
    selected = next(value for value in yul.exporter.storage.PROFILES.values() if value['contract'] == contract)
    return {'schema': selected['caseSchema'], 'program': {}, 'source': 'policy fixture only',
        'contract': {'name': contract, 'deployPath': [contract + 'Deploy'], 'runtimePath': [contract + 'Deploy', contract]}}


class YulEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='semantic-yul-policy-')
        self.directory = Path(self.temp.name).resolve()

    def tearDown(self):
        self.temp.cleanup()

    def fixture(self, folder=None, case=None):
        folder = folder or self.directory
        folder.mkdir(exist_ok=True)
        case = case or policy_case()
        contract = case['contract']['name']
        source = folder / 'case.sol'
        source.write_text(case['source'])
        save(folder / 'case.json', case)
        hull = {'schema': yul.exporter.hull.SCHEMA, 'upstreamCommit': yul.common.UPSTREAM_COMMIT,
            'program': {'objects': [{'name': contract + 'Deploy', 'inners': [{'name': contract, 'inners': []}]}]}}
        save(folder / yul.EVIDENCE['hull'], hull)
        hp = {'schema': hull['schema'], 'upstreamCommit': hull['upstreamCommit'], 'patches': {'policy.rs': 'a' * 64},
            'binarySha256': 'b' * 64, 'outputSha256': yul.common.file_digest(folder / yul.EVIDENCE['hull']),
            'command': ['/old/driver', str(source), '--std-root', '/old/std', '--emit-hull', '--root', str(folder)],
            'sources': {source.as_uri(): yul.common.file_digest(source), 'file:///old/std/lib.sol': 'c' * 64}}
        save(folder / yul.EVIDENCE['hullProvenance'], hp)
        save(folder / 'hull.json', hull)
        save(folder / 'hull.json.provenance.json', hp)
        (folder / yul.EVIDENCE['yul']).write_text('policy Yul fixture')
        save(folder / yul.EVIDENCE['solcInput'], yul.exporter.standard_input('policy Yul fixture'))
        response = {'contracts': {'checked.yul': {contract + 'Deploy': {'evm': {
            'bytecode': {'object': '600000', 'linkReferences': {}},
            'deployedBytecode': {'object': '00', 'linkReferences': {}, 'immutableReferences': {}}}}}},
            'sources': {'checked.yul': {'id': 0, 'ast': {'nodeType': 'YulObject', 'name': contract + 'Deploy',
                'subObjects': [{'nodeType': 'YulObject', 'name': contract, 'subObjects': []}]}}}}
        save(folder / yul.EVIDENCE['solcOutput'], response)
        artifact = yul.exporter.artifact_from_output(response, contract)
        save(folder / yul.ARTIFACT, artifact)
        record = {'schema': yul.exporter.SCHEMA, 'upstreamCommit': yul.common.UPSTREAM_COMMIT,
            'backend': copy.deepcopy(yul.BACKEND), 'selectedObject': contract + 'Deploy', 'runtimeObject': contract,
            'exporterSha256': yul.common.file_digest(ROOT / 'scripts/export-rust-yul.py'),
            'outputSha256': yul.common.file_digest(folder / yul.ARTIFACT),
            'compiler': {'path': '/old/solc', 'sha256': 'd' * 64, 'versionOutput': 'Version: ' + yul.exporter.SOLC_VERSION + '.Linux.g++\n'},
            'toolBuild': {'upstreamCommit': hp['upstreamCommit'], 'patches': hp['patches'], 'binarySha256': hp['binarySha256']},
            'hullProvenance': hp, 'sources': hp['sources'],
            'commands': {'hull': ['/policy/python', 'policy-exporter'],
                'yul': hp['command'][:4] + ['--emit-yul', '--emit-yul-object', contract + 'Deploy'] + hp['command'][5:],
                'solc': ['/old/solc', '--standard-json']},
            'artifacts': {key: {'file': name, 'sha256': yul.common.file_digest(folder / name)} for key, name in yul.EVIDENCE.items()},
            'scope': 'policy fixture, not compiler execution'}
        save(folder / yul.PROVENANCE, record)
        report = {'backend': 'yul', 'pathBackends': dict(yul.PATH_BACKENDS),
            'exportProvenance': {'hull': hp}, 'yulExportProvenance': record,
            'tools': {'solc': {'path': '/different/solc', 'sha256': record['compiler']['sha256'],
                'version': record['compiler']['versionOutput'].strip()}, 'yulExporterSha256': record['exporterSha256'],
                'yulTransportSha256': yul.common.file_digest(ROOT / 'scripts/semantic-yul.py')},
            'rawObservations': {'rustEvm': {'status': 'returned'}},
            'artifacts': {name: yul.common.file_digest(folder / name) for name in yul.FILES + yul.MAIN_FILES}}
        return record, hp, report

    def rewrite_record(self, record):
        save(self.directory / yul.PROVENANCE, record)

    def rehash(self, record, key):
        record['artifacts'][key]['sha256'] = yul.common.file_digest(self.directory / yul.EVIDENCE[key])
        self.rewrite_record(record)

    def test_complete_export_and_archive_bind_all_evidence(self):
        record, hp, report = self.fixture()
        self.assertEqual(yul.validate_export(self.directory, CONTRACT, hp, LIMIT), record)
        self.assertEqual(yul.validate_archive(self.directory, report, LIMIT), record)

    def test_relocation_does_not_resolve_former_source_or_compiler_paths(self):
        old = self.directory / 'old'
        record, _, report = self.fixture(old)
        new = self.directory / 'relocated with spaces'
        shutil.copytree(old, new)
        shutil.rmtree(old)
        self.assertEqual(yul.validate_archive(new, report, LIMIT), record)

    def test_missing_hash_escape_symlink_and_oversize_fail(self):
        record, hp, _ = self.fixture()
        for key in yul.EVIDENCE:
            bad = copy.deepcopy(record)
            bad['artifacts'][key]['file'] = '../' + yul.EVIDENCE[key]
            self.rewrite_record(bad)
            with self.assertRaises(ValueError):
                yul.validate_export(self.directory, CONTRACT, hp, LIMIT)
        self.rewrite_record(record)
        member = self.directory / yul.EVIDENCE['yul']
        member.unlink()
        with self.assertRaises(ValueError):
            yul.validate_export(self.directory, CONTRACT, hp, LIMIT)
        member.symlink_to(self.directory / 'case.sol')
        with self.assertRaises(ValueError):
            yul.validate_export(self.directory, CONTRACT, hp, LIMIT)
        with self.assertRaises(yul.common.Finding):
            yul.validate_export(self.directory, CONTRACT, hp, 1)

    def test_bytecode_edit_is_rejected_even_if_the_artifact_hash_is_updated(self):
        record, hp, _ = self.fixture()
        artifact = yul.common.read_json(self.directory / yul.ARTIFACT)
        artifact['runtimeCode'] = '0x01'
        save(self.directory / yul.ARTIFACT, artifact)
        record['outputSha256'] = yul.common.file_digest(self.directory / yul.ARTIFACT)
        self.rewrite_record(record)
        with self.assertRaisesRegex(ValueError, 'saved solc output'):
            yul.validate_export(self.directory, CONTRACT, hp, LIMIT)

    def test_input_settings_and_yul_cannot_change_under_updated_evidence_hashes(self):
        record, hp, _ = self.fixture()
        request = yul.common.read_json(self.directory / yul.EVIDENCE['solcInput'])
        for key, value in (('evmVersion', 'cancun'), ('optimizer', {'enabled': False}), ('optimizer', {'enabled': 1}),
                           ('outputSelection', {'*': {'*': ['*']}})):
            changed = copy.deepcopy(request)
            changed['settings'][key] = value
            save(self.directory / yul.EVIDENCE['solcInput'], changed)
            self.rehash(record, 'solcInput')
            with self.assertRaisesRegex(ValueError, 'compiler settings'):
                yul.validate_export(self.directory, CONTRACT, hp, LIMIT)
        save(self.directory / yul.EVIDENCE['solcInput'], request)
        self.rehash(record, 'solcInput')
        (self.directory / yul.EVIDENCE['yul']).write_text('changed policy Yul')
        self.rehash(record, 'yul')
        with self.assertRaises(ValueError):
            yul.validate_export(self.directory, CONTRACT, hp, LIMIT)

    def test_main_hull_binding_rejects_source_patch_binary_and_output_changes(self):
        record, hp, _ = self.fixture()
        for field, value in (('sources', {'file:///changed.sol': 'e' * 64}), ('patches', {'other': 'f' * 64}),
                             ('binarySha256', 'e' * 64), ('outputSha256', 'e' * 64)):
            changed = copy.deepcopy(hp)
            changed[field] = value
            with self.assertRaises(ValueError):
                yul.validate_export(self.directory, CONTRACT, changed, LIMIT)
        record['toolBuild']['binarySha256'] = 'f' * 64
        self.rewrite_record(record)
        with self.assertRaisesRegex(ValueError, 'compiler build'):
            yul.validate_export(self.directory, CONTRACT, hp, LIMIT)

    def test_main_hull_bytes_and_sidecar_cannot_drift_under_updated_archive_hashes(self):
        _, _, report = self.fixture()
        for name in yul.MAIN_FILES:
            path = self.directory / name
            original = path.read_bytes()
            path.write_text('{"policy":"changed main Hull"}')
            changed = copy.deepcopy(report)
            changed['artifacts'][name] = yul.common.file_digest(path)
            with self.assertRaisesRegex(ValueError, 'main Hull bytes'):
                yul.validate_archive(self.directory, changed, LIMIT)
            path.write_bytes(original)
            changed = copy.deepcopy(report)
            del changed['artifacts'][name]
            with self.assertRaisesRegex(ValueError, 'archive omits'):
                yul.validate_archive(self.directory, changed, LIMIT)

    def test_archive_requires_inventory_sidecar_tools_and_separate_backend_roles(self):
        _, _, report = self.fixture()
        for key in ('artifacts', 'tools', 'yulExportProvenance'):
            changed = copy.deepcopy(report)
            del changed[key]
            with self.assertRaises(ValueError):
                yul.validate_archive(self.directory, changed, LIMIT)
        for key in ('solc', 'yulExporterSha256', 'yulTransportSha256'):
            changed = copy.deepcopy(report)
            del changed['tools'][key]
            with self.assertRaises(ValueError):
                yul.validate_archive(self.directory, changed, LIMIT)
        for key, value in (('sha256', '0' * 64), ('version', 'Version: another release')):
            changed = copy.deepcopy(report)
            changed['tools']['solc'][key] = value
            with self.assertRaisesRegex(ValueError, 'solc binary'):
                yul.validate_archive(self.directory, changed, LIMIT)
        changed = copy.deepcopy(report)
        changed['pathBackends']['importedHull'] = 'yul'
        with self.assertRaisesRegex(ValueError, 'relabelled'):
            yul.validate_archive(self.directory, changed, LIMIT)

    def test_pre_export_failure_can_replay_without_claiming_missing_execution_evidence(self):
        self.assertIsNone(yul.validate_archive(self.directory, {'backend': 'yul', 'observations': {}}, LIMIT))
        for extra in ({'yulExportProvenance': None}, {'rawObservations': {'rustEvm': {}}},
                      {'evmDeployment': {}}, {'executionContext': {}}, {'observations': None}):
            with self.assertRaises(ValueError):
                yul.validate_archive(self.directory, {'backend': 'yul', **extra}, LIMIT)

    def test_execute_forwards_only_yul_export_and_preserves_main_hull(self):
        record, _, report = self.fixture()
        original_hull = (self.directory / 'hull.json').read_bytes()
        args = SimpleNamespace(output=self.directory, solc=Path('/chosen/solc'), upstream=Path('/chosen/upstream'),
            target_dir=Path('/chosen/target'), timeout=5, artifact_limit=LIMIT)
        runner = SimpleNamespace(guard=lambda: None)
        with patch.object(yul.common, 'checked_process') as process:
            result = yul.execute(args, runner, policy_case(), self.directory / 'case.sol', self.directory / 'hull.json', report)
        self.assertEqual(result, (b'\x60\x00\x00', b'\x00'))
        command = process.call_args.args[2]
        self.assertEqual(command[command.index('--solc') + 1], '/chosen/solc')
        self.assertEqual(command[command.index('--output') + 1], str(self.directory / 'yul.json'))
        self.assertNotIn('--optimization', command)
        self.assertEqual((self.directory / 'hull.json').read_bytes(), original_hull)
        self.assertEqual(report['yulExportProvenance'], record)

    def test_storage_family_cases_are_validated_by_the_storage_adapter_with_its_failures(self):
        self.assertEqual(len(yul.STORAGE_SCHEMAS), 15)
        self.assertEqual(yul.STORAGE_SCHEMAS, {value['caseSchema'] for value in yul.exporter.storage.PROFILES.values()})
        for value in (storage_case(), storage_case('SynthesizedMethods'), policy_case(), None, {'schema': 'unknown'}):
            with self.subTest(case=value), patch.object(yul.exporter.storage, 'validate_case') as storage, \
                    patch.object(yul.common, 'validate_case') as pure:
                yul.validate_case(value)
                stored = isinstance(value, dict) and value.get('schema') in yul.STORAGE_SCHEMAS
                self.assertEqual((storage.call_count, pure.call_count), (1, 0) if stored else (0, 1))
        # A storage-family scope failure keeps its category and stage in the transport's own Finding class.
        failure = yul.exporter.storage.common.Finding('unsupported-scope', 'input', 'storage wrapper differs from the fixed profile')
        with patch.object(yul.exporter.storage, 'validate_case', side_effect=failure), self.assertRaises(yul.common.Finding) as caught:
            yul.validate_case(storage_case())
        self.assertEqual((caught.exception.category, caught.exception.stage, caught.exception.detail),
                         ('unsupported-scope', 'input', 'storage wrapper differs from the fixed profile'))
        # The real validator still refuses the envelope.
        with self.assertRaises((ValueError, yul.common.Finding)):
            yul.validate_case(storage_case())

    def test_storage_family_archive_and_execution_bind_the_same_evidence(self):
        case = storage_case()
        with patch.object(yul.exporter.storage, 'validate_case') as validate:
            record, _, report = self.fixture(case=case)
            del report['rawObservations']
            report['histories'] = {'rustEvm': {'status': 'complete'}}
            self.assertEqual(record['selectedObject'], 'SynthesizedLedgerDeploy')
            self.assertEqual(yul.validate_archive(self.directory, report, LIMIT), record)
            args = SimpleNamespace(output=self.directory, solc=Path('/chosen/solc'), upstream=Path('/chosen/upstream'),
                target_dir=Path('/chosen/target'), timeout=5, artifact_limit=LIMIT)
            with patch.object(yul.common, 'checked_process') as process:
                result = yul.execute(args, SimpleNamespace(guard=lambda: None), case, self.directory / 'case.sol',
                                     self.directory / 'hull.json', report)
            self.assertEqual(result, (b'\x60\x00\x00', b'\x00'))
            command = process.call_args.args[2]
            self.assertEqual(command[command.index('--contract') + 1], 'SynthesizedLedger')
            self.assertEqual(validate.call_count, 2)
            # A stateful report that ran the EVM cannot drop its export provenance.
            for histories in ({'rustEvm': {}}, None):
                with self.assertRaises(ValueError):
                    yul.validate_archive(self.directory, {'backend': 'yul', 'histories': histories}, LIMIT)
            self.assertIsNone(yul.validate_archive(self.directory, {'backend': 'yul', 'histories': {'directCore': {}}}, LIMIT))
            # The storage-family evidence cannot be read back under a pure or call wrapper.
            for contract in ('SynthesizedG0', 'SynthesizedCaller'):
                with self.assertRaises(ValueError):
                    yul.validate_export(self.directory, contract, report['exportProvenance']['hull'], LIMIT)

    def test_execute_replay_allows_path_relocation_but_rejects_compiler_or_bytecode_drift(self):
        record, _, report = self.fixture()
        args = SimpleNamespace(output=self.directory, solc=Path('/chosen/solc'), upstream=Path('/chosen/upstream'),
            target_dir=Path('/chosen/target'), timeout=5, artifact_limit=LIMIT)
        runner = SimpleNamespace(guard=lambda: None)
        old = copy.deepcopy(report)
        old['yulExportProvenance']['compiler']['path'] = '/removed/old/solc'
        with patch.object(yul.common, 'checked_process'):
            yul.execute(args, runner, policy_case(), self.directory / 'case.sol', self.directory / 'hull.json', report, old)
        for key, value in (('backend', {}), ('exporterSha256', '0' * 64), ('toolBuild', {}), ('outputSha256', '0' * 64),
                           ('compiler', {**record['compiler'], 'sha256': '0' * 64}),
                           ('compiler', {**record['compiler'], 'versionOutput': 'changed'})):
            changed = copy.deepcopy(old)
            changed['yulExportProvenance'][key] = value
            with patch.object(yul.common, 'checked_process'), self.assertRaises(yul.common.Finding):
                yul.execute(args, runner, policy_case(), self.directory / 'case.sol', self.directory / 'hull.json', report, changed)


if __name__ == '__main__':
    unittest.main()
