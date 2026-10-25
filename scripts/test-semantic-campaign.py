#!/usr/bin/env python3
"""Campaign policy tests; real compiler/EVM runs are checked separately."""
import copy
from contextlib import redirect_stdout
import importlib.util
import io
import json
import os
import signal
import subprocess
from pathlib import Path
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("semantic_campaign", ROOT / "scripts/semantic-campaign.py")
campaign = importlib.util.module_from_spec(spec)
spec.loader.exec_module(campaign)


def matched():
    observed = {path: {"status": "returned", "word": "7"} for path in campaign.PATHS}
    return {"comparison": campaign.m2.compare(observed), "observations": observed}


def options(directory):
    return SimpleNamespace(output=Path(directory), profile='closed-g0', seed=1, nodes=16, cases=2, attempts=16,
        seconds=30, disk_bytes=16 * 1024 * 1024, shrink_attempts=4, shrink_candidates=8,
        direct_fuel=1000, core_fuel=1000, gas=100000, case_timeout=10,
        case_tool=Path('/unused/case-tool'), core_runner=Path('/unused/core-runner'),
        anvil=Path('/unused/anvil'), test_perturb_path=None, case=None, corpus=None)


def function_case(count):
    """A Core declaration-shape fixture, not a simulated compiler result."""
    def function(body):
        return {'tag': 'lambda', 'parameterType': 'word', 'resultType': 'word', 'body': body}

    body = function({'tag': 'apply', 'function': {'tag': 'var', 'index': 1},
                     'argument': {'tag': 'var', 'index': 0}})
    for _ in range(count):
        body = {'tag': 'let', 'initializer': function({'tag': 'var', 'index': 0}), 'body': body}
    return {'schema': campaign.m2.FUNCTION_CASE_SCHEMA, 'input': '0', 'source': 'coverage policy fixture',
        'program': {'schema': 'solcore-semantic-core', 'resultType': 'word', 'dataDefinitions': [],
            'body': {'tag': 'apply', 'function': body, 'argument': {'tag': 'word', 'value': '0x' + '00' * 32}}},
        'provenance': {**{key: 'test' for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion', *campaign.INPUT_VERSIONS)},
            'origin': {'kind': 'function-imported', 'helperCount': 999}, 'features': ['functionCall', 'local']},
        'contract': {'name': 'SynthesizedFunctions', 'method': 'run', 'signature': 'run(uint256)',
            'deployPath': ['SynthesizedFunctionsDeploy'], 'runtimePath': ['SynthesizedFunctionsDeploy', 'SynthesizedFunctions'],
            'calldata': '0xa444f5e9' + '00' * 32, 'constructorCalldata': '0x'}}


class AnalysisTests(unittest.TestCase):
    def test_normal_analysis_never_changes_observations(self):
        report = matched()
        before = copy.deepcopy(report)
        analysis = campaign.analyze(report)
        self.assertFalse(analysis['synthetic'])
        self.assertIsNone(analysis['testAdapter'])
        self.assertEqual(analysis['comparison']['category'], 'matched')
        self.assertEqual(report, before)

    def test_explicit_adapter_records_actual_match_and_synthetic_difference(self):
        report = matched()
        before = copy.deepcopy(report)
        analysis = campaign.analyze(report, 'rustEvm')
        self.assertTrue(analysis['synthetic'])
        self.assertEqual(analysis['actualComparison']['category'], 'matched')
        self.assertEqual(analysis['comparison']['category'], 'semantic-mismatch')
        self.assertEqual(analysis['observations']['rustEvm']['word'], '6')
        self.assertEqual(report, before)
        self.assertEqual(campaign.fingerprint(analysis)['disagreeingPairs'],
            ['directCore/rustEvm', 'importedHull/rustEvm'])

    def test_adapter_does_not_hide_real_failure(self):
        for category in ('semantic-mismatch', 'execution-error', 'inconclusive-resource'):
            report = matched()
            report['comparison'] = {'category': category, 'pairs': {}}
            analysis = campaign.analyze(report, 'directCore')
            self.assertFalse(analysis['synthetic'])
            self.assertEqual(analysis['comparison'], report['comparison'])

    def test_reduction_keeps_category_stage_pairs_and_synthetic_flag(self):
        original = campaign.analyze(matched(), 'rustEvm')
        fingerprint = campaign.fingerprint(original)
        self.assertTrue(campaign.same_failure(fingerprint, original))
        for changed in (
                campaign.analyze(matched()), campaign.analyze(matched(), 'importedHull'),
                {**original, 'synthetic': False},
                {**original, 'comparison': {**original['comparison'], 'stage': 'different'}},
                {**original, 'comparison': {'category': 'source-rejected', 'pairs': {}}}):
            self.assertFalse(campaign.same_failure(fingerprint, changed))

    def test_reduction_does_not_replace_word_mismatch_with_revert(self):
        original = campaign.analyze(matched(), 'rustEvm')
        changed = copy.deepcopy(original)
        changed['observations']['rustEvm'] = {'status': 'reverted', 'output': '0x'}
        self.assertFalse(campaign.same_failure(campaign.fingerprint(original), changed))
        changed = copy.deepcopy(original)
        changed['observations']['rustEvm'] = {'status': 'returned', 'output': '0x'}
        self.assertFalse(campaign.same_failure(campaign.fingerprint(original), changed))

    def test_reduction_does_not_switch_failing_runtime(self):
        base = {'synthetic': False, 'comparison': {'category': 'execution-error', 'pairs': {}},
                'observations': {'directCore': {'status': 'core-fault'}, 'rustEvm': {'status': 'returned', 'word': '1'}}}
        changed = copy.deepcopy(base)
        changed['observations'] = {'directCore': {'status': 'returned', 'word': '1'}, 'rustEvm': {'status': 'evm-exceptional'}}
        self.assertFalse(campaign.same_failure(campaign.fingerprint(base), changed))

    def test_resource_exhaustion_is_not_shrink_target(self):
        analysis = {'synthetic': False, 'comparison': {'category': 'inconclusive-resource', 'pairs': {}}}
        self.assertFalse(campaign.same_failure(campaign.fingerprint(analysis), analysis))

    def test_compact_report_drops_logs_but_retains_evidence_hashes(self):
        report = {**matched(), 'processes': [{'stdout': 'abc', 'stderr': 'def', 'returncode': 0}], 'anvilLog': 'log'}
        compact = campaign.compact_report(report)
        self.assertNotIn('stdout', compact['processes'][0])
        self.assertEqual(compact['processes'][0]['stdoutSha256'], campaign.m2.digest(b'abc'))
        self.assertIn('exact archive replay unavailable', compact['archivePolicy'])
        self.assertEqual(report['anvilLog'], 'log')


class BudgetAndReceiptTests(unittest.TestCase):
    def test_retained_finding_always_has_history_without_reduction(self):
        for budget, consumed, expected in ((0, 0, 'no-attempts'), (2, 2, 'attempt-limit'), (2, 0, 'pending')):
            with self.subTest(budget=budget, consumed=consumed), tempfile.TemporaryDirectory() as directory:
                config = options(directory)
                config.shrink_attempts = budget
                instance = campaign.Campaign(config)
                instance.shrink_attempts = consumed
                folder = instance.work / 'case'
                folder.mkdir()
                case = {'program': {'body': {'tag': 'word', 'value': '0x0'}}}
                (folder / 'case.json').write_text(json.dumps(case))
                analysis = campaign.analyze(matched(), 'rustEvm')
                finding = instance.retain_finding(0, folder, case, {}, analysis)
                history = json.loads((Path(directory) / finding['history']).read_text())
                self.assertEqual(history['status'], expected)
                self.assertEqual(history['steps'], [])
                self.assertEqual(history['finalProgramSha256'], finding['originalProgramSha256'])
                self.assertEqual(history['finalArchive'], finding['originalArchive'])

    def test_rejection_counts_are_explicit_subsets_of_errors(self):
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory))
            counts = instance.summary['counts']
            for category in ('source-rejected', 'compilation-rejected', 'unsupported-scope'):
                campaign.count_outcome(counts, {'synthetic': False, 'comparison': {'category': category}})
            self.assertEqual(counts['sourceRejected'], 1)
            self.assertEqual(counts['compilationRejected'], 1)
            self.assertEqual(counts['errors'], 3)
            self.assertEqual(counts['executed'], 3)
            self.assertEqual(counts['matched'], 0)
            self.assertEqual(counts['completed'], 0)

    def test_unexecuted_cases_and_disk_stop_cannot_count_as_passes(self):
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory))
            instance.summary['counts']['generated'] = 2
            instance.checkpoint()
            saved = json.loads((Path(directory) / 'summary.json').read_text())
            self.assertEqual(saved['counts']['unexecuted'], 2)
            self.assertEqual(saved['counts']['matched'], 0)
            # A sparse file tests the actual directory-size guard without a
            # simulated compiler/EVM result or a large allocation in memory.
            with (Path(directory) / 'full.bin').open('wb') as output:
                output.truncate(instance.args.disk_bytes)
            with self.assertRaises(campaign.m2.Finding) as caught:
                instance.guard()
            self.assertEqual(caught.exception.stage, 'campaign-disk')

    def test_time_guard_preserves_existing_summary(self):
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory))
            instance.deadline = time.monotonic() - 1
            with self.assertRaises(campaign.m2.Finding) as caught:
                instance.guard()
            self.assertEqual(caught.exception.stage, 'campaign-time')
            self.assertTrue((Path(directory) / 'summary.json').exists())

    def test_literal_coverage_uses_original_ast(self):
        program = {'body': {'tag': 'let', 'initializer': {'tag': 'word', 'value': '0xff'},
                           'body': {'tag': 'word', 'value': '0x0'}}}
        self.assertEqual(campaign.word_literals(program), {'255', '0'})

    def test_required_coverage_counts_only_matched_cases(self):
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory))
            coverage = instance.summary['coverage']
            coverage.update(requiredFeatures=['let', 'if'], generatedFeatures=['let', 'if'],
                            matchedFeatures=['if'], requiredWordLiterals=['0', '1'], matchedWordLiterals=['1'])
            instance.checkpoint()
            self.assertEqual(coverage['missingFeatures'], ['let'])
            self.assertEqual(coverage['missingWordLiterals'], ['0'])

    def test_boundary_literals_do_not_replace_executed_input_coverage(self):
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory))
            coverage = instance.summary['coverage']
            coverage.update(requiredInputs=list(campaign.INPUT_BOUNDARIES),
                generatedInputs=list(campaign.INPUT_BOUNDARIES), matchedInputs=['0'],
                matchedWordLiterals=list(campaign.INPUT_BOUNDARIES))
            instance.checkpoint()
            self.assertEqual(coverage['missingInputs'], sorted(campaign.INPUT_BOUNDARIES[1:], key=int))

    def test_helper_counts_come_from_declarations_and_exclude_the_entry(self):
        for count in (1, 2, 3):
            case = function_case(count)
            self.assertEqual(campaign.declared_helper_count(case['program']), count)
            # The provenance deliberately claims 999 helpers; it is not evidence.
            self.assertEqual(campaign.helper_counts(case), {count})
        case['schema'] = campaign.m2.INPUT_CASE_SCHEMA
        self.assertEqual(campaign.helper_counts(case), set())

    def test_malformed_function_declaration_shapes_are_rejected(self):
        malformed = [None, {}, function_case(0)['program'], function_case(4)['program']]
        missing_apply = function_case(1)['program']
        missing_apply['body'] = missing_apply['body']['function']
        malformed.append(missing_apply)
        for part in ('argument', 'initializer', 'entry', 'parameterType'):
            program = function_case(1)['program']
            if part == 'argument':
                program['body']['argument'] = {'tag': 'bool', 'value': False}
            elif part == 'initializer':
                program['body']['function']['initializer'] = {'tag': 'word', 'value': '0x' + '00' * 32}
            elif part == 'entry':
                program['body']['function']['body'] = {'tag': 'var', 'index': 0}
            else:
                program['body']['function']['initializer']['parameterType'] = 'bool'
            malformed.append(program)
        for program in malformed:
            with self.subTest(program=program), self.assertRaises(ValueError):
                campaign.declared_helper_count(program)

    def test_declared_helper_requirements_count_only_matched_cases(self):
        with tempfile.TemporaryDirectory() as directory:
            config = options(directory)
            config.profile, config.cases, config.shrink_attempts = 'runtime-functions', 3, 0
            instance = campaign.Campaign(config)
            cases = [function_case(count) for count in (1, 2, 3)]
            instance.summary['coverage']['requiredHelperCounts'] = [1, 2, 3]
            instance.prepare_cases = lambda: {'schema': 'solcore-lean.semantic-corpus.v1',
                'cases': cases, 'excluded': [], 'requested': 3, 'attempted': 3, 'status': 'complete'}

            def execute_case(case):
                count = campaign.declared_helper_count(case['program'])
                folder = instance.work / str(count)
                folder.mkdir()
                report = matched()
                if count != 1:
                    report['comparison'] = {'category': 'inconclusive-resource' if count == 2 else 'source-rejected', 'pairs': {}}
                return folder, report, campaign.analyze(report)

            instance.execute_case = execute_case
            with redirect_stdout(io.StringIO()):
                instance.run()
            coverage = instance.summary['coverage']
            self.assertEqual(coverage['generatedHelperCounts'], [1, 2, 3])
            self.assertEqual(coverage['matchedHelperCounts'], [1])
            self.assertEqual(coverage['missingHelperCounts'], [2, 3])

    def test_missing_helper_counts_fail_even_when_every_executed_case_matches(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'campaign'

            def run(instance):
                instance.summary['status'] = 'complete'
                instance.summary['counts'].update(generated=2, executed=2, completed=2, matched=2)
                instance.summary['coverage'].update(requiredHelperCounts=[1, 2, 3],
                    generatedHelperCounts=[1], matchedHelperCounts=[1])

            with patch.object(sys, 'argv', ['semantic-campaign', '--output', str(output),
                    '--profile', 'runtime-functions', '--cases', '2']), \
                    patch.object(campaign.Campaign, 'run', run), redirect_stdout(io.StringIO()):
                self.assertEqual(campaign.main(), 1)
            summary = json.loads((output / 'summary.json').read_text())
            self.assertEqual(summary['status'], 'coverage-incomplete')
            self.assertEqual(summary['coverage']['missingHelperCounts'], [2, 3])

    def test_generation_fuel_failures_have_a_separate_counter(self):
        rows = [{'category': 'excluded'}, {'category': 'inconclusive-resource'},
            {'detail': {'excluded': [{'category': 'inconclusive-resource'}]}}]
        self.assertEqual(campaign.generation_resource_exclusions(rows), 2)
        for invalid in ([None], [{'detail': {'excluded': ['invalid']}}]):
            with self.assertRaises(ValueError):
                campaign.generation_resource_exclusions(invalid)


class ManifestTests(unittest.TestCase):
    def valid(self):
        return json.loads((ROOT / 'scripts/semantic-corpus.json').read_text())

    def test_corpus_requires_object_and_exact_entry_source(self):
        for value in ([], None, 'manifest'):
            with self.assertRaises(ValueError):
                campaign.validate_manifest(value)
        for operation in ('both', 'neither'):
            value = self.valid()
            if operation == 'both':
                value['cases'][0]['program'] = {}
            else:
                del value['cases'][0]['generation']
            with self.assertRaises(ValueError):
                campaign.validate_manifest(value)

    def test_corpus_requires_string_lists_and_bounded_requests(self):
        for key in ('requiredFeatures', 'requiredWordLiterals'):
            value = self.valid()
            value[key] = 'not-an-array'
            with self.assertRaises(ValueError):
                campaign.validate_manifest(value)
        for field, bad in (('seed', '01'), ('seed', str(2**64)), ('maxProgramNodes', True), ('maxProgramNodes', 513)):
            value = self.valid()
            value['cases'][0]['generation'][field] = bad
            with self.assertRaises(ValueError):
                campaign.validate_manifest(value)

    def test_runtime_manifest_requires_its_version_and_exact_inputs(self):
        value = self.valid()
        value['profile'] = 'runtime-word'
        value['profileVersion'] = 'runtime-input-test'
        value['functionVersion'] = 'function-test'
        value['abstractionVersion'] = 'abstraction-test'
        value['requiredInputs'] = list(campaign.INPUT_BOUNDARIES)
        for entry in value['cases']:
            entry['input'] = '0'
        campaign.validate_manifest(value)
        campaign.validate_manifest({**value, 'profile': 'runtime-functions', 'requiredHelperCounts': [1, 2, 3]})
        for key in (*campaign.INPUT_VERSIONS, 'requiredInputs'):
            broken = copy.deepcopy(value)
            del broken[key]
            with self.assertRaises(ValueError):
                campaign.validate_manifest(broken)
        for invalid in (None, 0, '01', str(2**256), '2'):
            broken = copy.deepcopy(value)
            broken['cases'][0]['input'] = invalid
            with self.assertRaises(ValueError):
                campaign.validate_manifest(broken)
        with self.assertRaises(ValueError):
            campaign.validate_manifest({**value, 'profile': 'closed-g0'})
        with self.assertRaises(ValueError):
            campaign.validate_manifest({**value, 'profile': 'unknown'})

    def function_manifest(self):
        case = function_case(1)
        function_program = {**case['program'], 'resultType': {'tag': 'function', 'parameter': 'word', 'result': 'word'},
            'body': case['program']['body']['function']}
        return {'schema': 'solcore-lean.semantic-corpus-manifest.v1', 'profile': 'runtime-functions',
            **{key: case['provenance'][key] for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion', *campaign.INPUT_VERSIONS)},
            'requiredFeatures': [], 'requiredWordLiterals': [], 'requiredInputs': ['0'], 'requiredHelperCounts': [1, 2, 3],
            'cases': [{'id': str(index), 'input': '0', 'program': function_program,
                'expectedFeatures': case['provenance']['features']} for index in range(2)]}

    def test_helper_count_requirements_are_explicit_profile_specific_subsets(self):
        value = self.function_manifest()
        for valid in ([], [1], [3, 1], [1, 2, 3]):
            campaign.validate_manifest({**value, 'requiredHelperCounts': valid})
        missing = copy.deepcopy(value)
        del missing['requiredHelperCounts']
        with self.assertRaises(ValueError):
            campaign.validate_manifest(missing)
        for invalid in (None, '1', [True], [1.0], [0], [4], ['1'], [1, 1]):
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'requiredHelperCounts': invalid})
        for profile in ('closed-g0', 'runtime-word'):
            other = self.valid() if profile == 'closed-g0' else {**value, 'profile': profile}
            other.pop('requiredHelperCounts', None)
            campaign.validate_manifest(other)
            campaign.validate_manifest({**other, 'requiredHelperCounts': []})
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**other, 'requiredHelperCounts': [1]})

    def test_partial_materialization_preserves_generated_helper_coverage(self):
        with tempfile.TemporaryDirectory() as directory:
            config = options(directory)
            config.profile = 'runtime-functions'
            config.corpus = Path(directory) / 'manifest.json'
            config.corpus.write_text(json.dumps(self.function_manifest()))
            instance = campaign.Campaign(config)
            calls = 0

            def tool(_arguments, _stage):
                nonlocal calls
                calls += 1
                if calls == 2:
                    raise campaign.m2.Finding('inconclusive-resource', 'test-budget', 'stopped during materialization')
                return function_case(1)

            instance.tool = tool
            with self.assertRaises(campaign.m2.Finding):
                instance.prepare_cases()
            saved = json.loads((Path(directory) / 'summary.json').read_text())
            self.assertEqual(saved['counts']['generated'], 1)
            self.assertEqual(saved['coverage']['generatedHelperCounts'], [1])
            self.assertEqual(saved['coverage']['matchedHelperCounts'], [])
            self.assertEqual(saved['coverage']['requiredHelperCounts'], [1, 2, 3])
            self.assertEqual(saved['coverage']['missingHelperCounts'], [1, 2, 3])

    def test_generation_profile_selects_native_generator(self):
        for profile, command in (('closed-g0', 'generate'), ('runtime-word', 'input-generate'),
                                 ('runtime-functions', 'function-generate')):
            with self.subTest(profile=profile), tempfile.TemporaryDirectory() as directory:
                config = options(directory)
                config.profile = profile
                instance = campaign.Campaign(config)
                calls = []

                def tool(arguments, stage):
                    calls.append((arguments, stage))
                    return {'generation': 'dispatch test only'}

                instance.tool = tool
                instance.prepare_cases()
                self.assertEqual(calls, [([command, '1', '16', '2', '16', '1000'], 'generation')])

    def test_secondary_finding_archive_survives_work_cleanup(self):
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory))
            folder = instance.work / 'candidate'
            folder.mkdir()
            (folder / 'case.json').write_text('{}')
            (folder / 'report.json').write_text('{}')
            analysis = {'synthetic': False, 'comparison': {'category': 'compiler-crash', 'stage': 'rust-code-images', 'pairs': {}}, 'observations': {}}
            history = Path(directory) / 'findings' / 'real' / '0000' / 'shrink.json'
            history.parent.mkdir(parents=True)
            step = {'programSha256': 'candidate-hash'}
            instance.retain_secondary(folder, analysis, history, step)
            self.assertFalse(folder.exists())
            saved = Path(directory) / step['secondaryArchive']
            self.assertTrue((saved / 'case.json').exists())
            self.assertTrue((saved / 'report.json').exists())
            self.assertFalse(instance.summary['secondaryFindings'][0]['automaticReduction'])


class CancellationTests(unittest.TestCase):
    def test_sigterm_stops_owned_process_and_saves_summary(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            marker = folder / 'started'
            helper = folder / 'case-tool'
            helper.write_text('#!' + sys.executable + '\nimport os,time\nfrom pathlib import Path\n' +
                              'Path(' + repr(str(marker)) + ').write_text(str(os.getpid()))\ntime.sleep(20)\n')
            helper.chmod(0o700)
            output = folder / 'campaign'
            process = subprocess.Popen([sys.executable, str(ROOT / 'scripts/semantic-campaign.py'),
                '--output', str(output), '--case-tool', str(helper), '--cases', '1', '--seconds', '30'],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            try:
                deadline = time.monotonic() + 5
                while not marker.exists() and process.poll() is None and time.monotonic() < deadline:
                    time.sleep(0.02)
                self.assertTrue(marker.exists())
                child_pid = int(marker.read_text())
                process.send_signal(signal.SIGTERM)
                stdout, stderr = process.communicate(timeout=5)
                self.assertEqual(process.returncode, 1, stderr + stdout)
                summary = json.loads((output / 'summary.json').read_text())
                self.assertEqual(summary['status'], 'interrupted')
                self.assertEqual(summary['counts']['matched'], 0)
                self.assertFalse((output / '.work').exists())
                with self.assertRaises(ProcessLookupError):
                    os.kill(child_pid, 0)
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()


if __name__ == '__main__':
    unittest.main()
