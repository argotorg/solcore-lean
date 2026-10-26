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


def mutation_policy_case(template=0, updates=1):
    """Recipe bookkeeping fixture only; it is never passed off as a real run."""
    case = function_case(1)
    case['schema'] = campaign.m2.MUTATION_CASE_SCHEMA
    case['contract'].update(name='SynthesizedMutation', deployPath=['SynthesizedMutationDeploy'],
        runtimePath=['SynthesizedMutationDeploy', 'SynthesizedMutation'])
    case['provenance']['templateVersion'] = 'test'
    case['provenance']['origin'] = {'kind': 'mutation-generated', 'seed': '0', 'maxProgramNodes': 96,
        'helpers': [{'template': template, 'updates': updates}]}
    return case


def loop_policy_case(mask=7, value=7, helpers=2):
    """Loop envelope/coverage fixture; no compiler or runtime is simulated."""
    case = function_case(helpers)
    step = {'schema': 'solcore-semantic-core', 'dataDefinitions': [],
        'resultType': {'tag': 'function', 'parameter': 'word', 'result': 'word'},
        'body': copy.deepcopy(case['program']['body']['function'])}
    case.update(schema=campaign.m2.LOOP_CASE_SCHEMA, input=str(value),
        loopPlan={'schema': 'solcore-lean.loop-plan.v1', 'mask': mask, 'stepProgram': step})
    case['contract'].update(name='SynthesizedLoops', deployPath=['SynthesizedLoopsDeploy'],
        runtimePath=['SynthesizedLoopsDeploy', 'SynthesizedLoops'], calldata='0xa444f5e9' + f'{value:064x}')
    for key in campaign.PROFILE_VERSION_FIELDS['runtime-loops']:
        case['provenance'][key] = 'test'
    case['provenance']['origin'] = {'kind': 'loop-generated', 'seed': '0', 'maxProgramNodes': 384,
        'mask': mask, 'stepOrigin': {'kind': 'aggregate-generated', 'helpers': [{'template': 3}]}}
    return case


def generic_policy_case(variant="word", value=1, helpers=2):
    """Generic transport/coverage fixture; not a simulated compiler result."""
    case = loop_policy_case(7, value, helpers)
    step = case.pop('loopPlan')['stepProgram']
    case.update(schema=campaign.m2.GENERIC_CASE_SCHEMA,
        genericPlan={'schema': 'solcore-lean.generic-plan.v1', 'variant': variant, 'stepProgram': step})
    case['contract'].update(name='SynthesizedGenerics', deployPath=['SynthesizedGenericsDeploy'],
        runtimePath=['SynthesizedGenericsDeploy', 'SynthesizedGenerics'])
    case['provenance']['origin'].update(kind='generic-generated', variant=variant)
    del case['provenance']['origin']['mask']
    return case


def closure_policy_case(variant="snapshot", value=1, helpers=2):
    """Closure metadata policy fixture only; no result oracle or fake execution."""
    case = generic_policy_case('word', value, helpers)
    step = case.pop('genericPlan')['stepProgram']
    case.update(schema=campaign.m2.CLOSURE_CASE_SCHEMA,
        closurePlan={'schema': 'solcore-lean.closure-plan.v1', 'variant': variant, 'stepProgram': step})
    case['contract'].update(name='SynthesizedClosures', deployPath=['SynthesizedClosuresDeploy'],
        runtimePath=['SynthesizedClosuresDeploy', 'SynthesizedClosures'])
    case['provenance']['origin'].update(kind='closure-generated', variant=variant)
    return case


def comptime_policy_case(variant="offset", value=1, helpers=2):
    """Original-AST coverage fixture only; never a simulated compiler result."""
    case = closure_policy_case('snapshot', value, helpers)
    step = case.pop('closurePlan')['stepProgram']
    constant = {'schema': 'solcore-semantic-core', 'resultType': 'word', 'dataDefinitions': [],
        'body': {'tag': 'binary', 'op': 'wordAdd', 'left': {'tag': 'word', 'value': '0x' + f'{1:064x}'},
                 'right': {'tag': 'word', 'value': '0x' + f'{2:064x}'}}}
    case.update(schema=campaign.m2.COMPTIME_CASE_SCHEMA,
        comptimePlan={'schema': 'solcore-lean.comptime-plan.v1', 'variant': variant, 'stepProgram': step,
                      'constantProgram': constant})
    case['contract'].update(name='SynthesizedComptime', deployPath=['SynthesizedComptimeDeploy'],
        runtimePath=['SynthesizedComptimeDeploy', 'SynthesizedComptime'])
    case['provenance']['origin'].update(kind='comptime-generated', variant=variant)
    case['provenance']['constantFeatures'] = ['wordLiteral', 'binary:Solcore.Core.Wire.BinaryOp.wordAdd']
    return case


def module_policy_case(value=1, helpers=2):
    """Four-file transport and coverage fixture, not a compilable result oracle."""
    case = comptime_policy_case('offset', value, helpers)
    plan = case.pop('comptimePlan')
    plan.pop('variant')
    plan['schema'] = 'solcore-lean.module-plan.v1'
    case.update(schema=campaign.m2.MODULE_CASE_SCHEMA, modulePlan=plan)
    case['sourceBundle'] = {'schema': campaign.m2.bundle_transport.SCHEMA, 'entry': 'case.sol',
        'files': [{'path': name, 'source': case['source'] if name == 'case.sol' else '// provider fixture'}
                  for name in campaign.m2.bundle_transport.FILES]}
    case['contract'].update(name='SynthesizedModules', deployPath=['SynthesizedModulesDeploy'],
        runtimePath=['SynthesizedModulesDeploy', 'SynthesizedModules'])
    case['provenance']['origin'].update(kind='module-generated')
    case['provenance']['origin'].pop('variant')
    return case


class AnalysisTests(unittest.TestCase):
    def test_backend_is_normalized_and_part_of_the_reduction_fingerprint(self):
        legacy = campaign.analyze(matched(), 'rustEvm')
        self.assertEqual(legacy['backend'], 'sonatina-o0')
        legacy_fingerprint = campaign.fingerprint(legacy)
        legacy_fingerprint.pop('backend')
        self.assertTrue(campaign.same_failure(legacy_fingerprint, legacy))
        optimized = campaign.analyze({**matched(), 'backend': 'sonatina-o2'}, 'rustEvm')
        self.assertEqual(campaign.fingerprint(optimized)['backend'], 'sonatina-o2')
        self.assertFalse(campaign.same_failure(legacy_fingerprint, optimized))
        self.assertFalse(campaign.same_failure(campaign.fingerprint(optimized), legacy))
        yul_analysis = campaign.analyze({**matched(), 'backend': 'yul'}, 'rustEvm')
        self.assertEqual(campaign.fingerprint(yul_analysis)['backend'], 'yul')
        self.assertFalse(campaign.same_failure(campaign.fingerprint(optimized), yul_analysis))
        self.assertFalse(campaign.same_failure(campaign.fingerprint(yul_analysis), legacy))
        for invalid in ('unknown-backend', None, 2):
            with self.assertRaises(ValueError):
                campaign.analyze({**matched(), 'backend': invalid})
            with self.assertRaises(ValueError):
                campaign.fingerprint({**legacy, 'backend': invalid})

    def test_selected_backend_reaches_original_and_reducer_executions(self):
        for backend in ('sonatina-o2', 'yul'):
            # Adapter boundary policy fixture; this does not pretend to run Rust/EVM.
            with tempfile.TemporaryDirectory() as directory:
                args = options(directory)
                args.backend, args.test_perturb_path = backend, 'rustEvm'
                args.solc = Path('/chosen/pinned-solc')
                args.upstream, args.target_dir = Path('/unused/upstream'), Path('/unused/target')
                instance = campaign.Campaign(args)
                original = {'source': 'policy original', 'program': {'body': {'tag': 'word', 'value': '7'}}}
                candidate = {'source': 'policy reduced', 'program': {'body': {'tag': 'word', 'value': '0'}}}
                selected = []

                def execute(adapter_args, report):
                    selected.append((adapter_args.backend, adapter_args.solc))
                    report.update(matched(), backend=adapter_args.backend)
                    campaign.save_json(adapter_args.output / 'case.json', json.loads(adapter_args.case.read_text()))

                with patch.object(campaign.m2, 'execute', side_effect=execute):
                    folder, report, analysis = instance.execute_case(original)
                    finding = instance.retain_finding(0, folder, original, report, analysis)
                    instance.tool = lambda *_: {'schema': 'solcore-lean.semantic-corpus.v1', 'cases': [candidate]}
                    instance.shrink(original, finding)
                self.assertEqual(selected, [(backend, args.solc), (backend, args.solc)])
                self.assertEqual(instance.summary['backend'], backend)
                self.assertEqual(instance.summary['configuration']['backend'], backend)
                history = json.loads((Path(directory) / finding['history']).read_text())
                self.assertTrue(history['steps'][0]['accepted'])
                self.assertEqual(history['steps'][0]['fingerprint']['backend'], backend)


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

    def test_mutation_templates_have_independent_version_provenance(self):
        for profile in ('runtime-mutation', 'runtime-aggregates'):
            value = {**self.function_manifest(), 'profile': profile,
                     'templateVersion': 'template-test'}
            del value['abstractionVersion']
            campaign.validate_manifest(value)
            missing = {**value, 'abstractionVersion': 'unrelated-literal-abstraction'}
            del missing['templateVersion']
            with self.assertRaisesRegex(ValueError, 'templateVersion'):
                campaign.validate_manifest(missing)
            case = function_case(3)
            case['schema'] = campaign.PROFILE_SCHEMAS[profile]
            self.assertEqual(campaign.helper_counts(case), {3})

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
                                 ('runtime-functions', 'function-generate'),
                                 ('runtime-mutation', 'mutation-generate'),
                                 ('runtime-aggregates', 'aggregate-generate'),
                                 ('runtime-loops', 'loop-generate')):
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


class RecipeCoverageTests(unittest.TestCase):
    def manifest(self):
        case = mutation_policy_case()
        return {'schema': 'solcore-lean.semantic-corpus-manifest.v1', 'profile': 'runtime-mutation',
            **{key: case['provenance'][key] for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion', *campaign.PROFILE_VERSION_FIELDS['runtime-mutation'])},
            'requiredFeatures': [], 'requiredWordLiterals': [], 'requiredInputs': [], 'requiredHelperCounts': [],
            'generationRecipeRequirements': {'templates': [0, 1, 2, 3], 'updates': [1, 2, 3, 4]},
            'cases': [{'id': str(index), 'input': '0', 'generation': {'seed': '0', 'maxProgramNodes': 96},
                'expectedFeatures': case['provenance']['features']} for index in range(2)]}

    def test_recipe_requirements_are_optional_unique_bounded_and_profile_specific(self):
        manifest = self.manifest()
        campaign.validate_manifest(manifest)
        omitted = copy.deepcopy(manifest)
        del omitted['generationRecipeRequirements']
        campaign.validate_manifest(omitted)
        campaign.validate_manifest({**manifest, 'generationRecipeRequirements': {'templates': [], 'updates': []}})
        for invalid in (None, [], {}, {'templates': []}, {'templates': [], 'updates': [], 'other': []},
                {'templates': [False], 'updates': []}, {'templates': [4], 'updates': []},
                {'templates': [0, 0], 'updates': []}, {'templates': [], 'updates': [0]},
                {'templates': [], 'updates': [5]}, {'templates': [], 'updates': [1.0]},
                {'templates': [], 'updates': [1, 1]}, {'templates': '0', 'updates': []}):
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                campaign.validate_manifest({**manifest, 'generationRecipeRequirements': invalid})
        for profile in ('closed-g0', 'runtime-word', 'runtime-functions'):
            with self.assertRaises(ValueError):
                campaign.recipe_requirements({'profile': profile,
                    'generationRecipeRequirements': {'templates': [0], 'updates': []}})
            self.assertEqual(campaign.recipe_requirements({'profile': profile}), {'templates': [], 'updates': []})
            self.assertEqual(campaign.recipe_requirements({'profile': profile,
                'generationRecipeRequirements': {'templates': [], 'updates': []}}), {'templates': [], 'updates': []})

    def test_recipe_inventory_uses_only_generated_mutation_metadata(self):
        case = mutation_policy_case(3, 4)
        self.assertEqual(campaign.generation_recipes(case), {'Templates': {3}, 'Updates': {4}})
        for kind in ('mutation-imported', 'mutation-reduced', 'function-generated'):
            changed = copy.deepcopy(case)
            changed['provenance']['origin']['kind'] = kind
            self.assertEqual(campaign.generation_recipes(changed), {'Templates': set(), 'Updates': set()})
        case['schema'] = campaign.m2.FUNCTION_CASE_SCHEMA
        self.assertEqual(campaign.generation_recipes(case), {'Templates': set(), 'Updates': set()})

    def test_aggregate_recipes_require_only_templates_and_cannot_use_mutation_origins(self):
        manifest = {**self.manifest(), 'profile': 'runtime-aggregates',
            'generationRecipeRequirements': {'templates': [0, 1, 2, 3], 'updates': []}}
        campaign.validate_manifest(manifest)
        with self.assertRaisesRegex(ValueError, 'no update-count'):
            campaign.validate_manifest({**manifest,
                'generationRecipeRequirements': {'templates': [0], 'updates': [1]}})
        case = mutation_policy_case(3, 4)
        case['schema'] = campaign.m2.AGGREGATE_CASE_SCHEMA
        self.assertEqual(campaign.generation_recipes(case), {'Templates': set(), 'Updates': set()})
        case['provenance']['origin'] = {'kind': 'aggregate-generated', 'helpers': [{'template': 3}]}
        self.assertEqual(campaign.generation_recipes(case), {'Templates': {3}, 'Updates': set()})
        for invalid in (False, 4, -1, '0'):
            case['provenance']['origin']['helpers'][0]['template'] = invalid
            with self.assertRaises(ValueError):
                campaign.generation_recipes(case)

    def test_malformed_generated_metadata_is_rejected(self):
        for helpers in (None, [], [None], [{}], [{'template': 0, 'updates': 1}] * 4,
                [{'template': True, 'updates': 1}], [{'template': 4, 'updates': 1}],
                [{'template': 0, 'updates': 0}], [{'template': 0, 'updates': '1'}]):
            case = mutation_policy_case()
            case['provenance']['origin']['helpers'] = helpers
            with self.subTest(helpers=helpers), self.assertRaises(ValueError):
                campaign.generation_recipes(case)

    def test_nonmatched_policy_outcomes_do_not_satisfy_recipe_requirements(self):
        with tempfile.TemporaryDirectory() as directory:
            config = options(directory)
            config.profile, config.cases, config.shrink_attempts = 'runtime-mutation', 3, 0
            instance = campaign.Campaign(config)
            cases = [mutation_policy_case(index, index + 1) for index in range(3)]
            instance.summary['recipeCoverage'].update(requiredTemplates=[0, 1, 2], requiredUpdates=[1, 2, 3])
            instance.prepare_cases = lambda: {'schema': 'solcore-lean.semantic-corpus.v1',
                'cases': cases, 'excluded': [], 'requested': 3, 'attempted': 3, 'status': 'complete'}

            def execute_case(case):
                index = case['provenance']['origin']['helpers'][0]['template']
                folder = instance.work / str(index)
                folder.mkdir()
                report = matched()
                if index:
                    report['comparison'] = {'category': 'inconclusive-resource' if index == 1 else 'source-rejected', 'pairs': {}}
                return folder, report, campaign.analyze(report)

            # This substitutes outcomes only for policy control-flow testing;
            # actual compiler/EVM evidence is produced by the external suite.
            instance.execute_case = execute_case
            with redirect_stdout(io.StringIO()):
                instance.run()
            coverage = instance.summary['recipeCoverage']
            self.assertEqual(coverage['generatedTemplates'], [0, 1, 2])
            self.assertEqual(coverage['generatedUpdates'], [1, 2, 3])
            self.assertEqual(coverage['matchedTemplates'], [0])
            self.assertEqual(coverage['matchedUpdates'], [1])
            self.assertEqual(coverage['missingTemplates'], [1, 2])
            self.assertEqual(coverage['missingUpdates'], [2, 3])

    def test_partial_generation_saves_unverified_recipe_inventory(self):
        with tempfile.TemporaryDirectory() as directory:
            config = options(directory)
            config.profile = 'runtime-mutation'
            config.corpus = Path(directory) / 'manifest.json'
            config.corpus.write_text(json.dumps(self.manifest()))
            instance = campaign.Campaign(config)
            calls = 0

            def tool(_arguments, _stage):
                nonlocal calls
                calls += 1
                if calls == 2:
                    raise campaign.m2.Finding('inconclusive-resource', 'test-budget', 'partial generation')
                return {'cases': [mutation_policy_case()]}

            instance.tool = tool
            with self.assertRaises(campaign.m2.Finding):
                instance.prepare_cases()
            saved = json.loads((Path(directory) / 'summary.json').read_text())['recipeCoverage']
            self.assertEqual(saved['generatedTemplates'], [0])
            self.assertEqual(saved['generatedUpdates'], [1])
            self.assertEqual(saved['matchedTemplates'], [])
            self.assertEqual(saved['matchedUpdates'], [])
            self.assertEqual(saved['missingTemplates'], [0, 1, 2, 3])
            self.assertEqual(saved['missingUpdates'], [1, 2, 3, 4])
            self.assertIn('matched entries verified by native replay', saved['classification'])

    def test_missing_recipe_requirements_fail_an_otherwise_matched_campaign(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'campaign'

            def run(instance):
                instance.summary['status'] = 'complete'
                instance.summary['counts'].update(generated=2, executed=2, completed=2, matched=2)
                instance.summary['recipeCoverage'].update(requiredTemplates=[0, 1], requiredUpdates=[1, 2],
                    generatedTemplates=[0, 1], generatedUpdates=[1, 2], matchedTemplates=[0], matchedUpdates=[1])

            with patch.object(sys, 'argv', ['semantic-campaign', '--output', str(output),
                    '--profile', 'runtime-mutation', '--cases', '2']), \
                    patch.object(campaign.Campaign, 'run', run), redirect_stdout(io.StringIO()):
                self.assertEqual(campaign.main(), 1)
            summary = json.loads((output / 'summary.json').read_text())
            self.assertEqual(summary['status'], 'coverage-incomplete')
            self.assertEqual(summary['recipeCoverage']['missingTemplates'], [1])
            self.assertEqual(summary['recipeCoverage']['missingUpdates'], [2])


class LoopCoverageTests(unittest.TestCase):
    def manifest(self):
        case = loop_policy_case()
        return {'schema': 'solcore-lean.semantic-corpus-manifest.v1', 'profile': 'runtime-loops',
            **{key: case['provenance'][key] for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion',
                                                       *campaign.PROFILE_VERSION_FIELDS['runtime-loops'])},
            'requiredFeatures': [], 'requiredWordLiterals': [], 'requiredInputs': list(campaign.LOOP_INPUTS),
            'requiredHelperCounts': [1, 2, 3], 'loopRequirements': {'masks': [1, 3, 7], 'iterations': [0, 1, 3, 7]},
            'cases': [{'id': 'loop', 'input': '7', 'loopPlan': case['loopPlan'],
                       'expectedFeatures': case['provenance']['features']}]}

    def test_plan_requirements_and_source_selection_are_profile_specific(self):
        value = self.manifest()
        campaign.validate_manifest(value)
        entry = value['cases'][0]
        for invalid in (None, {}, {'masks': [2], 'iterations': []}, {'masks': [True], 'iterations': []},
                {'masks': [1, 1], 'iterations': []}, {'masks': [], 'iterations': [8]},
                {'masks': [], 'iterations': [1.0]}):
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'loopRequirements': invalid})
        for changed in ({**entry, 'program': {}}, {**entry, 'generation': {'seed': '0', 'maxProgramNodes': 384}},
                        {'id': 'loop', 'input': '7', 'program': {}, 'expectedFeatures': []}):
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'cases': [changed]})
        with self.assertRaises(ValueError):
            campaign.loop_requirements({'profile': 'runtime-aggregates', 'loopRequirements': value['loopRequirements']})
        for input_value in campaign.LOOP_INPUTS:
            campaign.validate_manifest({**value, 'cases': [{'id': 'generated', 'input': input_value,
                'generation': {'seed': '0', 'maxProgramNodes': 384}, 'expectedFeatures': []}]})
        for missing in ('stepProfileVersion', 'stepTemplateVersion', 'stepFunctionVersion'):
            invalid = copy.deepcopy(value)
            del invalid[missing]
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)

    def test_coverage_reads_the_step_graph_and_prescribed_bound(self):
        case = loop_policy_case(3, 7, 3)
        case['program'] = {}  # The plan graph, not the loop scaffold, supplies helper counts.
        self.assertEqual(campaign.helper_counts(case), {3})
        self.assertEqual(campaign.specified_loops(case), {'Masks': {3}, 'Iterations': {3}})
        self.assertEqual(campaign.generation_recipes(case), {'Templates': {3}, 'Updates': set()})
        case['input'] = str(2**255)
        self.assertEqual(campaign.specified_loops(case), {'Masks': {3}, 'Iterations': {0}})
        case['loopPlan']['stepProgram']['resultType'] = 'word'
        with self.assertRaises(ValueError):
            campaign.helper_counts(case)
        case['provenance']['origin']['stepOrigin']['kind'] = 'mutation-generated'
        with self.assertRaises(ValueError):
            campaign.generation_recipes(case)

    def test_generated_manifest_requests_all_six_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            config = options(directory)
            config.profile, config.cases = 'runtime-loops', 1
            value = self.manifest()
            del value['cases'][0]['loopPlan']
            value['cases'][0]['generation'] = {'seed': '0', 'maxProgramNodes': 384}
            config.corpus = Path(directory) / 'manifest.json'
            config.corpus.write_text(json.dumps(value))
            instance = campaign.Campaign(config)
            calls = []
            def tool(arguments, stage):
                calls.append((arguments, stage))
                return {'cases': [loop_policy_case()]}
            instance.tool = tool
            self.assertEqual(len(instance.prepare_cases()['cases']), 1)
            self.assertEqual(calls, [(['loop-generate', '0', '384', '6', '1', '1000'], 'corpus-generation')])
            self.assertEqual(instance.summary['loopCoverage']['generatedIterations'], [7])
            self.assertEqual(instance.summary['loopCoverage']['matchedIterations'], [])

    def test_nonmatching_outcomes_cannot_satisfy_loop_coverage(self):
        with tempfile.TemporaryDirectory() as directory:
            config = options(directory)
            config.profile, config.cases, config.shrink_attempts = 'runtime-loops', 3, 0
            instance = campaign.Campaign(config)
            cases = [loop_policy_case(n, n) for n in (1, 3, 7)]
            instance.summary['loopCoverage'].update(requiredMasks=[1, 3, 7], requiredIterations=[1, 3, 7])
            instance.prepare_cases = lambda: {'schema': 'solcore-lean.semantic-corpus.v1', 'cases': cases,
                'excluded': [], 'requested': 3, 'attempted': 3, 'status': 'complete'}
            def execute_case(case):
                mask = case['loopPlan']['mask']
                folder = instance.work / str(mask)
                folder.mkdir()
                report = matched()
                if mask != 1:
                    report['comparison'] = {'category': 'inconclusive-resource' if mask == 3 else 'source-rejected', 'pairs': {}}
                return folder, report, campaign.analyze(report)
            instance.execute_case = execute_case
            with redirect_stdout(io.StringIO()):
                instance.run()
            coverage = instance.summary['loopCoverage']
            self.assertEqual(coverage['generatedIterations'], [1, 3, 7])
            self.assertEqual(coverage['matchedIterations'], [1])
            self.assertEqual(coverage['missingIterations'], [3, 7])
            self.assertEqual(coverage['missingMasks'], [3, 7])

    def test_missing_loop_coverage_fails_an_otherwise_matched_campaign(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'campaign'
            def run(instance):
                instance.summary['status'] = 'complete'
                instance.summary['counts'].update(generated=1, executed=1, completed=1, matched=1)
                instance.summary['loopCoverage'].update(requiredMasks=[1, 3], requiredIterations=[0, 1, 3],
                    generatedMasks=[1], matchedMasks=[1], generatedIterations=[1], matchedIterations=[1])
            with patch.object(sys, 'argv', ['semantic-campaign', '--output', str(output), '--profile', 'runtime-loops', '--cases', '1']), \
                    patch.object(campaign.Campaign, 'run', run), redirect_stdout(io.StringIO()):
                self.assertEqual(campaign.main(), 1)
            summary = json.loads((output / 'summary.json').read_text())
            self.assertEqual(summary['status'], 'coverage-incomplete')
            self.assertEqual(summary['loopCoverage']['missingIterations'], [0, 3])


class GenericCoverageTests(unittest.TestCase):
    def manifest(self):
        case = generic_policy_case()
        return {'schema': 'solcore-lean.semantic-corpus-manifest.v1', 'profile': 'runtime-generics',
            **{key: case['provenance'][key] for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion',
                                                       *campaign.PROFILE_VERSION_FIELDS['runtime-generics'])},
            'requiredFeatures': [], 'requiredWordLiterals': [], 'requiredInputs': list(campaign.INPUT_BOUNDARIES),
            'requiredHelperCounts': [1, 2, 3],
            'genericRequirements': {'instantiations': [v + ':' + p for v in ('word', 'pair', 'sum') for p in ('even', 'odd')]},
            'cases': [{'id': 'generic', 'input': '1', 'genericPlan': case['genericPlan'],
                       'expectedFeatures': case['provenance']['features']}]}

    def test_generic_requirements_and_plan_are_profile_specific(self):
        value = self.manifest()
        campaign.validate_manifest(value)
        for invalid in (None, {}, {'instantiations': ['word:even', 'word:even']},
                {'instantiations': ['closure:odd']}, {'instantiations': [True]},
                {'instantiations': ['word:even'], 'unknown': []}):
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'genericRequirements': invalid})
        entry = value['cases'][0]
        for changed in ({**entry, 'program': {}}, {**entry, 'generation': {'seed': '0', 'maxProgramNodes': 384}},
                {'id': 'generic', 'input': '1', 'program': {}, 'expectedFeatures': []},
                {'id': 'generic', 'input': '1', 'loopPlan': {}, 'expectedFeatures': []}):
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'cases': [changed]})
        for profile in ('runtime-aggregates', 'runtime-loops', 'closed-g0'):
            with self.assertRaises(ValueError):
                campaign.generic_requirements({'profile': profile, 'genericRequirements': value['genericRequirements']})
        for missing in campaign.PROFILE_VERSION_FIELDS['runtime-generics']:
            invalid = copy.deepcopy(value)
            del invalid[missing]
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)

    def test_coverage_crosses_type_and_parity_and_excludes_wrapper_helpers(self):
        for variant in ('word', 'pair', 'sum'):
            for value in (0, 1, 2**255, 2**256 - 1):
                case = generic_policy_case(variant, value, 3)
                case['program'] = {}  # Only the original step declares counted helpers.
                self.assertEqual(campaign.helper_counts(case), {3})
                self.assertEqual(campaign.specified_generics(case), {variant + (':odd' if value & 1 else ':even')})
                self.assertEqual(campaign.generation_recipes(case), {'Templates': {3}, 'Updates': set()})
        self.assertEqual(campaign.specified_generics(loop_policy_case()), set())
        case['genericPlan']['stepProgram']['resultType'] = 'word'
        with self.assertRaises(ValueError):
            campaign.helper_counts(case)
        case['provenance']['origin']['stepOrigin']['kind'] = 'mutation-generated'
        with self.assertRaises(ValueError):
            campaign.generation_recipes(case)

    def test_generated_manifest_requests_all_four_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            config = options(directory)
            config.profile, config.cases = 'runtime-generics', 1
            value = self.manifest()
            del value['cases'][0]['genericPlan']
            value['cases'][0]['generation'] = {'seed': '0', 'maxProgramNodes': 384}
            config.corpus = Path(directory) / 'manifest.json'
            config.corpus.write_text(json.dumps(value))
            instance = campaign.Campaign(config)
            calls = []
            def tool(arguments, stage):
                calls.append((arguments, stage))
                return {'cases': [generic_policy_case()]}
            instance.tool = tool
            self.assertEqual(len(instance.prepare_cases()['cases']), 1)
            self.assertEqual(calls, [(['generic-generate', '0', '384', '4', '1', '1000'], 'corpus-generation')])
            self.assertEqual(instance.summary['genericCoverage']['generatedInstantiations'], ['word:odd'])
            self.assertEqual(instance.summary['genericCoverage']['matchedInstantiations'], [])

    def test_rejections_and_exhaustion_do_not_satisfy_instantiation_coverage(self):
        with tempfile.TemporaryDirectory() as directory:
            config = options(directory)
            config.profile, config.cases, config.shrink_attempts = 'runtime-generics', 3, 0
            instance = campaign.Campaign(config)
            cases = [generic_policy_case(variant) for variant in ('word', 'pair', 'sum')]
            instance.summary['genericCoverage']['requiredInstantiations'] = ['word:odd', 'pair:odd', 'sum:odd']
            instance.prepare_cases = lambda: {'schema': 'solcore-lean.semantic-corpus.v1', 'cases': cases,
                'excluded': [], 'requested': 3, 'attempted': 3, 'status': 'complete'}
            def execute_case(case):
                variant = case['genericPlan']['variant']
                folder = instance.work / variant
                folder.mkdir()
                report = matched()
                if variant != 'word':
                    report['comparison'] = {'category': 'inconclusive-resource' if variant == 'pair' else 'source-rejected', 'pairs': {}}
                return folder, report, campaign.analyze(report)
            instance.execute_case = execute_case
            with redirect_stdout(io.StringIO()):
                instance.run()
            coverage = instance.summary['genericCoverage']
            self.assertEqual(coverage['generatedInstantiations'], ['pair:odd', 'sum:odd', 'word:odd'])
            self.assertEqual(coverage['matchedInstantiations'], ['word:odd'])
            self.assertEqual(coverage['missingInstantiations'], ['pair:odd', 'sum:odd'])
            self.assertTrue(campaign.missing_coverage(instance.summary))

    def test_missing_instantiation_fails_an_otherwise_matched_campaign(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'campaign'
            def run(instance):
                instance.summary['status'] = 'complete'
                instance.summary['counts'].update(generated=1, executed=1, completed=1, matched=1)
                instance.summary['genericCoverage'].update(requiredInstantiations=['word:even', 'word:odd'],
                    generatedInstantiations=['word:odd'], matchedInstantiations=['word:odd'])
            with patch.object(sys, 'argv', ['semantic-campaign', '--output', str(output), '--profile', 'runtime-generics', '--cases', '1']), \
                    patch.object(campaign.Campaign, 'run', run), redirect_stdout(io.StringIO()):
                self.assertEqual(campaign.main(), 1)
            summary = json.loads((output / 'summary.json').read_text())
            self.assertEqual(summary['status'], 'coverage-incomplete')
            self.assertEqual(summary['genericCoverage']['missingInstantiations'], ['word:even'])


class ClosureCoverageTests(unittest.TestCase):
    def manifest(self):
        case = closure_policy_case()
        return {'schema': 'solcore-lean.semantic-corpus-manifest.v1', 'profile': 'runtime-closures',
            **{key: case['provenance'][key] for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion',
                                                       *campaign.PROFILE_VERSION_FIELDS['runtime-closures'])},
            'requiredFeatures': [], 'requiredWordLiterals': [], 'requiredInputs': list(campaign.INPUT_BOUNDARIES),
            'requiredHelperCounts': [1, 2, 3], 'closureRequirements': {'variants': ['snapshot', 'independent']},
            'cases': [{'id': 'closure', 'input': '1', 'closurePlan': case['closurePlan'],
                       'expectedFeatures': case['provenance']['features']}]}

    def test_capture_recipes_are_profile_specific(self):
        value = self.manifest()
        campaign.validate_manifest(value)
        for invalid in (None, {}, {'variants': ['snapshot', 'snapshot']}, {'variants': ['reference']},
                {'variants': [True]}, {'variants': ['independent'], 'unknown': []}):
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'closureRequirements': invalid})
        entry = value['cases'][0]
        for changed in ({**entry, 'program': {}}, {**entry, 'generation': {'seed': '0', 'maxProgramNodes': 384}},
                {'id': 'closure', 'input': '1', 'program': {}, 'expectedFeatures': []},
                {'id': 'closure', 'input': '1', 'genericPlan': {}, 'expectedFeatures': []}):
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'cases': [changed]})
        for profile in ('runtime-generics', 'runtime-loops', 'closed-g0'):
            with self.assertRaises(ValueError):
                campaign.closure_requirements({'profile': profile, 'closureRequirements': value['closureRequirements']})
        for missing in campaign.PROFILE_VERSION_FIELDS['runtime-closures']:
            invalid = copy.deepcopy(value)
            del invalid[missing]
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)

    def test_capture_coverage_uses_the_plan_and_counts_only_step_helpers(self):
        for variant in ('snapshot', 'independent'):
            case = closure_policy_case(variant, 0, 3)
            case['program'] = {}  # Original step, not wrapper/capture lambda count.
            self.assertEqual(campaign.helper_counts(case), {3})
            self.assertEqual(campaign.specified_closures(case), {variant})
            self.assertEqual(campaign.generation_recipes(case), {'Templates': {3}, 'Updates': set()})
        self.assertEqual(campaign.specified_closures(generic_policy_case()), set())
        case['closurePlan']['stepProgram']['resultType'] = 'word'
        with self.assertRaises(ValueError):
            campaign.helper_counts(case)
        case['provenance']['origin']['stepOrigin']['kind'] = 'mutation-generated'
        with self.assertRaises(ValueError):
            campaign.generation_recipes(case)

    def test_generated_manifest_requests_all_four_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            config = options(directory)
            config.profile, config.cases = 'runtime-closures', 1
            value = self.manifest()
            del value['cases'][0]['closurePlan']
            value['cases'][0]['generation'] = {'seed': '0', 'maxProgramNodes': 384}
            config.corpus = Path(directory) / 'manifest.json'
            config.corpus.write_text(json.dumps(value))
            instance = campaign.Campaign(config)
            calls = []
            def tool(arguments, stage):
                calls.append((arguments, stage))
                return {'cases': [closure_policy_case()]}
            instance.tool = tool
            self.assertEqual(len(instance.prepare_cases()['cases']), 1)
            self.assertEqual(calls, [(['closure-generate', '0', '384', '4', '1', '1000'], 'corpus-generation')])
            self.assertEqual(instance.summary['closureCoverage']['generatedVariants'], ['snapshot'])
            self.assertEqual(instance.summary['closureCoverage']['matchedVariants'], [])

    def test_missing_or_nonmatching_capture_recipe_cannot_complete_coverage(self):
        for failure in ('inconclusive-resource', 'source-rejected', 'compilation-rejected'):
            with tempfile.TemporaryDirectory() as directory:
                config = options(directory)
                config.profile, config.cases, config.shrink_attempts = 'runtime-closures', 2, 0
                instance = campaign.Campaign(config)
                cases = [closure_policy_case(v) for v in ('snapshot', 'independent')]
                instance.summary['closureCoverage']['requiredVariants'] = ['snapshot', 'independent']
                instance.prepare_cases = lambda: {'schema': 'solcore-lean.semantic-corpus.v1', 'cases': cases,
                    'excluded': [], 'requested': 2, 'attempted': 2, 'status': 'complete'}
                def execute_case(case):
                    variant = case['closurePlan']['variant']
                    folder = instance.work / variant
                    folder.mkdir()
                    report = matched()
                    if variant != 'snapshot':
                        report['comparison'] = {'category': failure, 'pairs': {}}
                    return folder, report, campaign.analyze(report)
                instance.execute_case = execute_case
                with redirect_stdout(io.StringIO()):
                    instance.run()
                coverage = instance.summary['closureCoverage']
                self.assertEqual(coverage['generatedVariants'], ['independent', 'snapshot'])
                self.assertEqual(coverage['matchedVariants'], ['snapshot'])
                self.assertEqual(coverage['missingVariants'], ['independent'])
                self.assertTrue(campaign.missing_coverage(instance.summary))

    def test_missing_capture_recipe_fails_an_otherwise_matched_campaign(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'campaign'
            def run(instance):
                instance.summary['status'] = 'complete'
                instance.summary['counts'].update(generated=1, executed=1, completed=1, matched=1)
                instance.summary['closureCoverage'].update(requiredVariants=['snapshot', 'independent'],
                    generatedVariants=['snapshot'], matchedVariants=['snapshot'])
            with patch.object(sys, 'argv', ['semantic-campaign', '--output', str(output), '--profile', 'runtime-closures', '--cases', '1']), \
                    patch.object(campaign.Campaign, 'run', run), redirect_stdout(io.StringIO()):
                self.assertEqual(campaign.main(), 1)
            summary = json.loads((output / 'summary.json').read_text())
            self.assertEqual(summary['status'], 'coverage-incomplete')
            self.assertEqual(summary['closureCoverage']['missingVariants'], ['independent'])


class ComptimeCoverageTests(unittest.TestCase):
    def manifest(self):
        case = comptime_policy_case()
        return {'schema': 'solcore-lean.semantic-corpus-manifest.v1', 'profile': 'runtime-comptime',
            **{key: case['provenance'][key] for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion',
                                                       *campaign.PROFILE_VERSION_FIELDS['runtime-comptime'])},
            'requiredFeatures': [], 'requiredWordLiterals': [], 'requiredInputs': list(campaign.INPUT_BOUNDARIES),
            'requiredHelperCounts': [1, 2, 3], 'comptimeRequirements': {'variants': ['offset', 'scale']},
            'requiredConstantFeatures': case['provenance']['constantFeatures'],
            'cases': [{'id': 'comptime', 'input': '1', 'comptimePlan': case['comptimePlan'],
                       'expectedConstantFeatures': case['provenance']['constantFeatures'],
                       'expectedFeatures': case['provenance']['features']}]}

    def test_comptime_recipes_and_original_constant_features_are_required(self):
        value = self.manifest()
        campaign.validate_manifest(value)
        for invalid in (None, {}, {'variants': ['offset', 'offset']}, {'variants': ['runtime']},
                {'variants': [True]}, {'variants': ['scale'], 'unknown': []}):
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'comptimeRequirements': invalid})
        for invalid in (None, ['wordLiteral', 'wordLiteral'], [True], {}):
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'requiredConstantFeatures': invalid})
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'cases': [{**value['cases'][0], 'expectedConstantFeatures': invalid}]})
        for key in ('requiredConstantFeatures', *campaign.PROFILE_VERSION_FIELDS['runtime-comptime']):
            invalid = copy.deepcopy(value)
            del invalid[key]
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        for profile in ('runtime-generics', 'runtime-closures', 'closed-g0'):
            with self.assertRaises(ValueError):
                campaign.comptime_requirements({'profile': profile, 'comptimeRequirements': value['comptimeRequirements']})
            with self.assertRaises(ValueError):
                campaign.constant_requirements({'profile': profile, 'requiredConstantFeatures': ['wordLiteral']})
        entry = value['cases'][0]
        for changed in ({**entry, 'program': {}}, {**entry, 'generation': {'seed': '0', 'maxProgramNodes': 384}},
                {'id': 'comptime', 'input': '1', 'closurePlan': {}, 'expectedFeatures': []}):
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'cases': [changed]})

    def test_constant_features_and_step_helpers_are_separate(self):
        for variant in ('offset', 'scale'):
            case = comptime_policy_case(variant, 0, 3)
            case['program'] = {}
            self.assertEqual(campaign.helper_counts(case), {3})
            self.assertEqual(campaign.specified_comptime(case), {variant})
            self.assertEqual(campaign.generation_recipes(case), {'Templates': {3}, 'Updates': set()})
            self.assertEqual(campaign.constant_features(case), set(case['provenance']['constantFeatures']))
        self.assertEqual(campaign.constant_features(closure_policy_case()), set())
        self.assertEqual(campaign.specified_comptime(closure_policy_case()), set())
        case['provenance']['constantFeatures'] = ['wordLiteral', 'wordLiteral', 'binary:Solcore.Core.Wire.BinaryOp.wordAdd']
        self.assertEqual(campaign.constant_features(case), {'wordLiteral', 'binary:Solcore.Core.Wire.BinaryOp.wordAdd'})
        for invalid in (None, {}, [True]):
            case['provenance']['constantFeatures'] = invalid
            with self.assertRaises(ValueError):
                campaign.constant_features(case)

    def test_generated_manifest_requests_four_inputs_and_checks_constant_inventory(self):
        for forged in (False, True):
            with tempfile.TemporaryDirectory() as directory:
                config = options(directory)
                config.profile, config.cases = 'runtime-comptime', 1
                value = self.manifest()
                del value['cases'][0]['comptimePlan']
                value['cases'][0]['generation'] = {'seed': '0', 'maxProgramNodes': 384}
                if forged:
                    value['cases'][0]['expectedConstantFeatures'] = ['wordLiteral']
                config.corpus = Path(directory) / 'manifest.json'
                config.corpus.write_text(json.dumps(value))
                instance = campaign.Campaign(config)
                calls = []
                def tool(arguments, stage):
                    calls.append((arguments, stage))
                    return {'cases': [comptime_policy_case()]}
                instance.tool = tool
                if forged:
                    with self.assertRaisesRegex(ValueError, 'constant feature inventory changed'):
                        instance.prepare_cases()
                else:
                    self.assertEqual(len(instance.prepare_cases()['cases']), 1)
                    self.assertEqual(instance.summary['comptimeCoverage']['generatedVariants'], ['offset'])
                    self.assertEqual(instance.summary['constantCoverage']['generatedFeatures'], sorted(value['requiredConstantFeatures']))
                    self.assertEqual(instance.summary['constantCoverage']['matchedFeatures'], [])
                self.assertEqual(calls, [(['comptime-generate', '0', '384', '4', '1', '1000'], 'corpus-generation')])

    def test_nonmatching_cases_cannot_satisfy_constant_or_variant_coverage(self):
        for failure in ('inconclusive-resource', 'source-rejected', 'compilation-rejected'):
            with tempfile.TemporaryDirectory() as directory:
                config = options(directory)
                config.profile, config.cases, config.shrink_attempts = 'runtime-comptime', 2, 0
                instance = campaign.Campaign(config)
                cases = [comptime_policy_case(v) for v in ('offset', 'scale')]
                cases[0]['provenance']['constantFeatures'] = ['wordLiteral']
                instance.summary['comptimeCoverage']['requiredVariants'] = ['offset', 'scale']
                instance.summary['constantCoverage']['requiredFeatures'] = cases[1]['provenance']['constantFeatures']
                instance.prepare_cases = lambda: {'schema': 'solcore-lean.semantic-corpus.v1', 'cases': cases,
                    'excluded': [], 'requested': 2, 'attempted': 2, 'status': 'complete'}
                def execute_case(case):
                    variant = case['comptimePlan']['variant']
                    folder = instance.work / variant
                    folder.mkdir()
                    report = matched()
                    if variant != 'offset':
                        report['comparison'] = {'category': failure, 'pairs': {}}
                    return folder, report, campaign.analyze(report)
                instance.execute_case = execute_case
                with redirect_stdout(io.StringIO()):
                    instance.run()
                self.assertEqual(instance.summary['comptimeCoverage']['matchedVariants'], ['offset'])
                self.assertEqual(instance.summary['comptimeCoverage']['missingVariants'], ['scale'])
                self.assertEqual(instance.summary['constantCoverage']['matchedFeatures'], ['wordLiteral'])
                self.assertEqual(instance.summary['constantCoverage']['missingFeatures'], ['binary:Solcore.Core.Wire.BinaryOp.wordAdd'])
                self.assertTrue(campaign.missing_coverage(instance.summary))

    def test_missing_constant_coverage_fails_an_otherwise_matched_campaign(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'campaign'
            def run(instance):
                instance.summary['status'] = 'complete'
                instance.summary['counts'].update(generated=1, executed=1, completed=1, matched=1)
                instance.summary['constantCoverage'].update(requiredFeatures=['wordLiteral', 'if'],
                    generatedFeatures=['wordLiteral'], matchedFeatures=['wordLiteral'])
            with patch.object(sys, 'argv', ['semantic-campaign', '--output', str(output), '--profile', 'runtime-comptime', '--cases', '1']), \
                    patch.object(campaign.Campaign, 'run', run), redirect_stdout(io.StringIO()):
                self.assertEqual(campaign.main(), 1)
            summary = json.loads((output / 'summary.json').read_text())
            self.assertEqual(summary['status'], 'coverage-incomplete')
            self.assertEqual(summary['constantCoverage']['missingFeatures'], ['if'])


class ModuleCoverageTests(unittest.TestCase):
    def manifest(self):
        case = module_policy_case()
        return {'schema': 'solcore-lean.semantic-corpus-manifest.v1', 'profile': 'runtime-modules',
            **{key: case['provenance'][key] for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion',
                                                       *campaign.PROFILE_VERSION_FIELDS['runtime-modules'])},
            'requiredFeatures': [], 'requiredWordLiterals': [], 'requiredInputs': list(campaign.INPUT_BOUNDARIES),
            'requiredHelperCounts': [1, 2, 3], 'moduleRequirements': {'branches': ['even', 'odd']},
            'requiredConstantFeatures': case['provenance']['constantFeatures'],
            'cases': [{'id': 'module', 'input': '1', 'modulePlan': case['modulePlan'],
                       'expectedConstantFeatures': case['provenance']['constantFeatures'],
                       'expectedFeatures': case['provenance']['features']}]}

    def test_bundle_profile_requires_its_plan_and_both_feature_inventories(self):
        value = self.manifest()
        campaign.validate_manifest(value)
        for invalid in (None, {}, {'branches': ['odd', 'odd']}, {'branches': ['left']},
                {'branches': [True]}, {'branches': ['even'], 'unknown': []}):
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'moduleRequirements': invalid})
        for invalid in (None, ['wordLiteral', 'wordLiteral'], [True], {}):
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'requiredConstantFeatures': invalid})
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'cases': [{**value['cases'][0], 'expectedConstantFeatures': invalid}]})
        for key in ('requiredConstantFeatures', *campaign.PROFILE_VERSION_FIELDS['runtime-modules']):
            invalid = copy.deepcopy(value)
            del invalid[key]
            with self.assertRaises(ValueError):
                campaign.validate_manifest(invalid)
        for profile in ('runtime-generics', 'runtime-comptime', 'closed-g0'):
            with self.assertRaises(ValueError):
                campaign.module_requirements({'profile': profile, 'moduleRequirements': value['moduleRequirements']})
        entry = value['cases'][0]
        for changed in ({**entry, 'program': {}}, {**entry, 'generation': {'seed': '0', 'maxProgramNodes': 384}},
                {'id': 'module', 'input': '1', 'comptimePlan': {}, 'expectedFeatures': []}):
            with self.assertRaises(ValueError):
                campaign.validate_manifest({**value, 'cases': [changed]})

    def test_original_constant_and_step_features_exclude_module_wrappers(self):
        for value in (0, 1, 2**255, 2**256 - 1):
            case = module_policy_case(value, 3)
            case['program'] = {}
            self.assertEqual(campaign.helper_counts(case), {3})
            self.assertEqual(campaign.specified_modules(case), {'odd' if value & 1 else 'even'})
            self.assertEqual(campaign.generation_recipes(case), {'Templates': {3}, 'Updates': set()})
            self.assertEqual(campaign.constant_features(case), set(case['provenance']['constantFeatures']))
        self.assertEqual(campaign.specified_modules(comptime_policy_case()), set())
        case['provenance']['constantFeatures'] = ['wordLiteral', 'wordLiteral']
        self.assertEqual(campaign.constant_features(case), {'wordLiteral'})

    def test_generated_manifest_requests_four_inputs_and_checks_constant_inventory(self):
        for forged in (False, True):
            with tempfile.TemporaryDirectory() as directory:
                config = options(directory)
                config.profile, config.cases = 'runtime-modules', 1
                value = self.manifest()
                del value['cases'][0]['modulePlan']
                value['cases'][0]['generation'] = {'seed': '0', 'maxProgramNodes': 384}
                if forged: value['cases'][0]['expectedConstantFeatures'] = ['wordLiteral']
                config.corpus = Path(directory) / 'manifest.json'
                config.corpus.write_text(json.dumps(value))
                instance = campaign.Campaign(config)
                calls = []
                def tool(arguments, stage):
                    calls.append((arguments, stage))
                    return {'cases': [module_policy_case()]}
                instance.tool = tool
                if forged:
                    with self.assertRaisesRegex(ValueError, 'constant feature inventory changed'):
                        instance.prepare_cases()
                else:
                    self.assertEqual(len(instance.prepare_cases()['cases']), 1)
                    self.assertEqual(instance.summary['moduleCoverage']['generatedBranches'], ['odd'])
                    self.assertEqual(instance.summary['constantCoverage']['generatedFeatures'], sorted(value['requiredConstantFeatures']))
                    self.assertEqual(instance.summary['constantCoverage']['matchedFeatures'], [])
                self.assertEqual(calls, [(['module-generate', '0', '384', '4', '1', '1000'], 'corpus-generation')])

    def test_resource_and_rejection_cannot_satisfy_module_branch_or_constant_coverage(self):
        for failure in ('inconclusive-resource', 'source-rejected', 'compilation-rejected'):
            with tempfile.TemporaryDirectory() as directory:
                config = options(directory)
                config.profile, config.cases, config.shrink_attempts = 'runtime-modules', 2, 0
                instance = campaign.Campaign(config)
                cases = [module_policy_case(i) for i in (0, 1)]
                cases[0]['provenance']['constantFeatures'] = ['wordLiteral']
                instance.summary['moduleCoverage']['requiredBranches'] = ['even', 'odd']
                instance.summary['constantCoverage']['requiredFeatures'] = cases[1]['provenance']['constantFeatures']
                instance.prepare_cases = lambda: {'schema': 'solcore-lean.semantic-corpus.v1', 'cases': cases,
                    'excluded': [], 'requested': 2, 'attempted': 2, 'status': 'complete'}
                def execute_case(case):
                    folder = instance.work / case['input']
                    folder.mkdir()
                    report = matched()
                    if case['input'] != '0': report['comparison'] = {'category': failure, 'pairs': {}}
                    return folder, report, campaign.analyze(report)
                instance.execute_case = execute_case
                with redirect_stdout(io.StringIO()): instance.run()
                self.assertEqual(instance.summary['moduleCoverage']['matchedBranches'], ['even'])
                self.assertEqual(instance.summary['moduleCoverage']['missingBranches'], ['odd'])
                self.assertEqual(instance.summary['constantCoverage']['matchedFeatures'], ['wordLiteral'])
                self.assertEqual(instance.summary['constantCoverage']['missingFeatures'], ['binary:Solcore.Core.Wire.BinaryOp.wordAdd'])
                self.assertTrue(campaign.missing_coverage(instance.summary))

    def test_missing_module_branch_fails_an_otherwise_matched_campaign(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'campaign'
            def run(instance):
                instance.summary['status'] = 'complete'
                instance.summary['counts'].update(generated=1, executed=1, completed=1, matched=1)
                instance.summary['moduleCoverage'].update(requiredBranches=['even', 'odd'],
                    generatedBranches=['odd'], matchedBranches=['odd'])
            with patch.object(sys, 'argv', ['semantic-campaign', '--output', str(output), '--profile', 'runtime-modules', '--cases', '1']), \
                    patch.object(campaign.Campaign, 'run', run), redirect_stdout(io.StringIO()):
                self.assertEqual(campaign.main(), 1)
            summary = json.loads((output / 'summary.json').read_text())
            self.assertEqual(summary['status'], 'coverage-incomplete')
            self.assertEqual(summary['moduleCoverage']['missingBranches'], ['even'])


class PrimitiveCoverageTests(unittest.TestCase):
    def case(self, value='255'):
        # Admission/coverage policy fixture, never a claimed compiler execution.
        number = int(value)
        body = {'tag': 'binary', 'op': 'wordDiv', 'left': {'tag': 'var', 'index': 0},
                'right': {'tag': 'word', 'value': '0x' + f'{2:064x}'}}
        function = {'tag': 'lambda', 'parameterType': 'word', 'resultType': 'word', 'body': body}
        return {'schema': campaign.m2.PRIMITIVE_CASE_SCHEMA, 'input': value, 'source': '// primitive policy fixture',
            'program': {'schema': 'solcore-semantic-core', 'resultType': 'word', 'dataDefinitions': [],
                'body': {'tag': 'apply', 'function': function,
                         'argument': {'tag': 'word', 'value': '0x' + f'{number:064x}'}}},
            'provenance': {**{key: 'test' for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion',
                                                   *campaign.PRIMITIVE_VERSIONS)},
                'origin': {'kind': 'primitive-generated', 'seed': '1', 'maxProgramNodes': 96},
                'features': ['binary:Solcore.Core.Wire.BinaryOp.wordDiv', 'local', 'wordLiteral']},
            'contract': {'name': 'SynthesizedPrimitives', 'method': 'run', 'signature': 'run(uint256)',
                'deployPath': ['SynthesizedPrimitivesDeploy'], 'runtimePath': ['SynthesizedPrimitivesDeploy', 'SynthesizedPrimitives'],
                'calldata': '0xa444f5e9' + f'{number:064x}', 'constructorCalldata': '0x'}}

    def manifest(self, generated=False):
        case = self.case()
        program = {**case['program'], 'resultType': {'tag': 'function', 'parameter': 'word', 'result': 'word'},
                   'body': case['program']['body']['function']}
        entry = {'id': 'primitive', 'input': '255', 'expectedFeatures': case['provenance']['features'],
                 **({'generation': {'seed': '1', 'maxProgramNodes': 96}} if generated else {'program': program})}
        return {'schema': 'solcore-lean.semantic-corpus-manifest.v1', 'profile': 'runtime-primitives',
            **{key: case['provenance'][key] for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion',
                                                     *campaign.PRIMITIVE_VERSIONS)},
            'requiredFeatures': sorted(campaign.PRIMITIVE_FEATURES), 'requiredWordLiterals': [],
            'requiredInputs': list(campaign.PRIMITIVE_INPUTS), 'cases': [entry]}

    def test_primitive_bank_does_not_change_legacy_generation_order(self):
        self.assertEqual(campaign.profile_inputs('runtime-primitives'),
            ('0', '1', '2', '255', '256', str(2**256 - 1), str(2**255), str(2**255 - 1)))
        self.assertEqual(campaign.profile_inputs('runtime-word'), campaign.INPUT_BOUNDARIES)
        self.assertEqual(campaign.INPUT_BOUNDARIES, ('0', '1', str(2**256 - 1), str(2**255)))
        self.assertEqual(campaign.profile_inputs('runtime-loops'), campaign.LOOP_INPUTS)
        self.assertEqual(len(campaign.PRIMITIVE_FEATURES), 14)
        self.assertIn('binary:Solcore.Core.Wire.BinaryOp.wordPow', campaign.PRIMITIVE_FEATURES)
        self.assertFalse(any('wordExp' in feature for feature in campaign.PRIMITIVE_FEATURES))

    def test_fixed_manifest_cannot_drop_new_operator_or_input_requirements(self):
        value = self.manifest()
        campaign.validate_manifest(value)
        for key in ('requiredFeatures', 'requiredInputs'):
            for missing in value[key]:
                with self.subTest(key=key, missing=missing), self.assertRaises(ValueError):
                    campaign.validate_manifest({**value, key: [x for x in value[key] if x != missing]})
        for key in campaign.PRIMITIVE_VERSIONS:
            broken = copy.deepcopy(value)
            del broken[key]
            with self.assertRaisesRegex(ValueError, key):
                campaign.validate_manifest(broken)
        generated = self.manifest(True)
        for invalid in ('3', '254'):
            bad = copy.deepcopy(generated); bad['cases'][0]['input'] = invalid
            with self.assertRaises(ValueError): campaign.validate_manifest(bad)
        for invalid in (3, 7, 513):
            bad = copy.deepcopy(generated); bad['cases'][0]['generation']['maxProgramNodes'] = invalid
            with self.assertRaises(ValueError): campaign.validate_manifest(bad)
        # Imported cases can use other runtime inputs; bank requirements are global.
        imported = self.manifest(); imported['cases'][0]['input'] = '3'
        campaign.validate_manifest(imported)

    def test_generated_manifest_requests_eight_and_checks_origin_features_and_versions(self):
        for tamper in (None, 'seed', 'nodes', 'features', 'boundaryVersion'):
            with self.subTest(tamper=tamper), tempfile.TemporaryDirectory() as directory:
                config = options(directory); config.profile, config.cases = 'runtime-primitives', 1
                config.corpus = Path(directory) / 'manifest.json'
                config.corpus.write_text(json.dumps(self.manifest(True)))
                instance = campaign.Campaign(config); calls = []
                case = self.case()
                if tamper == 'seed': case['provenance']['origin']['seed'] = '2'
                if tamper == 'nodes': case['provenance']['origin']['maxProgramNodes'] = 97
                if tamper == 'features': case['provenance']['features'] = []
                if tamper == 'boundaryVersion': case['provenance']['boundaryVersion'] = 'forged-bank'
                def tool(arguments, stage):
                    calls.append((arguments, stage)); return {'cases': [case]}
                instance.tool = tool
                if tamper:
                    with self.assertRaises(ValueError): instance.prepare_cases()
                else:
                    self.assertEqual(instance.prepare_cases()['cases'], [case])
                    self.assertEqual(instance.summary['coverage']['generatedInputs'], ['255'])
                    self.assertEqual(instance.summary['coverage']['matchedInputs'], [])
                self.assertEqual(calls, [(['primitive-generate', '1', '96', '8', '1', '1000'], 'corpus-generation')])

    def test_imported_function_routes_to_primitive_emit_without_using_saved_golden(self):
        with tempfile.TemporaryDirectory() as directory:
            config = options(directory); config.profile, config.cases = 'runtime-primitives', 1
            value = self.manifest(); value['cases'][0]['expectedCore'] = 'untrusted-golden-is-ignored'
            config.corpus = Path(directory) / 'manifest.json'; config.corpus.write_text(json.dumps(value))
            instance = campaign.Campaign(config); calls = []
            def tool(arguments, stage):
                calls.append((arguments[0], json.loads(Path(arguments[1]).read_text()), arguments[2:], stage))
                return self.case()
            instance.tool = tool
            self.assertEqual(instance.prepare_cases()['cases'], [self.case()])
            self.assertEqual(calls, [('primitive-emit', value['cases'][0]['program'], ['255', '1000'], 'corpus-emission')])
            self.assertEqual(campaign.helper_counts(self.case()), set())

    def test_primitive_coverage_requires_matched_cases_not_generated_ast_claims(self):
        for failure in ('inconclusive-resource', 'source-rejected', 'compilation-rejected'):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as directory:
                config = options(directory); config.profile, config.cases, config.shrink_attempts = 'runtime-primitives', 1, 0
                instance = campaign.Campaign(config); case = self.case()
                def prepare():
                    instance.summary['coverage'].update(requiredFeatures=list(campaign.PRIMITIVE_FEATURES),
                        requiredInputs=list(campaign.PRIMITIVE_INPUTS))
                    return {'schema': 'solcore-lean.semantic-corpus.v1', 'cases': [case],
                        'excluded': [], 'requested': 1, 'attempted': 1, 'status': 'complete'}
                def execute(_case):
                    folder = instance.work / 'candidate'; folder.mkdir()
                    report = {'comparison': {'category': failure, 'pairs': {}}, 'observations': {}}
                    return folder, report, campaign.analyze(report)
                instance.prepare_cases, instance.execute_case = prepare, execute
                with redirect_stdout(io.StringIO()): instance.run()
                coverage = instance.summary['coverage']
                self.assertEqual(coverage['matchedFeatures'], [])
                self.assertEqual(coverage['matchedInputs'], [])
                self.assertEqual(set(coverage['missingFeatures']), campaign.PRIMITIVE_FEATURES)
                self.assertEqual(set(coverage['missingInputs']), set(campaign.PRIMITIVE_INPUTS))
                self.assertTrue(campaign.missing_coverage(instance.summary))

    def test_default_limits_and_native_random_command(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'campaign'
            seen = []
            def run(instance):
                instance.tool = lambda arguments, stage: seen.append((arguments, stage)) or {}
                instance.prepare_cases(); instance.summary['status'] = 'generation-exhausted'
            with patch.object(sys, 'argv', ['semantic-campaign', '--output', str(output), '--profile', 'runtime-primitives', '--cases', '1']), \
                    patch.object(campaign.Campaign, 'run', run), redirect_stdout(io.StringIO()):
                campaign.main()
            self.assertEqual(seen, [(['primitive-generate', '1', '96', '1', '512', '1000000'], 'generation')])

    def test_primitive_execution_and_shrink_keep_every_backend(self):
        for backend in campaign.m2.BACKENDS:
            with self.subTest(backend=backend), tempfile.TemporaryDirectory() as directory:
                config = options(directory); config.profile, config.backend = 'runtime-primitives', backend
                config.test_perturb_path = 'rustEvm'; config.upstream, config.target_dir = Path('/unused/upstream'), Path('/unused/target')
                instance = campaign.Campaign(config); selected = []
                original, candidate = self.case('255'), self.case('1')
                def execute(args, report):
                    selected.append(args.backend); report.update(matched(), backend=args.backend)
                    campaign.save_json(args.output / 'case.json', json.loads(args.case.read_text()))
                with patch.object(campaign.m2, 'execute', side_effect=execute):
                    folder, report, analysis = instance.execute_case(original)
                    finding = instance.retain_finding(0, folder, original, report, analysis)
                    instance.tool = lambda *_: {'schema': 'solcore-lean.semantic-corpus.v1', 'cases': [candidate]}
                    instance.shrink(original, finding)
                self.assertEqual(selected, [backend, backend])
                history = json.loads((Path(directory) / finding['history']).read_text())
                self.assertTrue(history['steps'][0]['accepted'])
                self.assertEqual(history['steps'][0]['fingerprint']['backend'], backend)


class CallGraphCoverageTests(unittest.TestCase):
    def case(self, value='255', helpers=2):
        case = function_case(helpers)
        case.update(schema=campaign.m2.CALL_GRAPH_CASE_SCHEMA, input=value)
        case['program']['body']['argument']['value'] = '0x' + f'{int(value):064x}'
        case['provenance'].update({key: 'test' for key in campaign.m2.CALL_GRAPH_VERSIONS})
        case['provenance'].update(helperCount=helpers, callShapes=['nested-call', 'local-call'],
            origin={'kind': 'call-graph-generated', 'seed': '1', 'maxProgramNodes': 192})
        case['contract'].update(name='SynthesizedCallGraphs', deployPath=['SynthesizedCallGraphsDeploy'],
            runtimePath=['SynthesizedCallGraphsDeploy', 'SynthesizedCallGraphs'],
            calldata='0xa444f5e9' + f'{int(value):064x}')
        return case

    def manifest(self, generated=False):
        case = self.case()
        program = {**case['program'], 'resultType': {'tag': 'function', 'parameter': 'word', 'result': 'word'},
            'body': case['program']['body']['function']}
        return {'schema': 'solcore-lean.semantic-corpus-manifest.v1', 'profile': 'runtime-call-graphs',
            **{key: case['provenance'][key] for key in ('generatorVersion', 'emitterVersion', 'wrapperVersion',
                *campaign.m2.CALL_GRAPH_VERSIONS)},
            'requiredFeatures': ['functionCall', 'local'], 'requiredWordLiterals': [],
            'requiredInputs': list(campaign.PRIMITIVE_INPUTS), 'requiredHelperCounts': [1, 2, 3],
            'requiredCallShapes': list(campaign.m2.CALL_SHAPES),
            'cases': [{'id': 'graph', 'input': '255', 'expectedFeatures': ['functionCall', 'local'],
                'expectedCallShapes': case['provenance']['callShapes'], 'expectedHelperCount': 2,
                **({'generation': {'seed': '1', 'maxProgramNodes': 192}} if generated else {'program': program})}]}

    def test_manifest_shape_input_and_node_gates(self):
        manifest = self.manifest(True)
        campaign.validate_manifest(manifest)
        for value in (None, ['unknown'], ['nested-call', 'nested-call'], ['local-call', 'nested-call']):
            with self.assertRaisesRegex(ValueError, 'canonical'):
                campaign.validate_manifest({**manifest, 'requiredCallShapes': value})
        missing = dict(manifest); del missing['requiredCallShapes']
        with self.assertRaises(ValueError): campaign.validate_manifest(missing)
        for field in campaign.m2.CALL_GRAPH_VERSIONS:
            missing = dict(manifest); del missing[field]
            with self.assertRaisesRegex(ValueError, field): campaign.validate_manifest(missing)
        with self.assertRaisesRegex(ValueError, 'eight boundary'):
            campaign.validate_manifest({**manifest, 'requiredInputs': ['0']})
        for value in (12, 513, True):
            changed = copy.deepcopy(manifest); changed['cases'][0]['generation']['maxProgramNodes'] = value
            with self.assertRaises(ValueError): campaign.validate_manifest(changed)
        for value in (13, 512):
            changed = copy.deepcopy(manifest); changed['cases'][0]['generation']['maxProgramNodes'] = value
            campaign.validate_manifest(changed)
        old = PrimitiveCoverageTests().manifest(); old['requiredCallShapes'] = ['nested-call']
        with self.assertRaisesRegex(ValueError, 'only call-graph'): campaign.validate_manifest(old)

    def test_helper_count_is_checked_against_declarations_not_claimed_origin(self):
        for count in (1, 2, 3):
            case = self.case(helpers=count)
            self.assertEqual(campaign.helper_counts(case), {count})
            case['provenance']['helperCount'] = 1 if count != 1 else 2
            with self.assertRaisesRegex(ValueError, 'declaration'): campaign.helper_counts(case)
        self.assertEqual(campaign.profile_inputs('runtime-call-graphs'), campaign.PRIMITIVE_INPUTS)
        self.assertEqual(campaign.generation_recipes(self.case()), {'Templates': set(), 'Updates': set()})

    def test_materialization_routes_eight_inputs_and_matches_expected_metadata(self):
        for generated in (False, True):
            for tamper in (None, 'shapes', 'helper', 'version', 'seed'):
                if not generated and tamper == 'seed': continue
                with self.subTest(generated=generated, tamper=tamper), tempfile.TemporaryDirectory() as directory:
                    config = options(directory); config.profile, config.cases = 'runtime-call-graphs', 1
                    config.corpus = Path(directory) / 'manifest.json'
                    manifest = self.manifest(generated); config.corpus.write_text(json.dumps(manifest))
                    instance = campaign.Campaign(config); calls = []; case = self.case()
                    if tamper == 'shapes': case['provenance']['callShapes'] = ['diamond']
                    if tamper == 'helper': case['provenance']['helperCount'] = 3
                    if tamper == 'version': case['provenance']['callShapeVersion'] = 'wrong'
                    if tamper == 'seed': case['provenance']['origin']['seed'] = '9'
                    def tool(arguments, stage):
                        calls.append((arguments, stage))
                        if generated: return {'cases': [case]}
                        self.assertEqual(json.loads(Path(arguments[1]).read_text()), manifest['cases'][0]['program'])
                        return case
                    instance.tool = tool
                    if tamper:
                        with self.assertRaises(ValueError): instance.prepare_cases()
                    else:
                        self.assertEqual(instance.prepare_cases()['cases'], [case])
                        self.assertEqual(instance.summary['callShapeCoverage']['generatedShapes'], ['nested-call', 'local-call'])
                        self.assertEqual(instance.summary['callShapeCoverage']['matchedShapes'], [])
                    if generated:
                        self.assertEqual(calls, [(['call-graph-generate', '1', '192', '8', '1', '1000'], 'corpus-generation')])
                    else:
                        self.assertEqual(calls[0][0][0], 'call-graph-emit')
                        self.assertEqual(calls[0][0][2:], ['255', '1000'])

    def test_only_actual_matched_cases_satisfy_required_shapes(self):
        for category in ('matched', 'inconclusive-resource', 'source-rejected', 'semantic-mismatch'):
            with self.subTest(category=category), tempfile.TemporaryDirectory() as directory:
                config = options(directory); config.profile, config.cases, config.shrink_attempts = 'runtime-call-graphs', 1, 0
                instance = campaign.Campaign(config); case = self.case()
                def prepare():
                    instance.summary['callShapeCoverage']['requiredShapes'] = list(campaign.m2.CALL_SHAPES)
                    return {'schema': 'solcore-lean.semantic-corpus.v1', 'cases': [case], 'excluded': [],
                        'requested': 1, 'attempted': 1, 'status': 'complete'}
                def execute(_case):
                    folder = instance.work / 'candidate'; folder.mkdir()
                    report = matched()
                    if category != 'matched': report['comparison'] = {'category': category, 'pairs': {}}
                    return folder, report, campaign.analyze(report)
                instance.prepare_cases, instance.execute_case = prepare, execute
                with redirect_stdout(io.StringIO()): instance.run()
                coverage = instance.summary['callShapeCoverage']
                expected = ['nested-call', 'local-call'] if category == 'matched' else []
                self.assertEqual(coverage['matchedShapes'], expected)
                self.assertEqual(coverage['missingShapes'], [s for s in campaign.m2.CALL_SHAPES if s not in expected])
                self.assertTrue(campaign.missing_coverage(instance.summary))

    def test_complete_shape_coverage_and_old_profiles_are_separate(self):
        with tempfile.TemporaryDirectory() as directory:
            config = options(directory); config.profile = 'runtime-call-graphs'
            instance = campaign.Campaign(config)
            case = self.case(); case['provenance']['callShapes'] = list(campaign.m2.CALL_SHAPES)
            instance.summary['callShapeCoverage']['requiredShapes'] = list(campaign.m2.CALL_SHAPES)
            instance.record_call_shapes(case, matched=True); instance.checkpoint()
            self.assertEqual(instance.summary['callShapeCoverage']['missingShapes'], [])
            self.assertFalse(campaign.missing_coverage(instance.summary))
        with tempfile.TemporaryDirectory() as directory:
            instance = campaign.Campaign(options(directory))
            self.assertNotIn('callShapeCoverage', instance.summary)
            instance.record_call_shapes(function_case(1)); instance.checkpoint()
            self.assertNotIn('callShapeCoverage', instance.summary)

    def test_default_random_limits_and_explicit_limits_route_unchanged(self):
        for extra, expected in (([], ['192', '1', '1024']), (['--nodes', '128', '--attempts', '7'], ['128', '1', '7'])):
            with tempfile.TemporaryDirectory() as directory:
                seen = []
                def run(instance):
                    instance.tool = lambda arguments, stage: seen.append(arguments) or {}
                    instance.prepare_cases(); instance.summary['status'] = 'generation-exhausted'
                with patch.object(sys, 'argv', ['semantic-campaign', '--output', str(Path(directory)/'run'),
                        '--profile', 'runtime-call-graphs', '--cases', '1', *extra]),                         patch.object(campaign.Campaign, 'run', run), redirect_stdout(io.StringIO()):
                    campaign.main()
                self.assertEqual(seen, [['call-graph-generate', '1', *expected, '1000000']])

    def test_call_graph_shrink_keeps_schema_backend_and_explicit_synthetic_separation(self):
        for backend in campaign.m2.BACKENDS:
            with self.subTest(backend=backend), tempfile.TemporaryDirectory() as directory:
                config = options(directory); config.profile, config.backend = 'runtime-call-graphs', backend
                config.test_perturb_path = 'rustEvm'; config.upstream, config.target_dir = Path('/unused/u'), Path('/unused/t')
                instance = campaign.Campaign(config); selected = []
                original, candidate = self.case('255'), self.case('1')
                def execute(args, report):
                    selected.append(args.backend); report.update(matched(), backend=args.backend)
                    campaign.save_json(args.output/'case.json', json.loads(args.case.read_text()))
                with patch.object(campaign.m2, 'execute', side_effect=execute):
                    folder, report, analysis = instance.execute_case(original)
                    finding = instance.retain_finding(0, folder, original, report, analysis)
                    instance.tool = lambda *_: {'schema': 'solcore-lean.semantic-corpus.v1', 'cases': [candidate]}
                    instance.shrink(original, finding)
                self.assertEqual(selected, [backend, backend])
                history = json.loads((Path(directory)/finding['history']).read_text())
                self.assertTrue(history['steps'][0]['accepted'])
                self.assertEqual(history['steps'][0]['actualComparison']['category'], 'matched')
                self.assertEqual(history['steps'][0]['fingerprint']['backend'], backend)


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
