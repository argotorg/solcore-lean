#!/usr/bin/env python3
"""Campaign policy tests; real compiler/EVM runs are checked separately."""
import copy
import importlib.util
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

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("semantic_campaign", ROOT / "scripts/semantic-campaign.py")
campaign = importlib.util.module_from_spec(spec)
spec.loader.exec_module(campaign)


def matched():
    observed = {path: {"status": "returned", "word": "7"} for path in campaign.PATHS}
    return {"comparison": campaign.m2.compare(observed), "observations": observed}


def options(directory):
    return SimpleNamespace(output=Path(directory), seed=1, nodes=16, cases=2, attempts=16,
        seconds=30, disk_bytes=16 * 1024 * 1024, shrink_attempts=4, shrink_candidates=8,
        direct_fuel=1000, core_fuel=1000, gas=100000, case_timeout=10,
        case_tool=Path('/unused/case-tool'), core_runner=Path('/unused/core-runner'),
        anvil=Path('/unused/anvil'), test_perturb_path=None)


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
