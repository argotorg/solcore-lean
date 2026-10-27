#!/usr/bin/env python3
"""Orchestration policy tests; fake campaign summaries are not EVM executions."""
from __future__ import annotations

import contextlib
import copy
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
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("semantic_suite", ROOT / "scripts/semantic-suite.py")
suite = importlib.util.module_from_spec(spec)
spec.loader.exec_module(suite)


def completed(profile="closed-g0", count=4):
    return {"schema": suite.CAMPAIGN_SCHEMAS[suite.PROFILES[profile][1]], "status": "complete", "synthetic": False,
            "configuration": {"profile": profile}, "counts": {"generated": count, "executed": count,
                "completed": count, "matched": count, "unexecuted": 0, "errors": 0, "inconclusive": 0},
            "coverage": {"requiredFeatures": ["wordLiteral"], "matchedFeatures": ["wordLiteral"], "missingFeatures": []},
            "findings": [], "secondaryFindings": []}


class SuiteTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="semantic-suite-test-")
        self.directory = Path(self.temporary.name).resolve()

    def tearDown(self):
        self.temporary.cleanup()

    def args(self, *extra):
        return suite.parse_args(["--output", str(self.directory / "run"), *extra])

    def test_twenty_five_profiles_match_real_manifests_and_campaign_families(self):
        args = self.args()
        self.assertEqual(len(args.profile), 25)
        self.assertEqual(args.profile, list(suite.PROFILES))
        self.assertEqual(sum(suite.requested(args, p) for p in args.profile
            if p not in ("runtime-primitives", "runtime-call-graphs", "runtime-call-graph-loops",
                         "runtime-aggregate-call-graphs", "stateful-keyed-storage", "stateful-dynamic-array",
                         "stateful-logs", "stateful-call-value", "stateful-bytes", "stateful-forwarded-value",
                         "stateful-mapping", "stateful-ledger")), 378)
        self.assertGreater(suite.requested(args, "runtime-primitives"), 0)
        self.assertGreater(suite.requested(args, "runtime-call-graph-loops"), 0)
        self.assertGreater(suite.requested(args, "runtime-aggregate-call-graphs"), 0)
        for profile in args.profile:
            command = suite.command(args, profile, self.directory / profile, 30, 64 * 1024**2)
            self.assertEqual(command[command.index("--profile") + 1], profile)
            self.assertEqual(Path(command[command.index("--corpus") + 1]), suite.manifest(profile))
            self.assertNotIn("--cases", command)
            self.assertNotIn("--seed", command)
            self.assertNotIn("lake", command)
            self.assertNotIn("cargo", command)
        self.assertEqual(suite.PROFILES["stateful-storage-rollback"][1], "storage")
        self.assertEqual(suite.PROFILES["stateful-calls"][1], "call")
        self.assertEqual(suite.PROFILES["stateful-keyed-storage"], ("semantic-keyed-storage", "storage", 384))
        self.assertEqual(suite.requested(args, "stateful-keyed-storage"),
                         len(json.loads(suite.manifest("stateful-keyed-storage").read_text())["cases"]))
        self.assertEqual(suite.PROFILES["stateful-dynamic-array"], ("semantic-dynamic-array", "storage", 384))
        self.assertEqual(suite.requested(args, "stateful-dynamic-array"),
                         len(json.loads(suite.manifest("stateful-dynamic-array").read_text())["cases"]))
        self.assertEqual(suite.PROFILES["stateful-logs"], ("semantic-log", "storage", 384))
        self.assertEqual(suite.requested(args, "stateful-logs"),
                         len(json.loads(suite.manifest("stateful-logs").read_text())["cases"]))
        self.assertIn("stateful-logs", suite.DECLARED_SLOT_PROFILES)
        self.assertEqual(suite.PROFILES["stateful-call-value"], ("semantic-call-value", "storage", 384))
        self.assertEqual(suite.requested(args, "stateful-call-value"),
                         len(json.loads(suite.manifest("stateful-call-value").read_text())["cases"]))
        self.assertEqual(suite.PROFILES["stateful-bytes"], ("semantic-bytes", "storage", 384))
        self.assertEqual(suite.requested(args, "stateful-bytes"),
                         len(json.loads(suite.manifest("stateful-bytes").read_text())["cases"]))
        self.assertIn("stateful-bytes", suite.DECLARED_SLOT_PROFILES)
        self.assertEqual(suite.PROFILES["stateful-forwarded-value"], ("semantic-forward", "call", 384))
        self.assertEqual(suite.requested(args, "stateful-forwarded-value"),
                         len(json.loads(suite.manifest("stateful-forwarded-value").read_text())["cases"]))
        self.assertEqual(suite.PROFILES["stateful-mapping"], ("semantic-mapping", "storage", 384))
        self.assertEqual(suite.requested(args, "stateful-mapping"),
                         len(json.loads(suite.manifest("stateful-mapping").read_text())["cases"]))
        self.assertIn("stateful-mapping", suite.DECLARED_SLOT_PROFILES)
        self.assertEqual(suite.PROFILES["stateful-ledger"], ("semantic-ledger", "storage", 384))
        self.assertEqual(suite.requested(args, "stateful-ledger"),
                         len(json.loads(suite.manifest("stateful-ledger").read_text())["cases"]))
        # The ledger declares its slots but runs its own multi-sender Hull runner.
        self.assertNotIn("stateful-ledger", suite.DECLARED_SLOT_PROFILES)

    def test_primitive_profile_routes_its_manifest_and_random_defaults_under_all_backends(self):
        self.assertEqual(suite.PROFILES['runtime-primitives'], ('semantic-primitive', 'pure', 96))
        for backend in suite.adapter.BACKENDS:
            fixed = self.args('--backend', backend, '--profile', 'runtime-primitives')
            command = suite.command(fixed, 'runtime-primitives', self.directory / backend, 30, 64 * 1024**2)
            self.assertEqual(command[command.index('--corpus') + 1], str(suite.manifest('runtime-primitives')))
            self.assertEqual(command[command.index('--backend') + 1], backend)
            self.assertEqual(Path(command[1]).name, 'semantic-campaign.py')
            random = self.args('--mode', 'random', '--backend', backend, '--profile', 'runtime-primitives')
            command = suite.command(random, 'runtime-primitives', self.directory / (backend + '-random'), 30, 64 * 1024**2)
            self.assertEqual(command[command.index('--nodes') + 1], '96')
            self.assertEqual(command[command.index('--attempts') + 1], '512')
            self.assertEqual('--solc' in command, backend == 'yul')

    def test_missing_primitive_operator_or_boundary_prevents_suite_pass(self):
        for backend in suite.adapter.BACKENDS:
            summary = completed('runtime-primitives')
            summary.update(backend=backend)
            summary['configuration']['backend'] = backend
            self.assertEqual(suite.classify(summary, 'runtime-primitives', 4, 0, backend=backend), 'passed')
            for field, missing in [('missingFeatures', ['binary:Solcore.Core.Wire.BinaryOp.wordPow']),
                                   ('missingInputs', ['256'])]:
                changed = copy.deepcopy(summary)
                changed['coverage'][field] = missing
                self.assertEqual(suite.classify(changed, 'runtime-primitives', 4, 0, backend=backend), 'incomplete')
            other = 'sonatina-o2' if backend != 'sonatina-o2' else 'yul'
            self.assertEqual(suite.classify(summary, 'runtime-primitives', 4, 0, backend=other), 'adapter-error')

    def test_call_graph_matrix_counts_come_from_its_manifest(self):
        self.assertEqual(json.loads(suite.manifest('runtime-call-graphs').read_text())['requiredCallShapes'],
            list(suite.adapter.CALL_SHAPES))
        for backend, old_count, profile_count in (('sonatina-o0', 459, 25), ('sonatina-o2', 459, 25), ('yul', 417, 14)):
            args = self.args('--backend', backend)
            count = suite.requested(args, 'runtime-call-graphs')
            self.assertGreater(count, 0)
            self.assertEqual(len(args.profile), profile_count)
            keyed = (suite.requested(args, 'stateful-keyed-storage') + suite.requested(args, 'stateful-dynamic-array')
                     + suite.requested(args, 'stateful-logs') + suite.requested(args, 'stateful-call-value')
                     + suite.requested(args, 'stateful-bytes') + suite.requested(args, 'stateful-forwarded-value')
                     + suite.requested(args, 'stateful-mapping') + suite.requested(args, 'stateful-ledger')
                     if backend != 'yul' else 0)
            self.assertEqual(sum(suite.requested(args, p) for p in args.profile),
                old_count + count + suite.requested(args, 'runtime-call-graph-loops')
                + suite.requested(args, 'runtime-aggregate-call-graphs') + keyed)
            command = suite.command(args, 'runtime-call-graphs', self.directory/backend, 30, 64*1024**2)
            self.assertEqual(command[command.index('--corpus')+1], str(suite.manifest('runtime-call-graphs')))
            self.assertEqual(command[command.index('--backend')+1], backend)

    def test_call_graph_random_defaults_preserve_legacy_and_explicit_attempts(self):
        for backend in suite.adapter.BACKENDS:
            args = self.args('--mode', 'random', '--backend', backend)
            command = suite.command(args, 'runtime-call-graphs', self.directory/backend, 30, 64*1024**2)
            self.assertEqual(command[command.index('--nodes')+1], '192')
            self.assertEqual(command[command.index('--attempts')+1], '1024')
            self.assertEqual('--solc' in command, backend == 'yul')
            self.assertEqual(suite.profile_attempts(args, 'runtime-primitives'), 512)
            explicit = self.args('--mode', 'random', '--attempts', '7')
            command = suite.command(explicit, 'runtime-call-graphs', self.directory/'explicit', 30, 64*1024**2)
            self.assertEqual(command[command.index('--attempts')+1], '7')
            self.assertEqual(command[command.index('--seed')+1], str(suite.derived_seed(
                explicit.seed, 'runtime-call-graphs', explicit.shard_index, explicit.shard_count, 7)))

    def test_call_graph_loop_matrix_counts_come_from_its_manifest(self):
        profile = 'runtime-call-graph-loops'
        self.assertEqual(suite.PROFILES[profile], ('semantic-call-graph-loop', 'pure', 256))
        self.assertEqual(suite.manifest(profile), ROOT / 'scripts/semantic-call-graph-loop-corpus.json')
        data = json.loads(suite.manifest(profile).read_text())
        self.assertEqual(data['profile'], profile)
        self.assertEqual(data['requiredCallShapes'], list(suite.adapter.CALL_SHAPES))
        self.assertEqual(data['loopRequirements'], {'masks': [0, 1, 3, 7], 'iterations': [0, 1, 3, 7]})
        count = len(data['cases'])
        self.assertGreater(count, 0)
        for backend in suite.adapter.BACKENDS:
            args = self.args('--backend', backend)
            self.assertIn(profile, args.profile)
            self.assertEqual(suite.requested(args, profile), count)
            command = suite.command(args, profile, self.directory / backend, 30, 64 * 1024**2)
            self.assertEqual(Path(command[1]).name, 'semantic-campaign.py')
            self.assertEqual(command[command.index('--profile') + 1], profile)
            self.assertEqual(command[command.index('--corpus') + 1], str(suite.manifest(profile)))
            self.assertEqual(command[command.index('--backend') + 1], backend)
            self.assertEqual(command[command.index('--attempts') + 1], str(max(512, count)))
            self.assertEqual('--solc' in command, backend == 'yul')
            for flag in ('--cases', '--seed', '--nodes'):
                self.assertNotIn(flag, command)
            selected = self.args('--backend', backend, '--profile', profile)
            self.assertEqual(selected.profile, [profile])
            self.assertEqual(suite.requested(selected, profile), count)
        # A small explicit attempt budget can never truncate the fixed manifest.
        command = suite.command(self.args('--attempts', '3'), profile, self.directory / 'small', 30, 64 * 1024**2)
        self.assertEqual(command[command.index('--attempts') + 1], str(count))

    def test_call_graph_loop_random_defaults_use_its_node_budget_and_ordinary_attempts(self):
        profile = 'runtime-call-graph-loops'
        for backend in suite.adapter.BACKENDS:
            args = self.args('--mode', 'random', '--backend', backend)
            self.assertEqual(suite.profile_attempts(args, profile), 512)
            command = suite.command(args, profile, self.directory / backend, 30, 64 * 1024**2)
            self.assertNotIn('--corpus', command)
            self.assertEqual(command[command.index('--profile') + 1], profile)
            self.assertEqual(command[command.index('--nodes') + 1], '256')
            self.assertEqual(command[command.index('--attempts') + 1], '512')
            self.assertEqual(command[command.index('--cases') + 1], '4')
            self.assertEqual(command[command.index('--seed') + 1], str(suite.derived_seed(
                args.seed, profile, args.shard_index, args.shard_count, 512)))
            self.assertEqual('--solc' in command, backend == 'yul')
        explicit = self.args('--mode', 'random', '--attempts', '7', '--nodes', '100', '--cases', '2')
        command = suite.command(explicit, profile, self.directory / 'explicit', 30, 64 * 1024**2)
        self.assertEqual(command[command.index('--attempts') + 1], '7')
        self.assertEqual(command[command.index('--nodes') + 1], '100')
        self.assertEqual(command[command.index('--cases') + 1], '2')
        self.assertEqual(command[command.index('--seed') + 1], str(suite.derived_seed(
            explicit.seed, profile, explicit.shard_index, explicit.shard_count, 7)))
        # Only the call-graph profile keeps its larger legacy attempt budget.
        self.assertEqual([p for p in suite.PROFILES if suite.profile_attempts(self.args('--mode', 'random'), p) == 1024],
            ['runtime-call-graphs'])

    def test_call_graph_loop_summary_needs_both_loop_and_shape_coverage_to_pass(self):
        profile = 'runtime-call-graph-loops'
        for backend in suite.adapter.BACKENDS:
            summary = completed(profile)
            summary.update(backend=backend, loopCoverage={'missingMasks': [], 'missingIterations': []},
                callShapeCoverage={'missingShapes': []})
            summary['configuration']['backend'] = backend
            self.assertEqual(suite.classify(summary, profile, 4, 0, backend=backend), 'passed')
            for group, field, missing in (('loopCoverage', 'missingMasks', [0]), ('loopCoverage', 'missingIterations', [3]),
                                          ('callShapeCoverage', 'missingShapes', ['diamond'])):
                changed = copy.deepcopy(summary)
                changed[group][field] = missing
                self.assertEqual(suite.classify(changed, profile, 4, 0, backend=backend), 'incomplete')
                self.assertEqual(suite.missing_coverage(changed), {group: {field: missing}})
            changed = copy.deepcopy(summary)
            changed['coverage']['missingHelperCounts'] = [2]
            self.assertEqual(suite.classify(changed, profile, 4, 0, backend=backend), 'incomplete')
            other = 'sonatina-o2' if backend != 'sonatina-o2' else 'yul'
            self.assertEqual(suite.classify(summary, profile, 4, 0, backend=other), 'adapter-error')
        # The summary must come from this profile's pure campaign family.
        wrong = completed('runtime-loops')
        self.assertEqual(suite.classify(wrong, profile, 4, 0), 'adapter-error')

    def test_missing_call_shapes_prevent_suite_pass(self):
        for backend in suite.adapter.BACKENDS:
            summary = completed('runtime-call-graphs')
            summary.update(backend=backend, callShapeCoverage={'missingShapes': []})
            summary['configuration']['backend'] = backend
            self.assertEqual(suite.classify(summary, 'runtime-call-graphs', 4, 0, backend=backend), 'passed')
            summary['callShapeCoverage']['missingShapes'] = ['predicate-call']
            self.assertEqual(suite.classify(summary, 'runtime-call-graphs', 4, 0, backend=backend), 'incomplete')
            summary['callShapeCoverage']['missingShapes'] = []
            summary['coverage']['missingHelperCounts'] = [3]
            self.assertEqual(suite.classify(summary, 'runtime-call-graphs', 4, 0, backend=backend), 'incomplete')

    def test_aggregate_call_graph_matrix_counts_come_from_its_manifest(self):
        profile = 'runtime-aggregate-call-graphs'
        self.assertEqual(suite.PROFILES[profile], ('semantic-aggregate-call-graph', 'pure', 192))
        self.assertEqual(suite.manifest(profile), ROOT / 'scripts/semantic-aggregate-call-graph-corpus.json')
        data = json.loads(suite.manifest(profile).read_text())
        self.assertEqual(data['profile'], profile)
        self.assertEqual(data['requiredAggregateShapes'], list(suite.adapter.AGGREGATE_SHAPES))
        self.assertEqual(data['requiredHelperCounts'], [1, 2, 3])
        # The scalar call-shape and loop requirements belong to other profiles.
        self.assertEqual(data.get('requiredCallShapes', []), [])
        self.assertEqual(data.get('loopRequirements', {'masks': [], 'iterations': []}), {'masks': [], 'iterations': []})
        count = len(data['cases'])
        self.assertGreater(count, 0)
        self.assertEqual(len({entry['id'] for entry in data['cases']}), count)
        for backend in suite.adapter.BACKENDS:
            args = self.args('--backend', backend)
            self.assertIn(profile, args.profile)
            self.assertEqual(suite.requested(args, profile), count)
            # The matrix total grows by exactly this manifest's case count on every backend.
            others = [p for p in args.profile if p != profile]
            self.assertEqual(sum(suite.requested(args, p) for p in args.profile),
                sum(suite.requested(args, p) for p in others) + count)
            command = suite.command(args, profile, self.directory / backend, 30, 64 * 1024**2)
            self.assertEqual(Path(command[1]).name, 'semantic-campaign.py')
            self.assertEqual(command[command.index('--profile') + 1], profile)
            self.assertEqual(command[command.index('--corpus') + 1], str(suite.manifest(profile)))
            self.assertEqual(command[command.index('--backend') + 1], backend)
            self.assertEqual(command[command.index('--attempts') + 1], str(max(512, count)))
            self.assertEqual('--solc' in command, backend == 'yul')
            for flag in ('--cases', '--seed', '--nodes'):
                self.assertNotIn(flag, command)
            selected = self.args('--backend', backend, '--profile', profile)
            self.assertEqual(selected.profile, [profile])
            self.assertEqual(suite.requested(selected, profile), count)
        # A small explicit attempt budget can never truncate the fixed manifest.
        command = suite.command(self.args('--attempts', '3'), profile, self.directory / 'small', 30, 64 * 1024**2)
        self.assertEqual(command[command.index('--attempts') + 1], str(count))
        # Fixed mode requires the manifest to stay non-empty and declared under its own profile.
        corrupted = self.directory / 'corrupted.json'
        for corrupt in ({**data, 'profile': 'runtime-call-graphs'}, {**data, 'cases': []},
                        {key: value for key, value in data.items() if key != 'cases'}):
            corrupted.write_text(json.dumps(corrupt))
            with patch.object(suite, 'manifest', return_value=corrupted), \
                    self.assertRaisesRegex(ValueError, 'fixed manifest profile or cases changed'):
                suite.requested(self.args(), profile)

    def test_aggregate_call_graph_random_defaults_use_its_node_budget_and_ordinary_attempts(self):
        profile = 'runtime-aggregate-call-graphs'
        for backend in suite.adapter.BACKENDS:
            args = self.args('--mode', 'random', '--backend', backend)
            self.assertEqual(suite.profile_attempts(args, profile), 512)
            command = suite.command(args, profile, self.directory / backend, 30, 64 * 1024**2)
            self.assertNotIn('--corpus', command)
            self.assertEqual(Path(command[1]).name, 'semantic-campaign.py')
            self.assertEqual(command[command.index('--profile') + 1], profile)
            self.assertEqual(command[command.index('--nodes') + 1], '192')
            self.assertEqual(command[command.index('--attempts') + 1], '512')
            self.assertEqual(command[command.index('--cases') + 1], '4')
            self.assertEqual(command[command.index('--seed') + 1], str(suite.derived_seed(
                args.seed, profile, args.shard_index, args.shard_count, 512)))
            self.assertEqual('--solc' in command, backend == 'yul')
        explicit = self.args('--mode', 'random', '--attempts', '7', '--nodes', '100', '--cases', '2')
        command = suite.command(explicit, profile, self.directory / 'explicit', 30, 64 * 1024**2)
        self.assertEqual(command[command.index('--attempts') + 1], '7')
        self.assertEqual(command[command.index('--nodes') + 1], '100')
        self.assertEqual(command[command.index('--cases') + 1], '2')
        self.assertEqual(command[command.index('--seed') + 1], str(suite.derived_seed(
            explicit.seed, profile, explicit.shard_index, explicit.shard_count, 7)))
        # Its seed stream is its own, and only the scalar call-graph profile keeps the larger legacy attempt budget.
        args = self.args('--mode', 'random')
        seeds = {p: suite.derived_seed(args.seed, p, args.shard_index, args.shard_count, suite.profile_attempts(args, p))
                 for p in suite.PROFILES}
        self.assertEqual(sum(seed == seeds[profile] for seed in seeds.values()), 1)
        self.assertEqual([p for p in suite.PROFILES if suite.profile_attempts(args, p) == 1024], ['runtime-call-graphs'])

    def test_aggregate_call_graph_dispatch_records_its_manifest_or_seed_in_the_suite_report(self):
        profile = 'runtime-aggregate-call-graphs'
        count = len(json.loads(suite.manifest(profile).read_text())['cases'])
        fixed = self.args('--profile', profile)
        fixed.output.mkdir()
        with patch.object(suite, 'run_process', side_effect=self.mock_campaign({})), contextlib.redirect_stdout(io.StringIO()):
            run = suite.Suite(fixed)
            run.run()
        row = run.report['profiles'][0]
        self.assertEqual(run.report['status'], 'passed')
        self.assertEqual((row['profile'], row['status'], row['requested'], row['output']), (profile, 'passed', count, '00-' + profile))
        self.assertEqual(row['manifest'], 'scripts/semantic-aggregate-call-graph-corpus.json')
        self.assertEqual(row['manifestSha256'], suite.digest(suite.manifest(profile)))
        self.assertEqual(row['command'][row['command'].index('--corpus') + 1], str(suite.manifest(profile)))
        self.assertEqual(row['campaign']['counts']['matched'], count)
        sampled = suite.parse_args(['--output', str(self.directory / 'sampled'), '--mode', 'random', '--profile', profile])
        sampled.output.mkdir()
        with patch.object(suite, 'run_process', side_effect=self.mock_campaign({})), contextlib.redirect_stdout(io.StringIO()):
            run = suite.Suite(sampled)
            run.run()
        row = run.report['profiles'][0]
        self.assertEqual(run.report['status'], 'passed')
        self.assertEqual((row['requested'], row['attempts']), (4, 512))
        self.assertEqual(row['seed'], str(suite.derived_seed(sampled.seed, profile, 0, 1, 512)))
        self.assertNotIn('manifest', row)
        self.assertEqual(row['command'][row['command'].index('--nodes') + 1], '192')

    def test_missing_aggregate_shapes_or_helper_counts_prevent_suite_pass(self):
        profile = 'runtime-aggregate-call-graphs'
        for backend in suite.adapter.BACKENDS:
            summary = completed(profile)
            summary.update(backend=backend, aggregateShapeCoverage={'missingShapes': []})
            summary['configuration']['backend'] = backend
            self.assertEqual(suite.classify(summary, profile, 4, 0, backend=backend), 'passed')
            self.assertEqual(suite.missing_coverage(summary), {})
            changed = copy.deepcopy(summary)
            changed['aggregateShapeCoverage']['missingShapes'] = ['nested-case']
            self.assertEqual(suite.classify(changed, profile, 4, 0, backend=backend), 'incomplete')
            self.assertEqual(suite.missing_coverage(changed), {'aggregateShapeCoverage': {'missingShapes': ['nested-case']}})
            for field, missing in (('missingHelperCounts', [3]), ('missingInputs', ['256']), ('missingFeatures', ['case'])):
                changed = copy.deepcopy(summary)
                changed['coverage'][field] = missing
                self.assertEqual(suite.classify(changed, profile, 4, 0, backend=backend), 'incomplete')
                self.assertEqual(suite.missing_coverage(changed), {'coverage': {field: missing}})
            # A campaign that itself reports incomplete coverage or exhausted generation never passes.
            for status in ('coverage-incomplete', 'generation-exhausted'):
                changed = copy.deepcopy(summary)
                changed['status'] = status
                self.assertEqual(suite.classify(changed, profile, 4, 1, backend=backend), 'incomplete')
            # Both gaps are reported together and neither hides the other.
            changed = copy.deepcopy(summary)
            changed['aggregateShapeCoverage']['missingShapes'] = ['aggregate-let', 'nested-case']
            changed['coverage']['missingHelperCounts'] = [1]
            self.assertEqual(suite.missing_coverage(changed), {'aggregateShapeCoverage': {'missingShapes': ['aggregate-let', 'nested-case']},
                                                              'coverage': {'missingHelperCounts': [1]}})
            self.assertEqual(suite.classify(changed, profile, 4, 0, backend=backend), 'incomplete')
            other = 'sonatina-o2' if backend != 'sonatina-o2' else 'yul'
            self.assertEqual(suite.classify(summary, profile, 4, 0, backend=other), 'adapter-error')
        # The summary must come from this profile's pure campaign.
        self.assertEqual(suite.classify(completed('runtime-call-graphs'), profile, 4, 0), 'adapter-error')
        self.assertEqual(suite.classify({**completed(profile), 'synthetic': True}, profile, 4, 0), 'adapter-error')

    def test_backend_selection_reaches_every_campaign_family(self):
        self.assertEqual(self.args().backend, 'sonatina-o0')
        for backend in suite.adapter.BACKENDS:
            args = self.args('--backend', backend)
            for profile in args.profile:
                command = suite.command(args, profile, self.directory / profile, 30, 64 * 1024**2)
                self.assertEqual(command[command.index('--backend') + 1], backend)
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            self.args('--backend', 'unknown-backend')

    def test_yul_defaults_to_all_fourteen_pure_profiles_and_forwards_only_its_compiler(self):
        args = self.args('--backend', 'yul', '--solc', '/chosen/pinned-solc')
        self.assertEqual(len(args.profile), 14)
        self.assertEqual(sum(suite.requested(args, profile) for profile in args.profile
            if profile not in ("runtime-primitives", "runtime-call-graphs", "runtime-call-graph-loops",
                               "runtime-aggregate-call-graphs")), 336)
        self.assertIn("runtime-primitives", args.profile)
        self.assertIn("runtime-call-graph-loops", args.profile)
        self.assertIn("runtime-aggregate-call-graphs", args.profile)
        self.assertTrue(all(suite.PROFILES[profile][1] == 'pure' for profile in args.profile))
        for profile in args.profile:
            command = suite.command(args, profile, self.directory / profile, 30, 64 * 1024**2)
            self.assertEqual(command[command.index('--solc') + 1], '/chosen/pinned-solc')
        for backend in suite.adapter.SONATINA_BACKENDS:
            sonatina = self.args('--backend', backend, '--solc', '/unused/solc')
            self.assertEqual(len(sonatina.profile), 25)
            for profile in sonatina.profile:
                self.assertNotIn('--solc', suite.command(sonatina, profile, self.directory / profile, 30, 64 * 1024**2))

    def test_explicit_yul_stateful_profiles_are_errors_instead_of_silent_omissions(self):
        for profile in ('stateful-storage', 'stateful-storage-rollback', 'stateful-calls', 'stateful-keyed-storage',
                        'stateful-dynamic-array', 'stateful-logs', 'stateful-call-value', 'stateful-bytes',
                        'stateful-forwarded-value', 'stateful-mapping', 'stateful-ledger'):
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                self.args('--backend', 'yul', '--profile', 'closed-g0', '--profile', profile)
            with self.assertRaises(ValueError):
                suite.command(self.args('--backend', 'yul'), profile, self.directory / profile, 30, 64 * 1024**2)
        selected = self.args('--backend', 'yul', '--profile', 'runtime-modules')
        self.assertEqual(selected.profile, ['runtime-modules'])

    def test_backend_completion_cannot_switch_or_relabel_a_legacy_run(self):
        legacy = completed()
        self.assertEqual(suite.classify(legacy, 'closed-g0', 4, 0), 'passed')
        self.assertEqual(suite.classify(legacy, 'closed-g0', 4, 0, backend='sonatina-o2'), 'adapter-error')
        optimized = {**legacy, 'backend': 'sonatina-o2'}
        self.assertEqual(suite.classify(optimized, 'closed-g0', 4, 0, backend='sonatina-o2'), 'passed')
        self.assertEqual(suite.classify(optimized, 'closed-g0', 4, 0), 'adapter-error')
        for backend in (None, 'yul', 2):
            self.assertEqual(suite.classify({**legacy, 'backend': backend}, 'closed-g0', 4, 0), 'adapter-error')
        optimized['configuration'] = {'profile': 'closed-g0', 'backend': 'sonatina-o0'}
        self.assertEqual(suite.classify(optimized, 'closed-g0', 4, 0, backend='sonatina-o2'), 'adapter-error')
        optimized['configuration']['backend'] = 'sonatina-o2'
        optimized['findings'] = [{'fingerprint': {'category': 'execution-error', 'synthetic': False}}]
        self.assertEqual(suite.classify(optimized, 'closed-g0', 4, 1, backend='sonatina-o2'), 'adapter-error')
        optimized['findings'][0]['fingerprint']['backend'] = 'sonatina-o2'
        self.assertEqual(suite.classify(optimized, 'closed-g0', 4, 1, backend='sonatina-o2'), 'failed')

    def test_optimized_suite_summary_records_backend_and_checks_campaign_receipt(self):
        args = self.args('--backend', 'sonatina-o2', '--profile', 'closed-g0')
        args.output.mkdir()
        with patch.object(suite, 'run_process', side_effect=self.mock_campaign({})), contextlib.redirect_stdout(io.StringIO()):
            run = suite.Suite(args)
            run.run()
        self.assertEqual(run.report['backend'], 'sonatina-o2')
        self.assertEqual(run.report['profiles'][0]['backend'], 'sonatina-o2')
        # The policy fixture deliberately returns a legacy O0 receipt.
        self.assertEqual(run.report['profiles'][0]['status'], 'adapter-error')
        self.assertEqual(run.report['status'], 'failed')

    def test_random_seeds_are_order_independent_reproducible_and_sharded(self):
        args = self.args("--mode", "random", "--seed", "123", "--shard-index", "2", "--shard-count", "4")
        seeds = {p: suite.derived_seed(args.seed, p, 2, 4, suite.profile_attempts(args, p)) for p in suite.PROFILES}
        self.assertEqual(seeds, {p: suite.derived_seed(123, p, 2, 4, 1024 if p == "runtime-call-graphs" else 512) for p in reversed(suite.PROFILES)})
        self.assertEqual(len(set(seeds.values())), 25)
        self.assertNotEqual(seeds["closed-g0"], suite.derived_seed(123, "closed-g0", 1, 4, 512))
        for profile, seed in seeds.items():
            self.assertLess(seed + suite.profile_attempts(args, profile) - 1, 1 << 64)
        command = suite.command(args, "runtime-loops", self.directory / "loop", 10, 64 * 1024**2)
        self.assertNotIn("--corpus", command)
        self.assertEqual(command[command.index("--seed") + 1], str(seeds["runtime-loops"]))
        self.assertEqual(command[command.index("--nodes") + 1], "384")

    def test_distinct_native_tools_and_all_external_overrides_forward(self):
        args = self.args("--bin-dir", str(self.directory / "bin"), "--anvil", str(self.directory / "anvil"),
                         "--upstream", str(self.directory / "upstream"), "--target-dir", str(self.directory / "target"))
        expected = {"closed-g0": ("semantic-case-tool", "rust-hull-scenario"),
                    "runtime-aggregate-call-graphs": ("semantic-case-tool", "rust-hull-scenario"),
                    "stateful-storage": ("semantic-storage-tool", "rust-hull-storage-scenario"),
                    "stateful-storage-rollback": ("semantic-storage-rollback-tool", "rust-hull-storage-scenario"),
                    "stateful-calls": ("semantic-call-tool", "rust-hull-call-scenario"),
                    "stateful-keyed-storage": ("semantic-keyed-storage-tool", "rust-hull-keyed-storage-scenario"),
                    "stateful-dynamic-array": ("semantic-dynamic-array-tool", "rust-hull-keyed-storage-scenario"),
                    "stateful-logs": ("semantic-log-tool", "rust-hull-keyed-storage-scenario"),
                    "stateful-call-value": ("semantic-call-value-tool", "rust-hull-value-scenario"),
                    "stateful-bytes": ("semantic-bytes-tool", "rust-hull-keyed-storage-scenario"),
                    "stateful-forwarded-value": ("semantic-forward-tool", "rust-hull-forward-scenario"),
                    "stateful-mapping": ("semantic-mapping-tool", "rust-hull-keyed-storage-scenario"),
                    "stateful-ledger": ("semantic-ledger-tool", "rust-hull-ledger-scenario")}
        for profile, (tool, runner) in expected.items():
            command = suite.command(args, profile, self.directory / profile, 10, 64 * 1024**2)
            self.assertEqual(Path(command[command.index("--case-tool") + 1]).name, tool)
            self.assertEqual(Path(command[command.index("--core-runner") + 1]).name, runner)
            for key in ("anvil", "upstream", "target_dir"):
                self.assertEqual(command[command.index("--" + key.replace("_", "-")) + 1], str(getattr(args, key)))

    def test_invalid_bounds_duplicate_profiles_and_fixed_truncation_rejected(self):
        for arguments in (("--cases", "1"), ("--nodes", "32"), ("--seconds", "nan"), ("--seconds", "0"),
                          ("--disk-bytes", "1"), ("--seed", str(1 << 64)), ("--shard-count", "0"),
                          ("--shard-index", "2", "--shard-count", "2"), ("--mode", "random", "--nodes", "513"),
                          ("--profile", "closed-g0", "--profile", "closed-g0")):
            with self.subTest(arguments=arguments), contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                self.args(*arguments)

    def test_only_complete_matching_counts_pass(self):
        good = completed()
        self.assertEqual(suite.classify(good, "closed-g0", 4, 0), "passed")
        for key in ("generated", "executed", "completed", "matched"):
            changed = copy.deepcopy(good)
            changed["counts"][key] = 3
            self.assertEqual(suite.classify(changed, "closed-g0", 4, 0), "incomplete")
        self.assertEqual(suite.classify(good, "closed-g0", 4, 1), "incomplete")

    def test_every_coverage_dimension_can_prevent_pass(self):
        for group in ("coverage", "recipeCoverage", "loopCoverage", "genericCoverage", "moduleCoverage", "constantCoverage"):
            changed = completed()
            changed[group] = {"missingFeatures": ["missing"]}
            self.assertEqual(suite.classify(changed, "closed-g0", 4, 0), "incomplete")

    def test_genuine_finding_survives_later_timeout(self):
        summary = completed()
        summary.update(status="budget-exhausted", findings=[{"archive": "findings/real/0", "fingerprint": {"category": "semantic-mismatch", "synthetic": False}}])
        summary["counts"].update(mismatched=1, inconclusive=1, matched=2)
        self.assertEqual(suite.classify(summary, "closed-g0", 4, 1, "time-limit"), "failed")

    def test_resource_archives_are_not_genuine_failures_but_secondary_mismatches_are(self):
        summary = completed()
        summary["findings"] = [{"fingerprint": {"category": "inconclusive-resource", "synthetic": False}}]
        self.assertEqual(suite.classify(summary, "closed-g0", 4, 1), "inconclusive-resource")
        summary["secondaryFindings"] = [{"fingerprint": {"category": "semantic-mismatch", "synthetic": False}}]
        self.assertEqual(suite.classify(summary, "closed-g0", 4, 1, "interrupted"), "failed")

    def test_missing_malformed_wrong_profile_and_synthetic_never_pass(self):
        for summary in (None, {}, {**completed(), "schema": "wrong"}, {**completed(), "synthetic": True},
                        {**completed(), "configuration": {"profile": "runtime-word"}}):
            self.assertEqual(suite.classify(summary, "closed-g0", 4, 0), "adapter-error")
        self.assertEqual(suite.classify(None, "closed-g0", 4, -15, "interrupted"), "inconclusive-resource")

    def test_exhausted_generation_and_resources_are_not_success(self):
        summary = completed()
        summary["status"] = "generation-exhausted"
        self.assertEqual(suite.classify(summary, "closed-g0", 4, 1), "incomplete")
        summary["status"] = "budget-exhausted"
        self.assertEqual(suite.classify(summary, "closed-g0", 4, 1), "inconclusive-resource")

    def mock_campaign(self, statuses):
        def run(command, args, deadline, stdout, stderr):
            profile = command[command.index("--profile") + 1]
            folder = Path(command[command.index("--output") + 1])
            folder.mkdir()
            summary = completed(profile, suite.requested(args, profile))
            category = statuses.get(profile, "passed")
            if category == "failed":
                summary["counts"].update(matched=0, errors=1)
                summary["findings"] = [{"archive": "findings/real/original", "fingerprint": {"category": "execution-error", "synthetic": False}}]
                artifact = folder / "findings/real/original"
                artifact.mkdir(parents=True)
                (artifact / "case.json").write_text("preserve me")
            if category == "resource":
                summary["status"] = "budget-exhausted"
            suite.save(folder / "summary.json", summary)
            stdout.write_text("policy fixture; not an EVM execution\n")
            stderr.write_text("")
            return (0 if category == "passed" else 1), None
        return run

    def test_all_profiles_dispatch_sequentially_and_keep_genuine_archives(self):
        args = self.args()
        args.output.mkdir()
        with patch.object(suite, "run_process", side_effect=self.mock_campaign({"runtime-word": "failed"})), contextlib.redirect_stdout(io.StringIO()):
            run = suite.Suite(args)
            run.run()
        self.assertEqual(run.report["status"], "failed")
        self.assertEqual(run.report["unexecutedProfiles"], [])
        self.assertEqual([row["profile"] for row in run.report["profiles"]], list(suite.PROFILES))
        self.assertTrue((args.output / "01-runtime-word/findings/real/original/case.json").exists())

    def test_global_time_before_execution_records_exact_unexecuted_profiles(self):
        args = self.args("--profile", "closed-g0", "--profile", "stateful-calls")
        args.output.mkdir()
        run = suite.Suite(args)
        run.deadline = time.monotonic() - 1
        with patch.object(suite, "run_process") as process:
            run.run()
            process.assert_not_called()
        self.assertEqual(run.report["status"], "inconclusive-resource")
        self.assertEqual(run.report["unexecutedProfiles"], args.profile)

    def test_global_disk_reserve_stops_before_another_profile(self):
        args = self.args("--profile", "closed-g0", "--disk-bytes", str(32 * 1024**2))
        args.output.mkdir()
        run = suite.Suite(args)
        with patch.object(suite, "directory_bytes", return_value=args.disk_bytes - args.reserve_bytes), patch.object(suite, "run_process") as process:
            run.run()
            process.assert_not_called()
        self.assertEqual(run.report["stop"], "disk-limit")
        self.assertEqual(run.report["status"], "inconclusive-resource")

    def test_success_requires_every_selected_profile(self):
        args = self.args("--profile", "closed-g0", "--profile", "stateful-calls")
        args.output.mkdir()
        with patch.object(suite, "run_process", side_effect=self.mock_campaign({})), contextlib.redirect_stdout(io.StringIO()):
            run = suite.Suite(args)
            run.run()
        self.assertEqual(run.report["status"], "passed")
        self.assertEqual(len(run.report["profiles"]), 2)

    def test_output_directory_is_never_overwritten(self):
        output = self.directory / "exists"
        output.mkdir()
        with self.assertRaises(FileExistsError):
            suite.main(["--output", str(output)])

    def test_interruption_between_profiles_preserves_prior_genuine_failure(self):
        def interrupted(run):
            run.report["profiles"] = [{"profile": "closed-g0", "status": "failed"}]
            raise KeyboardInterrupt
        with patch.object(suite.Suite, "run", interrupted), contextlib.redirect_stdout(io.StringIO()):
            code = suite.main(["--output", str(self.directory / "interrupted")])
        report = json.loads((self.directory / "interrupted/summary.json").read_text())
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "failed")
        self.assertEqual(report["stop"], "interrupted")

    def test_real_output_limit_stops_owned_child_and_caps_logs(self):
        args = self.args("--output-limit", "1024", "--cleanup-seconds", ".1")
        args.output.mkdir()
        stdout, stderr = args.output / "out.log", args.output / "err.log"
        command = [sys.executable, "-c", "import sys,time;sys.stdout.write('x'*5000);sys.stdout.flush();time.sleep(30)"]
        code, reason = suite.run_process(command, args, time.monotonic() + 5, stdout, stderr)
        self.assertEqual(reason, "output-limit")
        self.assertNotEqual(code, 0)
        self.assertLessEqual(stdout.stat().st_size, 1024)

    def test_unavailable_process_inventory_fails_before_launch(self):
        args = self.args()
        args.output.mkdir()
        with patch.object(suite, "process_table", side_effect=PermissionError("process inventory denied")), patch.object(subprocess, "Popen") as launch:
            with self.assertRaises(PermissionError):
                suite.run_process(["not-launched"], args, time.monotonic() + 1, args.output / "out", args.output / "err")
            launch.assert_not_called()

    def test_cleanup_inspection_error_still_reaps_known_process(self):
        process = subprocess.Popen([sys.executable, "-c", "import time;time.sleep(60)"], start_new_session=True)
        try:
            with patch.object(suite, "process_table", side_effect=PermissionError("inspection lost")), self.assertRaises(PermissionError):
                suite.stop_owned(process, {}, .1)
            self.assertIsNotNone(process.returncode)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()

    def test_real_sigterm_writes_incomplete_summary_and_kills_owned_grandchild(self):
        pidfile = self.directory / "grandchild.pid"
        child = "import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)"
        fake_campaign = ("import subprocess,sys,time,signal;from pathlib import Path;"
                         "signal.signal(signal.SIGTERM,signal.SIG_IGN);"
                         f"p=subprocess.Popen([sys.executable,'-c',{child!r}],start_new_session=True);"
                         f"Path({str(pidfile)!r}).write_text(str(p.pid));time.sleep(60)")
        arguments = ["--output", str(self.directory / "suite"), "--profile", "closed-g0", "--profile", "stateful-calls", "--cleanup-seconds", ".1"]
        driver = ("import importlib.util,sys;"
                  f"spec=importlib.util.spec_from_file_location('runner',{str(ROOT / 'scripts/semantic-suite.py')!r});"
                  "m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);"
                  f"m.command=lambda *args:[sys.executable,'-c',{fake_campaign!r}];"
                  "m.digest=lambda path:'policy-fixture';"
                  f"raise SystemExit(m.main({arguments!r}))")
        process = subprocess.Popen([sys.executable, "-B", "-c", driver], stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        try:
            deadline = time.monotonic() + 5
            while not pidfile.exists() and process.poll() is None and time.monotonic() < deadline:
                time.sleep(.05)
            self.assertTrue(pidfile.exists())
            time.sleep(.2)  # Let the parent inventory observe the separate-session child.
            process.send_signal(signal.SIGTERM)
            process.communicate(timeout=8)
            self.assertEqual(process.returncode, 1)
            report = json.loads((self.directory / "suite/summary.json").read_text())
            self.assertEqual(report["status"], "inconclusive-resource")
            self.assertEqual(report["unexecutedProfiles"], ["stateful-calls"])
            pid = int(pidfile.read_text())
            state = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True).stdout.strip()
            self.assertTrue(not state or state.startswith("Z"))
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.communicate()
            if pidfile.exists():
                with contextlib.suppress(ProcessLookupError):
                    os.kill(int(pidfile.read_text()), signal.SIGKILL)

    def test_real_timeout_kills_separate_session_descendant(self):
        args = self.args("--cleanup-seconds", ".1")
        args.output.mkdir()
        pidfile = self.directory / "child.pid"
        child = "import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)"
        parent = ("import subprocess,sys,time,signal;from pathlib import Path;"
                  "signal.signal(signal.SIGTERM,signal.SIG_IGN);"
                  f"p=subprocess.Popen([sys.executable,'-c',{child!r}],start_new_session=True);"
                  f"Path({str(pidfile)!r}).write_text(str(p.pid));time.sleep(60)")
        try:
            _, reason = suite.run_process([sys.executable, "-c", parent], args, time.monotonic() + .7,
                                          args.output / "out.log", args.output / "err.log")
            self.assertEqual(reason, "time-limit")
            pid = int(pidfile.read_text())
            for _ in range(40):
                status = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True).stdout.strip()
                if not status or status.startswith("Z"):
                    break
                time.sleep(.05)
            self.assertTrue(not status or status.startswith("Z"), "owned separate-session child survived timeout")
        finally:
            if pidfile.exists():
                with contextlib.suppress(ProcessLookupError):
                    os.kill(int(pidfile.read_text()), signal.SIGKILL)

    def test_normal_exit_and_error_exit_clean_tracked_descendants(self):
        args = self.args("--cleanup-seconds", ".1")
        args.output.mkdir()
        for expected in (0, 3):
            with self.subTest(exit_code=expected):
                pidfile = self.directory / f"child-{expected}.pid"
                child = "import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)"
                parent = ("import subprocess,sys,time;from pathlib import Path;"
                          f"p=subprocess.Popen([sys.executable,'-c',{child!r}],start_new_session=True);"
                          f"Path({str(pidfile)!r}).write_text(str(p.pid));time.sleep(.4);sys.exit({expected})")
                try:
                    code, reason = suite.run_process([sys.executable, "-c", parent], args, time.monotonic() + 4,
                        args.output / f"out-{expected}.log", args.output / f"err-{expected}.log")
                    self.assertEqual(code, expected)
                    self.assertIsNone(reason)
                    pid = int(pidfile.read_text())
                    # SIGKILL delivery is asynchronous; an untracked child would sleep for 60 s.
                    for _ in range(40):
                        state = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True).stdout.strip()
                        if not state or state.startswith("Z"):
                            break
                        time.sleep(.05)
                    self.assertTrue(not state or state.startswith("Z"), f"tracked descendant survived exit: state {state!r}")
                finally:
                    if pidfile.exists():
                        with contextlib.suppress(ProcessLookupError):
                            os.kill(int(pidfile.read_text()), signal.SIGKILL)

    def test_pid_reuse_does_not_target_unrelated_process(self):
        with patch.object(suite, "process_table", return_value={123: (1, 123, "new identity")}), patch.object(os, "kill") as kill, patch.object(os, "killpg") as killpg:
            suite.signal_owned({123: "old identity"}, signal.SIGKILL)
            kill.assert_not_called()
            killpg.assert_not_called()


if __name__ == "__main__":
    unittest.main()
