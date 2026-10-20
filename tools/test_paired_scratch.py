import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
import paired_scratch


def row(cpu=10, exit_code=0):
    return dict(cpu_seconds=cpu, measurement_complete=True, exit_code=exit_code, outcome='no goals')


class PairTests(unittest.TestCase):
    def test_normal_load_always_runs_b_after_a(self):
        calls = []
        def sample(pc, arm, number, retain):
            calls.append((pc, arm, number))
            return row()
        result = paired_scratch.run_pairs(['69a4', '6a14'], sample, lambda _: None,
                                           load=lambda: (90, 80, 70))
        self.assertEqual(result['status'], 'complete')
        self.assertEqual(calls, [(pc, arm, pair) for pc in ['69a4', '6a14']
                                for pair in range(1, 6) for arm in ['A', 'B']])
        self.assertTrue(all(pair['load_average_start'] == [90, 80, 70]
                            and pair['load_average_end'] == [90, 80, 70]
                            for block in result['blocks'].values() for pair in block['pairs']))

    def test_all_eight_small_blocks_get_five_pairs(self):
        small = ['69a4', '69d8', '69e0', '6a00', '6a14', '6a64', '6a6c', '6ab4']
        result = paired_scratch.run_pairs(small, lambda *_: row(), lambda _: None)
        self.assertEqual(sum(len(block['pairs']) for block in result['blocks'].values()), 40)
        self.assertTrue(all(block['samples_per_arm'] == 5 for block in result['blocks'].values()))

    def test_large_blocks_use_three_samples_and_median_cpu_ratio(self):
        for pc in ['6974', '6a08', '6aa8', '0x800d6974']:
            with self.subTest(pc=pc):
                values = iter([1, 3, 2, 2, 100, 100])
                result = paired_scratch.run_pairs([pc], lambda *_: row(next(values)), lambda _: None)
                block = result['blocks'][pc]
                self.assertEqual(block['samples_per_arm'], 3)
                self.assertEqual(block['comparison_ratio'], 1.5)
                self.assertEqual(block['median_ratio'], 1)

    def test_promotions_preserve_interleaving_and_distinct_flat_entries(self):
        pcs = ['6960', '6a38', '6ad8', '698cLiteral', '698cShortString', '697c',
               '69e8', '69b0', '6ae0', '6a40', '6b08', '6a78', '6a24', '6ac4']
        calls = []
        def sample(pc, arm, number, retain):
            calls.append((pc, arm, number))
            return row()
        result = paired_scratch.run_pairs(pcs, sample, lambda _: None)
        for pc in pcs:
            count = 5 if pc == '6960' else 3
            self.assertEqual([call for call in calls if call[0] == pc],
                             [(pc, arm, n) for n in range(1, count + 1) for arm in ['A', 'B']])
            block = result['blocks'][pc]
            self.assertEqual(block['samples_per_arm'], count)
            self.assertEqual(block['method'], 'median of paired ratios' if count == 5 else 'median CPU ratio')
        for pc in ('0x800d698cLiteral', '800D698CSHORTSTRING', '0x800d6a38'):
            self.assertEqual(paired_scratch.sample_count(pc), 3)
        self.assertEqual(paired_scratch.sample_count('0x800d6960'), 5)

    def test_promotion_noise_and_fixed_limit_meet_at_300_seconds(self):
        for pc in paired_scratch.PROMOTED_ENTRIES | paired_scratch.R4_ENTRIES:
            short = paired_scratch.promotion_policy(pc, 299.999)
            self.assertTrue(short['aa_floor_required'])
            self.assertIsNone(short['fixed_limit'])
            for cpu in (300, 1900):
                long = paired_scratch.promotion_policy(pc, cpu)
                self.assertFalse(long['aa_floor_required'])
                self.assertEqual(long['fixed_limit'], .1)
        self.assertEqual(paired_scratch.promotion_policy('6960', 31)['first_release'], 'R4')
        self.assertEqual(paired_scratch.promotion_policy('69e8', 362)['first_release'], 'R4')
        self.assertIsNone(paired_scratch.promotion_policy('6974', 400))
        self.assertIsNone(paired_scratch.promotion_policy('69a4', 10))

    def test_promotion_noise_requires_matching_short_baseline_reference(self):
        sources = {'698cLiteral': dict(statement_sha256='statement', source_A_sha256='source')}
        setup = dict(recipe='private', recipe_sha256='hash', ocamlpath='private-lib')
        reference = dict(status='complete', mode='compare', sources=copy.deepcopy(sources),
                         compiler_setups={'A': setup}, blocks={'698cLiteral': dict(median_cpu_A=216)})
        paired_scratch.check_noise_reference(['698cLiteral'], reference, sources, setup)
        for cpu in (300, 301, None, float('nan')):
            changed = copy.deepcopy(reference)
            changed['blocks']['698cLiteral']['median_cpu_A'] = cpu
            with self.assertRaisesRegex(ValueError, 'below 300'):
                paired_scratch.check_noise_reference(['698cLiteral'], changed, sources, setup)
        for key in ('statement_sha256', 'source_A_sha256'):
            changed = copy.deepcopy(reference)
            changed['sources']['698cLiteral'][key] = 'different'
            with self.assertRaisesRegex(ValueError, 'different baseline source'):
                paired_scratch.check_noise_reference(['698cLiteral'], changed, sources, setup)
        with self.assertRaisesRegex(ValueError, 'different baseline compiler'):
            paired_scratch.check_noise_reference(['698cLiteral'], reference, sources, {})
        with self.assertRaisesRegex(ValueError, 'completed comparison'):
            paired_scratch.check_noise_reference(['698cLiteral'], None, sources, setup)
        # The historical eight-entry noise command keeps its original interface.
        paired_scratch.check_noise_reference(['69a4'], None, {}, {})

    def test_instruction_metric_selects_instruction_ratio_and_retains_cpu_statistics(self):
        def sample(pc, arm, number, retain):
            return {**row(10 if arm == 'A' else 20), 'user_instructions': 100,
                    'instruction_measurement_complete': True}
        report = paired_scratch.run_pairs(['69a4'], sample, lambda _: None, metric='instructions')
        block = report['blocks']['69a4']
        self.assertEqual(block['median_ratio'], 2)
        self.assertEqual(block['comparison_ratio'], 1)
        self.assertEqual(block['method'], 'median of paired instruction ratios')
        self.assertEqual(block['instruction_statistics']['median_absolute_deviation'], 0)
        values = iter([1, 3, 2, 2, 100, 100])
        report = paired_scratch.run_pairs(['6974'],
            lambda *_: {**row(), 'user_instructions': next(values), 'instruction_measurement_complete': True},
            lambda _: None, metric='instructions')
        self.assertEqual(report['blocks']['6974']['comparison_ratio'], 1.5)

    def test_missing_instruction_count_stops_without_cpu_fallback_or_retry(self):
        calls = []
        def sample(*args):
            calls.append(args[:3])
            return {**row(), 'instruction_measurement_complete': False, 'user_instructions': None}
        report = paired_scratch.run_pairs(['69a4'], sample, lambda _: None, metric='instructions')
        self.assertEqual(report['status'], 'sample-failed')
        self.assertEqual(calls, [('69a4', 'A', 1)])
        self.assertIsNone(report['blocks']['69a4']['pairs'][0]['A']['user_instructions'])

    def test_decision_floor_cannot_mix_cpu_and_instruction_metrics(self):
        cpu = dict(status='complete', mode='noise', blocks={'69a4': dict(median_absolute_deviation=.3)})
        instructions = dict(status='complete', mode='noise', metric='instructions',
                            blocks={'69a4': dict(instruction_statistics=dict(median_absolute_deviation=.001))})
        self.assertEqual(paired_scratch.noise_floor(cpu, '69a4'), .3)
        self.assertEqual(paired_scratch.noise_floor(instructions, '69a4', 'instructions'), .001)
        for report, metric in [(cpu, 'instructions'), (instructions, 'cpu')]:
            with self.assertRaisesRegex(ValueError, 'different metric'):
                paired_scratch.noise_floor(report, '69a4', metric)
        for update in [dict(status='running'), dict(mode='compare')]:
            with self.assertRaisesRegex(ValueError, 'completed A/A'):
                paired_scratch.noise_floor({**instructions, **update}, '69a4', 'instructions')
        with self.assertRaisesRegex(ValueError, 'different decision metric'):
            paired_scratch.check_noise_reference(['69a4'], cpu, {}, {}, 'instructions')
        with self.assertRaisesRegex(ValueError, 'different decision metric'):
            paired_scratch.check_noise_reference(['69a4'], instructions, {}, {}, 'cpu')

    def test_both_noise_statistics_remain_distinct(self):
        pairs = [dict(A=row(), B=row(cpu)) for cpu in [8, 9, 10, 11, 12]]
        stats = paired_scratch.ratios(pairs)
        self.assertEqual(stats['median_ratio'], 1)
        self.assertAlmostEqual(stats['median_absolute_deviation'], .1)
        self.assertEqual(stats['absolute_median_deviation'], 0)

    def test_failed_sample_is_retained_without_retry(self):
        snapshots = []
        result = paired_scratch.run_pairs(['69a4'], lambda *_: row(exit_code=1),
                                           lambda r: snapshots.append(copy.deepcopy(r)))
        self.assertEqual(result['status'], 'sample-failed')
        self.assertEqual(len(result['blocks']['69a4']['pairs']), 1)
        self.assertEqual(snapshots[-1]['blocks']['69a4']['pairs'][0]['A']['exit_code'], 1)

    def test_started_watch_is_retained_before_a_sample_error(self):
        snapshots = []
        def sample(pc, arm, number, retain):
            retain(dict(log='/retained.log', writer='exact-writer'))
            raise ValueError('sample error')
        with self.assertRaisesRegex(ValueError, 'sample error'):
            paired_scratch.run_pairs(['69a4'], sample,
                                      lambda r: snapshots.append(copy.deepcopy(r)))
        self.assertEqual(snapshots[-1]['blocks']['69a4']['pairs'][0]['A']['log'], '/retained.log')

    def test_unavailable_or_nonfinite_cpu_refuses_a_pair(self):
        for value in (None, float('inf'), float('nan'), 0):
            with self.subTest(value=value):
                result = paired_scratch.run_pairs(['69a4'], lambda *_: row(value), lambda _: None)
                self.assertEqual(result['status'], 'sample-failed')

    def test_changed_statement_refuses_before_a_compile(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for arm, goal in [('A', 'True'), ('B', 'False')]:
                file = root / arm / 'Block800d69a4.v'
                file.parent.mkdir()
                file.write_text(f'Lemma DesignedBoundary_800d69a4 : {goal}.\nProof.\n  exact I.\nQed.\n')
            args = SimpleNamespace(pcs=['69a4'], workspace=root / 'A', changed_workspace=root / 'B')
            with patch.object(paired_scratch.scratch_block, 'find_block',
                              side_effect=lambda workspace, pc: workspace / 'Block800d69a4.v'):
                with self.assertRaisesRegex(ValueError, 'different boundary statements'):
                    paired_scratch.source_scope(args)

    def test_changed_source_refuses_before_a_watcher(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            module = root / 'Block800d69a4.v'
            module.write_text('changed')
            args = SimpleNamespace(workspace=root, build_dir=root, extra=None, mode='noise',
                                   sources={'69a4': {'source_A_sha256': 'old'}},
                                   compiler_setups={'A': {}}, tool_versions={})
            with patch.object(paired_scratch.scratch_block, 'find_block', return_value=module), \
                    patch.object(paired_scratch.subprocess, 'check_output') as launch:
                with self.assertRaisesRegex(ValueError, 'source changed'):
                    paired_scratch.watched_sample('69a4', 'A', 1, lambda _: None, args)
                launch.assert_not_called()

    def test_outside_workspace_build_accepts_explicit_private_recipe(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            working, objects, findlib, build = [root / name for name in ['working', 'objects', 'lib', 'build']]
            for path in [working, objects, findlib, build]:
                path.mkdir()
            plugin = findlib / 'zesu-signature-gates/plugin/signature_gates_plugin.cmxs'
            plugin.parent.mkdir(parents=True)
            plugin.write_bytes(b'prepared')
            recipe = build / 'coqc_recipe.json'
            recipe.write_text(json.dumps(dict(working_dir=str(working),
                                              command=['coqc', '-R', str(objects), 'ZesuSsz', 'A.v'])))
            with self.assertRaisesRegex(ValueError, 'explicit OCAMLPATH'):
                paired_scratch.compiler_setup(build)
            setup = paired_scratch.compiler_setup(build, ocamlpath=str(findlib))
            self.assertEqual(setup['project_objects'], str(objects))
            self.assertEqual(setup['working_dir'], str(working))

    def test_both_arms_use_one_helper_with_separate_recipes_and_findlib(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            workspaces, builds, setups, logs = {}, {}, {}, {}
            for arm in ['A', 'B']:
                workspace, build = root / ('source-' + arm), root / ('build-' + arm)
                module = workspace / 'ZesuSsz/Proofs/DecodeItem/Auto/Block800d69a4.v'
                module.parent.mkdir(parents=True)
                module.write_text('Lemma DesignedBoundary_800d69a4 : True.\nProof.\nexact I.\nQed.\n')
                output = build / 'scratch-blocks' / arm
                output.mkdir(parents=True)
                scratch = output / module.name
                scratch.write_text(paired_scratch.scratch_block.scratch_source(module))
                (output / 'compiler.json').write_text(json.dumps({**row(), 'peak_rss_kib': 1024}))
                log = root / (arm + '.log')
                log.write_text('scratch_source=' + str(scratch) + '\nNo more goals.\n')
                recipe = root / (arm + '-recipe.json')
                recipe.write_text(json.dumps({'arm': arm}))
                workspaces[arm], builds[arm], logs[arm] = workspace, build, log
                setups[arm] = dict(recipe=str(recipe),
                                   recipe_sha256=hashlib.sha256(recipe.read_bytes()).hexdigest(),
                                   ocamlpath='/private/findlib-' + arm)
            args = SimpleNamespace(workspace=workspaces['A'], changed_workspace=workspaces['B'],
                                   build_dir=builds['A'], changed_build_dir=builds['B'], extra=None,
                                   mode='compare', writer_prefix='test', compiler_setups=setups,
                                   pcs=['69a4'], tool_versions={})
            args.sources = paired_scratch.source_scope(args)
            calls = []
            def launch(command, cwd, text):
                arm = 'A' if cwd == workspaces['A'] else 'B'
                calls.append((arm, command))
                return f"watching 'test' (runner pid 123); output: {logs[arm]}\n"
            with patch.object(paired_scratch.subprocess, 'check_output', side_effect=launch), \
                    patch.object(paired_scratch, 'process_identity', return_value=None):
                for arm in ['A', 'B']:
                    self.assertEqual(paired_scratch.watched_sample('69a4', arm, 1, lambda _: None, args)['exit_code'], 0)
            helper = str(Path(paired_scratch.__file__).with_name('scratch_block.sh').resolve())
            for arm, command in calls:
                self.assertIn(helper, command)
                self.assertEqual(command[-2:], ['--source-workspace', str(workspaces[arm])])
                self.assertIn('ZESU_SCRATCH_RECIPE=' + setups[arm]['recipe'], command)
                self.assertIn('ZESU_SCRATCH_RECIPE_SHA256=' + setups[arm]['recipe_sha256'], command)
                self.assertIn('OCAMLPATH=' + setups[arm]['ocamlpath'], command)

    def test_changed_frozen_helper_refuses_before_a_watcher(self):
        with tempfile.TemporaryDirectory() as directory:
            helper = Path(directory) / 'helper.py'
            helper.write_text('changed')
            args = SimpleNamespace(workspace=Path(directory), build_dir=Path(directory),
                                   extra=None, mode='noise', compiler_setups={'A': {}},
                                   tool_versions={str(helper): 'old'})
            with patch.object(paired_scratch.subprocess, 'check_output') as launch:
                with self.assertRaisesRegex(ValueError, 'helper changed'):
                    paired_scratch.watched_sample('69a4', 'A', 1, lambda _: None, args)
                launch.assert_not_called()


if __name__ == '__main__':
    unittest.main()
