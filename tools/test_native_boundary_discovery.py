import copy
import argparse
import asyncio
import contextlib
import io
import hashlib
import sys
import tempfile
import unittest
from unittest.mock import patch, AsyncMock
import json
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent/'block'))
import discovery


class NativeClosureTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        path = Path(self.directory.name)/'Boundary.v'
        path.write_text('Lemma boundary : decodeItemSelectedCode -∗ instr_body 0x10 entry.\nProof.\ntry zesu_block.\nQed.\n')
        self.block = {'successors': ['0x20', '0x30']}
        self.rendered = {'scope': 'unproved native designed boundary', 'successors': ['0x20', '0x30']}
        self.evidence = {'outcome': 'verified', 'block_closed': True,
                         'inherited_debts': {'pending_goals': [], 'shelved_goals': []},
                         'debt_groups': {'groups': {'goals': [], 'stack': [], 'shelf': [], 'given_up': []}},
                         'source': str(path), 'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                         'calls': [{'tool': 'rocq_compile_file', 'arguments': {}, 'result': {'success': True}},
                                   {'tool': 'rocq_verify', 'arguments': {}, 'result': {'success': True, 'assumptions': []}},
                                   {'tool': 'rocq_check', 'arguments': {'body': 'try zesu_block.', 'timeout': 300},
                                    'result': {'success': True}}]}

    def test_verified_debt_free_all_successor_boundary_counts(self):
        self.assertTrue(discovery.native_boundary_closed(self.evidence, self.rendered, self.block))

    def test_missing_groups_and_all_debt_groups_prevent_closure(self):
        for group in ('goals', 'stack', 'shelf', 'given_up'):
            evidence = copy.deepcopy(self.evidence)
            del evidence['debt_groups']['groups'][group]
            self.assertFalse(discovery.native_boundary_closed(evidence, self.rendered, self.block))
            evidence = copy.deepcopy(self.evidence)
            evidence['debt_groups']['groups'][group] = [[[], [{'ty': 'True'}]]] if group == 'stack' else [{'ty': 'True'}]
            self.assertFalse(discovery.native_boundary_closed(evidence, self.rendered, self.block))

    def test_inherited_debts_failed_kernel_and_assumptions_prevent_closure(self):
        evidence = copy.deepcopy(self.evidence)
        evidence['inherited_debts']['pending_goals'] = ['P']
        self.assertFalse(discovery.native_boundary_closed(evidence, self.rendered, self.block))
        for index in (0, 1):
            evidence = copy.deepcopy(self.evidence)
            evidence['calls'][index]['result']['success'] = False
            self.assertFalse(discovery.native_boundary_closed(evidence, self.rendered, self.block))
        evidence = copy.deepcopy(self.evidence)
        evidence['calls'][1]['result']['assumptions'] = ['unproved']
        self.assertFalse(discovery.native_boundary_closed(evidence, self.rendered, self.block))

    def test_changed_source_or_missing_successor_prevents_closure(self):
        rendered = {**self.rendered, 'successors': ['0x20']}
        self.assertFalse(discovery.native_boundary_closed(self.evidence, rendered, self.block))
        Path(self.evidence['source']).write_text('Changed source')
        self.assertFalse(discovery.native_boundary_closed(self.evidence, self.rendered, self.block))

    def test_image_only_terminal_cannot_count_as_level1_boundary(self):
        terminal = {'scope': self.rendered['scope'], 'successors': [], 'terminal_scope': 'result image only'}
        self.assertFalse(discovery.native_boundary_closed(self.evidence, terminal, {'successors': []}))
        terminal['terminal_scope'] = 'existing owned Level1 continuation; no added image continuation'
        self.assertTrue(discovery.native_boundary_closed(self.evidence, terminal, {'successors': []}))

    def test_failed_primary_and_short_budget_prevent_closure(self):
        for update in ({'timeout': 299}, {'success': False}):
            evidence = copy.deepcopy(self.evidence)
            destination = 'arguments' if 'timeout' in update else 'result'
            evidence['calls'][2][destination].update(update)
            self.assertFalse(discovery.native_boundary_closed(evidence, self.rendered, self.block))

    def test_reuse_checks_actual_obligation_capture_and_exports(self):
        root = Path(self.directory.name)
        design = root/'design.json'
        design.write_text('{}')
        exported = root/'export.json'
        exported.write_text('{}')
        evidence = copy.deepcopy(self.evidence)
        evidence['exports'] = [{'success': True, 'path': str(exported),
                                'sha256': hashlib.sha256(exported.read_bytes()).hexdigest()}]
        bound = root/'evidence.json'
        bound.write_text(json.dumps(evidence))
        previous = {'entry': '0x10', 'captures': [{'native_evidence': {
            'path': str(bound), 'sha256': hashlib.sha256(bound.read_bytes()).hexdigest()}}]}
        options = {'design': str(design), 'workspace': str(root),
                   'terminal_descriptor': {'kind': 'owned_continuation', 'address': 'ret'}}
        rendered = {'source': Path(evidence['source']).read_text()}
        with patch('successor_entailment.native_boundary_source', return_value=rendered) as render:
            result = discovery.reuse_native_capture({'entry_pc': '0x10'}, self.block, {}, previous, options)
            self.assertTrue(result['reused_native_attempt'])
            self.assertIsNone(render.call_args.kwargs['terminal'])
            terminal_block = {'successors': []}
            discovery.reuse_native_capture({'entry_pc': '0x10'}, terminal_block, {}, previous, options)
            self.assertEqual(render.call_args.kwargs['terminal'], options['terminal_descriptor'])
            exported.write_text('changed')
            with self.assertRaisesRegex(ValueError, 'goal export changed'):
                discovery.reuse_native_capture({'entry_pc': '0x10'}, self.block, {}, previous, options)
        with patch('successor_entailment.native_boundary_source', return_value={'source': 'different'}):
            with self.assertRaisesRegex(ValueError, 'obligation changed'):
                discovery.reuse_native_capture({'entry_pc': '0x10'}, self.block, {}, previous, options)


class TerminalDescriptorTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.owner = self.root/'Example/Entries.v'
        self.owner.parent.mkdir()
        self.owner.write_text('Definition caller (args : nat) := args.\n')
        self.descriptor = {'kind': 'owned_continuation', 'address': 'returnAddress args',
            'definition': 'Example.Entries.caller',
            'source_hashes': {'Example/Entries.v': discovery.digest(self.owner)}}
        self.path = self.root/'terminal.json'
        self.path.write_text(json.dumps(self.descriptor))

    def test_descriptor_binds_the_named_existing_definition(self):
        loaded = discovery.load_terminal_descriptor(self.path, 'returnAddress args', self.root)
        self.assertEqual(loaded, self.descriptor)
        options = {'terminal': 'returnAddress args', 'workspace': str(self.root),
                   'terminal_descriptor': loaded}
        self.assertEqual(discovery.designed_terminal({'successors': []}, options), loaded)
        self.assertIsNone(discovery.designed_terminal({'successors': ['0x20']}, options))

    def test_changed_source_and_missing_definition_reject(self):
        self.owner.write_text('Definition another := 0.\n')
        with self.assertRaises(ValueError):
            discovery.load_terminal_descriptor(self.path, 'returnAddress args', self.root)
        self.descriptor['source_hashes']['Example/Entries.v'] = discovery.digest(self.owner)
        self.path.write_text(json.dumps(self.descriptor))
        with self.assertRaisesRegex(ValueError, 'Missing executable Definition'):
            discovery.load_terminal_descriptor(self.path, 'returnAddress args', self.root)

    def test_wrong_kind_address_and_unsafe_terminal_reject(self):
        for update, address in [({'kind': 'image'}, 'returnAddress args'),
                ({'address': 'other args'}, 'returnAddress args'),
                ({'address': 'args. Abort.'}, 'args. Abort.')]:
            value = {**self.descriptor, **update}
            self.path.write_text(json.dumps(value))
            with self.assertRaises(ValueError):
                discovery.load_terminal_descriptor(self.path, address, self.root)

    def test_default_descriptor_stays_exact(self):
        owner = self.root/'ZesuSsz/Contracts/DecodeItemBranchEntries.v'
        owner.parent.mkdir(parents=True)
        owner.write_text('existing source')
        self.assertEqual(discovery.designed_terminal({'successors': []},
            {'terminal': 'ret', 'workspace': str(self.root)}),
            {'kind': 'owned_continuation', 'address': 'ret',
             'definition': 'ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemBranchContinuation',
             'source_hashes': {'ZesuSsz/Contracts/DecodeItemBranchEntries.v': discovery.digest(owner)}})


class CoqcFallbackTests(unittest.IsolatedAsyncioTestCase):
    async def test_failed_pet_entry_uses_same_native_source_and_explicit_debts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            rendered = {'source': 'frozen native statement'}
            debts = {'pending_goals': [], 'shelved_goals': ['inherited debt']}
            evidence = {'outcome': 'native-residual', 'primary_tactic_entered': True,
                'active_goals': [{'conclusion': 'actual successor predicate'}],
                'inherited_debts': debts, 'compiler': {'peak_rss_kib': 1024},
                'block_closed': False, 'contract_closed': False, 'source_sha256': 'bound source'}
            setup = {'residual_class': 'entry_unavailable', 'calls': ['failed start']}
            options = {'build_dir': str(root), 'seconds': 300}
            row = {'entry_pc': '0x10', 'entry_class': 'root'}
            with patch('coqc_primary.run_primary', return_value=evidence) as run, \
                    patch('chain_root.inherited_debts', return_value=debts):
                result = await discovery.fallback_designed_block(row, {}, rendered,
                    options, root, setup, discovery.time.monotonic())
            run.assert_called_once_with(rendered, root/'coqc-fallback', str(root),
                inherited_debts=debts, seconds=300)
            self.assertEqual(result['outcomes'], ['native-residual'])
            self.assertFalse(result['block_closed'])
            retained = json.loads((root/'fallback-evidence.json').read_text())
            self.assertEqual(retained['failed_mcp_setup'], setup)
            self.assertEqual(retained['inherited_debts'], debts)


class FirstNativeRunTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.sha = 'a' * 40
        self.owner = self.root/'Example/Entries.v'
        self.owner.parent.mkdir()
        self.owner.write_text('Definition caller (args : nat) := args.\n')
        self.descriptor = {'kind': 'owned_continuation', 'address': 'returnAddress args',
            'definition': 'Example.Entries.caller',
            'source_hashes': {'Example/Entries.v': discovery.digest(self.owner)}}
        self.write_json('terminal.json', self.descriptor)
        default_owner = self.root/'ZesuSsz/Contracts/DecodeItemBranchEntries.v'
        default_owner.parent.mkdir(parents=True)
        default_owner.write_text('existing continuation source')
        self.row = {'entry_pc': '0x10', 'incoming_edges': [],
            'entry_definition': 'Example.Entries.caller',
            'resource_predicate': 'Example.Entries.caller',
            'binders': [{'name': 'args', 'type': 'nat'}], 'arguments': ['args'],
            'source_hashes': self.descriptor['source_hashes']}
        self.design = {'entry_pc': '0x10', 'hashes': {'selected_elf_sha256': 'elf'},
                       'blocks': [self.row]}
        self.write_json('design.json', self.design)
        self.write_json('cfg.json', {'artifact_identity': 'code'})
        self.write_json('manifest.json', {'artifact_identity': 'code', 'elf_sha256': 'elf'})
        self.write_json('bindings.json', {})
        (self.root/'code.txt').write_text('  Example.code -∗\n')
        self.block = {'start': '0x10', 'successors': []}
        self.state = {'imports': [], 'spatial': ['Example.Entries.caller args'],
            'entry_source': {'path': str(self.owner), 'sha256': discovery.digest(self.owner),
                             'declaration': 'Definition caller'}}
        self.record = {'entry': '0x10', 'captures': [], 'outcomes': ['native-residual'],
                       'block_closed': False}
        self.write_json('baseline.json', {'root_commit': self.sha, 'inputs': {},
            'pairs': [{'entry': '0x10', 'target': 'returnAddress args',
                       'sources': {'switch-on': hashlib.sha256(b'abstract source').hexdigest()}}]})

    def write_json(self, name, value):
        (self.root/name).write_text(json.dumps(value))

    def options(self, **changes):
        values = dict(first_native_run=self.sha, designed_successors=True,
            native_baseline_report=None, native_resume_report=None,
            resume_report=None, entries=None)
        values.update(changes)
        return argparse.Namespace(**values)

    def validate(self, **changes):
        with patch('discovery.subprocess.check_output', return_value=self.sha + '\n'), \
                contextlib.redirect_stderr(io.StringIO()):
            return discovery.first_native_root(self.options(**changes),
                argparse.ArgumentParser(), self.root)

    def invoke(self, extra, *, binding_error=None, head_results=None, pool_effect=None):
        arguments = ['discovery.py', '--design', str(self.root/'design.json'),
            '--trace-import', 'Example.index', '--code-premises', str(self.root/'code.txt'),
            '--binding-report', str(self.root/'bindings.json'), '--cfg', str(self.root/'cfg.json'),
            '--manifest', str(self.root/'manifest.json'), '--out', str(self.root/'out'),
            '--terminal', 'returnAddress args', *extra]
        with contextlib.ExitStack() as stack:
            stack.enter_context(patch.object(sys, 'argv', arguments))
            stack.enter_context(contextlib.chdir(self.root))
            git = stack.enter_context(patch('discovery.subprocess.check_output',
                return_value=self.sha + '\n', side_effect=head_results))
            validator = stack.enter_context(patch('discovery.check_entry_bindings.validate_report',
                side_effect=binding_error))
            stack.enter_context(patch('discovery.entry_schema.design_states',
                return_value=({16: self.state}, {})))
            stack.enter_context(patch('discovery.prepare',
                return_value=([(self.row, self.block, self.state)], [])))
            stack.enter_context(patch('discovery.machine', return_value={}))
            renderer = stack.enter_context(patch('successor_entailment.native_boundary_source',
                return_value={'source': 'abstract source'}))
            pool = stack.enter_context(patch('discovery.ProcessPoolExecutor'))
            pool.return_value.__enter__.return_value.map.return_value = [copy.deepcopy(self.record)]
            if pool_effect is not None:
                pool.return_value.__enter__.return_value.map.side_effect = pool_effect
            stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
            stack.enter_context(contextlib.redirect_stderr(io.StringIO()))
            result = discovery.main()
            return result, json.loads((self.root/'out/report.json').read_text()), pool, renderer, validator, git

    def first_arguments(self):
        return ['--designed-successors', '--first-native-run', self.sha,
                '--terminal-descriptor', str(self.root/'terminal.json')]

    def test_first_native_valid(self):
        result, report, pool, renderer, validator, _ = self.invoke(self.first_arguments())
        self.assertEqual(result, 0)
        options = pool.return_value.__enter__.return_value.map.call_args.args[1][0][-1]
        self.assertEqual(options['terminal_descriptor'], self.descriptor)
        self.assertTrue(options['designed_successors'])
        renderer.assert_not_called()
        validator.assert_called_once()
        self.assertTrue(report['first_native_run'])

    def test_first_native_requires_designed(self):
        with self.assertRaises(SystemExit):
            self.validate(designed_successors=False)

    def test_first_native_forbids_baseline(self):
        with self.assertRaises(SystemExit):
            self.validate(native_baseline_report=Path('baseline.json'))

    def test_first_native_forbids_native_reuse(self):
        with self.assertRaises(SystemExit):
            self.validate(native_resume_report=Path('prior.json'))

    def test_first_native_forbids_capture_reuse(self):
        with self.assertRaises(SystemExit):
            self.validate(resume_report=Path('capture.json'))

    def test_first_native_forbids_legacy_entry(self):
        with self.assertRaises(SystemExit):
            self.validate(entries=Path('legacy.json'))

    def test_first_native_root_mismatch(self):
        with self.assertRaises(SystemExit):
            self.validate(first_native_run='b' * 40)

    def test_first_native_root_malformed(self):
        for value in ('', 'a' * 39, 'a' * 41, 'g' * 40, 'A' * 40):
            with self.subTest(value=value), self.assertRaises(SystemExit):
                self.validate(first_native_run=value)

    def test_first_native_entry_binding_failure(self):
        with self.assertRaisesRegex(ValueError, 'changed executable entry'):
            self.invoke(self.first_arguments(), binding_error=ValueError('changed executable entry'))

    def test_first_native_terminal_owner_failure(self):
        self.owner.write_text('Definition another := 0.\n')
        with self.assertRaises(ValueError):
            self.invoke(self.first_arguments())

    def test_first_native_artifact_mismatch(self):
        self.write_json('cfg.json', {'artifact_identity': 'another code'})
        with self.assertRaisesRegex(ValueError, 'different artifact identity'):
            self.invoke(self.first_arguments())

    def test_first_native_report_identity(self):
        _, report, _, _, _, git = self.invoke(self.first_arguments())
        self.assertEqual(report['measurement_root'], self.sha)
        self.assertIsNone(report['frozen_baseline_report'])
        self.assertFalse(report['capture_only'])
        self.assertEqual(git.call_count, 2)
        with self.assertRaisesRegex(ValueError, 'changed during execution'):
            self.invoke(self.first_arguments(), head_results=[self.sha, 'b' * 40])

    def test_comparison_baseline_still_required(self):
        with self.assertRaises(SystemExit):
            self.invoke(['--designed-successors'])

    def test_comparison_input_check_preserved(self):
        baseline = json.loads((self.root/'baseline.json').read_text())
        baseline['inputs'] = {str(self.owner): '0' * 64}
        self.write_json('baseline.json', baseline)
        with self.assertRaisesRegex(ValueError, 'frozen native comparison input changed'):
            self.invoke(['--designed-successors', '--native-baseline-report', str(self.root/'baseline.json')])

    def test_comparison_source_check_preserved(self):
        baseline = json.loads((self.root/'baseline.json').read_text())
        baseline['pairs'][0]['sources']['switch-on'] = '0' * 64
        self.write_json('baseline.json', baseline)
        with self.assertRaisesRegex(ValueError, 'differs from the frozen full-ON baseline'):
            self.invoke(['--designed-successors', '--native-baseline-report', str(self.root/'baseline.json')])

    def test_comparison_output_preserved(self):
        arguments = ['--designed-successors', '--native-baseline-report', str(self.root/'baseline.json')]
        _, report, _, renderer, _, git = self.invoke(arguments)
        self.assertNotIn('first_native_run', report)
        self.assertEqual(report['measurement_root'], self.sha)
        self.assertEqual(report['frozen_baseline_report'], str(self.root/'baseline.json'))
        self.assertTrue(report['designed_successors'])
        self.assertFalse(renderer.call_args.kwargs['enabled'])
        git.assert_not_called()

    def test_capture_descriptor_rejection_preserved(self):
        with self.assertRaises(SystemExit):
            self.invoke(['--terminal-descriptor', str(self.root/'terminal.json')])

    def test_native_renderer_and_debt_policy_preserved(self):
        marker = {'block_closed': False, 'inherited_debts': {'shelved_goals': ['debt']}}
        with patch('discovery.probe_designed_block', new_callable=AsyncMock, return_value=marker) as native:
            result = asyncio.run(discovery.probe_block(self.row, self.block, self.state,
                                                       {'designed_successors': True}))
        self.assertEqual(result, marker)
        native.assert_awaited_once()
