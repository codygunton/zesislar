import copy
import hashlib
import sys
import tempfile
import unittest
from unittest.mock import patch
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
        options = {'design': str(design), 'workspace': str(root)}
        rendered = {'source': Path(evidence['source']).read_text()}
        with patch('successor_entailment.native_boundary_source', return_value=rendered):
            result = discovery.reuse_native_capture({'entry_pc': '0x10'}, self.block, {}, previous, options)
            self.assertTrue(result['reused_native_attempt'])
            exported.write_text('changed')
            with self.assertRaisesRegex(ValueError, 'goal export changed'):
                discovery.reuse_native_capture({'entry_pc': '0x10'}, self.block, {}, previous, options)
        with patch('successor_entailment.native_boundary_source', return_value={'source': 'different'}):
            with self.assertRaisesRegex(ValueError, 'obligation changed'):
                discovery.reuse_native_capture({'entry_pc': '0x10'}, self.block, {}, previous, options)


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
