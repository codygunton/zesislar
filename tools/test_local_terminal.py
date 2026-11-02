"""Preserve source-bound local continuations without inventing terminal constants."""
from copy import deepcopy
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).parent / 'block'))
from successor_entailment import typed_local_continuation, native_boundary_source
import chain_root


class LocalTerminalTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        path = self.root / 'Entry.v'
        path.write_text('Definition entry (args : Args) (ret : Z) (K : iProp Sigma) : iProp Sigma := (resource args ∗ K)%I.\n')
        self.original = dict(entry_pc='0x10', entry_definition='Entry.entry',
                             resource_predicate='Entry.entry',
                             binders=[dict(name='args', type='Args'), dict(name='ret', type='Z'), dict(name='K', type='iProp Sigma')],
                             arguments=['args', 'ret', 'K'],
                             source_hashes={'Entry.v': hashlib.sha256(path.read_bytes()).hexdigest()})
        self.terminal = dict(kind='typed_local_continuation', address='ret',
                             parameter=dict(name='K', type='iProp Sigma'),
                             source_hashes=self.original['source_hashes'])

    def test_exact_local_parameter(self):
        self.assertEqual(typed_local_continuation(self.terminal, self.original, self.root), 'K')

    def test_refuses_changed_descriptor(self):
        for field, value in [('parameter', dict(name='other', type='iProp Sigma')),
                             ('parameter', dict(name='K', type='Prop')),
                             ('address', 'other'), ('address', '0'),
                             ('source_hashes', {'Entry.v': '0' * 64}),
                             ('definition', 'Fake.constant')]:
            with self.subTest(field=field, value=value):
                changed = deepcopy(self.terminal)
                changed[field] = value
                self.assertRaises(ValueError, typed_local_continuation, changed, self.original, self.root)

    def test_refuses_changed_source_telescope_or_application(self):
        for field in ['binders', 'arguments']:
            changed = deepcopy(self.original)
            if field == 'binders':
                changed[field][-1]['type'] = 'Other'
            else:
                changed[field][-1] = 'arbitrary'
            self.assertRaises(ValueError, typed_local_continuation, self.terminal, changed, self.root)

    def test_refuses_changed_source_bytes(self):
        (self.root / 'Entry.v').write_text('Definition entry := False.\n')
        self.assertRaises(ValueError, typed_local_continuation, self.terminal, self.original, self.root)

    def test_terminal_preserves_entry_and_exact_source_prefix(self):
        original = self.original
        state = dict(root_provenance={k: original[k] for k in ['entry_definition', 'resource_predicate', 'binders', 'arguments', 'source_hashes']},
                     binders='`{!islaG Sigma} `{!threadG} (args : Args) (ret : Z) (K : iProp Sigma)',
                     coq=[], spatial=['Entry.entry (args) (ret) (K)'])
        marker = chain_root.boundary_stop('ret')
        prefix = 'Require Import A.\n(* exact source: 0 <= 1; Z.of_nat *)\n'
        source = prefix + 'Lemma infer_boundary ' + state['binders'] + ' (' + marker + ' : iProp Sigma) :\n  instr_pre (ret) ' + marker + ' -∗\n  instr_body 0x10 (Entry.entry (args) (ret) (K)).\nProof.\ntry zesu_block.\nAbort.\n'
        design = dict(entry_pc='0x10', blocks=[original], table_convention=dict(existential_binders="Each row's binders, in their listed order"))
        with patch('successor_entailment.chain_root.render_probe', return_value=source):
            rendered = native_boundary_source(state, dict(start='0x10', successors=[]), design, self.root, terminal=self.terminal)
        self.assertTrue(rendered['source'].startswith(prefix))
        self.assertIn('(K : iProp Sigma)', rendered['source'])
        self.assertIn('Entry.entry (args) (ret) (K)', rendered['source'])
        self.assertNotIn(marker, rendered['source'])
        self.assertNotIn('instr_pre', rendered['source'])
        self.assertEqual(rendered['terminal_scope'], 'source-bound typed local continuation')
        self.assertRaises(ValueError, native_boundary_source, state, dict(start='0x10', successors=['0x20']), design, self.root, terminal=self.terminal)


if __name__ == '__main__':
    unittest.main()
