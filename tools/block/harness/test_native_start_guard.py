import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE / 'code'), str(HERE.parents[1]), str(HERE.parents[2])]
import native_start_guard as G
from declaration_preflight import declaration_search_fixture
from scratch_statement import source_statement


class NativeStartGuard(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.counter = 0
        self.statement = 'Lemma DesignedBoundary_Test (x : nat) : x = x.\n'
        self.source = self.root / 'Caller.v'
        self.source.write_text('Lemma repair : True.\nProof.\nexact I.\nQed.\n' +
                               self.statement + 'Proof.\nzesu_block.\nQed.\n')

    def export(self, **changes):
        goal = {'info': {'evar': 'opaque'}, 'ty': 'eq nat x x',
                'hyps': [{'names': ['x'], 'ty': 'nat', 'def': None}]}
        kernel = {'goals': [goal], 'stack': [], 'shelf': [], 'given_up': []}
        kernel.update(changes)
        value = copy.deepcopy(kernel)
        value.update(kernel_groups=kernel,
                     local_definition_export={'original_state_preserved': True})
        self.counter += 1
        path = self.root / ('state%d.json' % self.counter)
        path.write_text(json.dumps(value))
        return {'success': True, 'path': str(path),
                'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}

    def test_repair_proof_before_requested_theorem(self):
        spec = source_statement(self.source)
        fixture, line = declaration_search_fixture(self.source, spec, self.root, 'block')
        span = G.theorem_span(fixture, self.statement, 'DesignedBoundary_Test')
        self.assertEqual(span['proof_line'], line)
        self.assertEqual(line, 5)
        raw = fixture.read_bytes()
        self.assertEqual(raw[span['declaration_start_byte']:span['declaration_end_byte']], self.statement.encode())

    def test_statement_change_refuses(self):
        with self.assertRaisesRegex(ValueError, 'authenticated statement'):
            G.theorem_span(self.source, self.statement.replace('x = x', 'True'), 'DesignedBoundary_Test')

    def test_partial_statement_refuses(self):
        with self.assertRaisesRegex(ValueError, 'complete declaration'):
            G.theorem_span(self.source, self.statement[:20], 'DesignedBoundary_Test')

    def test_ambiguous_theorem_name_refuses(self):
        self.source.write_text(self.source.read_text() + self.statement + 'Proof.\nAbort.\n')
        with self.assertRaisesRegex(ValueError, 'ambiguous'):
            G.theorem_span(self.source, self.statement, 'DesignedBoundary_Test')

    def test_goal_ids_do_not_change_kernel_identity(self):
        reference = self.export()
        goal = {'info': {'evar': 'different'}, 'ty': 'eq nat x x',
                'hyps': [{'names': ['x'], 'ty': 'nat', 'def': None}]}
        self.assertTrue(G.compare_initial(self.export(goals=[goal]), reference)['matched'])

    def test_wrong_initial_target_refuses(self):
        with self.assertRaisesRegex(ValueError, 'differs'):
            G.compare_initial(self.export(goals=[{'ty': 'True', 'hyps': []}]), self.export())

    def test_changed_ordered_hypotheses_refuse(self):
        one = {'names': ['x'], 'ty': 'nat', 'def': None}
        two = {'names': ['y'], 'ty': 'nat', 'def': '0'}
        ref = self.export(goals=[{'ty': 'True', 'hyps': [one, two]}])
        with self.assertRaisesRegex(ValueError, 'differs'):
            G.compare_initial(self.export(goals=[{'ty': 'True', 'hyps': [two, one]}]), ref)

    def test_changed_local_definition_refuses(self):
        goal = {'ty': 'eq nat x x', 'hyps': [{'names': ['x'], 'ty': 'nat', 'def': '1'}]}
        with self.assertRaisesRegex(ValueError, 'differs'):
            G.compare_initial(self.export(goals=[goal]), self.export())

    def test_extra_goal_groups_refuse(self):
        goal = {'ty': 'True', 'hyps': []}
        for group, extra in [('goals', [goal, goal]), ('stack', [([], [])]),
                             ('shelf', [goal]), ('given_up', [goal])]:
            with self.subTest(group=group), self.assertRaisesRegex(ValueError, 'exactly one'):
                G.compare_initial(self.export(**{group: extra}), self.export())

    def test_changed_export_bytes_refuse(self):
        export = self.export()
        Path(export['path']).write_text('{}')
        with self.assertRaises(ValueError):
            G.compare_initial(export, self.export())


if __name__ == '__main__':
    unittest.main()
