#!/usr/bin/env python3
"""Test source checks for the solver-context boundary."""
from pathlib import Path
import tempfile
import unittest

from check_solver_context import inspect


class SolverContextTests(unittest.TestCase):
    def inspect(self, source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Control.v'
            path.write_text(source, encoding='utf-8')
            return inspect(path)

    def test_comments_and_strings(self):
        calls, _ = self.inspect('(* lia (* nia *) *) idtac "bv_solve". lia.')
        self.assertEqual([call['solver'] for call in calls], ['lia'])

    def test_selected_callback_only(self):
        calls, _ = self.inspect(
            'SearchBudget.zesu_solve_selected ("site"%string) '
            'ltac:(first [Lia.lia | bv_solve]); nia.')
        self.assertEqual([call['protected'] for call in calls], [True, True, False])

    def test_solver_declaration_is_not_a_call(self):
        calls, _ = self.inspect('Ltac Lia.lia ::= idtac. Ltac bv_solve ::= lia.')
        self.assertEqual([call['solver'] for call in calls], ['lia'])

    def test_captured_and_backend_calls(self):
        calls, _ = self.inspect('Ltac alias := Lia.lia. xlia Lia.zchecker.')
        self.assertEqual([call['solver'] for call in calls], ['Lia.lia', 'xlia'])
        self.assertFalse(any(call['protected'] for call in calls))

    def test_whole_block_retry_marker(self):
        _, forbidden = self.inspect('pose proof zesu_context_collection_off_intro.')
        self.assertEqual(len(forbidden), 1)

    def test_zify_entry_and_shape_predicate(self):
        calls, _ = self.inspect('Ltac2 p () := zify_opaque x a. Zify.zify_op.')
        self.assertEqual([call['solver'] for call in calls], ['Zify.zify_op'])

    def test_cascade_callback(self):
        calls, _ = self.inspect(
            'Ltac zesu_finish_residual_cascade := first [solve ['
            'ContextCollection.zesu_solve_solver ("cascade.byte"%string) '
            'ltac:(lia)] | solve [bv_solve]].')
        self.assertEqual([call['protected'] for call in calls], [True, False])


if __name__ == '__main__':
    unittest.main()
