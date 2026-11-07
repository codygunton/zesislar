"""Review controls for the universal solver source scanner."""
from pathlib import Path
import tempfile
import unittest

from check_solver_context import inspect


class SolverContextReview(unittest.TestCase):
    def inspect(self, source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Control.v'
            path.write_text(source, encoding='utf-8')
            return inspect(path)

    def test_captured_solver_alias_is_unprotected(self):
        calls, _ = self.inspect('Ltac captured := Lia.lia. Ltac use := captured.')
        self.assertEqual([(call['solver'], call['protected']) for call in calls],
                         [('Lia.lia', False)])

    def test_callback_does_not_protect_following_call(self):
        calls, _ = self.inspect('SearchBudget.zesu_solve_selected ("site"%string) '
                                'ltac:(lia); nia.')
        self.assertEqual([call['protected'] for call in calls], [True, False])

    def test_qualified_collection_off_retry_is_forbidden(self):
        _, forbidden = self.inspect('first [zesu_block2 | pose proof '
                                   'ContextCollection.zesu_context_collection_off_intro; '
                                   'zesu_block2].')
        self.assertEqual(len(forbidden), 1)

    def test_tactic_declaration_keeps_body_call(self):
        calls, _ = self.inspect('Ltac Lia.lia ::= nia.')
        self.assertEqual([call['solver'] for call in calls], ['nia'])

    def test_multiline_selected_callback_is_protected(self):
        calls, _ = self.inspect('SearchBudget.zesu_solve_selected\n'
                                '  ("site"%string)\n  ltac:(Lia.lia).')
        self.assertEqual([call['protected'] for call in calls], [True])

    def test_untrusted_wrapper_name_is_not_protection(self):
        calls, _ = self.inspect('Fake.zesu_solve_selected ("site"%string) ltac:(lia).')
        self.assertEqual([call['protected'] for call in calls], [False])

    def test_custom_certificate_entry_is_a_call(self):
        calls, _ = self.inspect('Ltac range_interval := ltac2:(RF.rc_lia ()).')
        self.assertEqual([call['solver'] for call in calls], ['RF.rc_lia'])

    def test_ltac2_declaration_name_is_not_a_call(self):
        calls, _ = self.inspect('Ltac2 lia () := ().')
        self.assertEqual(calls, [])


if __name__ == '__main__':
    unittest.main()
