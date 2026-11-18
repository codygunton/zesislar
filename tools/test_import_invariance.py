import unittest

import import_invariance as I


CALLER = """Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
Lemma x : True.
"""


class ImportInvarianceTests(unittest.TestCase):
    def test_import_goes_after_the_final_import(self):
        text = I.insert_after_imports(CALLER, 'From Coq Require Import Lia.')
        self.assertEqual(text.splitlines()[2:5], [
            'Require Import ZesuSsz.Automation2.All.', 'From Coq Require Import Lia.',
            'Local Open Scope Z_scope.'])

    def test_caller_without_imports_is_refused(self):
        with self.assertRaises(ValueError):
            I.insert_after_imports('Lemma x : True.\n', 'From Coq Require Import Lia.')

    def test_stream_keeps_every_record_in_order(self):
        log = ('@@T kind=alt site=l_liStep stage=zesu_run_pass ms=4.8 ok=1\n'
               '@@T kind=lia site=Lia.lia stage=zesu_run_pass ms=1086 ok=0\n'
               'Chars 1 - 2 [Proof.]\n'
               '@@T kind=altfail site=l_region_fault stage=zesu_run_pass ms=13181 ok=0\n')
        self.assertEqual(I.search_stream(log), [('alt', 'l_liStep', 'zesu_run_pass'),
                                                ('lia', 'Lia.lia', 'zesu_run_pass'),
                                                ('altfail', 'l_region_fault', 'zesu_run_pass')])

    def test_first_difference(self):
        base = [('alt', 'a', 's'), ('altfail', 'b', 's')]
        self.assertIsNone(I.first_difference(base, list(base)))
        self.assertEqual(I.first_difference(base, [('alt', 'a', 's'), ('alt', 'b', 's')]), 1)
        self.assertEqual(I.first_difference(base, base[:1]), 1)


if __name__ == '__main__':
    unittest.main()
