"""Check the leftover classes of tools/bench/triage.py: one synthetic leftover per class."""

import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest

import triage as T
from test_bench_report import write_run

CLASSES = T.load_classes()
EQ = '@Coq.Init.Logic.eq'
CALLER_WITH_CALL = ('Lemma L : instr_pre 0x10 (ZesuSsz.Generated.F.FP301.Pilot0044Entries.e args K)%I -∗\n'
                    '  instr_pre 0x800d6960 (ZesuSsz.Interfaces.DecodeItem.decodeItemCallSpec2)%I -∗ True.\n')
CALLER_WITHOUT_CALL = 'Lemma L : instr_pre 0x10 (ZesuSsz.Generated.F.FP301.Pilot0044Entries.e args K)%I -∗ True.\n'
BOOL_GUARD = ('%s (@Coq.Init.Datatypes.bool) (@Coq.Init.Datatypes.negb (@stdpp.decidable.bool_decide (%s '
              '(@stdpp.bitvector.definitions.bv (64)%%N) x (@stdpp.bitvector.definitions.BV (64)%%N (0)%%Z '
              '(@Coq.Init.Logic.I))))) (@Coq.Init.Datatypes.true)' % (EQ, EQ))
RESULT_EXISTS = ('@Coq.Init.Logic.ex (@ZesuSsz.Contracts.R.NextUint64Return) '
                 '(fun (result : (@ZesuSsz.Contracts.R.NextUint64Return)) => (@Coq.Init.Logic.and (%s '
                 '(@Coq.Init.Datatypes.list (@EvmSailRlp.evm_rlp_types.byte)) '
                 '(@ZesuSsz.Contracts.R.nextResultBytes result) x) (%s Z y y)))' % (EQ, EQ))


def pure(conclusion, premises=''):
    return {'kind': 'final', 'statement': 'forall (x : Z) (y : Z), %s%s' % (premises, conclusion)}


def spatial(site):
    return {'kind': 'final', 'status': 'skip', 'site': site}


class Classes(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='triage-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def block(self, leftovers, end='failed', caller=CALLER_WITHOUT_CALL, errors=()):
        directory = self.root / str(len(list(self.root.iterdir())))
        directory.mkdir()
        (directory / 'Caller0044.v').write_text(caller)
        return {'dir': str(directory), 'verdict': 'NOT-CLOSED', 'end': end, 'cpu': 1.0,
                'leftovers': leftovers, 'errors': list(errors)}

    def label(self, *leftovers, **options):
        return T.triage_block(self.block(list(leftovers), **options), CLASSES)['class']

    def test_one_leftover_per_class(self):
        self.assertEqual(self.label(end='cpu-cap'), 'OVER')
        self.assertEqual(self.label(spatial('(∃_y,____y)%I'), end='memory-fence'), 'OVER')
        self.assertEqual(self.label(pure('%s Z x y' % EQ)), 'WITNESS')
        self.assertEqual(self.label(pure('@Coq.Init.Logic.ex Z (fun z => z = x)')), 'WITNESS')
        self.assertEqual(self.label(spatial('(∃_y,____y)%I'), caller=CALLER_WITH_CALL), 'CALL')
        self.assertEqual(self.label(spatial('(find_in_context_(FindMemMapsTo___)___)')), 'LOOKUP')
        self.assertEqual(self.label(spatial('(find_in_context_(FindRegMapsTo_"mcause")___)')), 'FAULT')
        self.assertEqual(self.label(pure('@ZesuSsz.Automation2.Hist.zesu_hist (x = y)')), 'HIST')
        self.assertEqual(self.label(pure('%s (list Z) (@stdpp.list.take Z 8 x) (@Coq.Lists.List.nth Z 0 y 0)' % EQ)),
                         'WORD')
        self.assertEqual(self.label(pure('@Coq.ZArith.BinInt.Z.le x (@Coq.ZArith.BinInt.Z.add y 1)')), 'PURE')
        self.assertEqual(self.label(pure('@ZesuSsz.Contracts.N.nextUint64Meaning x y')), 'MEANING')
        self.assertEqual(self.label(pure(BOOL_GUARD)), 'GUARD')
        self.assertEqual(self.label(pure('@Coq.ZArith.BinInt.Z.lt (@stdpp.bitvector.definitions.bv_unsigned (64)%N '
                                         '(@stdpp.bitvector.definitions.bv_concat (64)%N (56)%N (8)%N x y)) z')),
                         'WORD-ORDER')
        self.assertEqual(self.label(pure('@Coq.Init.Peano.le (@Coq.ZArith.BinInt.Z.to_nat (@stdpp.bitvector.definitions'
                                         '.bv_unsigned (64)%N (@ZesuSsz.Contracts.P.parentHeaderStackPointer args))) x')),
                         'FRAME-ORDER')
        self.assertEqual(self.label(pure('@ZesuSsz.Contracts.M.parentHeaderMemcpyDomain (@stdpp.bitvector.definitions'
                                         '.bv_unsigned (64)%N x)')), 'MEMCPY')
        self.assertEqual(self.label(spatial('(∃_y,____y)%I')), 'EXIST')  # no callee spec: not CALL

    def test_result_existential_is_meaning_not_witness(self):
        self.assertEqual(self.label(pure(RESULT_EXISTS)), 'MEANING')
        self.assertEqual(self.label(pure(RESULT_EXISTS, premises='x <= y -> ' * 500)), 'MEANING')  # over 4 KB
        self.assertEqual(self.label(pure('@Coq.Init.Logic.ex (@ZesuSsz.Contracts.R.NextUint64Return) '
                                         '(fun (result : (@ZesuSsz.Contracts.R.NextUint64Return)) => result = x)')),
                         'WITNESS')  # an existential over a return value that states no result bytes

    def test_unclassified_keeps_its_head(self):
        big = pure('@Coq.ZArith.BinInt.Z.le x y', premises='x <= y -> ' * 500)  # over 4 KB: not PURE
        result = T.triage_block(self.block([big]), CLASSES)
        self.assertEqual(result['class'], T.UNCLASSIFIED)
        self.assertEqual(result['head'], 'pure @Coq.ZArith.BinInt.Z.le x y')
        self.assertEqual(self.label(pure('@Coq.ZArith.BinInt.Z.lt x y', premises='x <= y -> ' * 500)), T.UNCLASSIFIED)
        errors = [{'text': '\n (in proof X): Attempt to save an incomplete proof\n'}]
        result = T.triage_block(self.block([], errors=errors), CLASSES)
        self.assertEqual((result['class'], result['head']), (T.UNCLASSIFIED, 'error Attempt to save an incomplete proof'))

    def test_block_class_is_first_in_table_order(self):
        result = T.triage_block(self.block([pure('@Coq.ZArith.BinInt.Z.le x y'),
                                            spatial('(find_in_context_(FindMemMapsTo___)___)')]), CLASSES)
        self.assertEqual(result['class'], 'LOOKUP')
        self.assertEqual(dict(result['leftovers']), {'LOOKUP': 1, 'PURE': 1})


class Command(unittest.TestCase):
    def test_rows_of_a_run(self):
        with tempfile.TemporaryDirectory() as name:
            log = ('@@T kind=step site=(find_in_context_(FindMemMapsTo___)___) stage=zesu_run_pass ms=1 ok=0 cpu_ms=1\n'
                   '@@X skip final spatial\n')
            closed = 'Chars 0 - 5 [zesu_block2.] 50. secs (50.u,0.s)\n'
            run = write_run(Path(name), 'run', [
                dict(log=log, cpu=10.0, peak_gib=1.0, verdict='NOT-CLOSED'),
                dict(log=closed, cpu=5.0, peak_gib=1.0, verdict='CLOSED', returncode=0),
                None])
            with contextlib.redirect_stdout(io.StringIO()) as out:
                T.main([str(run)])
            text = out.getvalue()
            self.assertIn('| decodeParentHeader/0300 | failed | 10.0 | LOOKUP | rule 1.1d-2, 1.1d-3 |', text)
            self.assertNotIn('decodeItem/0164 |', text)
            self.assertIn('no result yet: nextUint64/0064', text)
            with contextlib.redirect_stdout(io.StringIO()) as out:
                T.main([str(run), '--json'])
            self.assertEqual([row['class'] for row in json.loads(out.getvalue())['open']], ['LOOKUP'])


if __name__ == '__main__':
    unittest.main()
