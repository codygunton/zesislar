"""Invalidate only private output copies. These controls execute no prover."""
from pathlib import Path
import shutil
import tempfile
import unittest

import scratch
from entry_chain import binding
import compiler_snapshot as S


class DeclaredCompilerOutputs(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.bank=self.root/'bank';self.bank.mkdir()
        self.workspace=self.root/'workspace';self.workspace.mkdir()
        self.modules={'Fixture.A':'A.v','Fixture.B':'B.v'}
        self.inherited=[]
        for name in ['A','B']:
            for suffix,body in [('.v','nonproof source '+name),('.vo','retained object '+name)]:
                source=self.bank/(name+suffix)
                source.write_text(body)
                self.inherited.append(binding(source))
                shutil.copyfile(source,self.workspace/source.name)

    def invalidate(self):
        return S.declared_outputs(self.modules,list(self.modules),self.workspace,self.inherited,donor=self.bank)

    def test_only_declared_output_copies_are_removed(self):
        before=[binding(row['path']) for row in self.inherited]
        plan=self.invalidate()
        self.assertEqual(len(plan),2)
        self.assertEqual(self.inherited,before)
        self.assertEqual([binding(row['path']) for row in self.inherited],before)
        self.assertTrue(all((self.workspace/name).is_file() for name in ['A.v','B.v']))
        self.assertFalse(any((self.workspace/name).exists() for name in ['A.vo','B.vo']))
        self.assertEqual({row['module'] for row in plan},set(self.modules))
        S.require_absent_outputs(plan)

    def test_all_paths_validate_before_any_output_copy_is_removed(self):
        self.modules['Fixture.B']='../bank/B.v'
        with self.assertRaisesRegex(ValueError,'leaves its owned workspace'):
            self.invalidate()
        self.assertTrue((self.workspace/'A.vo').is_file())
        self.assertTrue((self.workspace/'B.vo').is_file())

    def test_an_inherited_output_binding_cannot_be_removed(self):
        self.inherited.append(binding(self.workspace/'A.vo'))
        with self.assertRaisesRegex(ValueError,'inherited donor binding'):
            self.invalidate()
        self.assertTrue((self.workspace/'A.vo').is_file())

    def test_existing_donor_outputs_cannot_be_invalidated(self):
        with self.assertRaisesRegex(ValueError,'inherited donor binding|existing donor output'):
            S.declared_outputs(self.modules,list(self.modules),self.bank,self.inherited,donor=self.bank)
        self.assertTrue((self.bank/'A.vo').is_file())

    def test_output_alias_is_refused(self):
        path=self.workspace/'A.vo';path.unlink();path.symlink_to(self.bank/'A.vo')
        with self.assertRaisesRegex(ValueError,'output alias'):
            self.invalidate()
        self.assertEqual((self.bank/'A.vo').read_text(),'retained object A')

    def test_parent_alias_cannot_redirect_the_unlink_operation(self):
        alias=self.workspace/'alias';alias.symlink_to(self.bank,target_is_directory=True)
        with self.assertRaises(OSError):
            S._remove_output_copy(self.workspace,alias/'A.vo')
        self.assertEqual((self.bank/'A.vo').read_text(),'retained object A')

    def test_reappearing_output_refuses_snapshot_publication(self):
        plan=self.invalidate()
        (self.workspace/'A.vo').write_text('unexpected output')
        with self.assertRaisesRegex(ValueError,'exists before snapshot publication'):
            S.require_absent_outputs(plan)


if __name__=='__main__':unittest.main()
