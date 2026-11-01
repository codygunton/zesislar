"""Temporary kernel accounting controls. These controls grant no slot identity."""
import copy
import shutil
from pathlib import Path
import sys
import unittest
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE)]
import admission_memory as M
import test_admission_memory as F


class StaticKernelAccounts(unittest.TestCase):
    process=F.ScopeTests.process
    write=F.ScopeTests.write
    def setUp(self):
        F.ScopeTests.setUp(self)
        (self.group/'cgroup.events').write_text('populated 1\n')
        self.data['shell_marker_directory']=str(self.root/'tokens')
        Path(self.data['shell_marker_directory']).mkdir()
        info=self.group.stat()
        self.bound={'scope':str(self.group),'device':info.st_dev,'inode':info.st_ino}
    def account(self,booking=8*M.GIB,canonical=True):
        self.data['legacy_kernel_accounts']={'static':{'aggregate':self.bound,'booking_bytes':booking,
            'canonical_owners':{self.key:self.owner} if canonical else {}}}
        self.data['fixed_claims']={self.key:booking} if canonical else {}
    def project(self):
        return M.projection(self.data,self.data['fixed_claims'],0,100*M.GIB,reader=self.reader)
    def test_static_canonical_alias_preserves_original_claim_and_counts_once(self):
        self.account()
        token=Path(self.data['shell_marker_directory'])/'99.legacy'
        token.write_text(f'confirmed\naggregate={self.group.name}\nmemory_claim_bytes={8*M.GIB}\nowner_start=1\n')
        before=copy.deepcopy(self.data)
        result=self.project()
        self.assertEqual(result['active_claim_bytes'],8*M.GIB)
        self.assertEqual(self.data,before)
        self.assertTrue(result['fits'])
    def test_empty_kernel_directory_retains_booking_until_absence(self):
        self.account(6*M.GIB,canonical=False)
        (self.group/'cgroup.events').write_text('populated 0\n')
        self.assertEqual(self.project()['active_claim_bytes'],6*M.GIB)
        shutil.rmtree(self.group)
        self.assertEqual(self.project()['active_claim_bytes'],0)
    def test_replaced_kernel_directory_gets_no_credit_or_alias_release(self):
        self.account()
        self.group.rename(self.group.with_name(self.group.name+'.old'))
        self.group.mkdir();(self.group/'memory.current').write_text(str(90*M.GIB))
        (self.group/'cgroup.events').write_text('populated 1\n')
        result=self.project()
        self.assertEqual(result['active_claim_bytes'],16*M.GIB)
        self.assertEqual(result['credited_live_bytes'],0)
    def test_static_account_does_not_replace_compiler_token_authentication(self):
        self.account()
        marker=Path(self.data['shell_marker_directory'])/'11.legacy'
        marker.write_text(f'13\nowner_start=101\nchild_start=103\naggregate={self.group.name}\n')
        (self.proc/'13/environ').write_bytes(b'')
        self.assertFalse(self.reader.compiler(marker)['verified'])


if __name__=='__main__':unittest.main()
