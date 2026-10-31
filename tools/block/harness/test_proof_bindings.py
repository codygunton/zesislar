import tempfile,unittest
from pathlib import Path
import scratch
from proof_bindings import check_proof_bindings,proof_rows
class SeparationControls(unittest.TestCase):
 def fixture(self,root):
  watcher=root/'watch.py';proof=root/'Proof.v';harness=root/'provider.py'
  for path in [watcher,proof,harness]:path.write_text('original')
  return {'watcher':scratch.binding(watcher),'bindings':[scratch.binding(p) for p in [watcher,proof,harness]],'scratch_provider':scratch.binding(harness)},watcher,proof,harness
 def test_coordination_change_preserves_post_call_check(self):
  with tempfile.TemporaryDirectory() as d:
   r,w,p,h=self.fixture(Path(d));w.write_text('changed coordinator');check_proof_bindings(r)
 def test_proof_change_refuses(self):
  with tempfile.TemporaryDirectory() as d:
   r,w,p,h=self.fixture(Path(d));p.write_text('changed proof')
   with self.assertRaises(ValueError):check_proof_bindings(r)
 def test_harness_change_refuses(self):
  with tempfile.TemporaryDirectory() as d:
   r,w,p,h=self.fixture(Path(d));h.write_text('changed harness')
   with self.assertRaises(ValueError):check_proof_bindings(r)
 def test_undeclared_coordination_looking_file_remains_bound(self):
  with tempfile.TemporaryDirectory() as d:
   r,w,p,h=self.fixture(Path(d));other=Path(d)/'ai-coord.py';other.write_text('original');r['bindings'].append(scratch.binding(other));other.write_text('changed')
   with self.assertRaises(ValueError):check_proof_bindings(r)
 def test_proof_cannot_be_declared_coordination(self):
  with tempfile.TemporaryDirectory() as d:
   r,w,p,h=self.fixture(Path(d));r['coordination_bindings']=[dict(scratch.binding(p),role='status')]
   with self.assertRaises(ValueError):proof_rows(r)
 def test_harness_cannot_be_declared_coordination(self):
  with tempfile.TemporaryDirectory() as d:
   r,w,p,h=self.fixture(Path(d));r['coordination_bindings']=[dict(scratch.binding(h),role='status')]
   with self.assertRaises(ValueError):proof_rows(r)
 def test_duplicates_remain_refused(self):
  with tempfile.TemporaryDirectory() as d:
   r,w,p,h=self.fixture(Path(d));r['bindings'].append(r['bindings'][0])
   with self.assertRaises(ValueError):proof_rows(r)
 def test_symlink_change_rechecks_coordination_classification(self):
  with tempfile.TemporaryDirectory() as d:
   r,w,p,h=self.fixture(Path(d));alias=Path(d)/'watcher-link';alias.symlink_to(w)
   r['watcher']=dict(r['watcher'],path=str(alias));r['bindings'][0]=dict(r['bindings'][0],path=str(alias))
   proof_rows(r)
   alias.unlink();alias.symlink_to(p)
   with self.assertRaises(ValueError):proof_rows(r)
if __name__=='__main__':unittest.main()
