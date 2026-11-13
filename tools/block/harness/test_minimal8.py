import sys,unittest
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import test_native_route as F
import memory_policy as M
import scratch_limits as L
class Minimal8(unittest.TestCase):
 setUp=F.NativeRoute.setUp
 file=F.NativeRoute.file
 js=F.NativeRoute.js
 fixture=F.NativeRoute.fixture
 def test_stock_family_default_stays16(self):self.assertEqual(M.FAMILY_DEFAULT_CLAIM,16*M.GIB)
 def test_native_parent_and_compile_limits_stay(self):
  self.assertEqual(M.NATIVE_FENCE,64*M.GIB);self.assertEqual(M.PARENT_FENCE,175*M.GIB);self.assertEqual(M.apply_job({'phase':'prerequisites'})['claim_bytes'],24*M.GIB)
 def test_unknown_native_keeps_full_fence(self):self.assertEqual(M.apply_job({'phase':'native','target':{}})['claim_bytes'],64*M.GIB)
 def test_bad_source_does_not_get_minimal8(self):
  value,route,c,j=self.fixture();profile=self.js('profile.json',{'schema':'scratch.admission-profile.v1','kind':'minimal_native_tactic','authority':route});Path(value['native_source']['path']).write_text('changed')
  with self.assertRaises(ValueError):M.workload_for_job(profile,j,c)
 def test_minimal_peak_reports_above8_without_changing_stock(self):
  self.assertFalse(L.claim_report_required(8*M.GIB,8*M.GIB,family=True,family_threshold_bytes=8*M.GIB))
  self.assertTrue(L.claim_report_required(9*M.GIB,8*M.GIB,family=True,family_threshold_bytes=8*M.GIB))
  self.assertFalse(L.claim_report_required(9*M.GIB,16*M.GIB,family=True))
 def growth(self,peak):
  value,route,c,j=self.fixture();directory=self.root/'prior';directory.mkdir();agg={'aggregate_path':'/sys/fs/cgroup/example','aggregate_device':1,'aggregate_inode':2}
  runtime=self.js('prior/RUNTIME.json',{'phase':'native','target':{'block':j['target']},'job_output':str(directory)})
  aggregate=self.js('prior/BATCH-IDENTITY.json',agg);accounting=self.js('prior/CPU-FINAL.json',{'aggregate_peak_bytes':peak,'final_memory_accounting_available':True,'memory_peak_source':agg['aggregate_path']+'/memory.peak'})
  return {'observed_growth':{'runtime':runtime,'aggregate':aggregate,'accounting':accounting}},j['target']
 def test_observed_peak_raises_claim_with_exact_bytes(self):
  profile,target=self.growth(10*M.GIB);self.assertEqual(M.minimal_growth_claim(profile,target),15*M.GIB)
 def test_growth_for_another_source_refuses(self):
  profile,target=self.growth(10*M.GIB);target=dict(target,source_sha256='0'*64)
  with self.assertRaises(ValueError):M.minimal_growth_claim(profile,target)
 def test_missing_growth_accounting_refuses(self):
  profile,target=self.growth(10*M.GIB);Path(profile['observed_growth']['accounting']['path']).unlink()
  with self.assertRaises((OSError,ValueError)):M.minimal_growth_claim(profile,target)
if __name__=='__main__':unittest.main()
