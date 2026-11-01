import _historical_fixtures as historical
historical.prepare()
from pathlib import Path
from unittest.mock import patch
import copy,json,sys,unittest
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import memory_policy as P
ROWS=[row for row in historical.read_json(HERE/'test-fixtures/COMPLETED-STOCK-MEASUREMENTS.json')['rows'] if row.get('format')=='legacy_r1_workload_rss_v1']
def target(row):return {'module':row['module'],'statement_sha256':row['statement_sha256'],'source_sha256':row['native_source']['sha256']}
class LegacyControls(unittest.TestCase):
 def test_all_twentyfive_completed_sources(self):
  self.assertEqual(len(ROWS),25)
  for row in ROWS:
   value,reason=P.completed(row,target(row));self.assertIsNone(reason);self.assertEqual(value['claim_bytes'],P.rounded_rss_claim(value['peak_bytes']));self.assertEqual(value['client_server_allowance_bytes'],4*P.GIB);self.assertEqual(value['memory_metric'],'workload_RSS')
 def test_allowance_and_upward_rounding(self):
  self.assertEqual(P.rounded_rss_claim(1*P.GIB),8*P.GIB);self.assertEqual(P.rounded_rss_claim(4*P.GIB),16*P.GIB);self.assertEqual(P.rounded_rss_claim(8*P.GIB),16*P.GIB);self.assertEqual(P.rounded_rss_claim(8*P.GIB+1),24*P.GIB)
 def mutate_compiler(self,change):
  row=ROWS[0];original=P.read;compiler=original(row['compiler']);change(compiler)
  with patch.object(P,'read',side_effect=lambda binding:compiler if binding==row['compiler'] else original(binding)):
   return P.completed(row,target(row))
 def test_partial_physical_measurement_refuses(self):self.assertIsNone(self.mutate_compiler(lambda x:x.update(measurement_complete=False))[0])
 def test_failed_physical_compile_refuses(self):self.assertIsNone(self.mutate_compiler(lambda x:x.update(exit_code=1))[0])
 def test_oom_physical_measurement_refuses(self):self.assertIsNone(self.mutate_compiler(lambda x:x.update(scope_memory_events_after={'oom_kill':1}))[0])
 def test_private_route_refuses(self):
  row=dict(ROWS[0],route='private_opening');self.assertIsNone(P.completed(row,target(row))[0])
 def test_source_boundary_mismatch_refuses(self):
  selected=target(ROWS[0]);selected['source_sha256']='0'*64;self.assertIsNone(P.completed(ROWS[0],selected)[0])
 def test_modern_fields_are_not_invented(self):
  result=P.read(ROWS[0]['result']);self.assertNotIn('normal_tactic_return',result);self.assertNotIn('aggregate_peak_bytes',result);self.assertIsNotNone(P.completed(ROWS[0],target(ROWS[0]))[0])
 def test_selects_largest_claim_not_raw_peak(self):
  modern={'module':'M','id':'modern'};legacy={'module':'M','id':'legacy'}
  def checked(row,selected):return ({'peak_bytes':10*P.GIB,'claim_bytes':16*P.GIB} if row is modern else {'peak_bytes':9*P.GIB,'claim_bytes':24*P.GIB}),None
  with patch.object(P,'completed',side_effect=checked):value,_=P.select([modern,legacy],{'module':'M'})
  self.assertEqual(value['claim_bytes'],24*P.GIB)
 def test_full_native_fence_is_unchanged(self):
  job=P.apply_job({'phase':'native','target':target(ROWS[0])},[ROWS[0]]);self.assertEqual(job['physical_fence_bytes'],64*P.GIB);self.assertEqual(P.PARENT_FENCE,175*P.GIB)
if __name__=='__main__':unittest.main()
