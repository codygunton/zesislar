import _historical_fixtures as historical
historical.prepare()
from pathlib import Path
from unittest.mock import patch
import copy,json,sys,unittest
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),'/home/cody/zesislar/tools/block','/home/cody/zesislar/tools']
import memory_policy as P
ROWS=historical.read_json(HERE/'test-fixtures/COMPLETED-STOCK-MEASUREMENTS.json')['rows']
ROW=next(r for r in ROWS if r.get('declaration_projection'))
TARGET={'module':ROW['module'],'source_sha256':ROW['native_source']['sha256'],'statement_sha256':'8171c09103807a8fce25145ffed0f47860d52883a15e4431e87aa6202017b843'}

class ProjectionControls(unittest.TestCase):
 def test_exact_projection_uses_sixteen_gib(self):
  value,reason=P.completed(ROW,TARGET)
  self.assertIsNone(reason);self.assertEqual(value['claim_bytes'],16*P.GIB)
  self.assertEqual(ROW['statement_sha256'],'4fdf2194a0261a0437886dbe7b1c1fd96192dd055ecf2b08b434273a1269e486')
 def test_missing_projection_keeps_full_fence(self):
  row=copy.deepcopy(ROW);row.pop('declaration_projection')
  job=P.apply_job({'phase':'native','target':TARGET},[row])
  self.assertEqual(job['claim_bytes'],64*P.GIB)
 def test_different_current_declaration_refuses(self):
  target=dict(TARGET,statement_sha256='0'*64)
  self.assertIsNone(P.completed(ROW,target)[0])
 def test_different_source_refuses(self):
  self.assertIsNone(P.completed(ROW,dict(TARGET,source_sha256='0'*64))[0])
 def altered_read(self,binding,change):
  original=P.read;value=copy.deepcopy(original(binding));change(value)
  return patch.object(P,'read',side_effect=lambda row:value if row==binding else original(row))
 def test_original_result_hash_remains_required(self):
  with self.altered_read(ROW['result'],lambda r:r.update(statement_sha256=TARGET['statement_sha256'])):
   self.assertIsNone(P.completed(ROW,TARGET)[0])
 def test_wrong_theorem_projection_refuses(self):
  with self.altered_read(ROW['declaration_projection'],lambda r:r.update(theorem='AnotherTheorem')):
   self.assertIsNone(P.completed(ROW,TARGET)[0])
 def test_interval_cannot_be_replaced_with_declaration(self):
  with self.altered_read(ROW['declaration_projection'],lambda r:r.update(legacy_interval=r['declaration'])):
   self.assertIsNone(P.completed(ROW,TARGET)[0])
 def test_declaration_cannot_include_import(self):
  with self.altered_read(ROW['declaration_projection'],lambda r:r.update(declaration=r['legacy_interval'])):
   self.assertIsNone(P.completed(ROW,TARGET)[0])
 def test_partial_compile_still_refuses(self):
  with self.altered_read(ROW['compiler'],lambda r:r.update(measurement_complete=False)):
   self.assertIsNone(P.completed(ROW,TARGET)[0])
 def test_unreleased_measurement_still_refuses(self):
  with self.altered_read(ROW['release_ledger'],lambda r:r['fixed_claims'].update({ROW['claim_key']:1})):
   self.assertIsNone(P.completed(ROW,TARGET)[0])
 def test_projection_preserves_fences(self):
  job=P.apply_job({'phase':'native','target':TARGET},[ROW])
  self.assertEqual(P.validate_job(job),16*P.GIB)
  self.assertEqual(job['physical_fence_bytes'],64*P.GIB)
  self.assertEqual(P.PARENT_FENCE,175*P.GIB)

if __name__=='__main__':unittest.main()
