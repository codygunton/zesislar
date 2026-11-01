import _historical_fixtures as historical
historical.prepare()
from pathlib import Path
import copy,json,sys,unittest
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import memory_policy as P
ROWS=historical.read_json(HERE/'test-fixtures/COMPLETED-STOCK-MEASUREMENTS.json')['rows']
ROW=next(r for r in ROWS if r.get('format')=='completed_stock_verification_repair_v1')
TARGET=P.read(ROW['verification_supplement'])['target']
class VerificationMemoryTests(unittest.TestCase):
 def test_exact_repair_uses_32_gib(self):
  # Test data exercises policy conversion. It is not admission evidence.
  with patch('verification_supplement.validate',return_value={'native_peak_bytes':20*P.GIB,'scope':'synthetic unit data'}):
   value,reason=P.completed(ROW,TARGET);self.assertIsNone(reason);self.assertEqual(value['claim_bytes'],32*P.GIB)
 def test_native_fence_remains_64(self):
  with patch('verification_supplement.validate',return_value={'native_peak_bytes':20*P.GIB,'scope':'synthetic unit data'}):
   job=P.apply_job({'phase':'native','target':TARGET},[ROW]);self.assertEqual(P.validate_job(job),32*P.GIB);self.assertEqual(job['physical_fence_bytes'],64*P.GIB)
 def test_missing_historical_object_refuses(self):
  with self.assertRaises(FileNotFoundError):P.completed(ROW,TARGET)
 def test_mismatched_source_keeps_full_claim(self):
  job=P.apply_job({'phase':'native','target':dict(TARGET,source_sha256='0'*64)},[ROW]);self.assertEqual(job['claim_bytes'],64*P.GIB)
 def test_missing_repair_keeps_original_refusal(self):
  row=copy.deepcopy(ROW);row.pop('format');self.assertIsNone(P.completed(row,TARGET)[0])
 def test_compilation_policy_stays_24(self):
  job=P.apply_job({'phase':'prerequisites','target':None},[ROW]);self.assertEqual(job['claim_bytes'],24*P.GIB);self.assertEqual(job['physical_fence_bytes'],64*P.GIB)
 def test_supplement_and_dependencies_enter_bindings(self):
  rows=P.verification_bindings(ROW);self.assertIn(ROW['verification_supplement'],rows);self.assertGreater(len(rows),1490)
if __name__=='__main__':unittest.main()
