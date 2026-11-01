from pathlib import Path
import hashlib,json,tempfile,unittest
import scratch
import _test_support

ROOT=_test_support.historical.directory('/home/cody/zesislar/_build/agents/worker-build-2/entry-normalization-native-matrix-v1')
class HookAdapterControls(unittest.TestCase):
 def test_all_production_statement_boundaries(self):
  for row in json.loads((ROOT/'TARGET-SELECTION-v3.json').read_text())['rows']:
   with self.subTest(key=row['key']):
    actual=scratch.source_statement(row['source'])
    self.assertEqual(actual['statement'],row['statement'])
    self.assertEqual(hashlib.sha256(actual['statement'].encode()).hexdigest(),row['statement_sha256'])
 def test_intervening_import_is_preserved_separately(self):
  row=next(r for r in json.loads((ROOT/'TARGET-SELECTION-v3.json').read_text())['rows'] if r['key']=='800d69b0')
  result=scratch.source_statement(row['source'])
  self.assertIn('Require Import',result['pre_proof_commands'])
  self.assertNotIn('Require Import',result['statement'])
  self.assertIn('DecodeItemEmptyStringOutputMeaning',result['pre_proof_commands'])
 def test_both_join_branches_select(self):
  for name in ['800d698cLiteral','800d698cShortString']:
   with tempfile.TemporaryDirectory() as d:
    args=_test_support.arguments([name,str(_test_support.SOURCE/'workspace/artifacts/default/ZesuSsz/Generated/DecodeItem/Entries.v'),'--target-adapter',str(ROOT/'TARGET-ADAPTER-v3.json'),'--output',d+'/out'])
    self.assertEqual(args.block,name.lower())
 def test_base_seed_requires_digest(self):
  with self.assertRaises(SystemExit):_test_support.arguments(['800d6a08',str(_test_support.SOURCE/'workspace/artifacts/default/ZesuSsz/Generated/DecodeItem/Entries.v'),'--base-runtime','/tmp/runtime.json'])
if __name__=='__main__':unittest.main()
