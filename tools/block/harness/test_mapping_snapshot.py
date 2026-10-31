"""Check seed-bound resolver reuse and exact refusal conditions."""
from copy import deepcopy
import json,os,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
HERE=Path(__file__).resolve().parent;sys.path[:0]=[str(HERE/'code'),str(HERE)]
import scratch,clone_copy,mapping_snapshot,check_data_only_lemmas
from installed_mappings import InstalledMappings
class SnapshotControls(unittest.TestCase):
 def setUp(self):
  t=tempfile.TemporaryDirectory(dir=HERE.parent);self.addCleanup(t.cleanup);self.root=Path(t.name);self.work=self.root/'seed';self.work.mkdir();self.seed=self.root/'RUNTIME.json';self.seed.write_text('{}')
  for name,text in [('Core',''),('Rules','Require Import T.Core.\n'),('Caller','Require Import T.Rules.\n')]:
   (self.work/(name+'.v')).write_text(text);(self.work/(name+'.vo')).write_bytes(('object:'+name).encode())
  self.tool=self.root/'coqdep';self.tool.write_text('pinned resolver')
  self.initial=self.instance(self.work);self.initial.scan_sources()
  entry=next(r for r in self.initial.entries if r['canonical']=='T.Core')
  requests=[r['statement'] for r in self.initial._find_request('T.Core')]
  self.initial.resolutions['T.Core']={'source':entry['source'],'object':entry['object'],'canonical':entry['canonical'],'requests':requests}
  parsers=[scratch.binding(HERE/'code/installed_mappings.py'),scratch.binding(Path(check_data_only_lemmas.__file__)),scratch.binding(HERE/'code/mapping_snapshot.py')]
  self.snapshot=mapping_snapshot.export(self.initial,scratch.binding(self.seed),self.work,parsers)
  self.path=self.root/'SNAPSHOT.json';self.save();self.other=self.root/'owned';clone_copy.copytree(self.work,self.other)
 def save(self):self.path.write_text(json.dumps(self.snapshot));self.binding=scratch.binding(self.path)
 def instance(self,work):return InstalledMappings(['-Q',str(work),'T'],coqdep=self.tool)
 def load(self,changes=None):
  obj=self.instance(self.other);mapping_snapshot.load(obj,self.binding,self.other,changes or {});return obj
 def test_cached_answer_uses_zero_coqdep_calls(self):
  obj=self.load()
  with patch.object(obj,'_query',side_effect=AssertionError('unexpected query')):
   self.assertEqual(obj.resolve('T.Core'),self.other/'Core.v')
  self.assertEqual(obj.seed_snapshot['hits'],1)
 def test_unchanged_sources_use_zero_parser_calls(self):
  with patch('installed_mappings.rocq_commands',side_effect=AssertionError('unexpected parse')):obj=self.load()
  self.assertEqual(obj.seed_snapshot['parsed_changed_sources'],0)
 def test_source_change_refuses(self):
  (self.other/'Core.v').write_text('changed')
  with self.assertRaisesRegex(ValueError,'source changed'):self.load()
 def test_object_change_refuses(self):
  (self.other/'Core.vo').write_bytes(b'changed')
  with self.assertRaisesRegex(ValueError,'object changed'):self.load()
 def test_added_object_refuses(self):
  (self.other/'Added.vo').write_bytes(b'new')
  with self.assertRaisesRegex(ValueError,'inventory changed'):self.load()
 def test_tool_change_refuses(self):
  self.tool.write_text('changed resolver')
  with self.assertRaisesRegex(ValueError,'another coqdep'):self.load()
 def test_flags_change_refuses(self):
  obj=InstalledMappings(['-R',str(self.other),'T'],coqdep=self.tool)
  with self.assertRaisesRegex(ValueError,'load paths differ'):mapping_snapshot.load(obj,self.binding,self.other,{})
 def test_dependency_context_change_requires_fresh_query(self):
  self.snapshot['resolutions']['T.Core']['contexts'][0][0]='changed-context';self.save()
  obj=self.load()
  expected=next(row for row in obj.entries if row['canonical']=='T.Core')
  with patch.object(obj,'_query',return_value=(expected,obj._find_request('T.Core')[0])) as query:
   self.assertEqual(obj.resolve('T.Core'),self.other/'Core.v')
  self.assertEqual(query.call_count,1)
  self.assertEqual(obj.seed_snapshot['misses'],1)
 def source_snapshot(self):
  origin=self.work/'Rules.v'
  expected=next(row for row in self.initial.entries if row['canonical']=='T.Core')
  with patch.object(self.initial,'_query',return_value=(expected,self.initial._find_request('T.Core',origin)[0])):
   self.initial.resolve('T.Core',origin=origin)
  self.snapshot=mapping_snapshot.export(self.initial,scratch.binding(self.seed),self.work,self.snapshot['parsers']);self.save()
 def test_source_bound_snapshot_reuses_the_exact_origin(self):
  self.source_snapshot();obj=self.load();origin=self.other/'Rules.v'
  with patch.object(obj,'_query',side_effect=AssertionError('unexpected query')):
   self.assertEqual(obj.resolve('T.Core',origin=origin),self.other/'Core.v')
  self.assertEqual(obj.seed_snapshot['hits'],1)
  self.assertEqual(next(iter(obj.context_resolutions))[1],str(origin))
 def test_source_bound_snapshot_refuses_changed_origin_before_hit(self):
  self.source_snapshot();obj=self.load();origin=self.other/'Rules.v'
  origin.write_text(origin.read_text()+'\n')
  with patch.object(obj,'_query',side_effect=AssertionError('unexpected query')):
   with self.assertRaisesRegex(ValueError,'request source changed'):obj.resolve('T.Core',origin=origin)
  self.assertEqual(obj.seed_snapshot['hits'],0)
 def test_snapshot_change_refuses(self):
  self.path.write_text(self.path.read_text()+' ')
  with self.assertRaisesRegex(ValueError,'binding changed'):self.load()
 def test_seed_change_refuses(self):
  self.seed.write_text('{"changed":true}')
  with self.assertRaisesRegex(ValueError,'binding changed'):self.load()
 def test_parser_identity_change_refuses(self):
  self.snapshot['parsers'][0]['sha256']='0'*64;self.save()
  with self.assertRaisesRegex(ValueError,'parser identity'):self.load()
 def test_exact_rules_change_parses_only_rules(self):
  path=self.other/'Rules.v';path.write_text('Require Import T.Core.\nRequire Export T.Core.\n');obj=self.other/'Rules.vo';obj.write_bytes(b'accepted changed Rules object')
  loaded=self.load({str(path):{'source_sha256':mapping_snapshot.digest(path),'object_sha256':mapping_snapshot.digest(obj)}})
  self.assertEqual(loaded.seed_snapshot['parsed_changed_sources'],1)
  self.assertEqual(len(loaded.requests['T.Core']),2)
  expected=next(r for r in loaded.entries if r['canonical']=='T.Core')
  with patch.object(loaded,'_query',side_effect=lambda module,request:(expected,request)) as query:loaded.resolve('T.Core')
  self.assertEqual(query.call_count,2)
 def test_wrong_rules_object_refuses(self):
  path=self.other/'Rules.v';path.write_text('changed')
  with self.assertRaisesRegex(ValueError,'Rules object'):self.load({str(path):{'source_sha256':mapping_snapshot.digest(path),'object_sha256':'0'*64}})
 def test_expected_removed_caller_is_allowed(self):
  path=self.other/'Caller.v';path.write_text('Require Import T.Core.\n');path.with_suffix('.vo').unlink()
  obj=self.load({str(path):{'source_sha256':mapping_snapshot.digest(path)}})
  self.assertTrue(obj.scanned_sources)
if __name__=='__main__':unittest.main()
