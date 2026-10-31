"""Focused controls. These controls run no native proof or claim."""
from pathlib import Path
import hashlib,json,sys,tempfile,unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parent))
import scratch
import _test_support
from scratch_limits import stop_reason,exact_aggregate
W=Path('/home/cody/zesislar/.worktrees/infra-a-check-entry-chain-3e40');BASE=W/'_build/check-entry-stage1-passfix-ten-runtime-v2'
ENTRY=Path(json.loads((BASE/'release-v1/RUNTIME.json').read_text())['prepared_workspace'])/'artifacts/default/ZesuSsz/Generated/DecodeItem/Entries.v'
class Controls(unittest.TestCase):
 def test_valid_block(self):
  with tempfile.TemporaryDirectory() as t:self.assertEqual(_test_support.arguments(['0x800d6a64',str(ENTRY),'--output',t+'/out']).block,'800d6a64')
 def test_unknown_block(self):
  with self.assertRaises(SystemExit):_test_support.arguments(['800d0000',str(ENTRY)])
 def test_missing_entry(self):
  with self.assertRaises(SystemExit):_test_support.arguments(['800d6a64','/missing.v'])
 def test_missing_rules(self):
  with self.assertRaises(SystemExit):_test_support.arguments(['800d6a64',str(ENTRY),'--rules','/missing.v'])
 def test_output_source_refused(self):
  with self.assertRaises(SystemExit):_test_support.arguments(['800d6a64',str(ENTRY),'--output',str(W/'tools/new-result')])
 def test_base_source_output_refused(self):
  with self.assertRaises(SystemExit):_test_support.arguments(['800d6a64',str(ENTRY),'--output','/home/cody/zesislar/ZesuSsz/new-result'])
 def test_peer_source_output_refused(self):
  with self.assertRaises(SystemExit):_test_support.arguments(['800d6a64',str(ENTRY),'--output','/home/cody/zesislar/.worktrees/other/tools/new-result'])
 def test_duplicate_binding_refused(self):
  row=scratch.binding(ENTRY)
  with self.assertRaises(ValueError):scratch.strict_bindings([row,row])
 def test_conflicting_binding_refused(self):
  row=scratch.binding(ENTRY)
  with self.assertRaises(ValueError):scratch.combined_bindings([row,dict(row,sha256='0'*64)])
 def test_changed_source_binding_refused(self):
  with self.assertRaises(ValueError):scratch.strict_bindings([dict(scratch.binding(ENTRY),sha256='0'*64)])
 def test_existing_entry_compilation_receipt(self):
  p=BASE/'jobs/prerequisites/native/dependency-ZesuSsz.Generated.DecodeItem.Entries.json';r=json.loads(p.read_text());self.assertEqual(scratch.digest(ENTRY),r['source_sha256']);self.assertEqual(scratch.digest(r['object']),r['object_sha256']);self.assertTrue(r['result']['success'])
 def test_real_residual_schema(self):
  out=BASE/'jobs/800d69d8';r=json.loads((out/'RESULT.json').read_text());v=scratch.summarize(r,out);self.assertEqual(v['status'],'open');self.assertEqual(v['group_counts']['active'],9);self.assertEqual(v['complete_state']['state_source'],'successful_command_returned_state')
 def test_precall_is_not_open_residual(self):
  out=BASE/'jobs/800d69d8';r=json.loads((out/'RESULT.json').read_text());r['complete_state']['state_source']='retained_pre_call_state'
  with self.assertRaises(ValueError):scratch.summarize(r,out)
 def test_real_closed_evidence(self):
  out=W/'_build/check-entry-captured-renderer-v3-cache-runtime-v2/jobs/800d697c';r=json.loads((out/'RESULT.json').read_text());v=scratch.summarize(r,out);self.assertEqual(v['status'],'closed')
 def test_closed_without_kernel_receipt_refused(self):
  out=W/'_build/check-entry-captured-renderer-v3-cache-runtime-v2/jobs/800d697c';r=json.loads((out/'RESULT.json').read_text());r['native_receipts']={}
  with self.assertRaises(ValueError):scratch.summarize(r,out)
 def test_infrastructure_is_distinct(self):
  with tempfile.TemporaryDirectory() as t:
   p=Path(t);(p/'RESULT.json').write_text('{}');self.assertEqual(scratch.summarize({'status':'infrastructure_failed'},p)['status'],'infrastructure_failed')
 def test_CPU_stop(self):self.assertEqual(stop_reason(7200,1,2,origin_cpu=0),'external_CPU_stop')
 def test_prior_CPU_counts(self):self.assertEqual(stop_reason(7300,1,2,100,origin_cpu=0),'external_CPU_stop')
 def test_memory_stop(self):self.assertEqual(stop_reason(1,68719476736,2),'external_memory_stop')
 def test_memory_exact_twice_permitted(self):self.assertIsNone(stop_reason(1,4,2))
 def test_before_stop_permitted(self):self.assertIsNone(stop_reason(7199,1,2))
 def test_invalid_aggregate_refused(self):
  with self.assertRaises(ValueError):exact_aggregate({'aggregate_path':'/tmp/other.slice'})
 def test_unchanged_header_retains_canonical(self):
  edges=[{'from':'A','to':'Coq.Lists.List'}];text='From Coq Require Import List.';self.assertEqual(scratch.canonical_edges('A',text,text,edges,{}),edges)
 def test_namespace_import_does_not_load_library(self):
  self.assertEqual(scratch.canonical_edges('A','Import ListNotations.',None,[],{}),[])
 def test_require_import_still_requires_mapping(self):
  with self.assertRaises(ValueError):scratch.canonical_edges('A','Require Import ListNotations.',None,[],{})
 def test_unknown_import_refused(self):
  with self.assertRaises(ValueError):scratch.canonical_edges('A','Require Import Unbound.Module.',None,[],{})
 def test_relative_projects(self):
  with tempfile.TemporaryDirectory() as t:
   p=Path(t);(p/'owned').mkdir();old=Path('/tmp/old-owned');line='-Q '+str(old/'owned')+' Mine\n'
   for n in ['_CoqProject','_RocqProject']:(p/n).write_text(line)
   scratch.relative_projects(p,old)
   for n in ['_CoqProject','_RocqProject']:self.assertEqual((p/n).read_text(),'-Q owned Mine\n')
if __name__=='__main__':unittest.main()
