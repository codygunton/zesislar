"""Check the typed temporary directory without a proof or admission claim."""
from copy import deepcopy
import json,os,unittest
from pathlib import Path
from unittest.mock import patch
import scratch
import stage1_runtime as stage
import collector
import proof_cache_key as key
import entry_chain_provider as provider
import test_runtime_exclusions as fixtures


class TypedTmpdir(fixtures.TwoPhase):
 def setUp(self):
  with patch('tempfile.tempdir','/home/cody/.cache/zesislar/shared-harness-tests'):
   super().setUp()
  self.out=self.work.parent/'outputs';self.out.mkdir()
  self.spec['roots'].append({'role':'attempt_outputs','path':str(self.out)})
  self.declared=self.spec['roots']
  self.spec['recipe']['configuration']['environment']['TMPDIR']=stage.owned_tmpdir(self.out,self.declared)

 def test_owned_path_and_permissions(self):
  value=self.spec['recipe']['configuration']['environment']['TMPDIR']
  self.assertEqual(value,{'kind':'path','value':str(self.out/'tmp'),'root_role':'attempt_outputs'})
  self.assertEqual((self.out/'tmp').stat().st_mode&0o777,0o700)
  self.assertEqual(stage.owned_tmpdir(self.out,self.declared),value)

 def test_both_keys_and_actual_environment(self):
  first=self.collect();before=key.build_keys(first['input'])
  (self.out/'tmp'/'generated-output.tmp').write_text('temporary output')
  second=self.collect(first['input']);after=key.build_keys(second['input'])
  self.assertEqual(before['recipe_key'],after['recipe_key'])
  self.assertEqual(before['attempt_key'],after['attempt_key'])
  self.assertEqual(second['execution_environment']['TMPDIR'],str(self.out/'tmp'))
  normalized=key.build_keys(second['input'])
  self.assertEqual(normalized['recipe']['configuration']['environment']['TMPDIR']['root_role'],'attempt_outputs')

 def test_tmpdir_change_changes_both_keys(self):
  first=self.collect();changed=deepcopy(first['input'])
  other=self.out/'other';other.mkdir()
  changed['recipe']['configuration']['environment']['TMPDIR']['value']=str(other)
  a,b=key.build_keys(first['input']),key.build_keys(changed)
  self.assertNotEqual(a['recipe_key'],b['recipe_key'])
  self.assertNotEqual(a['attempt_key'],b['attempt_key'])

 def test_symlink_refuses_before_collection(self):
  (self.out/'tmp').rmdir();(self.out/'tmp').symlink_to(self.work)
  with self.assertRaisesRegex(ValueError,'symbolic link'):stage.owned_tmpdir(self.out,self.declared)

 def test_wrong_root_role_refuses(self):
  with self.assertRaisesRegex(ValueError,'owned /home output'):
   stage.owned_tmpdir(self.out,[dict(row,role='unowned') if row['role']=='attempt_outputs' else row for row in self.declared])

 def test_wrong_owner_refuses(self):
  with patch.object(stage.os,'getuid',return_value=os.getuid()+1):
   with self.assertRaisesRegex(ValueError,'owned /home output'):stage.owned_tmpdir(self.out,self.declared)

 def test_native_provider_uses_bound_tmpdir(self):
  result=self.collect();environment=dict(result['execution_environment'])
  runtime_file=self.out/'RUNTIME.json';runtime_file.write_text('{}\n')
  environment.update(ENTRY_CHAIN_RUNTIME_JSON=str(runtime_file),ENTRY_CHAIN_RUNTIME_SHA256=scratch.digest(runtime_file),ZESU_AGGREGATE_SLICE='owned-test.slice')
  prospective=self.out/'prospective';prospective.mkdir()
  actual=prospective/'ACTUAL-ENVIRONMENT.json';scratch.save(actual,environment)
  phase=prospective/'PHASE2.json';scratch.save(phase,result)
  equality=prospective/'KEY-EQUALITY.json';scratch.save(equality,{'equal':True,'proof_calls_between_phases':0})
  launch=prospective/'MCP-LAUNCH.json';scratch.save(launch,{'test_data':True})
  scratch.save(prospective/'ACTUAL-BOUNDARY.json',{'environment':scratch.binding(actual),'phase2':scratch.binding(phase),'key_equality':scratch.binding(equality),'mcp_launch':scratch.binding(launch)})
  runtime={'phase':'native','prospective_directory':str(prospective),'runtime_path':str(runtime_file),'runtime_sha256':scratch.digest(runtime_file)}
  with patch.dict(os.environ,{'TMPDIR':'/tmp','ZESU_AGGREGATE_SLICE':'owned-test.slice'}):
   selected=provider.proof_environment(runtime,self.work,self.out,inherited={'TMPDIR':'/tmp'})
  self.assertEqual(selected['TMPDIR'],str(self.out/'tmp'))
  actual.write_text(json.dumps(dict(environment,TMPDIR='/tmp')))
  with self.assertRaises(ValueError):provider.proof_environment(runtime,self.work,self.out)


if __name__=='__main__':unittest.main()
