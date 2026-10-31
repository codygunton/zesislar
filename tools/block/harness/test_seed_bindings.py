"""Check shared seed references, cell deltas, containment, and refusal behavior."""
from copy import deepcopy
import ast,json,tempfile,unittest
from pathlib import Path
import scratch
from seed_bindings import compact,validate,capture_inventory,inventory,seal,clone_owned,descriptor,compact_collection,installation_path,mutable_execution
from unittest.mock import patch
from proof_bindings import check_proof_bindings
import clone_copy
HERE=Path(__file__).resolve().parent
class SeedReferences(unittest.TestCase):
 def setUp(self):
  t=tempfile.TemporaryDirectory(dir=HERE.parent);self.addCleanup(t.cleanup);self.root=Path(t.name);self.seed=self.root/'seed';self.seed.mkdir();self.owned=self.root/'owned'
  for name,text in [('artifacts/default/T/Proof.v','Lemma x : True.'),('artifacts/default/T/Proof.vo','compiled object'),('_CoqProject','-Q artifacts/default T'),('tools/wrapper.py','pinned tool'),('ordinary.txt','retained metadata')]:
   p=self.seed/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
  (self.seed/'_build').mkdir();(self.seed/'_build/default').symlink_to('../artifacts/default')
  self.tool=self.root/'external.py';self.tool.write_text('external tool');self.source_rows=[scratch.binding(p) for p in self.seed.rglob('*') if p.is_file() and not p.is_symlink()]
  seed_runtime=self.root/'SEED.json';scratch.save(seed_runtime,{'bindings':self.source_rows+[scratch.binding(self.tool)],'prepared_workspace':str(self.seed)})
  inventory=self.root/'FILES.jsonl';inventory.write_text(''.join(json.dumps({'relative':str(Path(r['path']).relative_to(self.seed)),'sha256':r['sha256']})+'\n' for r in self.source_rows))
  descriptor=self.root/'REFERENCE.json';scratch.save(descriptor,{'schema':'scratch.shared-seed-bindings.v1','seed_runtime':scratch.binding(seed_runtime),'inventory':scratch.binding(inventory),'prepared_workspace':str(self.seed),'symlinks':[{'relative':'_build/default','target':'../artifacts/default'}],'external_bindings':[scratch.binding(self.tool)]});self.descriptor=scratch.binding(descriptor)
  clone_copy.copytree(self.seed,self.owned,symlinks=True)
  self.runtime={'prepared_workspace':str(self.owned),'bindings':self.source_rows+[scratch.binding(p) for p in self.owned.rglob('*') if p.is_file() and not p.is_symlink()]+[scratch.binding(self.tool)],'job_controller':scratch.binding(self.tool),'proof_runtime':{'module_files':{'T.Proof':'artifacts/default/T/Proof.v'}},'jobs':[{'phase':'native','target':{'module':'T.Proof'},'ordered_modules':[]}], 'cache_producer_files':{'inputs':[],'implementation':[],'outputs':[]}}
 def make(self):return compact(self.runtime,self.descriptor,self.owned)
 def test_compact_preserves_owned_hash_checks_without_inventory_copy(self):
  before=len(self.runtime['bindings']);r=self.make();work=check_proof_bindings(r);self.assertLess(len(r['bindings']),before);self.assertEqual(len(r['seed_binding_reference']['deltas']),0);self.assertEqual(work['shared_seed_files_checked'],len(self.source_rows))
 def test_exact_source_delta_is_retained_and_checked(self):
  p=self.owned/'artifacts/default/T/Proof.v';p.write_text('changed bound caller');self.runtime['bindings']=[scratch.binding(p) if row['path']==str(p) else row for row in self.runtime['bindings']];r=self.make();check_proof_bindings(r);self.assertEqual(len(r['seed_binding_reference']['deltas']),1);p.write_text('unbound change')
  with self.assertRaisesRegex(ValueError,'owned seed input changed'):check_proof_bindings(r)
 def test_unchanged_source_mutation_refuses(self):
  r=self.make();(self.owned/'artifacts/default/T/Proof.v').write_text('unbound')
  with self.assertRaisesRegex(ValueError,'owned seed input changed'):check_proof_bindings(r)
 def test_object_mutation_refuses(self):
  r=self.make();(self.owned/'artifacts/default/T/Proof.vo').write_text('unbound')
  with self.assertRaisesRegex(ValueError,'owned seed input changed'):check_proof_bindings(r)
 def test_flag_mutation_refuses(self):
  r=self.make();(self.owned/'_CoqProject').write_text('different flags')
  with self.assertRaisesRegex(ValueError,'owned seed input changed'):check_proof_bindings(r)
 def test_owned_tool_mutation_refuses(self):
  r=self.make();(self.owned/'tools/wrapper.py').write_text('unbound')
  with self.assertRaisesRegex(ValueError,'owned seed input changed'):check_proof_bindings(r)
 def test_external_tool_mutation_refuses(self):
  r=self.make();self.tool.write_text('unbound')
  with self.assertRaises(ValueError):check_proof_bindings(r)
 def test_descriptor_mutation_refuses(self):
  r=self.make();Path(self.descriptor['path']).write_text('{}')
  with self.assertRaisesRegex(ValueError,'shared seed binding changed'):check_proof_bindings(r)
 def test_seed_runtime_mutation_refuses(self):
  r=self.make();(self.root/'SEED.json').write_text('{}')
  with self.assertRaisesRegex(ValueError,'shared seed binding changed'):check_proof_bindings(r)
 def test_seed_file_mutation_refuses_before_clone(self):
  r=self.make();r['prepared_workspace']=str(self.seed);r['seed_binding_reference']['workspace']=str(self.seed);(self.seed/'ordinary.txt').write_text('changed')
  with self.assertRaisesRegex(ValueError,'owned seed input changed'):check_proof_bindings(r)
 def test_manifest_mutation_refuses(self):
  r=self.make();(self.root/'FILES.jsonl').write_text('')
  with self.assertRaisesRegex(ValueError,'shared seed binding changed'):check_proof_bindings(r)
 def test_alias_escape_refuses(self):
  r=self.make();link=self.owned/'_build/default';link.unlink();link.symlink_to(self.root)
  with self.assertRaisesRegex(ValueError,'alias changed or escaped'):check_proof_bindings(r)
 def test_delta_escape_refuses(self):
  r=self.make();r['seed_binding_reference']['deltas']=[{'relative':'../outside','sha256':'0'*64}]
  with self.assertRaisesRegex(ValueError,'escapes'):check_proof_bindings(r)
 def test_reference_to_other_root_refuses(self):
  r=self.make();r['seed_binding_reference']['workspace']=str(self.seed)
  with self.assertRaisesRegex(ValueError,'another owned root'):check_proof_bindings(r)
 def test_duplicate_runtime_binding_refuses(self):
  self.runtime['bindings'].append(self.runtime['bindings'][0])
  with self.assertRaisesRegex(ValueError,'repeats a binding'):self.make()
 def test_undeclared_missing_file_refuses(self):
  (self.owned/'ordinary.txt').unlink()
  with self.assertRaisesRegex(ValueError,'undeclared seed input is absent'):self.make()
 def test_declared_native_output_absence_is_allowed(self):
  (self.owned/'artifacts/default/T/Proof.vo').unlink();r=self.make();check_proof_bindings(r);self.assertEqual(r['seed_binding_reference']['removed'],['artifacts/default/T/Proof.vo'])
 def test_compaction_is_idempotent(self):
  r=self.make();before=deepcopy(r);compact(r,self.descriptor,self.owned);self.assertEqual(r['bindings'],before['bindings']);check_proof_bindings(r)
 def test_source_and_object_deltas_survive_repeated_compaction(self):
  for name in ['artifacts/default/T/Proof.v','artifacts/default/T/Proof.vo']:
   path=self.owned/name;path.write_text('new approved '+name)
   self.runtime['bindings']=[scratch.binding(path) if r['path']==str(path) else r for r in self.runtime['bindings']]
  r=self.make();before=deepcopy(r['seed_binding_reference']);compact(r,self.descriptor,self.owned);self.assertEqual(r['seed_binding_reference'],before);check_proof_bindings(r)
  (self.owned/'artifacts/default/T/Proof.vo').write_text('unbound object mutation')
  with self.assertRaises(ValueError):check_proof_bindings(r)
 def test_flag_and_tool_deltas_survive_repeated_compaction(self):
  for name in ['_CoqProject','tools/wrapper.py']:
   path=self.owned/name;path.write_text('new approved '+name)
   self.runtime['bindings']=[scratch.binding(path) if r['path']==str(path) else r for r in self.runtime['bindings']]
  r=self.make();before=deepcopy(r['seed_binding_reference']);compact(r,self.descriptor,self.owned);self.assertEqual(r['seed_binding_reference'],before);check_proof_bindings(r)
 def test_changed_existing_delta_refuses_recompaction(self):
  path=self.owned/'artifacts/default/T/Proof.v';path.write_text('approved delta')
  self.runtime['bindings']=[scratch.binding(path) if r['path']==str(path) else r for r in self.runtime['bindings']]
  r=self.make();path.write_text('unbound delta change')
  with self.assertRaises(ValueError):compact(r,self.descriptor,self.owned)
 def second_pass_delta_mutation(self,name):
  path=self.owned/name;path.write_text('exact authorized delta')
  self.runtime['bindings']=[scratch.binding(path) if row['path']==str(path) else row for row in self.runtime['bindings']]
  runtime=self.make();compact(runtime,self.descriptor,self.owned);check_proof_bindings(runtime)
  path.write_text('unbound mutation after second pass')
  with self.assertRaises(ValueError):check_proof_bindings(runtime)
 def test_source_delta_mutation_after_second_pass_refuses(self):self.second_pass_delta_mutation('artifacts/default/T/Proof.v')
 def test_object_delta_mutation_after_second_pass_refuses(self):self.second_pass_delta_mutation('artifacts/default/T/Proof.vo')
 def test_flag_delta_mutation_after_second_pass_refuses(self):self.second_pass_delta_mutation('_CoqProject')
 def test_tool_delta_mutation_after_second_pass_refuses(self):self.second_pass_delta_mutation('tools/wrapper.py')
 def add_legacy_cache_rows(self):
  names=['.lia.cache','.nia.cache','__pycache__/runner.pyc','_build/log','_build/trace.csexp']
  manifest=self.root/'FILES.jsonl'
  with manifest.open('a') as stream:
   for name in names:
    for root in [self.seed,self.owned]:
     p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text('regenerated cache')
    stream.write(json.dumps({'relative':name,'sha256':scratch.binding(self.seed/name)['sha256']})+'\n')
    self.runtime['bindings'].append(scratch.binding(self.owned/name))
  descriptor=json.loads(Path(self.descriptor['path']).read_text());descriptor['inventory']=scratch.binding(manifest)
  Path(self.descriptor['path']).write_text(json.dumps(descriptor));self.descriptor=scratch.binding(Path(self.descriptor['path']))
  return names
 def test_cache_presence_before_capture_is_excluded(self):
  names=self.add_legacy_cache_rows();rows=[json.loads(line) for line in (self.root/'FILES.jsonl').read_text().splitlines()]
  captured=capture_inventory(rows)
  for name in names:self.assertNotIn(name,captured)
  runtime=self.make();check_proof_bindings(runtime)
  for row in runtime['bindings']:self.assertNotIn(Path(row['path']).name,{'.lia.cache','.nia.cache','runner.pyc','log','trace.csexp'})
 def test_cache_deletion_before_validation_is_allowed(self):
  names=self.add_legacy_cache_rows();runtime=self.make()
  for name in names:(self.owned/name).unlink()
  check_proof_bindings(runtime);compact(runtime,self.descriptor,self.owned)
 def test_cache_regeneration_between_phases_is_allowed(self):
  names=self.add_legacy_cache_rows();runtime=self.make();check_proof_bindings(runtime)
  for name in names:(self.owned/name).write_text('new regenerated contents')
  check_proof_bindings(runtime);compact(runtime,self.descriptor,self.owned);check_proof_bindings(runtime)
 def test_real_sources_and_objects_refuse_after_cache_regeneration(self):
  names=self.add_legacy_cache_rows();runtime=self.make()
  for name in names:(self.owned/name).write_text('new regenerated contents')
  for name in ['artifacts/default/T/Proof.v','artifacts/default/T/Proof.vo']:
   p=self.owned/name;original=p.read_bytes();p.write_text('unauthorized real input')
   with self.assertRaises(ValueError):check_proof_bindings(runtime)
   p.write_bytes(original)
 def test_generated_semantics_and_trace_named_sources_stay_bound(self):
  rows=[{'relative':name,'sha256':'a'*64} for name in ['generated/isla-traces/trace.v','generated/isla-traces/trace.vo','trace.csexp','log']]
  self.assertEqual(len(capture_inventory(rows)),4)
 def install_stage_tool_delta(self):
  # Execute the actual staging branch before the final compact call.
  tree=ast.parse((HERE/'code/entry_chain_run.py').read_text())
  stage=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='stage_job')
  statements=[n for n in stage.body if isinstance(n,ast.If) and "runtime['bindings'].extend((row['owned'] for row in transition['copies']))" in ast.unparse(n)]
  self.assertEqual(len(statements),1)
  source=self.root/'successor-wrapper.py';source.write_text('exact released tool')
  owned=self.owned/'tools/wrapper.py';clone_copy.copy2(source,owned)
  transition={'copies':[{'source':scratch.binding(source),'owned':scratch.binding(owned),'distinct_inode':True}]}
  self.runtime['bindings']=[row for row in self.runtime['bindings'] if row['path']!=str(owned)]
  namespace={'sealed':True,'config':{},'runtime':self.runtime,'transition':transition}
  exec(compile(ast.fix_missing_locations(ast.Module(body=statements,type_ignores=[])),'<stage-tool-delta>','exec'),namespace)
  return owned
 def test_actual_stage_transition_is_an_explicit_tool_delta(self):
  owned=self.install_stage_tool_delta();runtime=self.make();check_proof_bindings(runtime)
  self.assertIn({'relative':'tools/wrapper.py','sha256':scratch.digest(owned)},runtime['seed_binding_reference']['deltas'])
 def test_staged_transition_wrong_tool_refuses(self):
  owned=self.install_stage_tool_delta();runtime=self.make();owned.write_text('unlisted replacement')
  with self.assertRaises(ValueError):check_proof_bindings(runtime)
 def test_unknown_external_proof_inputs_under_BASE_stay_explicit(self):
  for suffix in ['.v','.vo','.vos','.vok','.glob','.cmxs','.cma','.cmxa','.so']:
   path=self.root/('external-proof'+suffix);path.write_text('exact external proof input')
   row=scratch.binding(path);self.runtime['bindings'].append(row)
  runtime=self.make();check_proof_bindings(runtime)
  for suffix in ['.v','.vo','.vos','.vok','.glob','.cmxs','.cma','.cmxa','.so']:
   path=self.root/('external-proof'+suffix);self.assertIn(scratch.binding(path),runtime['bindings'])
 def test_unknown_external_source_mutation_refuses(self):
  path=self.root/'external-proof.v';path.write_text('bound proof source');self.runtime['bindings'].append(scratch.binding(path))
  runtime=self.make();path.write_text('unbound proof source')
  with self.assertRaises(ValueError):check_proof_bindings(runtime)
 def test_unknown_external_object_mutation_refuses(self):
  path=self.root/'external-proof.vo';path.write_text('bound proof object');self.runtime['bindings'].append(scratch.binding(path))
  runtime=self.make();path.write_text('unbound proof object')
  with self.assertRaises(ValueError):check_proof_bindings(runtime)
 def test_conflicting_inherited_hash_refuses(self):
  path=self.seed/'artifacts/default/T/Proof.vo'
  self.runtime['bindings']=[dict(row,sha256='0'*64) if row['path']==str(path) else row for row in self.runtime['bindings']]
  with self.assertRaisesRegex(ValueError,'inherited seed binding has another hash'):self.make()
 def test_exact_inherited_path_and_hash_use_bound_seed_provenance(self):
  row=scratch.binding(self.seed/'artifacts/default/T/Proof.vo');runtime=self.make()
  self.assertNotIn(row,runtime['bindings']);check_proof_bindings(runtime)
 def sealed(self):
  seed_path=self.root/'SEED.json';runtime=json.loads(seed_path.read_text());runtime['physical_flags']=[]
  seed_path.write_text(json.dumps(runtime));definition=json.loads(Path(self.descriptor['path']).read_text())
  definition['seed_runtime']=scratch.binding(seed_path);Path(self.descriptor['path']).write_text(json.dumps(definition));self.descriptor=scratch.binding(Path(self.descriptor['path']))
  with patch('rocq_mcp.server._parse_project_flags',return_value=[]):
   self.descriptor=seal(self.descriptor,self.root/'sealed')
  return descriptor(self.descriptor)
 def test_seal_creates_read_only_distinct_inode_files(self):
  value=self.sealed();source=Path(value['prepared_workspace'])/'artifacts/default/T/Proof.vo'
  self.assertEqual(source.stat().st_mode&0o222,0);self.assertNotEqual(source.stat().st_ino,(self.seed/'artifacts/default/T/Proof.vo').stat().st_ino)
 def test_sealed_checks_do_not_read_seed_files_again(self):
  self.sealed();self.runtime['bindings']=[row for row in self.runtime['bindings'] if not Path(row['path']).is_relative_to(self.owned)]
  runtime=self.make()
  from seed_bindings import digest
  def guarded(path):
   self.assertFalse(Path(path).is_relative_to(self.owned));return digest(path)
  with patch('seed_bindings.digest',side_effect=guarded):validate(runtime['seed_binding_reference'],self.owned)
 def test_sealed_delta_mutation_still_refuses(self):
  self.sealed();path=self.owned/'artifacts/default/T/Proof.v';path.write_text('approved caller')
  self.runtime['bindings']=[scratch.binding(path) if row['path']==str(path) else row for row in self.runtime['bindings']]
  runtime=self.make();path.write_text('unbound caller')
  with self.assertRaises(ValueError):check_proof_bindings(runtime)
 def test_sealed_equal_hash_cell_flags_stay_explicit(self):
  self.sealed();runtime=self.make();self.assertIn('_CoqProject',{row['relative'] for row in runtime['seed_binding_reference']['deltas']})
  (self.owned/'_CoqProject').write_text('changed flags')
  with self.assertRaises(ValueError):check_proof_bindings(runtime)
 def test_sealed_clone_uses_no_file_content_hashes(self):
  value=self.sealed();destination=self.root/'trusted-copy'
  from seed_bindings import digest
  def guarded(path):
   self.assertFalse(Path(path).is_relative_to(Path(value['prepared_workspace'])));return digest(path)
  with patch('seed_bindings.digest',side_effect=guarded):clone_owned(self.descriptor,destination)
  self.assertEqual((destination/'artifacts/default/T/Proof.vo').read_bytes(),(self.seed/'artifacts/default/T/Proof.vo').read_bytes())
 def test_sealed_clone_refuses_changed_frozen_source_identity(self):
  value=self.sealed();path=Path(value['prepared_workspace'])/'artifacts/default/T/Proof.vo';path.chmod(0o644)
  with self.assertRaisesRegex(ValueError,'frozen identity'):clone_owned(self.descriptor,self.root/'refused-copy')
 def test_sealed_collection_replaces_only_exact_shared_rows(self):
  self.sealed();runtime=self.make();reference=runtime['seed_binding_reference'];root=str(self.owned)
  spec={'roots':[{'role':'system','path':'/'}],'files':[dict(scratch.binding(self.owned/'ordinary.txt'),id='shared',kind='configuration',root_role='system'),dict(scratch.binding(self.owned/'artifacts/default/T/Proof.v'),id='proof',kind='source',root_role='system')],
   'recipe':{'proof':'proof','dependencies':[{'id':'proof','requires':['shared']},{'id':'shared','requires':[]}],
    'producers':[{'implementation':[],'inputs':['shared'],'outputs':['proof']}],'toolchain':{'compiler':['shared']},'backend':{'files':['shared']}}}
  # Only actual cell files enter the delta list. The synthetic shared row is absent there.
  reference['deltas']=[row for row in reference['deltas'] if row['relative']!='ordinary.txt']
  result=compact_collection(spec,reference);ids={row['id'] for row in result['files']}
  self.assertEqual(ids,{'proof','sealed-shared-seed'});self.assertEqual(result['recipe']['dependencies'][0]['requires'],['sealed-shared-seed'])
 def test_unsealed_reference_cannot_enable_fast_collection(self):
  runtime=self.make()
  with self.assertRaisesRegex(ValueError,'sealed seed'):compact_collection({},runtime['seed_binding_reference'])
 def extra_external(self,path):
  path.parent.mkdir(parents=True,exist_ok=True);path.write_text('frozen source')
  value=json.loads(Path(self.descriptor['path']).read_text());value['external_bindings'].append(scratch.binding(path))
  Path(self.descriptor['path']).write_text(json.dumps(value));self.descriptor=scratch.binding(Path(self.descriptor['path']))
 def test_sealed_project_external_rows_stay_explicit(self):
  path=self.root/'project-helper.v';self.extra_external(path);self.sealed();runtime=self.make()
  self.assertIn(scratch.binding(path),runtime['bindings']);path.write_text('changed project helper')
  with self.assertRaises(ValueError):check_proof_bindings(runtime)
 def test_frozen_installation_scope_excludes_project_paths(self):
  self.assertFalse(installation_path(self.root/'tool.py'));self.assertTrue(installation_path('/usr/bin/python3'))
 def test_mutable_MCP_and_pytanque_sources_stay_explicit(self):
  paths=[self.root/'site-packages/rocq_mcp/server.py',self.root/'site-packages/pytanque/client.py']
  for path in paths:self.extra_external(path)
  self.sealed()
  with patch('seed_bindings.installation_path',return_value=True):runtime=self.make()
  for path in paths:self.assertIn(scratch.binding(path),runtime['bindings'])
  paths[1].write_text('changed execution source')
  with self.assertRaises(ValueError):check_proof_bindings(runtime)
 def test_conflicting_sealed_installation_hash_refuses(self):
  self.sealed();self.runtime['bindings']=[dict(row,sha256='0'*64) if row['path']==str(self.tool) else row for row in self.runtime['bindings']]
  with patch('seed_bindings.installation_path',return_value=True):
   with self.assertRaisesRegex(ValueError,'sealed external binding has another hash'):self.make()
 def test_sealed_recipe_refuses_unlisted_cell_source_hash(self):
  self.sealed();runtime=self.make();reference=runtime['seed_binding_reference'];reference['deltas']=[]
  spec={'roots':[{'role':'system','path':'/'}],'files':[dict(scratch.binding(self.owned/'ordinary.txt'),sha256='0'*64,id='shared',kind='source',root_role='system')],'recipe':{'proof':'shared'}}
  with self.assertRaisesRegex(ValueError,'unmodified sealed cell input'):compact_collection(spec,reference)
 def relay_launcher(self,argv):
  tree=ast.parse((HERE/'code/entry_chain_run.py').read_text());stage=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='stage_job')
  statements=[n for n in stage.body if isinstance(n,ast.If) and "runtime['mcp_argv'] = launcher" in ast.unparse(n)]
  self.assertEqual(len(statements),1);runtime={'mcp_argv':argv};namespace={'runtime':runtime,'sealed':True,'workspace':self.owned,'out':self.root/'job'}
  exec(compile(ast.fix_missing_locations(ast.Module(body=statements,type_ignores=[])),'<actual-relay-output>','exec'),namespace)
  return runtime['mcp_argv']
 def test_sealed_relay_receipt_uses_owned_job_output(self):
  argv=['python','relay.py','--receipt','{workspace}/STDIN-RELAY.json','--','mcp.py']
  updated=self.relay_launcher(argv);self.assertEqual(updated[3],str(self.root/'job/STDIN-RELAY.json'));self.assertEqual(argv[3],'{workspace}/STDIN-RELAY.json')
 def test_sealed_relay_unknown_output_refuses(self):
  with self.assertRaisesRegex(ValueError,'exact relay output'):self.relay_launcher(['python','--receipt','/unbound/output.json'])
 def test_sealed_relay_repeated_output_refuses(self):
  with self.assertRaisesRegex(ValueError,'exact relay output'):self.relay_launcher(['python','--receipt','{workspace}/STDIN-RELAY.json','--receipt','{workspace}/STDIN-RELAY.json'])
 def control_fixture(self):
  manifest=self.root/'FILES.jsonl'
  for module in ['Control','Unrelated']:
   for suffix in ['.v','.vo']:
    name='artifacts/default/T/'+module+suffix
    for root in [self.seed,self.owned]:(root/name).write_text('fixed '+module+suffix)
    with manifest.open('a') as stream:stream.write(json.dumps({'relative':name,'sha256':scratch.digest(self.seed/name)})+'\n')
   self.runtime['proof_runtime']['module_files']['T.'+module]='artifacts/default/T/'+module+'.v'
  value=json.loads(Path(self.descriptor['path']).read_text());value['inventory']=scratch.binding(manifest)
  Path(self.descriptor['path']).write_text(json.dumps(value));self.descriptor=scratch.binding(Path(self.descriptor['path']))
  self.runtime['bindings'].append(scratch.binding(self.owned/'artifacts/default/T/Control.v'))
  self.runtime['control_session']={'module':'T.Control','steps':[]}
 def test_exact_interactive_control_object_may_be_absent(self):
  self.control_fixture();(self.owned/'artifacts/default/T/Control.vo').unlink();runtime=self.make();check_proof_bindings(runtime)
  self.assertEqual(runtime['seed_binding_reference']['removed'],['artifacts/default/T/Control.vo'])
 def test_interactive_control_does_not_allow_unrelated_missing_objects(self):
  self.control_fixture();(self.owned/'artifacts/default/T/Unrelated.vo').unlink()
  with self.assertRaisesRegex(ValueError,'undeclared seed input is absent'):self.make()
 def test_interactive_control_source_must_be_explicit(self):
  self.control_fixture();self.runtime['bindings']=[row for row in self.runtime['bindings'] if row['path']!=str(self.owned/'artifacts/default/T/Control.v')]
  with self.assertRaisesRegex(ValueError,'source lacks an explicit binding'):self.make()
 def test_interactive_control_module_must_exist(self):
  self.control_fixture();self.runtime['control_session']['module']='T.Unknown'
  with self.assertRaisesRegex(ValueError,'no source mapping'):self.make()
 def test_sealed_focused_profile_does_not_require_native_authority(self):
  path=self.root/'FOCUSED.json';path.write_text(json.dumps({'schema':'scratch.admission-profile.v1','kind':'focused_check','sources':[]}))
  self.assertIsNone(scratch.sealed_rules_prefix(scratch.binding(path),True,True))
 def test_sealed_focused_profile_cannot_classify_native_execution(self):
  path=self.root/'FOCUSED.json';path.write_text(json.dumps({'schema':'scratch.admission-profile.v1','kind':'focused_check','sources':[]}))
  with self.assertRaisesRegex(ValueError,'declaration-only'):scratch.sealed_rules_prefix(scratch.binding(path),False,False)
 def test_sealed_unknown_profile_still_refuses(self):
  path=self.root/'UNKNOWN.json';path.write_text(json.dumps({'schema':'scratch.admission-profile.v1','kind':'unknown','sources':[]}))
  with self.assertRaisesRegex(ValueError,'exact native authority or focused'):scratch.sealed_rules_prefix(scratch.binding(path),True,True)
if __name__=='__main__':unittest.main()
