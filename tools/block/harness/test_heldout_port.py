"""Check blind reporting and the exact executable subset without native search."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE),str(HERE.parent),str(HERE.parents[1])]
import heldout_reporting as H
import memory_policy as P
import port_native_policy as N
from scratch_statement import source_statement


class HeldoutPortTests(unittest.TestCase):
 def test_profile_booking_option_cannot_change_blind_policy(self):
  self.profile['memory_booking']='full_physical_fence'
  with self.assertRaisesRegex(ValueError,'cannot change a blind PORT policy'):
   P.production_port_authority(self.profile)

 def setUp(self):
  temporary=tempfile.TemporaryDirectory();self.addCleanup(temporary.cleanup)
  self.root=Path(temporary.name)
  self.authority=json.loads((HERE/'policies/PORT-HELDOUT-RUN2-AUTHORITY.json').read_bytes())
  self.rows=[];self.targets=[];inventory=[];cases=[]
  for i,original in enumerate(self.authority['inventory']):
   key=original['block'];pc=original['pc'];statement='Lemma DesignedBoundary_fixture : True.\n'
   caller=None;module='Fixture.Native'+str(i)
   if i<18:
    path=self.root/('Caller'+str(i)+'.v')
    path.write_text('Require Import ZesuSsz.Automation.All.\n'+statement+'Proof.\n  zesu_block.\nQed.\n')
    caller=self.binding(path)
    statement=source_statement(path,'zesu_block.')['statement']
   statement_hash=hashlib.sha256(statement.encode()).hexdigest()
   frozen=dict(case_id=key,pc=hex(pc),native_tactic='zesu_block.',caller=caller,
               statement_sha256=statement_hash,score_group=original['score_group'])
   if i<18:
    frozen['caller_module']=module
    self.targets.append(dict(casekey=key,native_job_key=format(pc,'x'),pc=hex(pc),
                             module=module,path=caller['path'],hash=caller['sha256'],
                             statementhash=statement_hash))
    cases.append(dict(block=format(pc,'x'),pc=pc,module=module,source=caller,
                      statement_sha256=statement_hash))
   else:frozen['native_caller_transport_pending']=True
   self.rows.append(dict(case_id=key,frozen_case=frozen,statement_sha256=statement_hash,
                         ordered_edges_sha256=original['ordered_edges_sha256']))
   inventory.append(dict(original,statement_sha256=statement_hash))
  frozen=self.save('FROZEN.json',{})
  evidence=self.save('DECLARATIONS.json',{})
  self.authority.update(cases=cases,inventory=inventory,frozen_manifest=frozen,
      declaration_evidence=evidence,
      case_rebind=self.save('REBIND.json',dict(frozen_manifest=frozen,cases=self.rows)),
      eql18_targets=self.save('TARGETS.json',dict(frozen_CASES=frozen,cases=self.targets,
                                                declaration_evidence=evidence)),
      source_packet=self.save('SOURCE.json',{}),completed_common_ready=self.save('READY.json',{}))
  sources=[]
  for name in ['All','Hooks','Finish']:
   path=self.root/(name+'.v');path.write_text('(* Generic source fixture. *)\n')
   sources.append(dict(self.binding(path),module='ZesuSsz.Automation.'+name))
  self.authority['production_sources']=sources
  self.authority_path=self.root/'AUTHORITY.json'
  self.profile={'schema':'scratch.admission-profile.v1','kind':P.PORT_KIND,
                'authority':self.save_authority(),'memory_route':'measured_native'}
  self.profile_path=self.root/'PROFILE.json'

 def binding(self,path):
  return dict(path=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest())

 def save(self,name,value):
  path=self.root/name;path.write_text(json.dumps(value));return self.binding(path)

 def save_authority(self):
  binding=self.save('AUTHORITY.json',self.authority)
  if hasattr(self,'profile'):self.profile['authority']=binding
  self.enterContext(patch.object(P,getattr(self,'authority_constant','PORT_HELDOUT_AUTHORITY'),binding))
  return binding

 def add_raw_transports(self):
  targets=[]
  for i,row in enumerate(self.rows[18:]):
   source=row['frozen_case'];source['CFG_successors']=[dict(pc=hex(4096+j)) for j in range(2 if i<43 else 1)]
   path=self.root/('Raw'+str(i)+'.v')
   path.write_text('Require Import ZesuSsz.Automation.All.\nLemma DesignedBoundary_fixture : True.\nProof.\n  zesu_block.\nQed.\n')
   caller=self.binding(path);pc=int(source['pc'],0)
   target=dict(casekey=source['case_id'],native_job_key=format(pc,'x'),pc=hex(pc),
               module='Fixture.Raw'+str(i),path=caller['path'],hash=caller['sha256'],
               statementhash=source['statement_sha256'],frozen_case=deepcopy(source),
               ordered_source_edges=deepcopy(source['CFG_successors']),
               protected_interval=dict(sha256=source['statement_sha256']))
   targets.append(target)
   self.authority['cases'].append(dict(block=target['native_job_key'],pc=pc,
       module=target['module'],source=caller,statement_sha256=target['statementhash']))
   self.authority['inventory'][18+i]['transport']='ready'
  self.raw=dict(frozen_CASES=self.authority['frozen_manifest'],cases=targets,case_count=60,
                ordered_edges=103,caller_emission=self.save('EMISSION.json',{}),
                corrected_refusal_checks=self.save('REFUSALS.json',{}))
  self.authority.update(raw60_targets=self.save('RAW60.json',self.raw),
      raw60_emission=self.raw['caller_emission'],raw60_refusal_checks=self.raw['corrected_refusal_checks'],
      executable_case_count=78,transport_pending_count=0,
      case_rebind=self.save('REBIND.json',dict(frozen_manifest=self.authority['frozen_manifest'],cases=self.rows)))
  self.authority_constant='PORT_HELDOUT_AUTHORITY_78';self.save_authority()

 def job(self,case):
  return dict(key=case['block'],phase='native',ordered_modules=[],target=dict(
      module=case['module'],pc=case['pc'],source_sha256=case['source']['sha256'],
      statement_sha256=case['statement_sha256']))

 def test_eighteen_callers_use_stock_8_32_and_no_cpu_stop(self):
  profile=self.save('PROFILE.json',self.profile)
  for case in self.authority['cases']:
   raw=self.job(case)
   sources=[dict(case['source'],module=case['module'])]+self.authority['production_sources']
   config=dict(prepared_workspace='/',prerequisite_modules=[],declarations_only=False,
               proof_runtime=dict(module_files={r['module']:r['path'] for r in sources}))
   workload=P.workload_for_job(profile,raw,config)
   job=P.apply_job(raw,workload=workload)
   self.assertEqual(P.validate_job(job),8*P.GIB)
   self.assertEqual(job['physical_fence_bytes'],32*P.GIB)
   self.assertEqual(N.cpu_budgets(job),(None,None))
   runtime={'cache_attempt':{'limits':{}}};N.configure_cpu(runtime,job)
   self.assertEqual(runtime['search_CPU_policy']['instruction_checkpoint_search_CPU_seconds'],600)
   self.assertEqual(runtime['search_CPU_policy']['long_search_report_CPU_seconds'],21600)

 def test_all_sixty_pending_transports_refuse_native_admission(self):
  for row in self.authority['inventory'][18:]:
   raw=self.job(self.authority['cases'][0]);raw['key']=format(row['pc'],'x')
   with self.assertRaisesRegex(ValueError,'case is not authorized'):
    P.production_port_case(self.profile,raw)

 def test_each_caller_identity_remains_exact(self):
  for field in ['module','pc','source_sha256','statement_sha256']:
   raw=self.job(self.authority['cases'][0]);raw['target'][field]='changed'
   with self.assertRaises(ValueError):P.production_port_case(self.profile,raw)

 def test_invented_pending_caller_refuses(self):
  self.authority['cases'].append(deepcopy(self.authority['cases'][0]));self.save_authority()
  with self.assertRaisesRegex(ValueError,'exact transports'):P.production_port_authority(self.profile)

 def test_descriptor_or_edge_changes_refuse(self):
  self.authority['inventory'][0]['ordered_edges_sha256']='0'*64;self.save_authority()
  with self.assertRaisesRegex(ValueError,'exact transports'):P.production_port_authority(self.profile)

 def test_changed_manifest_bytes_refuse(self):
  Path(self.authority['case_rebind']['path']).write_text('{}')
  with self.assertRaisesRegex(ValueError,'binding changed'):P.production_port_authority(self.profile)

 def test_family_evidence_contains_the_frozen_and_transport_bindings(self):
  profile=self.save('PROFILE.json',self.profile);bindings=P.profile_bindings(profile)
  for key in ['case_rebind','eql18_targets','frozen_manifest','declaration_evidence']:
   self.assertIn(self.authority[key],bindings)

 def test_all_descriptors_and_address_aliases_remain_blind(self):
  for row in self.authority['inventory']:
   for key in [row['block'],format(row['pc'],'x'),'0x'+format(row['pc'],'X')]:
    self.assertTrue(H.selected(key),key)
    result=dict(group_counts={'active':1},CPU={'cpu_seconds':5},aggregate_peak_bytes=8,
                closure=None,release=None,complete_state='PRIVATE',first_error='PRIVATE',
                source='PRIVATE',goals=['PRIVATE'],private_errors=['PRIVATE'])
    visible=H.summary(key,result,[{'module':'Fixture.Rules','sha256':'frozen'}])
    self.assertNotIn('PRIVATE',json.dumps(visible))
    self.assertEqual(visible['group_counts'],{'active':1})
  self.assertFalse(H.selected('800d6974'))

 def test_successor_layout_installs_the_authority_helper(self):
  layout=json.loads((HERE/'TOOL-LAYOUT.json').read_bytes())
  self.assertEqual(layout['block/port_heldout_authority.py'],'code/port_heldout_authority.py')
  tools=self.root/'tools'
  for name in ['block/port_heldout_authority.py','block/memory_policy.py']:
   target=tools/name;target.parent.mkdir(parents=True,exist_ok=True)
   target.write_bytes((HERE/layout[name]).read_bytes())
  self.save_authority()
  script=('import sys,json; from pathlib import Path; '
          'sys.path.insert(0,sys.argv[1]); import port_heldout_authority as H; '
          'assert Path(H.__file__).parent==Path(sys.argv[1]); '
          'H.validate(json.loads(Path(sys.argv[2]).read_bytes()))')
  result=subprocess.run([sys.executable,'-I','-B','-c',script,str(tools/'block'),
                         str(self.authority_path)],capture_output=True,text=True)
  self.assertEqual(result.returncode,0,result.stderr)

 def test_all_transported_cases_use_the_same_native_policy(self):
  self.add_raw_transports()
  self.test_eighteen_callers_use_stock_8_32_and_no_cpu_stop()
  self.test_successor_layout_installs_the_authority_helper()
  self.assertEqual(len(P.production_port_authority(self.profile)['cases']),78)

 def test_raw_transport_cannot_change_frozen_edges(self):
  self.add_raw_transports();self.raw['cases'][0]['ordered_source_edges'][0]['pc']='0xdead'
  self.authority['raw60_targets']=self.save('RAW60.json',self.raw);self.save_authority()
  with self.assertRaisesRegex(ValueError,'frozen bytes or ordered edges'):
   P.production_port_authority(self.profile)

 def test_raw_transport_cannot_change_frozen_statement(self):
  self.add_raw_transports();self.raw['cases'][0]['protected_interval']['sha256']='0'*64
  self.authority['raw60_targets']=self.save('RAW60.json',self.raw);self.save_authority()
  with self.assertRaisesRegex(ValueError,'frozen bytes or ordered edges'):
   P.production_port_authority(self.profile)

 def test_raw_native_case_retains_each_exact_identity(self):
  self.add_raw_transports()
  for field in ['module','pc','source_sha256','statement_sha256']:
   raw=self.job(self.authority['cases'][18]);raw['target'][field]='changed'
   with self.assertRaises(ValueError):P.production_port_case(self.profile,raw)
  bindings=P.profile_bindings(self.save('PROFILE.json',self.profile))
  for key in ['raw60_targets','raw60_emission','raw60_refusal_checks']:
   self.assertIn(self.authority[key],bindings)


if __name__=='__main__':unittest.main()
