"""Keep unknown held-out jobs at their fence until a completed peak exists."""
from copy import deepcopy
import unittest

from test_heldout_port import HeldoutPortTests
import memory_policy as P


class CorrectedMemoryTests(unittest.TestCase):
 binding=HeldoutPortTests.binding
 save=HeldoutPortTests.save
 save_authority=HeldoutPortTests.save_authority
 add_raw_transports=HeldoutPortTests.add_raw_transports
 job=HeldoutPortTests.job

 def setUp(self):
  HeldoutPortTests.setUp(self)
  self.add_raw_transports()
  self.authority.update(claim_bytes=P.PORT_FENCE,memory_booking=deepcopy(P.HELDOUT_MEMORY_BOOKING))
  self.authority_constant='PORT_HELDOUT_MEMORY_AUTHORITY';self.save_authority()

 def configured(self,index=0):
  case=self.authority['cases'][index];raw=self.job(case)
  sources=[dict(case['source'],module=case['module'])]+self.authority['production_sources']
  config=dict(prepared_workspace='/',prerequisite_modules=[],declarations_only=False,
              proof_runtime=dict(module_files={r['module']:r['path'] for r in sources}))
  profile=self.save('PROFILE.json',self.profile)
  return raw,P.workload_for_job(profile,raw,config)

 def measurement(self,raw,peak):
  groups=dict(goals=[],stack=[],shelf=[],given_up=[])
  state=self.save('STATE.json',dict(groups,kernel_groups=deepcopy(groups)))
  cpu=dict(final_memory_accounting_available=True,aggregate_peak_bytes=peak,
           memory_events=dict(available=True,counters=dict(oom=0,oom_kill=0,oom_group_kill=0)),
           scope='Completed owned aggregate.',CPU_budget_enforced=False)
  target=raw['target']
  result=dict(module=target['module'],statement_sha256=target['statement_sha256'],
              status='passed',normal_tactic_return=True,CPU=cpu,aggregate_peak_bytes=peak,
              final_memory_accounting_available=True,complete_state=dict(state,state_source='successful_command_returned_state'),
              group_counts=dict(active=0,focus_frames=0,frame_goals=0,shelves=0,given_up=0))
  return dict(route='stock_zesu_block',module=target['module'],statement_sha256=target['statement_sha256'],
              native_source=self.authority['cases'][0]['source'],result=self.save('RESULT.json',result),
              closure=self.save('CLOSURE.json',dict(all_owned_actors_closed=True)),
              release=self.save('RELEASE.json',dict(released=True,bytes=P.PORT_FENCE)))

 def test_all_unknown_cases_book_full_fence(self):
  for index in range(78):
   raw,workload=self.configured(index)
   job=P.apply_job(raw,workload=workload)
   self.assertEqual(P.validate_job(job),P.PORT_FENCE)
   self.assertEqual(job['physical_fence_bytes'],P.PORT_FENCE)

 def test_completed_peak_uses_exact_upward_rounding_and_one_GiB_floor(self):
  for peak,expected in [(1,P.GIB),(6*P.GIB,9*P.GIB),(6*P.GIB+1,9*P.GIB+2)]:
   raw,workload=self.configured();row=self.measurement(raw,peak)
   job=P.apply_job(raw,[row],workload=workload)
   self.assertEqual(P.validate_job(job),expected)
   self.assertEqual(job['physical_fence_bytes'],P.PORT_FENCE)

 def test_live_partial_or_oom_measurements_cannot_reduce_booking(self):
  for change in [lambda r:r.update(normal_tactic_return=False),
                 lambda r:r.update(final_memory_accounting_available=False),
                 lambda r:r['CPU']['memory_events']['counters'].update(oom_kill=1)]:
   raw,workload=self.configured();row=self.measurement(raw,6*P.GIB)
   result=P.read(row['result']);change(result);row['result']=self.save('RESULT.json',result)
   self.assertEqual(P.apply_job(raw,[row],workload=workload)['claim_bytes'],P.PORT_FENCE)

 def test_underbooked_unknown_job_refuses(self):
  raw,workload=self.configured();job=P.apply_job(raw,workload=workload);job['claim_bytes']=8*P.GIB
  with self.assertRaisesRegex(ValueError,'claim or physical fence'):P.validate_job(job)

 def test_profile_booking_option_cannot_change_blind_policy(self):
  self.profile['memory_booking']='full_physical_fence'
  with self.assertRaisesRegex(ValueError,'cannot change a blind PORT policy'):
   P.production_port_authority(self.profile)

 def test_peak_above_fence_requires_review(self):
  raw,workload=self.configured();row=self.measurement(raw,24*P.GIB)
  with self.assertRaisesRegex(ValueError,'larger reviewed fence'):P.apply_job(raw,[row],workload=workload)

 def test_kind_limit_and_memory_hold_are_exact(self):
  self.assertEqual(self.authority['memory_booking']['maximum_live_cases_per_kind'],2)
  self.assertEqual(self.authority['memory_booking']['admission_resume_below_bytes'],150*P.GIB)
  self.authority['memory_booking']['maximum_live_cases_per_kind']=3;self.save_authority()
  with self.assertRaisesRegex(ValueError,'memory ruling'):P.production_port_authority(self.profile)

if __name__=='__main__':unittest.main()
