"""Refresh active profile metadata without changing an owned prepared bank."""
from copy import deepcopy
from pathlib import Path
import hashlib,json,sys,tempfile,unittest

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE),str(HERE.parents[1]),str(HERE.parents[2])]
import scratch
from memory_policy import FOCUSED_KIND,workload_for_job
import test_added_tool_transition as transitions


class ProfileSelection(unittest.TestCase):
 def setUp(self):
  temporary=tempfile.TemporaryDirectory();self.addCleanup(temporary.cleanup)
  self.root=Path(temporary.name).resolve()
  self.path=self.root/'PROFILE.json'
  scratch.save(self.path,dict(schema='scratch.admission-profile.v1',kind=FOCUSED_KIND,sources=[]))
  self.profile=scratch.binding(self.path)
  self.other=self.root/'OTHER.json';self.other.write_bytes(self.path.read_bytes())
  self.second=scratch.binding(self.other)

 def config(self,profiles):
  return dict(admission_profile=deepcopy(self.profile),jobs=[dict(workload=value) for value in profiles])

 def active(self,profile=None):return dict(kind=FOCUSED_KIND,profile=deepcopy(profile or self.profile))

 def test_inactive_inherited_profile_is_not_selected(self):
  config=self.config([None,None]);before=deepcopy(config)
  self.assertIsNone(scratch.refresh_admission_profile(config))
  self.assertEqual(config,before)

 def test_matching_active_profiles_are_selected(self):
  config=self.config([self.active(),None,self.active()])
  self.assertEqual(scratch.refresh_admission_profile(config),self.profile)

 def test_conflicting_active_profiles_refuse_even_with_override(self):
  config=self.config([self.active(),self.active(self.second)])
  for explicit in [None,self.other]:
   with self.subTest(explicit=explicit),self.assertRaisesRegex(ValueError,'profiles conflict'):
    scratch.refresh_admission_profile(config,explicit)

 def test_active_profile_requires_matching_top_level_binding(self):
  for top in [None,self.second]:
   config=self.config([self.active()]);config['admission_profile']=top
   with self.subTest(top=top),self.assertRaisesRegex(ValueError,'runtime binding'):
    scratch.refresh_admission_profile(config)

 def test_malformed_active_bindings_refuse(self):
  malformed=[None,{},[],dict(path='relative',sha256='a'*64),dict(path=str(self.path),sha256='bad'),
             dict(self.profile,extra=True)]
  for profile in malformed:
   with self.subTest(profile=profile),self.assertRaisesRegex(ValueError,'malformed'):
    scratch.refresh_admission_profile(self.config([dict(profile=profile)]))
  for workload in [[],False,'invalid']:
   with self.subTest(workload=workload),self.assertRaisesRegex(ValueError,'malformed'):
    scratch.refresh_admission_profile(self.config([workload]))

 def test_explicit_override_selects_bound_new_profile(self):
  config=self.config([self.active(),None]);before=deepcopy(config)
  selected=scratch.refresh_admission_profile(config,self.other)
  self.assertEqual(selected,self.second)
  job=dict(phase='prerequisites',ordered_modules=[])
  context=dict(declarations_only=True,proof_runtime=dict(module_files={}),prepared_workspace=str(self.root))
  self.assertEqual(workload_for_job(selected,job,context)['profile'],self.second)
  self.assertEqual(config,before)

 def test_explicit_override_keeps_policy_validation(self):
  scratch.save(self.other,dict(schema='unsupported',kind=FOCUSED_KIND,sources=[]))
  selected=scratch.refresh_admission_profile(self.config([None]),self.other)
  with self.assertRaisesRegex(ValueError,'unsupported'):
   workload_for_job(selected,dict(phase='prerequisites'),{})
  selected=scratch.refresh_admission_profile(self.config([None]),self.path)
  with self.assertRaisesRegex(ValueError,'declaration-only'):
   workload_for_job(selected,dict(phase='prerequisites'),dict(declarations_only=False,proof_runtime=dict(module_files={}),prepared_workspace=str(self.root)))


class InactiveSeedRefresh(unittest.TestCase):
 setUp=transitions.AddedToolTransition.setUp
 refresh=transitions.AddedToolTransition.refresh

 def test_public_refresh_clears_inactive_seed_profile_and_preserves_native_policy(self):
  profile=self.root/'INHERITED-PROFILE.json'
  scratch.save(profile,dict(schema='scratch.admission-profile.v1',kind=FOCUSED_KIND,sources=[]))
  self.config.update(declarations_only=False,admission_profile=scratch.binding(profile))
  self.config['bindings'].append(scratch.binding(profile))
  scratch.save(self.prior,self.config)
  original=deepcopy(self.config['bindings'])
  before={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in self.workspace.rglob('*') if p.is_file()}
  first,current=self.refresh()
  second,current=self.refresh(first,'refresh002')
  self.assertNotIn('admission_profile',current)
  self.assertIsNone(current['jobs'][0]['workload'])
  native=current['jobs'][1]
  self.assertIsNone(native['workload'])
  self.assertEqual(native['claim_bytes'],64*1024**3)
  self.assertEqual(native['physical_fence_bytes'],64*1024**3)
  self.assertFalse(current['declarations_only'])
  self.assertEqual(current['prepared_workspace'],str(self.workspace))
  for row in original:self.assertIn(row,current['bindings'])
  after={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in self.workspace.rglob('*') if p.is_file()}
  self.assertEqual(before,after)
  self.assertFalse((self.root/'refresh001/jobs').exists())
  self.assertFalse((self.root/'refresh002/jobs').exists())


if __name__=='__main__':unittest.main()
