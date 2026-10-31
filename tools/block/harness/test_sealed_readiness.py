import json,unittest
from pathlib import Path
from unittest.mock import patch
import scratch,full_chain
from seed_bindings import seal,clone_owned
from test_seed_bindings import SeedReferences

class SealedReadinessTests(unittest.TestCase):
 def fixture(self):
  f=SeedReferences();f.setUp();self.addCleanup(f.doCleanups)
  seed_path=f.root/'SEED.json';seed=json.loads(seed_path.read_text());seed['physical_flags']=[];scratch.save(seed_path,seed)
  reference_path=Path(f.descriptor['path']);value=json.loads(reference_path.read_text());value['seed_runtime']=scratch.binding(seed_path);scratch.save(reference_path,value);f.descriptor=scratch.binding(reference_path)
  reference=seal(f.descriptor,f.root/'sealed');workspace=f.root/'completed';clone_owned(reference,workspace)
  out=f.root/'job';(out/'native').mkdir(parents=True)
  source=workspace/'artifacts/default/T/Proof.v';obj=source.with_suffix('.vo')
  obj.unlink();obj.write_text('new physical object')
  seed_reference={'descriptor':reference,'workspace':str(workspace),'deltas':[],'removed':['artifacts/default/T/Proof.vo']}
  config={'prepared_workspace':str(workspace),'seed_binding_reference':seed_reference,'proof_runtime':{'module_files':{'T.Proof':'artifacts/default/T/Proof.v'}},'jobs':[{'ordered_modules':['T.Proof'],'output':str(out)}],'readiness':{'path':str(f.root/'READINESS.json')}}
  result={'success':True}
  for name,value in [('RUNTIME.json',{'prepared_workspace':str(workspace),'seed_binding_reference':seed_reference}),('RESULT.json',result),('CLOSURE.json',{'all_owned_actors_closed':True}),('RELEASE.json',{'released':True})]:scratch.save(out/name,value)
  receipt={'source':str(source),'source_sha256':scratch.digest(source),'object':str(obj),'object_sha256':scratch.digest(obj),'result':{'success':True}}
  scratch.save(out/'native/dependency-T.Proof.json',receipt)
  return f,config,result,out,receipt
 def test_retains_exact_owned_artifact_without_copy(self):
  f,c,r,out,receipt=self.fixture()
  with patch('clone_copy.copy2',side_effect=AssertionError('No second artifact copy')):value=full_chain.prerequisite_readiness(c,r)
  self.assertTrue(value['owned_sealed_artifacts_retained']);self.assertIn(scratch.binding(Path(receipt['object'])),value['objects'])
 def test_foreign_source_and_object_refuse(self):
  f,c,r,out,receipt=self.fixture();foreign=f.root/'foreign.v';foreign.write_text('Lemma x : True.');obj=foreign.with_suffix('.vo');obj.write_text('new physical object')
  receipt.update(source=str(foreign),source_sha256=scratch.digest(foreign),object=str(obj),object_sha256=scratch.digest(obj));scratch.save(out/'native/dependency-T.Proof.json',receipt)
  with self.assertRaisesRegex(ValueError,'logical module'):full_chain.prerequisite_readiness(c,r)
 def test_changed_artifact_refuses(self):
  f,c,r,out,receipt=self.fixture();Path(receipt['object']).write_text('unlisted object')
  with self.assertRaisesRegex(ValueError,'source or object changed'):full_chain.prerequisite_readiness(c,r)
 def test_unclosed_actor_refuses(self):
  f,c,r,out,receipt=self.fixture();scratch.save(out/'CLOSURE.json',{'all_owned_actors_closed':False})
  with self.assertRaisesRegex(ValueError,'closed and released'):full_chain.prerequisite_readiness(c,r)
 def test_other_workspace_refuses(self):
  f,c,r,out,receipt=self.fixture();value=json.loads((out/'RUNTIME.json').read_text());value['prepared_workspace']=str(f.root/'foreign');scratch.save(out/'RUNTIME.json',value)
  with self.assertRaisesRegex(ValueError,'another sealed workspace'):full_chain.prerequisite_readiness(c,r)

if __name__=='__main__':unittest.main()
