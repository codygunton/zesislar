from copy import deepcopy
import json,unittest
from pathlib import Path
import scratch
from seed_bindings import compact
from test_seed_bindings import SeedReferences

class DeclarationTargetTests(unittest.TestCase):
 def fixture(self):
  f=SeedReferences();f.setUp();self.addCleanup(f.doCleanups)
  for name in ['artifacts/default/T/Proof.glob','artifacts/default/T/Support.vo']:
   for root in [f.seed,f.owned]:(root/name).write_text('retained '+name)
  rows=[scratch.binding(p) for p in f.seed.rglob('*') if p.is_file() and not p.is_symlink()]
  runtime_path=f.root/'SEED.json';seed=json.loads(runtime_path.read_text());seed['bindings']=rows+[scratch.binding(f.tool)];scratch.save(runtime_path,seed)
  inventory_path=f.root/'FILES.jsonl';inventory_path.write_text(''.join(json.dumps({'relative':str(Path(r['path']).relative_to(f.seed)),'sha256':r['sha256']})+'\n' for r in rows))
  reference=json.loads(Path(f.descriptor['path']).read_text());reference.update(seed_runtime=scratch.binding(runtime_path),inventory=scratch.binding(inventory_path));scratch.save(f.descriptor['path'],reference);f.descriptor=scratch.binding(Path(f.descriptor['path']))
  f.runtime['bindings']=rows+[scratch.binding(p) for p in f.owned.rglob('*') if p.is_file() and not p.is_symlink()]+[scratch.binding(f.tool)]
  source=f.owned/'artifacts/default/T/Proof.v'
  target={'module':'T.Proof','pc':1,'source_sha256':scratch.digest(source),'statement_sha256':'0'*64}
  f.runtime.update(declarations_only=True,jobs=[{'phase':'prerequisites','target':deepcopy(target),'ordered_modules':[]},{'phase':'native','target':deepcopy(target)}])
  return f
 def test_selected_target_keeps_exact_output_omissions(self):
  f=self.fixture();scratch.check_declaration_target(f.runtime)
  for suffix in ['.vo','.glob']:(f.owned/('artifacts/default/T/Proof'+suffix)).unlink()
  # stage_job uses the existing target field, while retaining an empty compile list.
  staged={'prepared_workspace':str(f.owned),'bindings':[], 'module_files':f.runtime['proof_runtime']['module_files'],'target':{'block':f.runtime['jobs'][0]['target']},'ordered_modules':[]}
  compact(staged,f.descriptor,f.owned)
  self.assertEqual(staged['seed_binding_reference']['removed'],['artifacts/default/T/Proof.glob','artifacts/default/T/Proof.vo'])
  self.assertEqual(staged['ordered_modules'],[])
 def test_unrelated_object_still_refuses(self):
  f=self.fixture();(f.owned/'artifacts/default/T/Support.vo').unlink()
  staged={'prepared_workspace':str(f.owned),'bindings':[],'module_files':f.runtime['proof_runtime']['module_files'],'target':{'block':f.runtime['jobs'][0]['target']},'ordered_modules':[]}
  with self.assertRaisesRegex(ValueError,'undeclared seed input is absent'):compact(staged,f.descriptor,f.owned)
 def test_mismatched_target_refuses(self):
  f=self.fixture();f.runtime['jobs'][0]['target']['statement_sha256']='1'*64
  with self.assertRaisesRegex(ValueError,'declaration target differs'):scratch.check_declaration_target(f.runtime)
 def test_mismatched_source_identity_refuses(self):
  f=self.fixture()
  for job in f.runtime['jobs']:job['target']['source_sha256']='1'*64
  with self.assertRaisesRegex(ValueError,'carrier source differs'):scratch.check_declaration_target(f.runtime)

if __name__=='__main__':unittest.main()
