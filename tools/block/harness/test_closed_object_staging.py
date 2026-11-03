"""Only authenticated exact closed-origin output cells enter an owned bank."""
from pathlib import Path
import json,shutil,sys,tempfile,unittest
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE.parent),str(HERE.parents[1])]
from entry_chain import binding
import closed_object_staging as S
import object_import_migration as M
from closed_compilation_origin import LABEL

class ClosedObjectStagingTests(unittest.TestCase):
 def setUp(self):
  t=tempfile.TemporaryDirectory();self.addCleanup(t.cleanup);self.root=Path(t.name);self.old=self.root/'old';self.current=self.root/'current';self.old.mkdir();self.current.mkdir();self.module='Example.Owner';self.modules={self.module:'Owner.v'}
  for root in [self.old,self.current]:(root/'Owner.v').write_text('(* Exact declaration. *)\n')
  (self.old/'Owner.vo').write_bytes(b'physical object');(self.old/'Owner.vos').write_bytes(b'physical sidecar')
  side={'binding':binding(self.old/'Owner.vos')};self.physical=self.save('physical.json',{'compiler_outputs':{'sidecar':side,'sidecar_status':'compiled_output'}})
  self.receipt=self.save('receipt.json',{'object':binding(self.old/'Owner.vo'),'sidecar':side,'sidecar_status':'compiled_output','physical_result':self.physical})
  self.accepted={'kind':LABEL,'publication':{'path':'origin','sha256':'a'*64},'original_receipts':[self.receipt]}
  self.value={'schema':'entry-chain.object-import-migration.v1','module':self.module,'origin':self.accepted,'source':binding(self.old/'Owner.v'),'object':binding(self.old/'Owner.vo'),'owned_workspace':str(self.old),'compiler':{'path':'compiler','sha256':'b'*64}}
  self.reference=self.save('migration.json',self.value);self.config={'object_imports':{self.module:self.reference}}
  self.patches=[patch.object(M,'origin_context',return_value={'physical_flags':[]}),patch.object(M,'origin',return_value=(self.accepted,[])),patch.object(S.clone_copy,'copy2',side_effect=shutil.copy2)]
  for p in self.patches:p.start();self.addCleanup(p.stop)
 def save(self,name,value):
  p=self.root/name;p.write_text(json.dumps(value));return binding(p)
 def stage(self):return S.stage(self.config,self.current,self.modules)
 def test_exact_objects_and_sidecars_stage(self):
  result=self.stage();self.assertEqual(result['count'],1);self.assertFalse(result['compatibility_granted'])
  self.assertEqual((self.current/'Owner.vo').read_bytes(),b'physical object');self.assertEqual((self.current/'Owner.vos').read_bytes(),b'physical sidecar')
 def test_different_existing_bytes_refuse(self):
  (self.current/'Owner.vo').write_bytes(b'other')
  with self.assertRaisesRegex(ValueError,'different bytes'):self.stage()
  self.assertFalse((self.current/'Owner.vos').exists())
 def test_symlink_destination_refuses(self):
  (self.current/'Owner.vo').symlink_to(self.old/'Owner.vo')
  with self.assertRaises(ValueError):self.stage()
 def test_escaping_module_mapping_refuses(self):
  self.modules[self.module]='../old/Owner.v'
  with self.assertRaisesRegex(ValueError,'escapes'):self.stage()
 def test_changed_source_is_left_for_planner(self):
  (self.current/'Owner.v').write_text('(* Changed declaration. *)\n')
  self.assertEqual(self.stage()['count'],0);self.assertFalse((self.current/'Owner.vo').exists())
 def test_unauthorized_origin_copies_nothing(self):
  with patch.object(M,'origin',side_effect=ValueError('Origin refused')):
   with self.assertRaisesRegex(ValueError,'Origin refused'):self.stage()
  self.assertFalse((self.current/'Owner.vo').exists())
 def test_changed_physical_object_refuses(self):
  (self.old/'Owner.vo').write_bytes(b'changed')
  with self.assertRaises(ValueError):self.stage()
 def test_unattested_sidecar_refuses(self):
  value=json.loads(Path(self.receipt['path']).read_text());value['sidecar_status']='absent';Path(self.receipt['path']).write_text(json.dumps(value))
  with self.assertRaises(ValueError):self.stage()
 def test_ordinary_receipts_do_not_enter_this_route(self):
  self.value['origin']['kind']='individual-accepted-compilation';self.reference=self.save('migration.json',self.value);self.config['object_imports'][self.module]=self.reference
  self.assertEqual(self.stage()['count'],0)
 def test_migration_installation_uses_completed_adapter_map(self):
  source=(HERE/'scratch.py').read_text();start=source.index('def prepare(');end=source.index('def ',start+4);body=source[start:end]
  self.assertLess(body.index("modules.update(graph['module_files'])"),body.index('install_object_import_migrations(c,'))
  self.assertLess(body.index('install_object_import_migrations(c,'),body.index('closed_install=stage_closed_objects'))
 def test_unknown_module_refusal_remains(self):
  import scratch
  config={'proof_runtime':{'module_files':{}},'bindings':[]};manifest=self.save('manifest.json',{'schema':'entry-chain.object-import-migrations.v1','receipts':{self.module:self.reference}})
  with self.assertRaisesRegex(ValueError,'unknown module'):scratch.install_object_import_migrations(config,Path(manifest['path']))
  config['proof_runtime']['module_files'].update(self.modules)
  scratch.install_object_import_migrations(config,Path(manifest['path']))
  self.assertEqual(config['object_imports'][self.module],self.reference)
 def test_staging_precedes_unchanged_compatibility(self):
  source=(HERE/'scratch.py').read_text();a=source.index('closed_install=stage_closed_objects');b=source.index('missing=missing_prerequisite_objects');c=source.index('imports=compatibility(')
  self.assertLess(a,b);self.assertLess(b,c);self.assertIn("c['bindings']+inherited",source)
if __name__=='__main__':unittest.main()
