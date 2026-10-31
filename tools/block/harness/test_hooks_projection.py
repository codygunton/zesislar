import copy
import hashlib
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import test_native_route as fixtures
import native_route as N
from entry_chain import binding

class HooksProjection(unittest.TestCase):
 setUp=fixtures.NativeRoute.setUp
 file=fixtures.NativeRoute.file
 js=fixtures.NativeRoute.js
 fixture=fixtures.NativeRoute.fixture
 def projected(self):
  packet,route,config,job=self.fixture()
  definition=b'Ltac released_write_step := idtac.\n'
  before=b'(* Unrelated owner content. *)\n'
  owner=self.root/'Automation'/'Hooks.v';owner.parent.mkdir();owner.write_bytes(before+definition+b'(* Unrelated suffix. *)\n')
  prefix='Require Import Fixture.Tactic.\n'
  source=self.file('ProjectedHooks.v',prefix+definition.decode())
  projection={'schema':'scratch.hooks-projection.v1','module':N.HOOK_MODULE,
              'owner_source':binding(owner),'definition':{'start_byte':len(before),'end_byte':len(before)+len(definition),'sha256':hashlib.sha256(definition).hexdigest()},
              'projection_source':source,'prefix':prefix}
  manifest=self.js('projection.json',projection)
  packet['hooks_projection']=manifest
  packet['target_import_closure'].append(N.HOOK_MODULE)
  packet['source_inventory'].append(dict(source,module=N.HOOK_MODULE))
  packet['ordered_modules'].append(N.HOOK_MODULE)
  config['proof_runtime']['module_files'][N.HOOK_MODULE]='ProjectedHooks.v'
  obj=self.file('ProjectedHooks.vo','compiled Hooks projection')
  receipt=self.js('hooks-compile.json',{'source':source['path'],'source_sha256':source['sha256'],'object':obj['path'],'object_sha256':obj['sha256'],'result':{'success':True}})
  common=json.loads(Path(packet['common_prefix']['path']).read_text())
  common['modules'].append({'module':N.HOOK_MODULE,'source':source,'object':obj,'receipt':receipt})
  packet['common_prefix']=self.js('common-with-hooks.json',common)
  return packet,projection,manifest,config,job
 def checked(self,packet,manifest):
  route=self.js('projected-authority.json',packet)
  with patch.object(N,'RELEASED_HOOK_PROJECTION_SHA256',manifest['sha256']):
   return N.authority(route)
 def test_exact_projection_accepts(self):
  packet,projection,manifest,config,job=self.projected()
  self.assertEqual(self.checked(packet,manifest)['hooks_projection'],manifest)
  route=self.js('full-authority.json',packet)
  with patch.object(N,'RELEASED_HOOK_PROJECTION_SHA256',manifest['sha256']):
   N.validate(route,workspace=self.root,modules=config['proof_runtime']['module_files'],target=job['target'],ordered=[])
   bindings=N.input_bindings(route)
  self.assertIn(projection['owner_source'],bindings)
  self.assertIn(manifest,bindings)
 def test_owner_module_without_projection_refuses(self):
  packet,projection,manifest,config,job=self.projected();del packet['hooks_projection']
  with self.assertRaisesRegex(ValueError,'lacks its bound'):self.checked(packet,manifest)
 def test_unreleased_projection_refuses(self):
  packet,projection,manifest,config,job=self.projected()
  with patch.object(N,'RELEASED_HOOK_PROJECTION_SHA256','0'*64):
   with self.assertRaisesRegex(ValueError,'single reviewed'):N.authority(self.js('unreleased.json',packet))
 def test_owner_byte_change_refuses(self):
  packet,projection,manifest,config,job=self.projected();Path(projection['owner_source']['path']).write_text('changed')
  with self.assertRaisesRegex(ValueError,'input changed'):self.checked(packet,manifest)
 def test_rebound_projection_with_extra_command_refuses(self):
  packet,projection,manifest,config,job=self.projected();source=Path(projection['projection_source']['path'])
  source.write_text(source.read_text()+'Ltac extra := idtac.\n')
  projection['projection_source']=binding(source);manifest=self.js('extra-projection.json',projection);packet['hooks_projection']=manifest
  with self.assertRaisesRegex(ValueError,'diverges'):self.checked(packet,manifest)
 def test_definition_interval_change_refuses(self):
  packet,projection,manifest,config,job=self.projected();projection['definition']['end_byte']+=1
  manifest=self.js('other-interval.json',projection);packet['hooks_projection']=manifest
  with self.assertRaisesRegex(ValueError,'reviewed bytes'):self.checked(packet,manifest)
 def test_wrong_loaded_projection_refuses(self):
  packet,projection,manifest,config,job=self.projected();packet['source_inventory'][-1]['sha256']='0'*64
  with self.assertRaisesRegex(ValueError,'source inventory'):self.checked(packet,manifest)
 def test_uncompiled_projection_refuses(self):
  packet,projection,manifest,config,job=self.projected();common=json.loads(Path(packet['common_prefix']['path']).read_text());common['modules'].pop()
  packet['common_prefix']=self.js('uncompiled-prefix.json',common)
  with self.assertRaisesRegex(ValueError,'compiled prefix'):self.checked(packet,manifest)
 def test_other_production_modules_stay_forbidden(self):
  original,projection,manifest,config,job=self.projected()
  for name in ['ZesuSsz.Automation.All','ZesuSsz.Automation.Approved','ZesuSsz.Automation.Finish','ZesuSsz.Compliance.DecodeItemHints','ZesuSsz.Generated.DecodeItem.Registrations']:
   packet=copy.deepcopy(original);packet['target_import_closure'].append(name)
   with self.subTest(module=name),self.assertRaisesRegex(ValueError,'excluded production'):self.checked(packet,manifest)
 def test_reused_projection_object_change_refuses(self):
  packet,projection,manifest,config,job=self.projected();(self.root/'ProjectedHooks.vo').write_text('changed')
  with patch.object(N,'RELEASED_HOOK_PROJECTION_SHA256',manifest['sha256']):
   with self.assertRaisesRegex(ValueError,'input changed|compiled prefix'):
    N.validate(self.js('changed-object.json',packet),workspace=self.root,modules=config['proof_runtime']['module_files'],target=job['target'],ordered=[])

if __name__=='__main__':unittest.main()
