"""Bind the released minimal tactic route. Keep the stock route exact."""
from pathlib import Path
import hashlib,json,re

KIND='minimal_native_tactic'
STOCK_BODY='zesu_block.'
BLOCK2_BODY='zesu_block2.'
HOOK_MODULE='ZesuSsz.Automation.Hooks'
# Orch released only this reviewed F6 projection.
RELEASED_HOOK_PROJECTION_SHA256='d87c8149b8cb70084181b3c1877e6213029a7a870dcc04837c817b4c48514b74'

def bound(row):
 path=Path(row['path'])
 if hashlib.sha256(path.read_bytes()).hexdigest()!=row['sha256']:
  raise ValueError('A native-route authority input changed: '+str(path))
 return path

def read(row):return json.loads(bound(row).read_text())

def hook_projection(packet):
 row=packet.get('hooks_projection')
 if row is None:
  if HOOK_MODULE in packet['target_import_closure']:
   raise ValueError('The Hooks import lacks its bound F6 projection.')
  return []
 if (RELEASED_HOOK_PROJECTION_SHA256 is None or
     row.get('sha256')!=RELEASED_HOOK_PROJECTION_SHA256):
  raise ValueError('The Hooks projection is outside the single reviewed release.')
 projection=read(row)
 if projection.get('schema')!='scratch.hooks-projection.v1' or projection.get('module')!=HOOK_MODULE:
  raise ValueError('The Hooks projection has another schema or module.')
 if HOOK_MODULE not in packet['target_import_closure']:
  raise ValueError('The Hooks projection is absent from the actual import closure.')
 owner=bound(projection['owner_source'])
 if owner.name!='Hooks.v' or owner.parent.name!='Automation':
  raise ValueError('The hook definition does not belong to Automation/Hooks.v.')
 definition=projection['definition'];start,end=definition['start_byte'],definition['end_byte']
 data=owner.read_bytes()
 if (type(start) is not int or type(end) is not int or not 0<=start<end<=len(data)):
  raise ValueError('The hook definition has an invalid byte interval.')
 selected=data[start:end]
 if hashlib.sha256(selected).hexdigest()!=definition['sha256']:
  raise ValueError('The Hooks definition differs from its reviewed bytes.')
 source=projection['projection_source'];projected=bound(source)
 if projected.read_bytes()!=projection['prefix'].encode('utf-8')+selected:
  raise ValueError('The Hooks projection diverges from its owner definition.')
 matching=[r for r in packet['source_inventory'] if r['module']==HOOK_MODULE]
 if len(matching)!=1 or any(matching[0].get(k)!=source.get(k) for k in ['path','sha256']):
  raise ValueError('The Hooks projection differs from the loaded source inventory.')
 prefix=read(packet['common_prefix'])
 compiled=[r for r in prefix['modules'] if r['module']==HOOK_MODULE]
 if len(compiled)!=1 or compiled[0]['source']!=source:
  raise ValueError('The Hooks projection lacks its exact compiled prefix object.')
 return [row,projection['owner_source'],source]

def body(value):
 if value not in {STOCK_BODY,BLOCK2_BODY}:
  raise ValueError('The native body is outside the two released commands.')
 return value

def authority(binding):
 packet=read(binding)
 if packet.get('schema')!='scratch.minimal-native-authority.v1':
  raise ValueError('The minimal-native authority schema is unsupported.')
 body(packet['native_body'])
 hook_projection(packet)
 forbidden={'ZesuSsz.Automation.All','ZesuSsz.Automation.Approved','ZesuSsz.Automation.Finish','ZesuSsz.Compliance.DecodeItemHints','ZesuSsz.Generated.DecodeItem.Registrations'}
 if forbidden & set(packet['target_import_closure']):raise ValueError('The minimal import closure activates an excluded production module.')
 for key in ['ordered_modules','target_import_closure']:
  values=packet[key]
  if not isinstance(values,list) or len(values)!=len(set(values)) or any(not isinstance(v,str) or not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',v) for v in values):
   raise ValueError('The released module list is malformed or repeats a module.')
 rows=packet['source_inventory'];names=[r['module'] for r in rows]
 if len(names)!=len(set(names)):raise ValueError('The released source inventory repeats a module.')
 for row in rows:bound(row)
 for key in ['native_source','tactic_source']:
  row=packet[key];bound(row)
  if not any(all(r.get(k)==row.get(k) for k in ['module','path','sha256']) for r in rows):
   raise ValueError('A route source is absent from its released inventory.')
  if row['module'] not in packet['target_import_closure']:
   raise ValueError('A route source is absent from its released import closure.')
 if not set(packet['ordered_modules']).issubset(packet['target_import_closure']):
  raise ValueError('The compile list leaves the released import closure.')
 if 'common_prefix' not in packet or 'prerequisite_delta' not in packet:raise ValueError('The authority lacks its common prefix or exact arm delta.')
 return packet

def for_profile(profile_binding):
 if not profile_binding:return None
 profile=read(profile_binding)
 if profile.get('kind')!=KIND:return None
 authority(profile['authority'])
 return profile['authority']

def source_body(profile_binding):
 route=for_profile(profile_binding)
 return authority(route)['native_body'] if route else STOCK_BODY

def validate(route,*,workspace,modules,target,ordered):
 packet=authority(route);workspace=Path(workspace)
 if ordered!=[]:
  raise ValueError('The native phase must not repeat prerequisite compilation.')
 native=packet['native_source']
 if target['module']!=native['module'] or target['source_sha256']!=native['sha256']:
  raise ValueError('The native target differs from the reviewed source.')
 if native.get('statement_sha256') is not None and target['statement_sha256']!=native['statement_sha256']:
  raise ValueError('The native statement differs from the reviewed authority.')
 for row in packet['source_inventory']:
  if row['module'] not in modules:raise ValueError('A released private source has no staged mapping.')
  path=workspace/modules[row['module']]
  if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=row['sha256']:
   raise ValueError('A staged route source differs from the reviewed authority: '+row['module'])
 from scratch_statement import source_statement
 original=bound(packet['original_source'])
 original_statement=source_statement(original)['statement']
 actual_statement=source_statement(workspace/modules[native['module']],packet['native_body'])['statement']
 if actual_statement!=original_statement or hashlib.sha256(original_statement.encode()).hexdigest()!=target['statement_sha256']:
  raise ValueError('The native theorem differs from its original declaration.')
 from minimal_prefix import validate as validate_prefix
 validate_prefix(packet,workspace,modules)
 text=(workspace/modules[native['module']]).read_text()
 if re.search(r'\bLtac\b',text):raise ValueError('The native caller must not redefine a tactic.')
 return packet

def authority_body(binding):
 packet=read(binding)
 if packet.get('schema')!='scratch.minimal-native-authority.v1':raise ValueError('The minimal-native authority schema is unsupported.')
 return body(packet['native_body'])

def runtime_body(runtime):
 route=runtime.get('native_route')
 if not route:return STOCK_BODY
 packet=read(route)
 authority_body(route)
 if runtime.get('ordered_modules',[])!=[]:
  raise ValueError('The native phase must not repeat prerequisite compilation.')
 return packet['native_body']

def validate_runtime(runtime,workspace):
 route=runtime.get('native_route')
 if not route:return STOCK_BODY
 packet=validate(route,workspace=workspace,modules=runtime['module_files'],
                 target=runtime['target']['block'],ordered=runtime.get('ordered_modules',[]))
 from minimal_prefix import validate as validate_prefix
 validate_prefix(packet,workspace,runtime['module_files'],complete_delta=True,evidence=runtime.get('native_delta'))
 return packet['native_body']

def validate_closure(runtime,seen,files):
 route=runtime.get('native_route')
 if not route:return
 packet=authority(route)
 if sorted(seen)!=sorted(packet['target_import_closure']):
  raise ValueError('The actual target import closure differs from its authority.')
 inventory={r['module']:r for r in packet['source_inventory']}
 private=set(runtime['module_files']) & set(seen)
 if private!=set(inventory):
  raise ValueError('The loaded private closure differs from the reviewed source inventory.')
 actual={r['id']:r for r in files}
 for module,row in inventory.items():
  source=actual.get('module:'+module+':source')
  if not source or source['sha256']!=row['sha256']:
   raise ValueError('A compiler-resolved source differs from its reviewed authority.')

def input_bindings(route):
 if not route:return []
 packet=authority(route)
 from minimal_prefix import bindings as prefix_bindings
 return [route,packet['original_source']]+hook_projection(packet)+prefix_bindings(packet)+[{'path':r['path'],'sha256':r['sha256']} for r in packet['source_inventory']]


def validate_prerequisite_order(config):
 route=config.get('native_route')
 if not route:return
 packet=authority(route);pre,native=config['jobs']
 if pre['ordered_modules']!=packet['prerequisite_delta']:
  raise ValueError('The prerequisite list differs from the exact reviewed arm delta.')
 if native.get('ordered_modules',[]) or native.get('native_route')!=route:
  raise ValueError('The native phase repeats setup or loses its authority.')
