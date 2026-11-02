"""Install exact recovery tooling before any new scratch runtime is bound."""
import clone_copy
from pathlib import Path
import hashlib, json, os, shutil, tempfile

def binding(path):
 path=Path(path).resolve();return {'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

def owned_tool(workspace, relative):
 path=Path(relative)
 if path.is_absolute() or '..' in path.parts or str(path)!=relative:
  raise ValueError('A recovery tool path escapes the owned tools directory.')
 root=Path(workspace)/'tools';target=root/path
 if root.is_symlink() or root.resolve()!=root or target.resolve()!=target:
  raise ValueError('A recovery tool destination contains an alias.')
 if target.exists() and not target.is_file():raise ValueError('A recovery tool destination is not a file.')
 return target


def read_runtime(row):
 if binding(row['path'])!=row:raise ValueError('The predecessor runtime changed.')
 result=json.loads(Path(row['path']).read_text())
 if binding(row['path'])!=row:raise ValueError('The predecessor runtime changed during reading.')
 return result


def pinned_layout(harness):
 from harness_commit import check
 check(harness)
 here=Path(harness['root'])/'tools/block/harness'
 recorded=binding(here/'TOOL-LAYOUT.json')
 layout=json.loads(Path(recorded['path']).read_text())
 if binding(recorded['path'])!=recorded:raise ValueError('The predecessor layout changed.')
 check(harness)
 return here,layout,recorded


def absent_tool(item, config, seen=()):
 evidence=item.get('absent',{})
 if item.get('prepared') is not None or evidence.get('schema')!='prepared-tool.absent.v1':
  raise ValueError('A missing recovery tool lacks authenticated absence.')
 target=owned_tool(config['prepared_workspace'],item['relative'])
 if evidence.get('path')!=str(target) or target.exists() or target.is_symlink():
  raise ValueError('An authenticated absent recovery tool appeared or changed destination.')
 prior=evidence.get('runtime')
 if not isinstance(prior,dict) or prior not in config.get('bindings',[]):
  raise ValueError('An absent recovery tool lacks its bound predecessor runtime.')
 key=(prior['path'],prior['sha256'])
 if key in seen or len(seen)>=64:raise ValueError('The absent recovery tool lineage contains a cycle.')
 previous=read_runtime(prior)
 if previous.get('prepared_workspace')!=config['prepared_workspace'] or previous.get('harness')!=evidence.get('harness'):
  raise ValueError('An absent recovery tool names another predecessor workspace or harness.')
 here,layout,recorded=pinned_layout(previous['harness'])
 if evidence.get('layout')!=recorded:raise ValueError('An absent recovery tool names another pinned layout.')
 relative=item['relative']
 if relative in layout:
  candidates=[row for row in previous.get('prepared_tool_transition',[]) if row.get('relative')==relative]
  if len(candidates)!=1 or candidates[0].get('successor')!=binding(here/layout[relative]):
   raise ValueError('An absent recovery tool lacks its predecessor transition.')
  absent_tool(candidates[0],previous,seen+(key,))
 return True


def prepared_transitions(config, here, prior_runtime=None):
 here=Path(here);layout=json.loads((here/'TOOL-LAYOUT.json').read_text())
 previous=None;old_layout={};old_rows={}
 if prior_runtime is not None:
  if prior_runtime not in config.get('bindings',[]):raise ValueError('The predecessor runtime is not retained.')
  previous=read_runtime(prior_runtime)
  if previous['prepared_workspace']!=config['prepared_workspace']:
   raise ValueError('The prepared workspace changed during refresh.')
  old_here,old_layout,old_binding=pinned_layout(previous['harness'])
  transition=previous.get('prepared_tool_transition',[])
  if transition and sorted(row.get('relative','') for row in transition)!=sorted(old_layout):
   raise ValueError('The predecessor transition differs from its pinned layout.')
  old_rows={row['relative']:row for row in transition}
  # Removed successor entries remain checked historical inputs.
  for relative,source in old_layout.items():
   target=owned_tool(config['prepared_workspace'],relative)
   row=old_rows.get(relative)
   if row and row.get('successor')!=binding(old_here/source):
    raise ValueError('The predecessor successor binding changed.')
   if row and row.get('prepared') is None:
    absent_tool(row,previous)
   else:
    expected=row['prepared'] if row else dict(binding(old_here/source),path=str(target))
    if expected.get('path')!=str(target) or binding(target)!=expected:
     raise ValueError('A previously required recovery tool is missing or changed.')
 result=[]
 for relative,source in layout.items():
  target=owned_tool(config['prepared_workspace'],relative)
  missing=previous is not None and (relative not in old_layout or old_rows.get(relative,{}).get('prepared','present') is None)
  row={'relative':relative,'successor':binding(here/source)}
  if missing:
   if target.exists() or target.is_symlink():raise ValueError('A new recovery tool already occupies its absent destination.')
   row.update(prepared=None,absent={'schema':'prepared-tool.absent.v1','path':str(target),
     'runtime':prior_runtime,'harness':previous['harness'],'layout':old_binding})
   absent_tool(row,config)
  else:row['prepared']=binding(target)
  result.append(row)
 return result


def install_absent(source, target):
 # Publish without replacing a destination that appeared after the absence check.
 descriptor,name=tempfile.mkstemp(prefix='.new-tool-',dir=target.parent);os.close(descriptor)
 temporary=Path(name)
 try:
  clone_copy.copy2(source,temporary)
  os.link(temporary,target)
 finally:temporary.unlink(missing_ok=True)


def install_restart_tools(workspace,config,here):
 here=Path(here);from harness_commit import check
 check(config['harness'])
 if Path(workspace)==Path(config['prepared_workspace']) and any(item.get('prepared') is None for item in config.get('prepared_tool_transition',[])):
  raise ValueError('An absent recovery tool cannot change the prepared workspace.')
 layout=json.loads((here/'TOOL-LAYOUT.json').read_text())
 rows={'files':[binding(here/source) for source in layout.values()],
       'relative_paths':{str((here/source).resolve()):target for target,source in layout.items()},
       'claim_helpers':[binding(here/'code/entry_admission'/name) for name in ['claims.py','io_helpers.py']] + [binding(here/'code/admission_memory.py')]}
 records=[]
 for row in rows['files']:
  source=Path(row['path']);relative=rows.get('relative_paths',{}).get(row['path'],source.name)
  if Path(relative).is_absolute() or '..' in Path(relative).parts:raise ValueError('A recovery tool path escapes the owned tools directory.')
  target=owned_tool(workspace,relative);before=binding(target) if target.exists() else None
  absent=[item for item in config.get('prepared_tool_transition',[]) if item.get('relative')==relative and item.get('prepared') is None]
  target.parent.mkdir(parents=True,exist_ok=True)
  if absent:
   if len(absent)!=1:raise ValueError('An absent recovery tool has duplicate transitions.')
   absent_tool(absent[0],config)
   if target.exists() or target.is_symlink():raise ValueError('An absent recovery tool appeared in the new job.')
   install_absent(source,target)
  else:clone_copy.copy2(source,target)
  if binding(target)['sha256']!=row['sha256'] or target.stat().st_ino==source.stat().st_ino:raise ValueError('A recovery copy changed or shares its source inode.')
  records.append({'previous':before,'source':row,'owned':binding(target),'distinct_inode':True})
 guard=binding(here/'runtime-tools/resource_guard.sh')
 config['guard_override_base']=guard;config['guard_override']=guard
 config['admission']=dict(config['admission'],reviewed_helpers=str(here/'code/entry_admission'))
 config['aggregate_memory_ceiling_bytes']=64*1024**3
 config['client_PET_compiler_memory_ceiling_bytes']=64*1024**3
 return {'harness':config['harness'],'copies':records,'canonical_helpers':rows['claim_helpers'],'proof_started':False}


def verify_restart_runtime(config,here):
 here=Path(here);from harness_commit import check
 check(config['harness'])
 layout=json.loads((here/'TOOL-LAYOUT.json').read_text())
 manifest={'files':[binding(here/source) for source in layout.values()],
           'relative_paths':{str((here/source).resolve()):target for target,source in layout.items()}}
 if config.get('adoption_implementation')!=binding(here/'code/full_chain.py'):
  raise ValueError('The runtime lacks the clone-only completed-prefix helper.')
 expected=binding(here/'runtime-tools/resource_guard.sh')
 if config.get('guard_override')!=expected or config.get('guard_override_base')!=expected:
  raise ValueError('The runtime does not bind the corrected shared-parent guard.')
 if config.get('job_controller')!=binding(here/'code/entry_chain_run.py'):
  raise ValueError('The runtime does not bind the corrected shared controller.')
 if config.get('admission',{}).get('reviewed_helpers')!=str(here/'code/entry_admission'):
  raise ValueError('The runtime does not bind the corrected canonical claim helper.')
 transition=config.get('prepared_tool_transition',[])
 expected_relatives=[manifest.get('relative_paths',{}).get(row['path'],Path(row['path']).name) for row in manifest['files']]
 if transition and sorted(item.get('relative','') for item in transition)!=sorted(expected_relatives):
  raise ValueError('A prepared tool transition differs from the exact successor list.')
 for row in manifest['files']:
  relative=manifest.get('relative_paths',{}).get(row['path'],Path(row['path']).name)
  if Path(relative).is_absolute() or '..' in Path(relative).parts:raise ValueError('A recovery tool path escapes the owned tools directory.')
  owned=owned_tool(config['prepared_workspace'],relative)
  transition=config.get('prepared_tool_transition',[])
  candidates=[item for item in transition if item.get('relative')==relative]
  if transition and len(candidates)!=1:raise ValueError('A prepared tool lacks one exact successor binding.')
  expected=candidates[0]['prepared'] if candidates else row
  if candidates and (candidates[0]['successor']!=row or (expected is not None and expected['path']!=str(owned))):
   raise ValueError('A prepared tool transition names another source or destination.')
  if candidates and expected is None:
   absent_tool(candidates[0],config)
   continue
  if binding(row['path'])!=row or binding(owned)['sha256']!=expected['sha256']:
   raise ValueError('The runtime contains stale or changed recovery tooling.')
 if config.get('aggregate_memory_ceiling_bytes')!=64*1024**3:
  raise ValueError('The runtime declares another aggregate memory ceiling.')
 from native_route import validate_prerequisite_order
 validate_prerequisite_order(config)
 from memory_policy import validate_job
 for row in config.get('jobs',[]):validate_job(row)
 if config.get('cache_attempt',{}).get('limits',{}).get('memory_bytes')!=64*1024**3:
  raise ValueError('The runtime cache policy has another physical fence.')
 return True
