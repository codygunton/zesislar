"""Install exact recovery tooling before any new scratch runtime is bound."""
import clone_copy
from pathlib import Path
import hashlib, json, shutil

def binding(path):
 path=Path(path).resolve();return {'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

def install_restart_tools(workspace,config,here):
 here=Path(here);from harness_commit import check
 check(config['harness'])
 layout=json.loads((here/'TOOL-LAYOUT.json').read_text())
 rows={'files':[binding(here/source) for source in layout.values()],
       'relative_paths':{str((here/source).resolve()):target for target,source in layout.items()},
       'claim_helpers':[binding(here/'code/entry_admission'/name) for name in ['claims.py','io_helpers.py']]}
 records=[]
 for row in rows['files']:
  source=Path(row['path']);relative=rows.get('relative_paths',{}).get(row['path'],source.name)
  if Path(relative).is_absolute() or '..' in Path(relative).parts:raise ValueError('A recovery tool path escapes the owned tools directory.')
  target=Path(workspace)/'tools'/relative;before=binding(target) if target.exists() else None
  target.parent.mkdir(parents=True,exist_ok=True);clone_copy.copy2(source,target)
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
  owned=Path(config['prepared_workspace'])/'tools'/relative
  transition=config.get('prepared_tool_transition',[])
  candidates=[item for item in transition if item.get('relative')==relative]
  if transition and len(candidates)!=1:raise ValueError('A prepared tool lacks one exact successor binding.')
  expected=candidates[0]['prepared'] if candidates else row
  if candidates and (candidates[0]['successor']!=row or expected['path']!=str(owned)):
   raise ValueError('A prepared tool transition names another source or destination.')
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
