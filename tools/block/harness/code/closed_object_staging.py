"""Install exact closed-origin outputs before the ordinary compatibility planner.

Copying an authenticated physical output does not grant bank compatibility.
The existing planner must check every migrated import before execution.
"""
from pathlib import Path
import json
import clone_copy
from entry_chain import binding,read_bound
from closed_compilation_origin import LABEL


def stage(config, workspace, modules):
 from object_import_migration import POLICY,origin,origin_context,batch
 workspace=Path(workspace).resolve();policy=json.loads(POLICY.read_text());pending=[]
 with batch():
  for module,reference in sorted(config.get('object_imports',{}).items()):
   migrated=read_bound(reference)
   kind=migrated.get('origin',{}).get('kind')
   if migrated.get('schema')!='entry-chain.object-import-migration.v1' or kind not in {LABEL,'individual-object-from-accepted-correctness-gate'}:continue
   if migrated.get('module')!=module or module not in modules:raise ValueError('A staged closed object names another module.')
   original=Path(migrated['source']['path']);obj=Path(migrated['object']['path']);old=Path(migrated['owned_workspace']).resolve();target=workspace/modules[module]
   if kind=='individual-object-from-accepted-correctness-gate':
    if not target.resolve().is_relative_to(workspace):raise ValueError('A gate output destination leaves its workspace.')
    if binding(target)['sha256']!=migrated['source']['sha256']:continue
    prior=origin_context(policy,migrated['origin'])
    accepted,_=origin(policy,migrated['origin']['publication'],module,original,obj,migrated['compiler'],prior['physical_flags'],old)
    if accepted!=migrated['origin'] or binding(obj)!=migrated['object'] or binding(original)!=migrated['source']:
     raise ValueError('An authenticated gate output changed.')
    publication=read_bound(accepted['publication'])
    row=next(row for row in publication['modules'] if row['module']==module)
    if target.resolve()!=workspace/row['target_relative']:raise ValueError('A gate destination changes its exact module mapping.')
    destination=target.with_suffix('.vo')
    if any(part.is_symlink() for part in [destination,*destination.parents] if part!=workspace and part.is_relative_to(workspace)):
     raise ValueError('A gate output destination contains a symlink.')
    if destination.exists() and binding(destination)['sha256']!=migrated['object']['sha256']:
     raise ValueError('A gate output destination contains different bytes.')
    pending.append((module,reference,migrated['object'],None,target));continue
   if not target.resolve().is_relative_to(workspace) or target.resolve().relative_to(workspace)!=original.resolve().relative_to(old):raise ValueError('A closed object staging path escapes or changes its module mapping.')
   # A changed source remains a planner rebuild; no old object enters that cell.
   if binding(target)['sha256']!=migrated['source']['sha256']:continue
   prior=origin_context(policy,migrated['origin'])
   accepted,_=origin(policy,migrated['origin']['publication'],module,original,obj,migrated['compiler'],prior['physical_flags'],old)
   if accepted!=migrated['origin']:raise ValueError('A staged closed object has another authenticated origin.')
   receipt=read_bound(accepted['original_receipts'][0]);physical=read_bound(receipt['physical_result'])
   if migrated['object']!=binding(obj) or migrated['source']!=binding(original) or migrated['object']!=receipt['object']:
    raise ValueError('A staged closed physical object changed.')
   sidecar=receipt.get('sidecar');status=receipt.get('sidecar_status')
   if receipt.get('publication'):
    outputs=read_bound(receipt['publication'])['published_outputs']
   else:outputs=physical['compiler_outputs']
   if (status!='compiled_output' or outputs.get('sidecar_status')!=status or outputs.get('sidecar')!=sidecar or
       not sidecar or sidecar['binding']!=binding(original.with_suffix('.vos'))):
    raise ValueError('A closed object sidecar lacks its matching physical output.')
   for incoming,suffix in [(migrated['object'],'.vo'),(sidecar['binding'],'.vos')]:
    destination=target.with_suffix(suffix)
    if any(part.is_symlink() for part in [destination,*destination.parents] if part!=workspace and part.is_relative_to(workspace)):
     raise ValueError('A closed output destination contains a symlink.')
    if destination.exists() and binding(destination)['sha256']!=incoming['sha256']:
     raise ValueError('A closed output destination contains different bytes.')
   pending.append((module,reference,migrated['object'],sidecar['binding'],target))
  copied=[]
  for module,reference,obj,sidecar,target in pending:
   for source,suffix in [(obj,'.vo')]+([(sidecar,'.vos')] if sidecar else []):
    if binding(source['path'])!=source:raise ValueError('An authenticated closed output changed before copying.')
    destination=target.with_suffix(suffix)
    if not destination.resolve().is_relative_to(workspace):raise ValueError('A closed output alias leaves its workspace.')
    if destination.exists():
     if binding(destination)['sha256']!=source['sha256']:raise ValueError('A closed output destination changed before copying.')
    else:clone_copy.copy2(source['path'],destination)
    if binding(destination)['sha256']!=source['sha256']:raise ValueError('A staged closed output differs from its physical bytes.')
   copied.append({'module':module,'migration':reference,'object':binding(target.with_suffix('.vo')),'sidecar':binding(target.with_suffix('.vos')) if sidecar else None})
 return {'schema':'scratch.closed-object-staging.v1','installed':copied,'count':len(copied),'compatibility_granted':False,'required_next_step':'Unchanged object_imports.compatibility and normal invalidation before execution.','compiler_calls':0}
