"""Separate declared coordination tools from retained proof inputs."""
from pathlib import Path
import hashlib,json
_CLASSIFICATION = {}
from runtime_ignores import excluded as excluded_runtime_file
COORDINATION_ROLES=frozenset({'watcher','mailbox','status'})
PROOF_SUFFIXES=frozenset({'.v','.vo','.vos','.vok','.glob','.cmxs','.cma','.cmxa','.so'})
def coordination_rows(runtime):
    rows=[]
    if runtime.get('watcher'):rows.append(dict(runtime['watcher'],role='watcher'))
    rows.extend(runtime.get('coordination_bindings',[]))
    for row in rows:
        if set(row)!={'role','path','sha256'} or row['role'] not in COORDINATION_ROLES:
            raise ValueError('An unknown coordination-tool role cannot exclude a proof input.')
    return rows

def proof_rows(runtime):
    from binding_cache import resolve_input
    parents={}
    canonical=lambda path:str(resolve_input(path,parents))
    resolved=[canonical(row['path']) for row in runtime['bindings']]
    roles=coordination_rows(runtime)
    excluded={canonical(row['path']) for row in roles}
    protected={canonical(row['path']) for row in runtime.get('cache_producer_files',{}).get('implementation',[])}
    for field in ['job_controller','scratch_provider','result_adapter','guard_override','coqc_wrapper']:
        row=runtime.get(field)
        if isinstance(row,dict) and 'path' in row:protected.add(canonical(row['path']))
    identity={name:runtime.get(name) for name in ['bindings','coordination_bindings','watcher','cache_producer_files','job_controller','scratch_provider','result_adapter','guard_override','coqc_wrapper']}
    identity['resolved_paths']=resolved
    identity['excluded_paths']=sorted(excluded)
    identity['protected_paths']=sorted(protected)
    key=hashlib.sha256(json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).digest()
    if key in _CLASSIFICATION:return [dict(row) for row in _CLASSIFICATION[key]]
    result=[];seen=set()
    for row,path in zip(runtime['bindings'],resolved):
        if excluded_runtime_file(row['path']):continue
        if path in seen:raise ValueError('The runtime repeats a binding: '+path)
        seen.add(path)
        if path in excluded:
            if path in protected or Path(path).suffix in PROOF_SUFFIXES:
                raise ValueError('A coordination role names a proof or harness input.')
        else:result.append(row)
    _CLASSIFICATION.clear();_CLASSIFICATION[key]=[dict(row) for row in result]
    return result

def check_proof_bindings(runtime,force_full=False):
    from binding_cache import force_hashing
    with force_hashing(force_full):return _check_proof_bindings(runtime)

def _check_proof_bindings(runtime):
    from entry_chain import check_bindings
    seed_work={}
    if runtime.get('seed_binding_reference'):
        from seed_bindings import validate
        expected_root=runtime.get('prepared_workspace') or (str(Path(runtime['job_output'])/'workspace') if runtime.get('job_output') else None)
        if expected_root is None:raise ValueError('A seed reference lacks its runtime workspace.')
        seed_work=validate(runtime['seed_binding_reference'],expected_root)
    rows=proof_rows(runtime);check_bindings(rows)
    return {'proof_bindings_checked':len(rows),'coordination_tools_excluded':coordination_rows(runtime),**seed_work}
