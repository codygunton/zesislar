"""Check owned seed copies through one shared manifest and exact cell deltas."""
from pathlib import Path,PurePosixPath
import hashlib,json
from runtime_ignores import excluded

SCHEMA='scratch.shared-seed-bindings.v1'


def installation_path(path):
    path=Path(path).absolute();resolved=path.resolve()
    roots=[Path(value) for value in ['/home/cody/islaris/_opam',
        '/home/cody/.local/share/uv/tools/rocq-mcp','/home/cody/.local/share/uv/python',
        '/usr','/lib','/lib64','/bin','/sbin']]
    return any(path.is_relative_to(root) for root in roots) and any(resolved.is_relative_to(root.resolve()) for root in roots)


def mutable_execution(path):
    parts=Path(path).parts
    return Path(path).suffix in {'.py','.so'} and any(
        parts[index]=='site-packages' and parts[index+1] in {'rocq_mcp','pytanque'}
        for index in range(len(parts)-1))


def digest(path):
    with Path(path).open('rb') as stream:return hashlib.file_digest(stream,'sha256').hexdigest()


def bound(row):
    path=Path(row['path'])
    if digest(path)!=row['sha256']:raise ValueError('A shared seed binding changed: '+str(path))
    return path


def read(row):return json.loads(bound(row).read_text())


def seal(binding,output,collection=None,context=None):
    """Verify one ordered manifest and freeze distinct-inode project clones."""
    import clone_copy,os
    output=Path(output)
    if output.exists():raise ValueError('The sealed seed output already exists.')
    value=descriptor(binding);rows=inventory(value);source=Path(value['prepared_workspace'])
    runtime=read(value['seed_runtime'])
    output.mkdir(parents=True);workspace=output/'prepared';workspace.mkdir()
    for name,sha in sorted(rows.items()):
        original=source/name;target=workspace/name
        if digest(original)!=sha:raise ValueError('A seed input changed before sealing: '+name)
        target.parent.mkdir(parents=True,exist_ok=True);clone_copy.copy2(original,target)
        if digest(target)!=sha or target.stat().st_ino==original.stat().st_ino:
            raise ValueError('A sealed clone differs or shares its source inode.')
        target.chmod(target.stat().st_mode & ~0o222)
    for link in value['symlinks']:
        target=workspace/relative(link['relative']);target.parent.mkdir(parents=True,exist_ok=True)
        target.symlink_to(link['target'])
        if not target.resolve().is_relative_to(workspace.resolve()):raise ValueError('A sealed alias escapes.')
    def bind(path):return {'path':str(path.resolve()),'sha256':digest(path)}
    ordered=output/'FILES.jsonl'
    ordered_rows=[]
    for name,sha in sorted(rows.items()):
        info=(workspace/name).stat()
        ordered_rows.append({'relative':name,'sha256':sha,'device':info.st_dev,'inode':info.st_ino,
            'size':info.st_size,'mtime_ns':info.st_mtime_ns,'ctime_ns':info.st_ctime_ns,'mode':info.st_mode})
    ordered.write_text(''.join(json.dumps(row)+'\n' for row in ordered_rows))
    external=[]
    for row in value['external_bindings']:
        if excluded(row['path']):continue
        bound(row);external.append({'path':row['path'],'sha256':row['sha256']})
    if collection:
        report=read(collection)
        import proof_cache_key as keys
        declared={row['id']:{key:row[key] for key in ['id','kind','sha256']} for row in report['input']['files']}
        keys.recipe(report['input']['recipe'],declared,keys.roots_by_role(report['input']['roots']))
        old_workspace=next(Path(row['path']) for row in report['input']['roots'] if row['role']=='workspace')
        for row in report['input']['files']:
            path=Path(row['path'])
            if excluded(path) or path.is_relative_to(old_workspace):continue
            if digest(path)!=row['sha256']:raise ValueError('A shared collector input changed before sealing: '+str(path))
            external.append({'path':str(path),'sha256':row['sha256']})
    if context:
        selected=read(context)
        if selected.get('native_route'):
            from native_route import input_bindings
            for row in input_bindings(selected['native_route']):
                bound(row);external.append({'path':row['path'],'sha256':row['sha256']})
    exact={}
    for row in external:
        if row['path'] in exact and exact[row['path']]!=row['sha256']:raise ValueError('The sealed external inventory has conflicting hashes.')
        exact[row['path']]=row['sha256']
    external=[{'path':name,'sha256':sha} for name,sha in exact.items()]
    externals=output/'EXTERNAL-FILES.json';externals.write_text(json.dumps(external,sort_keys=True)+'\n')
    runtime['prepared_workspace']=str(workspace.resolve())
    runtime['physical_flags']=[word.replace(str(source),str(workspace.resolve())) for word in runtime['physical_flags']]
    from rocq_mcp.server import _parse_project_flags
    runtime['expected_mcp_flags']=_parse_project_flags(workspace)
    runtime['end_of_run_cleanup']={'enabled':False}
    provenance=value['seed_runtime']
    semantic=[]
    for field in ['job_controller','scratch_provider','result_adapter','guard_override','guard_override_base',
                  'adoption_implementation','cache_import_graph','dependency_resolution_cache','admission_profile',
                  'control_session','declaration_checks','source_overrides','cache_producer_files','readiness']:
        if field in runtime:semantic.extend(field_bindings(runtime[field]))
    explicit={row['path']:row for row in value['external_bindings']+semantic if not excluded(row['path'])}
    runtime['bindings']=list(explicit.values())
    runtime['sealed_provenance_runtime']=provenance
    seed_runtime=output/'RUNTIME.json';seed_runtime.write_text(json.dumps(runtime,indent=2)+'\n')
    value['seed_runtime']=bind(seed_runtime)
    receipt=output/'SEAL.json'
    receipt.write_text(json.dumps({'schema':'scratch.sealed-seed.v1','workspace':str(workspace.resolve()),
        'inventory':bind(ordered),'seed_runtime':value['seed_runtime'],'read_only':True,'verified_once':True,
        'provenance_runtime':provenance,'context':context,
        'file_count':len(rows),'collection':collection,'external_inventory':bind(externals),
        'external_file_count':len(external),'clone':'FICLONE; distinct inodes; no full-copy fallback'},indent=2)+'\n')
    value.update(prepared_workspace=str(workspace.resolve()),inventory=bind(ordered),sealed_boundary=bind(receipt))
    reference=output/'REFERENCE.json';reference.write_text(json.dumps(value,indent=2)+'\n')
    for path in [ordered,externals,receipt,reference,seed_runtime]:path.chmod(0o444)
    return bind(reference)


def clone_owned(binding,workspace):
    """Clone the sealed bytes without reading each file's contents again."""
    import fcntl,os,shutil
    value=descriptor(binding)
    if not value.get('sealed_boundary'):raise ValueError('A trusted clone requires a sealed seed.')
    source=Path(value['prepared_workspace']);workspace=Path(workspace)
    if workspace.exists():raise ValueError('A trusted clone destination already exists.')
    workspace.mkdir(parents=True)
    if source.stat().st_dev!=workspace.stat().st_dev:raise ValueError('A trusted clone cannot cross filesystems.')
    for line in bound(value['inventory']).read_text().splitlines():
        row=json.loads(line);name=relative(row['relative'])
        if excluded(name):continue
        original=source/name;before=original.stat()
        actual=(before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns,before.st_mode)
        expected=tuple(row[key] for key in ['device','inode','size','mtime_ns','ctime_ns','mode'])
        if actual!=expected or before.st_mode&0o222:raise ValueError('A sealed clone source lost its frozen identity.')
        target=workspace/name;target.parent.mkdir(parents=True,exist_ok=True)
        with original.open('rb') as old,target.open('xb') as new:fcntl.ioctl(new.fileno(),0x40049409,old.fileno())
        shutil.copystat(original,target)
        after=original.stat()
        if (after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns,after.st_mode)!=expected:
            raise ValueError('A sealed clone source changed during cloning.')
        if target.stat().st_ino==before.st_ino or target.stat().st_size!=before.st_size:
            raise ValueError('A trusted clone shares an inode or changed its size.')
    for link in value['symlinks']:
        target=workspace/relative(link['relative']);target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(link['target'])
        if not target.resolve().is_relative_to(workspace.resolve()):raise ValueError('A trusted clone alias escapes.')


def relative(value):
    path=PurePosixPath(value)
    if path.is_absolute() or '..' in path.parts or not path.parts or str(path)=='.':raise ValueError('A seed binding escapes its owned root.')
    return str(path)


def capture_inventory(records):
    rows={}
    for row in records:
        name=relative(row['relative'])
        if excluded(name):continue
        if name in rows:raise ValueError('The shared seed repeats a file.')
        rows[name]=row['sha256']
    return rows


def inventory(descriptor):
    return capture_inventory(json.loads(line) for line in bound(descriptor['inventory']).read_text().splitlines())


def compact_collection(spec,reference):
    """Replace only exact sealed identities with the one manifest dependency."""
    from copy import deepcopy
    value=descriptor(reference['descriptor'])
    if not value.get('sealed_boundary'):raise ValueError('A fast collection requires a sealed seed.')
    seal=read(value['sealed_boundary']);base=inventory(value)
    external={row['path']:row['sha256'] for row in read(seal['external_inventory'])
              if installation_path(row['path']) and not mutable_execution(row['path'])}
    delta={row['relative'] for row in reference['deltas']};workspace=Path(reference['workspace'])
    spec=deepcopy(spec);replaced=set();kept=[]
    for row in spec['files']:
        path=Path(row['path']);covered=False
        if path.is_relative_to(workspace):
            name=path.relative_to(workspace).as_posix()
            if name in base and name not in delta and base[name]!=row['sha256']:
                raise ValueError('An unmodified sealed cell input has another hash.')
            covered=name not in delta and base.get(name)==row['sha256']
        elif path.is_relative_to(Path(value['prepared_workspace'])):
            name=path.relative_to(Path(value['prepared_workspace'])).as_posix()
            if name in base and base[name]!=row['sha256']:raise ValueError('A read-only sealed input has another hash.')
            covered=base.get(name)==row['sha256']
        else:
            if row['path'] in external and external[row['path']]!=row['sha256']:
                raise ValueError('A frozen external input has another hash.')
            covered=external.get(row['path'])==row['sha256']
        if row['id']==spec['recipe']['proof'] or row['id'].startswith('tool:'):covered=False
        if covered:replaced.add(row['id'])
        else:kept.append(row)
    name='sealed-shared-seed'
    if any(row['id']==name for row in kept):raise ValueError('The input repeats its sealed seed identity.')
    roots={row['role']:Path(row['path']) for row in spec['roots']};path=Path(reference['descriptor']['path'])
    role=max((len(root.parts),role) for role,root in roots.items() if path.is_relative_to(root))[1]
    kept.append(dict(reference['descriptor'],id=name,kind='configuration',root_role=role))
    def refs(values):return list(dict.fromkeys(name if item in replaced else item for item in values))
    recipe=spec['recipe'];nodes=[]
    for row in recipe['dependencies']:
        if row['id'] in replaced:continue
        nodes.append(dict(row,requires=refs(row['requires'])))
    nodes.append({'id':name,'requires':[]});recipe['dependencies']=nodes
    for row in recipe['producers']:
        for group in ['implementation','inputs','outputs']:row[group]=refs(row[group])
    for group,values in recipe['toolchain'].items():recipe['toolchain'][group]=refs(values)
    if seal.get('collection'):
        baseline=read(seal['collection'])
        for group,values in recipe['toolchain'].items():
            if not values and baseline['input']['recipe']['toolchain'][group]:recipe['toolchain'][group]=[name]
    recipe['backend']['files']=refs(recipe['backend']['files'])
    def transports(item):
        if isinstance(item,dict):
            if item.get('kind')=='transport':
                item['semantic_dependencies']=refs(item['semantic_dependencies'])
            for value in item.values():transports(value)
        elif isinstance(item,list):
            for value in item:transports(value)
    transports(recipe['configuration']) if 'configuration' in recipe else None
    recipe['backend'].setdefault('features',{})['sealed_shared_inventory']=True
    spec['files']=kept
    return spec


def descriptor(binding):
    value=read(binding)
    if value['schema']!=SCHEMA:raise ValueError('The seed binding schema is unsupported.')
    if value.get('sealed_boundary'):
        receipt=read(value['sealed_boundary'])
        if (receipt['schema']!='scratch.sealed-seed.v1' or receipt['inventory']!=value['inventory']
            or receipt['seed_runtime']!=value['seed_runtime'] or receipt['workspace']!=value['prepared_workspace']
            or receipt['read_only'] is not True or receipt['verified_once'] is not True):
            raise ValueError('The sealed seed receipt differs from its descriptor.')
    else:bound(value['seed_runtime'])
    if value.get('protected_policy'):bound(value['protected_policy'])
    if value.get('capture_policy'):bound(value['capture_policy'])
    return value


def expected(reference):
    value=descriptor(reference['descriptor']);rows=inventory(value);seen=set()
    for name in reference['removed']:
        name=relative(name)
        if excluded(name):continue
        if name in seen or name not in rows:raise ValueError('An omitted seed file repeats or is unknown.')
        seen.add(name);del rows[name]
    for row in reference['deltas']:
        name=relative(row['relative'])
        if excluded(name):continue
        if name in seen:raise ValueError('A seed delta repeats or conflicts with an omission.')
        seen.add(name);rows[name]=row['sha256']
    return value,rows


def validate(reference,expected_root=None):
    value=descriptor(reference['descriptor']);root=Path(reference['workspace'])
    if not root.is_absolute() or not root.is_dir() or root.is_symlink():raise ValueError('The seed copy lacks its owned root.')
    resolved_root=root.resolve()
    if expected_root is not None and resolved_root!=Path(expected_root).resolve():raise ValueError('The seed reference names another owned root.')
    for link in value['symlinks']:
        name=relative(link['relative'])
        if excluded(name):continue
        path=root/name
        if not path.is_symlink() or str(path.readlink())!=link['target'] or not path.resolve().is_relative_to(resolved_root):raise ValueError('An owned seed alias changed or escaped.')
    if value.get('sealed_boundary'):
        seen=set();rows={}
        for name in reference['removed']:
            name=relative(name)
            if name in seen:raise ValueError('A sealed seed omission repeats.')
            seen.add(name)
        for row in reference['deltas']:
            name=relative(row['relative'])
            if excluded(name):continue
            if name in seen:raise ValueError('A sealed seed delta repeats or conflicts.')
            seen.add(name);rows[name]=row['sha256']
    else:_,rows=expected(reference)
    for name,sha in rows.items():
        path=root/name
        if not path.resolve().is_relative_to(resolved_root) or path.is_symlink() or not path.is_file() or digest(path)!=sha:raise ValueError('An owned seed input changed: '+str(path))
    return {'shared_seed_files_checked':0 if value.get('sealed_boundary') else len(rows),
            'cell_delta_files_checked':len(rows) if value.get('sealed_boundary') else 0,
            'sealed_seed':value.get('sealed_boundary'),'seed_descriptor':reference['descriptor'],'owned_root':str(root)}


def field_bindings(value):
    result=[]
    if isinstance(value,dict):
        if isinstance(value.get('path'),str) and isinstance(value.get('sha256'),str):result.append({'path':value['path'],'sha256':value['sha256']})
        for key,item in value.items():
            if key not in {'bindings','seed_binding_reference'}:result.extend(field_bindings(item))
    elif isinstance(value,list):
        for item in value:result.extend(field_bindings(item))
    return result


def compact(runtime,binding,workspace):
    """Retain actual inputs. Encapsulate historical seed inventories once."""
    value=descriptor(binding);base=inventory(value);root=Path(workspace).resolve();seed_root=Path(value['prepared_workspace']).resolve()
    sealed_external={}
    if value.get('sealed_boundary'):
        seal=read(value['sealed_boundary'])
        sealed_rows=read(seal['external_inventory'])
        sealed_external={row['path']:row['sha256'] for row in sealed_rows
                         if installation_path(row['path']) and not mutable_execution(row['path'])}
    original_seed=read(value['seed_runtime']);inherited={}
    for row in original_seed['bindings']:
        if excluded(row['path']):continue
        if row['path'] in inherited and inherited[row['path']]!=row['sha256']:raise ValueError('The bound seed repeats a path with conflicting hashes.')
        inherited[row['path']]=row['sha256']
    seen_bindings=set()
    for row in runtime['bindings']:
        if excluded(row['path']):continue
        name=str(Path(row['path']).resolve())
        if name in seen_bindings:raise ValueError('The runtime repeats a binding: '+name)
        seen_bindings.add(name)
    semantic=[]
    for name in ['job_controller','scratch_provider','result_adapter','guard_override','guard_override_base','adoption_implementation','cache_import_graph','dependency_resolution_cache','admission_profile','control_session','declaration_checks','source_overrides','cache_producer_files','readiness']:
        if name in runtime:semantic.extend(field_bindings(runtime[name]))
    if runtime.get('native_route'):
        from native_route import input_bindings
        semantic.extend(input_bindings(runtime['native_route']))
    protected={row['path'] for row in semantic};owned={};explicit={}
    previous=runtime.get('seed_binding_reference')
    if previous and previous['descriptor']==binding and Path(previous['workspace']).resolve()==root:
        validate(previous,root)
        owned={row['relative']:row['sha256'] for row in previous['deltas'] if not excluded(row['relative'])}
    for row in runtime['bindings']+semantic:
        if excluded(row['path']):continue
        path=Path(row['path']);resolved=path.resolve()
        if resolved.is_relative_to(root):
            name=resolved.relative_to(root).as_posix()
            if name in owned and owned[name]!=row['sha256']:raise ValueError('Conflicting owned seed bindings.')
            owned[name]=row['sha256'];continue
        if value.get('sealed_boundary') and resolved.is_relative_to(seed_root):
            name=resolved.relative_to(seed_root).as_posix()
            if name in base:
                if row['sha256']!=base[name]:raise ValueError('A read-only seed binding has another hash.')
                continue
        if row['path'] in sealed_external:
            if row['sha256']!=sealed_external[row['path']]:raise ValueError('A sealed external binding has another hash.')
            continue
        if row['path'] in protected:explicit[row['path']]={'path':row['path'],'sha256':row['sha256']};continue
        if row['path'] in inherited:
            if row['sha256']!=inherited[row['path']]:raise ValueError('An inherited seed binding has another hash: '+row['path'])
            continue
        explicit[row['path']]={'path':row['path'],'sha256':row['sha256']}
    for row in value['external_bindings']:
        if excluded(row['path']):continue
        if row['path'] in sealed_external:
            if row['sha256']!=sealed_external[row['path']]:raise ValueError('A required sealed external binding has another hash.')
            continue
        if row['path'] in explicit and explicit[row['path']]['sha256']!=row['sha256']:raise ValueError('A required external seed input conflicts.')
        explicit[row['path']]=row
    if value.get('sealed_boundary'):
        for row in sealed_rows:
            if mutable_execution(row['path']):explicit[row['path']]=row
    allowed=set()
    modules=runtime.get('proof_runtime',runtime).get('module_files',{})
    target=(runtime.get('target') or {}).get('block') if isinstance(runtime.get('target'),dict) else None
    names=[target['module']] if target else [job['target']['module'] for job in runtime.get('jobs',[]) if job.get('target')]
    names+=runtime.get('ordered_modules',[])
    for job in runtime.get('jobs',[]):names+=job.get('ordered_modules',[])
    session=runtime.get('control_session')
    if session:
        module=session.get('module')
        if module not in modules:raise ValueError('The interactive control module has no source mapping.')
        source=Path(modules[module]);source=source.relative_to(root) if source.is_absolute() else source
        if source.as_posix() not in owned:raise ValueError('The interactive control source lacks an explicit binding.')
        names.append(module)
    for name in names:
        if name not in modules:continue
        stem=Path(modules[name])
        for suffix in ['.vo','.vos','.vok','.glob','.aux']:allowed.add(stem.with_suffix(suffix).as_posix())
    removed=[]
    for name in base:
        if not (root/name).is_file():
            if name not in allowed:raise ValueError('An undeclared seed input is absent: '+name)
            removed.append(name)
    deltas=[{'relative':name,'sha256':sha} for name,sha in sorted(owned.items())
            if base.get(name)!=sha or value.get('sealed_boundary')]
    runtime['seed_binding_reference']={'descriptor':binding,'workspace':str(root),'deltas':deltas,'removed':sorted(removed)}
    explicit[binding['path']]=binding
    runtime['bindings']=list(explicit.values())
    runtime['binding_compaction']={'seed_file_count':len(base),'explicit_binding_count':len(runtime['bindings']),'cell_delta_count':len(deltas),'omitted_declared_outputs':len(removed),'historical_inventory_repeated':False}
    return runtime
