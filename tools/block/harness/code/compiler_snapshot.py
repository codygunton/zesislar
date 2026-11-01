"""Preserve full validation while sharing classified input identities with coqc."""
import hashlib
import hmac
import json
import os
from pathlib import Path
import stat
import tempfile
import secrets
import resource
import time

from binding_cache import identity, digest, force_hashing
from entry_chain import binding, read_bound

SCHEMA = 'entry-chain.compiler-validation.v1'


def binding_rows(runtime):
    reference = runtime.get('binding_inventory')
    if reference is None:
        return runtime['bindings']
    if 'bindings' in runtime:
        raise ValueError('The runtime repeats its binding inventory.')
    inventory = read_bound(reference)
    if not isinstance(inventory, dict) or set(inventory) != {'schema', 'bindings'} or inventory['schema'] != 'entry-chain.bindings.v1':
        raise ValueError('The runtime binding inventory is invalid.')
    return inventory['bindings']


def externalize(runtime, path):
    """Move every row to a bound file. Do not remove historical rows."""
    from entry_chain import save
    if 'binding_inventory' in runtime:
        raise ValueError('The runtime already has an external binding inventory.')
    save(path, {'schema': 'entry-chain.bindings.v1', 'bindings': runtime['bindings']})
    runtime['binding_inventory'] = binding(path)
    del runtime['bindings']


def declared_outputs(modules, order, workspace, inherited, *, donor=None):
    """Remove only output copies in a fresh owned declaration workspace."""
    if not order:return []
    workspace=Path(workspace).resolve()
    from binding_cache import resolve_input
    parents={}
    inherited_paths={str(resolve_input(row['path'],parents)) for row in inherited}
    plan=[]
    for module in order:
        relative=Path(modules[module])
        source=workspace/relative
        if relative.is_absolute() or '..' in relative.parts or not source.resolve().is_relative_to(workspace):
            raise ValueError('A declared compilation source leaves its owned workspace.')
        outputs=[source.with_suffix(ext) for ext in ['.vo','.vos','.vok','.glob','.aux']]
        outputs.append(source.with_name('.'+source.stem+'.aux'))
        for path in outputs:
            if path.is_symlink() or not path.resolve().is_relative_to(workspace):
                raise ValueError('A declared output alias leaves its owned workspace.')
            if str(path.resolve()) in inherited_paths:
                raise ValueError('A declared output is an inherited donor binding.')
            if donor is not None and workspace==Path(donor).resolve() and path.exists():
                raise ValueError('A declaration cannot remove an existing donor output.')
            if path.exists() and not path.is_file():
                raise ValueError('A declared output is not a regular file.')
        plan.append({'module':module,'source':binding(source),'object':str(source.with_suffix('.vo')),
                     'outputs':[str(path) for path in outputs]})
    # Validate every path before removing any copy.
    for row in plan:
        row['removed_copies']=[]
        for name in row['outputs']:
            path=Path(name)
            if path.exists():
                row['removed_copies'].append(_remove_output_copy(workspace,path))
    require_absent_outputs(plan)
    return plan


def _remove_output_copy(workspace,path):
    """Use directory descriptors so a parent alias cannot redirect deletion."""
    parts=path.relative_to(workspace).parts
    descriptor=os.open(workspace,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
    try:
        for part in parts[:-1]:
            child=os.open(part,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=descriptor)
            os.close(descriptor);descriptor=child
        selected=os.open(parts[-1],os.O_RDONLY|os.O_NOFOLLOW,dir_fd=descriptor)
        with os.fdopen(selected,'rb') as stream:
            before=os.fstat(stream.fileno())
            if not stat.S_ISREG(before.st_mode):raise ValueError('A declared output copy is not regular.')
            sha=hashlib.file_digest(stream,'sha256').hexdigest()
            if _fields(os.fstat(stream.fileno()))!=_fields(before):
                raise ValueError('A declared output changed during invalidation.')
        if _fields(os.stat(parts[-1],dir_fd=descriptor,follow_symlinks=False))!=_fields(before):
            raise ValueError('A declared output changed before invalidation.')
        os.unlink(parts[-1],dir_fd=descriptor)
        return {'path':str(path),'sha256':sha}
    finally:
        os.close(descriptor)


def require_absent_outputs(rows):
    for row in rows:
        for name in row['outputs']:
            path=Path(name)
            if path.exists() or path.is_symlink():
                raise ValueError('A declared compiler output exists before snapshot publication: '+name)


def _identity(path):
    return [list(part) for part in identity(Path(path))]


def _fields(info):
    return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns,
            info.st_ctime_ns, info.st_mode)


def _namespace(path):
    """Bind aliases without treating new directory entries as input mutation."""
    path = Path(path).absolute()
    rows = []
    for part in [*reversed(path.parents), path]:
        try:
            first, target = identity(part)
            compact = lambda value: [value[0], value[1], value[-1]] if stat.S_ISDIR(value[-1]) else list(value)
            value = [compact(first), compact(target), str(part.resolve())]
        except FileNotFoundError:
            value = None
        rows.append([str(part), value])
    return rows


def mapping_context(flags):
    roots = []
    index = 0
    while index < len(flags):
        flag = flags[index]
        if flag in {'-Q', '-R', '-I', '-coqlib'}:
            if index + 1 >= len(flags):
                raise ValueError('A physical compiler load path is incomplete.')
            roots.append({'path': str(Path(flags[index + 1]).absolute()),
                          'namespace': _namespace(flags[index + 1])})
            index += 3 if flag in {'-Q', '-R'} else 2
        else:
            index += 1
    return roots


def _private(info):
    return stat.S_ISREG(info.st_mode) and info.st_uid == os.getuid() and stat.S_IMODE(info.st_mode) == 0o600 and info.st_nlink == 1


def _publish(path, value, *, replace=False):
    path = Path(path)
    descriptor, temporary = tempfile.mkstemp(prefix='.compiler-validation-', dir=path.parent)
    try:
        with os.fdopen(descriptor, 'w') as stream:
            json.dump(value, stream, separators=(',', ':'), allow_nan=False)
            stream.flush()
            os.fsync(stream.fileno())
        if replace:
            os.replace(temporary, path)
        else:
            # Do not replace another session's snapshot.
            os.link(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)
    return binding(path)


def publish(runtime, validate, path, *, compiler='/home/cody/islaris/_opam/bin/coqc', environment=None):
    """Seal identities only when forced full validation spans unchanged files."""
    from proof_bindings import proof_rows
    if runtime.get('seed_binding_reference') or not runtime.get('physical_compiler'):
        # Seed validation consults additional descriptor files. Keep that path full.
        validate()
        return None
    rows = [dict(path=row['path'],sha256=row['sha256']) for row in proof_rows(runtime)]
    if runtime.get('binding_inventory'):
        rows = [*rows, runtime['binding_inventory']]
    rows.append({'path':runtime['runtime_path'],'sha256':runtime['runtime_sha256']})
    require_absent_outputs(runtime.get('declared_outputs',[]))
    compiler=Path(compiler).absolute()
    compiler_stamp=_identity(compiler)
    with force_hashing(True):
        compiler_sha=digest(compiler)
    if compiler_sha!=runtime['physical_compiler']['sha256'] or compiler.resolve()!=Path(runtime['physical_compiler']['path']).resolve():
        raise ValueError('The selected compiler differs from its bound physical identity.')
    environment=dict(os.environ if environment is None else environment)
    context=physical_context(compiler,runtime['physical_flags'],environment)
    before=[_identity(row['path']) for row in rows]
    bound_identities={tuple(value[1]) for value in before}
    initial=load_files(compiler,runtime['physical_flags'],environment)
    plugins=[]
    objects=[]
    with force_hashing(True):
        for selected in initial:
            stamp=_identity(selected)
            if tuple(stamp[1]) not in bound_identities:
                target=plugins if selected.suffix in PLUGINS else objects
                target.append({'path':str(selected),'sha256':digest(selected),'identity':stamp})
    validate()
    require_absent_outputs(runtime.get('declared_outputs',[]))
    if physical_context(compiler,runtime['physical_flags'],environment) != context or load_files(compiler,runtime['physical_flags'],environment)!=initial:
        raise ValueError('A compiler mapping changed during full validation.')
    for row, expected in zip(rows, before):
        if _identity(row['path']) != expected:
            raise ValueError('A compiler input changed during full validation: ' + row['path'])
    if _identity(compiler)!=compiler_stamp:
        raise ValueError('The selected compiler changed during full validation.')
    for row in plugins:
        if _identity(row['path'])!=row['identity']:
            raise ValueError('An initial plugin changed during full validation.')
    for row in objects:
        if _identity(row['path'])!=row['identity']:
            raise ValueError('An initial object changed during full validation.')
    return _publish(path, {'schema': SCHEMA,
        'runtime': {'path': runtime['runtime_path'], 'sha256': runtime['runtime_sha256']},
        'compiler':{'path':str(compiler),'sha256':compiler_sha,'identity':compiler_stamp},
        'mapping_context': context,'initial_plugins':plugins,'initial_objects':objects,'load_path_files':[str(p) for p in initial],
        'producer': producer(), 'objects': str(Path(path).parent / 'validated-objects'),
        'rows': [dict(row, identity=selected) for row, selected in zip(rows, before)]})


def _read_private(reference, *, with_binding=False):
    path = Path(reference['path'])
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(descriptor, 'rb') as stream:
        before = os.fstat(stream.fileno())
        if not _private(before):
            raise ValueError('The compiler snapshot is not a private regular file.')
        payload = stream.read()
        if _fields(os.fstat(stream.fileno())) != _fields(before) or _fields(path.lstat()) != _fields(before):
            raise ValueError('The compiler snapshot changed during reading.')
    if reference.get('sha256') is not None and hashlib.sha256(payload).hexdigest() != reference['sha256']:
        raise ValueError('The compiler snapshot hash differs.')
    from entry_chain import strict_loads
    value = strict_loads(payload.decode())
    if with_binding:
        return value, {'path': str(path), 'sha256': hashlib.sha256(payload).hexdigest()}
    return value


def read(reference, runtime_reference):
    """Authenticate the immutable snapshot before consulting any cached identity."""
    value = _read_private(reference)
    required={'schema', 'runtime', 'producer', 'objects', 'mapping_context', 'compiler', 'initial_plugins', 'load_path_files', 'rows'}
    if not isinstance(value, dict) or not required <= set(value) or set(value)-required-{'initial_objects'} or value['schema'] != SCHEMA or value['runtime'] != runtime_reference:
        raise ValueError('The compiler snapshot names another runtime.')
    if _identity(value['compiler']['path'])!=value['compiler']['identity']:
        raise ValueError('The selected compiler identity changed.')
    for row in value['mapping_context']['paths']:
        if _namespace(row['path']) != row['namespace']:
            raise ValueError('A compiler mapping namespace changed.')
    if not all(isinstance(value.get(name,[]),list) for name in ['rows','initial_plugins','initial_objects']):
        raise ValueError('The compiler snapshot rows are invalid.')
    seen = set()
    for row in value['rows']+value['initial_plugins']+value.get('initial_objects',[]):
        if not isinstance(row, dict) or set(row) != {'path', 'sha256', 'identity'} or row['path'] in seen:
            raise ValueError('The compiler snapshot repeats or changes a classified row.')
        seen.add(row['path'])
        if _identity(row['path']) != row['identity']:
            raise ValueError('A compiler input identity changed: ' + row['path'])
    return value


def producer():
    from check_entry_outside import ticks
    return {'pid': os.getpid(), 'startticks': ticks(os.getpid()), 'uid': os.getuid()}


def _encoded(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()


def output_artifact(path):
    """Bind one completed regular output, including its lexical namespace."""
    path=Path(path).absolute()
    if path.is_symlink() or not path.is_file():
        raise ValueError('A compiler output is missing or is not a regular file.')
    selected=_identity(path);namespace=_namespace(path);canonical=str(path.resolve())
    with force_hashing(True):row=binding(path)
    if (_identity(path)!=selected or _namespace(path)!=namespace or
            str(path.resolve())!=canonical):
        raise ValueError('A compiler output changed during hashing.')
    return {'binding':row,'lexical_path':str(path),'canonical_path':canonical,
            'identity':selected,'namespace':namespace}


def sidecar_prestate(source, obj, compiler, flags, report):
    """Permit absence or this run's authenticated sibling output only."""
    obj=Path(obj).absolute();path=obj.with_suffix('.vos')
    result={'source':source,'compiler':compiler,'physical_flags':list(flags),
            'snapshot':report['snapshot'],'producer':report['producer'],
            'primary_object':str(obj.resolve()),'path':str(path),
            'namespace':_namespace(path),'state':'absent','prior_receipt':None,'output':None}
    if path.exists() or path.is_symlink():
        current=output_artifact(path)
        candidates=[row for row in report['accepted_dependency_identities']
                    if row.get('kind')=='vos' and row['source']==source and
                    row['primary_object']==result['primary_object'] and
                    row['canonical_path']==current['canonical_path'] and
                    row['identity']==current['identity'] and row['sha256']==current['binding']['sha256']]
        if len(candidates)!=1:
            raise ValueError('A preexisting compiler sidecar lacks this run\'s exact receipt.')
        result.update(state='retained_authenticated_output',prior_receipt=candidates[0]['receipt'],output=current)
    check_sidecar_prestate(result)
    return result


def check_sidecar_prestate(value):
    """Recheck immediately before coqc. Never remove an existing sidecar."""
    path=Path(value['path'])
    if value['state']=='absent':
        if path.exists() or path.is_symlink() or _namespace(path)!=value['namespace']:
            raise ValueError('A compiler sidecar appeared before physical compilation.')
    elif value['state']=='retained_authenticated_output':
        _read_private(value['prior_receipt'])
        if output_artifact(path)!=value['output'] or _namespace(path)!=value['namespace']:
            raise ValueError('An authenticated compiler sidecar changed before compilation.')
    else:raise ValueError('The compiler sidecar pre-state is invalid.')


def compiler_outputs(obj, before):
    primary=output_artifact(obj);sidecar=output_artifact(Path(obj).with_suffix('.vos'))
    status=('retained_authenticated_output' if before['state']=='retained_authenticated_output'
            and sidecar==before['output'] else 'compiled_output')
    return {'object':primary,'sidecar':sidecar,'sidecar_status':status}


def _physical_record(reference, snapshot, snapshot_reference, source, compiler, flags, obj, prior):
    """Authenticate the completed wrapper record before sealing its outputs."""
    record=_read_private(reference)
    input_reference=record['input'];inputs=_read_private(input_reference)
    directory=Path(reference['path']).parent
    runtime=read_bound(snapshot['runtime'])
    job=Path(runtime.get('job_output',Path(snapshot['runtime']['path']).parent))
    if (Path(reference['path']).name!='PHYSICAL-RESULT.json' or
            Path(input_reference['path'])!=directory/'INPUT.json' or
            directory.parent!=job/'compiler-invocations' or directory.resolve()!=directory or
            record.get('returncode')!=0 or record.get('output_capture',{}).get('complete') is not True or
            record.get('output_validation',{}).get('success') is not True or
            inputs.get('source')!=source or inputs.get('compiler')!=compiler or
            inputs.get('validation')!={'runtime':snapshot['runtime'],'snapshot':snapshot_reference} or
            inputs.get('physical_argv')!=[compiler['path'],*flags,source['path']] or
            record.get('physical_argv')!=inputs['physical_argv']):
        raise ValueError('A successful physical compiler record differs from this run.')
    before=inputs.get('sidecar_prestate');outputs=record.get('compiler_outputs')
    if (not isinstance(before,dict) or not isinstance(outputs,dict) or
            before.get('source')!=source or before.get('compiler')!=compiler or
            before.get('physical_flags')!=flags or before.get('snapshot')!=snapshot_reference or
            before.get('producer')!=snapshot['producer'] or
            obj['path']!=str(Path(source['path']).with_suffix('.vo')) or
            before.get('primary_object')!=obj['path'] or
            before.get('path')!=str(Path(obj['path']).with_suffix('.vos')) or
            outputs['object']['binding']!=obj or
            outputs['sidecar']['binding']['path']!=str(Path(obj['path']).with_suffix('.vos')) or
            outputs['sidecar'].get('lexical_path')!=before.get('path')):
        raise ValueError('The physical compiler sidecar context differs.')
    if before.get('state')=='absent':
        namespace=before.get('namespace')
        if (before.get('prior_receipt') is not None or before.get('output') is not None or
                not isinstance(namespace,list) or not namespace or namespace[-1]!=[before['path'],None]):
            raise ValueError('An absent sidecar claims prior authentication.')
    elif before.get('state')=='retained_authenticated_output':
        if before.get('prior_receipt') not in prior:
            raise ValueError('The compiler sidecar names an unknown prior receipt.')
        previous=_read_private(before['prior_receipt'])
        if (previous.get('source')!=source or previous.get('compiler')!=compiler or
                previous.get('normalized_flags')!=flags or previous.get('producer')!=snapshot['producer'] or
                previous.get('snapshot')!=snapshot_reference or previous.get('sidecar')!=before.get('output') or
                before.get('namespace')!=before['output']['namespace']):
            raise ValueError('The retained sidecar differs from its authenticated receipt.')
    else:raise ValueError('The physical compiler sidecar pre-state is invalid.')
    retained=before['state']=='retained_authenticated_output' and outputs['sidecar']==before['output']
    expected='retained_authenticated_output' if retained else 'compiled_output'
    if outputs.get('sidecar_status')!=expected:
        raise ValueError('The physical compiler sidecar status differs.')
    return outputs,before


class OutputReceipts:
    """Authenticate only objects accepted after successful provider checks."""
    def __init__(self, snapshot, reference, key=None):
        self.snapshot = snapshot
        self.reference = reference
        self.key = key or secrets.token_hex(32)
        self.rows = []
        self.physical=[]
        self.root = Path(snapshot['objects'])
        self.root.mkdir(mode=0o700)
        self._write_index()

    def _write_index(self):
        index = {'schema': 'entry-chain.accepted-objects.v1',
                 'runtime': self.snapshot['runtime'], 'producer': self.snapshot['producer'],
                 'snapshot': self.reference, 'receipts': self.rows}
        mac = hmac.new(bytes.fromhex(self.key), _encoded(index), 'sha256').hexdigest()
        value = {'index': index, 'mac': mac}
        _publish(self.root / ('INDEX-%06d.json' % len(self.rows)), value)
        _publish(self.root / 'INDEX.json', value, replace=True)

    def accept(self, source, obj, compiler, flags, result, *, physical_result=None):
        if result.get('success') is not True:
            raise ValueError('A failed compilation cannot publish an accepted object.')
        if producer() != self.snapshot['producer']:
            raise ValueError('Another producer cannot publish an accepted object.')
        lexical=Path(obj).absolute()
        object_identity=_identity(lexical)
        object_namespace=_namespace(lexical)
        canonical=str(lexical.resolve())
        with force_hashing(True):
            receipt = {'runtime': self.snapshot['runtime'], 'producer': self.snapshot['producer'],
                       'snapshot': self.reference,
                       'source': binding(source), 'object': binding(obj),
                       'object_lexical_path':str(lexical),'object_canonical_path':canonical,
                       'object_identity':object_identity,'object_namespace':object_namespace,
                       'compiler': binding(compiler), 'normalized_flags': list(flags),
                       'successful_compilation': True, 'tool_result': result}
        if physical_result is None:
            runtime=read_bound(self.snapshot['runtime'])
            job=Path(runtime.get('job_output',Path(self.snapshot['runtime']['path']).parent))
            candidates=[]
            for path in (job/'compiler-invocations').glob('*/PHYSICAL-RESULT.json'):
                reference=binding(path)
                if reference in self.physical:continue
                physical=_read_private(reference)
                inputs=_read_private(physical['input'])
                if inputs.get('source')==receipt['source']:candidates.append(reference)
            if len(candidates)!=1:raise ValueError('The accepted output lacks one fresh physical compiler record.')
            physical_result=candidates[0]
        if physical_result in self.physical:raise ValueError('A physical compiler record was already accepted.')
        outputs,before=_physical_record(physical_result,self.snapshot,self.reference,
            receipt['source'],receipt['compiler'],list(flags),receipt['object'],self.rows)
        if output_artifact(obj)!=outputs['object'] or output_artifact(Path(obj).with_suffix('.vos'))!=outputs['sidecar']:
            raise ValueError('A compiler output changed after its physical record.')
        receipt.update(physical_result=physical_result,sidecar=outputs['sidecar'],sidecar_prestate=before,
                       sidecar_status=outputs['sidecar_status'])
        if (_identity(lexical)!=object_identity or _namespace(lexical)!=object_namespace
                or str(lexical.resolve())!=canonical):
            raise ValueError('An accepted object changed during receipt publication.')
        reference = _publish(self.root / ('OBJECT-%06d.json' % len(self.rows)), receipt)
        self.rows.append(reference)
        self._write_index()
        self.physical.append(physical_result)
        return reference


def accepted_objects(snapshot, reference, key, compiler, flags):
    """Check the authenticated receipt index before accepting a later object."""
    root = Path(snapshot['objects'])
    info = root.lstat()
    if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid() or stat.S_IMODE(info.st_mode) != 0o700:
        raise ValueError('The accepted-object directory is not private.')
    value, index_binding = _read_private({'path': str(root / 'INDEX.json')}, with_binding=True)
    if not isinstance(value, dict) or set(value) != {'index', 'mac'}:
        raise ValueError('The accepted-object index is invalid.')
    index = value['index']
    expected = hmac.new(bytes.fromhex(key), _encoded(index), 'sha256').hexdigest()
    if not isinstance(value['mac'], str) or not hmac.compare_digest(expected, value['mac']):
        raise ValueError('The accepted-object index authentication differs.')
    if set(index) != {'schema', 'runtime', 'producer', 'snapshot', 'receipts'} or index['schema'] != 'entry-chain.accepted-objects.v1' or index['runtime'] != snapshot['runtime'] or index['snapshot'] != reference or index['producer'] != snapshot['producer']:
        raise ValueError('The accepted-object index names another producer or job.')
    expected_names = ['OBJECT-%06d.json' % number for number in range(len(index['receipts']))]
    if sorted(path.name for path in root.glob('OBJECT-*.json')) != expected_names:
        raise ValueError('The accepted-object index is stale or a receipt is absent.')
    version = {'path': str(root / ('INDEX-%06d.json' % len(index['receipts']))),
               'sha256': index_binding['sha256']}
    _read_private(version)
    rows = [];latest={};prior=[];physical_seen=[]
    for number, receipt_reference in enumerate(index['receipts']):
        if receipt_reference['path'] != str(root / ('OBJECT-%06d.json' % number)):
            raise ValueError('An accepted-object receipt leaves its exact directory.')
        receipt = _read_private(receipt_reference)
        if (receipt.get('snapshot') != reference or receipt.get('runtime') != snapshot['runtime'] or receipt.get('producer') != snapshot['producer'] or
                receipt.get('successful_compilation') is not True or receipt.get('tool_result', {}).get('success') is not True or
                receipt.get('normalized_flags') != flags or receipt.get('compiler') != compiler):
            raise ValueError('An accepted-object receipt differs from its producer or compiler.')
        if not all(name in receipt for name in ['object_lexical_path','object_canonical_path','object_identity','object_namespace']):
            raise ValueError('An accepted object lacks its exact identity or namespace.')
        if not isinstance(receipt.get('physical_result'),dict) or not isinstance(receipt.get('sidecar'),dict):
            raise ValueError('An accepted object lacks its successful physical sidecar record.')
        if receipt['physical_result'] in physical_seen:
            raise ValueError('A physical compiler record authenticates multiple receipts.')
        outputs,before=_physical_record(receipt['physical_result'],snapshot,reference,
            receipt['source'],compiler,flags,receipt['object'],prior)
        primary={'binding':receipt['object'],'lexical_path':receipt['object_lexical_path'],
                 'canonical_path':receipt['object_canonical_path'],'identity':receipt['object_identity'],
                 'namespace':receipt['object_namespace']}
        if (primary!=outputs['object'] or receipt['sidecar']!=outputs['sidecar'] or
                receipt.get('sidecar_prestate')!=before or receipt.get('sidecar_status')!=outputs['sidecar_status']):
            raise ValueError('An accepted sidecar differs from its successful physical record.')
        for kind,artifact in [('vo',primary),('vos',receipt['sidecar'])]:
            lexical=Path(artifact['lexical_path']);canonical=artifact['canonical_path']
            object_identity=artifact['identity'];namespace=artifact['namespace']
            if (not lexical.is_absolute() or '..' in lexical.parts or
                    not isinstance(canonical,str) or canonical!=artifact['binding']['path'] or
                    str(lexical.resolve())!=canonical or
                    not isinstance(object_identity,list) or len(object_identity)!=2 or
                    any(not isinstance(part,list) or len(part)!=6 or
                        any(type(value) is not int for value in part) for part in object_identity) or
                    not isinstance(namespace,list) or _namespace(lexical)[:-1]!=namespace[:-1]):
                raise ValueError('An accepted object lacks its exact identity or namespace.')
            previous=latest.get(canonical)
            if previous is not None and (previous['source']!=receipt['source'] or
                    previous['artifact']['binding']['sha256']!=artifact['binding']['sha256']):
                raise ValueError('Accepted object receipts conflict for one canonical object.')
            latest[canonical]={'artifact':artifact,'source':receipt['source'],'kind':kind,
                'receipt':receipt_reference,'primary_object':receipt['object']['path']}
        with force_hashing(True):
            for row in [receipt['source'],receipt['object'],receipt['sidecar']['binding'],receipt['compiler']]:
                if digest(Path(row['path'])) != row['sha256']:
                    raise ValueError('An accepted compilation input changed: ' + row['path'])
        rows.append(receipt['object']);prior.append(receipt_reference);physical_seen.append(receipt['physical_result'])
    authenticated=[]
    for value in latest.values():
        artifact=value['artifact'];lexical=Path(artifact['lexical_path'])
        if (_identity(lexical)!=artifact['identity'] or _namespace(lexical)!=artifact['namespace']):
            raise ValueError('An accepted object identity changed after successful compilation.')
        authenticated.append(dict(artifact['binding'],identity=artifact['identity'],
            lexical_path=str(lexical),canonical_path=artifact['canonical_path'],namespace=artifact['namespace'],
            source=value['source'],kind=value['kind'],receipt=value['receipt'],primary_object=value['primary_object']))
    return rows, version, index['receipts'], authenticated


DEPENDENCIES = frozenset({'.vo', '.vos', '.cmxs', '.cma', '.so'})
PLUGINS = frozenset({'.cmxs', '.cma', '.so'})


def load_roots(compiler, flags, environment):
    roots=[Path(row['path']) for row in mapping_context(flags)]
    switch=Path(compiler).absolute().parent.parent
    roots.extend(switch/name for name in ['lib/coq','lib/coq-core','lib/coq-stdlib','lib/rocq'])
    for variable in ['OCAMLPATH','CAML_LD_LIBRARY_PATH','COQPATH']:
        roots.extend(Path(part).absolute() for part in environment.get(variable,'').split(':') if part)
    return list(dict.fromkeys(roots))


def physical_context(compiler, flags, environment):
    return {'flags':list(flags),'paths':[{'path':str(path),'namespace':_namespace(path)}
            for path in load_roots(compiler,flags,environment)]}


def load_files(compiler, flags, environment):
    paths=set()
    for root in load_roots(compiler,flags,environment):
        if not root.is_dir():continue
        for path in root.rglob('*'):
            if path.is_symlink() and path.is_dir():
                raise ValueError('A compiler load path contains an unclassified directory alias.')
            if path.suffix in DEPENDENCIES and path.is_file():paths.add(path.absolute())
    return sorted(paths)


def hash_inputs(source, compiler, flags):
    """Hash the source, compiler, and a conservative load-path dependency superset."""
    context=physical_context(compiler,flags,os.environ)
    initial=load_files(compiler,flags,os.environ)
    paths=sorted({Path(source).absolute(),Path(compiler).absolute(),*initial})
    rows=[];identities={}
    with force_hashing(True):
        for path in paths:
            identities[path]=_identity(path)
            rows.append({'path':str(path),'sha256':digest(path),'identity':identities[path]})
    if any(_identity(path)!=before for path,before in identities.items()):
        raise ValueError('A physical compiler input changed during hashing.')
    if load_files(compiler,flags,os.environ)!=initial or physical_context(compiler,flags,os.environ)!=context:
        raise ValueError('A physical compiler load path changed during hashing.')
    return rows


def validate_compiler(runtime, runtime_reference, snapshot_reference, source_binding, compiler, *, output_key=None):
    from harness_commit import check
    if not isinstance(source_binding,dict) or set(source_binding)!={'path','sha256'}:
        raise ValueError('The physical compiler source binding is incomplete.')
    source=Path(source_binding['path'])
    started=time.monotonic()
    usage=resource.getrusage(resource.RUSAGE_SELF)
    if runtime.get('harness') is not None:
        check(runtime['harness'])
    snapshot = read(snapshot_reference, runtime_reference)
    if str(Path(compiler).absolute())!=snapshot['compiler']['path']:
        raise ValueError('The physical compiler differs from the selected executable.')
    if physical_context(compiler,runtime['physical_flags'],os.environ) != snapshot['mapping_context']:
        raise ValueError('The compiler mapping context differs.')
    identities_done=time.monotonic()
    produced = []
    accepted_index = None
    accepted_receipts = []
    authenticated_objects=[]
    if output_key is not None:
        with force_hashing(True):
            compiler_binding = binding(compiler)
        produced, accepted_index, accepted_receipts, authenticated_objects = accepted_objects(snapshot, snapshot_reference, output_key, compiler_binding, runtime['physical_flags'])
    receipts_done=time.monotonic()
    inputs = hash_inputs(source, compiler, runtime['physical_flags'])
    hashing_done=time.monotonic()
    source_hash=next(row['sha256'] for row in inputs if row['path']==str(source.absolute()))
    if source_hash!=source_binding['sha256']:
        raise ValueError('The recorded physical source changed during admission.')
    retained=snapshot['rows']+snapshot['initial_plugins']+snapshot.get('initial_objects',[])
    expected={tuple(row['identity'][1]):row['sha256'] for row in retained}
    compiler_identity=tuple(_identity(compiler)[1])
    if compiler_identity not in expected or runtime['physical_compiler']['sha256']!=snapshot['compiler']['sha256']:
        raise ValueError('The physical compiler lacks its original binding.')
    produced_by_identity={}
    for row in authenticated_objects:
        key=tuple(row['identity'][1])
        previous=produced_by_identity.get(key)
        if previous is not None and (previous['sha256']!=row['sha256'] or previous['source']!=row['source']):
            raise ValueError('Accepted object receipts conflict for one physical identity.')
        produced_by_identity[key]=row
    initial_names=set(snapshot['load_path_files'])
    for row in inputs:
        selected=expected.get(tuple(row['identity'][1]))
        if Path(row['path']).suffix in DEPENDENCIES:
            key=tuple(row['identity'][1])
            if row['path'] not in initial_names and key not in produced_by_identity:
                raise ValueError('A new compiler dependency lacks a validated receipt: '+row['path'])
            if key in produced_by_identity:selected=produced_by_identity[key]['sha256']
            if selected is None:
                raise ValueError('A compiler dependency lacks an original binding: '+row['path'])
        if selected is not None and selected!=row['sha256']:
            raise ValueError('A physical compiler input hash differs: '+row['path'])
    # Hashing can overlap a mutation of an earlier retained input.
    for row in retained:
        if _identity(row['path']) != row['identity']:
            raise ValueError('A compiler input changed during input hashing: ' + row['path'])
    for row in authenticated_objects:
        if (_identity(row['lexical_path'])!=row['identity'] or
                _namespace(row['lexical_path'])!=row['namespace'] or
                str(Path(row['lexical_path']).resolve())!=row['canonical_path']):
            raise ValueError('An accepted object changed during input hashing.')
    ended=time.monotonic()
    final_usage=resource.getrusage(resource.RUSAGE_SELF)
    timing={'snapshot_and_identity_wall_seconds':identities_done-started,
            'accepted_receipts_wall_seconds':receipts_done-identities_done,
            'direct_hash_wall_seconds':hashing_done-receipts_done,
            'final_identity_wall_seconds':ended-hashing_done,
            'total_wall_seconds':ended-started,
            'self_CPU_seconds':final_usage.ru_utime+final_usage.ru_stime-usage.ru_utime-usage.ru_stime}
    return {'timing':timing,'snapshot': snapshot_reference,'producer':snapshot['producer'], 'retained_identities_checked': len(snapshot['rows']),
            'accepted_dependency_objects': produced,
            'accepted_dependency_identities': authenticated_objects,
            'initial_plugins_checked':len(snapshot['initial_plugins']),
            'initial_objects_checked':len(snapshot.get('initial_objects',[])),
            'accepted_output_index': accepted_index, 'accepted_output_receipts': accepted_receipts,
            'directly_hashed_inputs': inputs, 'dependency_scope': 'Complete physical load-path superset.'}
