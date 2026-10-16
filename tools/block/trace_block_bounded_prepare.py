"""Validate bounded guard bindings without changing the filtered protocol."""
from collections.abc import Mapping
import hashlib,json
from pathlib import Path
from trace_block_filtered import bind_descriptors
from trace_block_chunks import MAX_RECORD_BYTES


def bind_bounded_descriptors(descriptors):
    if not isinstance(descriptors,Mapping):raise ValueError('The bounded descriptor map is invalid.')
    ordinary=bind_descriptors(descriptors);result={}
    for client,descriptor in descriptors.items():
        expected=dict(ordinary[client]['typed_guard'])
        command=expected['command']
        if command.count('trace_block_ltac1_guard')!=1:raise ValueError('The canonical guard bridge is unsupported.')
        command=command.replace('trace_block_ltac1_guard','trace_bounded_ltac1_guard')
        expected.update(command=command,sha256=hashlib.sha256(command.encode()).hexdigest())
        actual=descriptor.get('typed_guard')
        if not isinstance(actual,Mapping)or dict(actual)!=expected:
            raise ValueError('The bounded descriptor differs from its exact guard command or hash.')
        result[client]=dict(descriptor,typed_guard=expected)
    return result


def bounded_guard_manifest(descriptors):
    bound=bind_bounded_descriptors(descriptors)
    value={'schema':2,'clients':{key:row['typed_guard']for key,row in bound.items()}}
    payload=(json.dumps(value,sort_keys=True,ensure_ascii=False,separators=(',',':'))+'\n').encode()
    if len(payload)>MAX_RECORD_BYTES:raise ValueError('The bounded guard manifest exceeds its physical limit.')
    return value,payload


def bounded_guard_manifest_environment(workspace,descriptors,reference):
    if not isinstance(reference,dict)or set(reference)!={'path','sha256'}:
        raise ValueError('The bounded guard manifest lacks its exact reference.')
    root=Path(workspace).resolve(strict=True);path=Path(reference['path'])
    if not path.is_absolute()or '..'in path.parts:
        raise ValueError('The bounded guard manifest path is not an exact absolute path.')
    relative=path.relative_to(root)
    current=root
    for part in relative.parts:
        current=current/part
        if current.is_symlink():raise ValueError('The bounded guard manifest contains a symlink.')
    _,expected=bounded_guard_manifest(descriptors)
    with path.open('rb')as stream:actual=stream.read(MAX_RECORD_BYTES+1)
    if actual!=expected or hashlib.sha256(actual).hexdigest()!=reference['sha256']:
        raise ValueError('The bounded guard manifest differs from its exact descriptors.')
    return {'ZESU_TRACE_GUARD_MANIFEST':str(path)}
