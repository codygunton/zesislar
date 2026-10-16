"""Resolve exact MCP operation references within one sealed controller root."""
from pathlib import Path
from collections.abc import Mapping
from trace_block_kernel_display import artifact,_fields,_same,_exact,_integer,_json


def _reference(value):
    _fields(value,'path sha256 bytes')
    return dict(value)


def _pointer(document,text):
    if not isinstance(text,str)or not text.startswith('#/'):
        raise ValueError('The operation record lacks its exact RFC6901 pointer.')
    current=document
    for encoded in text[2:].split('/'):
        import re
        if re.search(r'~(?![01])',encoded):raise ValueError('The operation pointer has invalid escaping.')
        key=encoded.replace('~1','/').replace('~0','~')
        if not isinstance(current,Mapping)or key not in current:
            raise ValueError('The operation pointer does not resolve to its exact record.')
        current=current[key]
    return current


def _response(value):
    if 'isError'in value and value['isError']is not False:
        raise ValueError('The MCP envelope reports an error.')
    result=value.get('structuredContent')
    if not isinstance(result,Mapping)or result.get('success')is not True:
        raise ValueError('The MCP envelope lacks its successful structured result.')
    return result


def checked_operation(runtime_root,*,expected_command,expected_source_state,record_reference,
                      response_reference,raw_reference,session_scope):
    _fields(record_reference,'path sha256 bytes pointer')
    ref={key:record_reference[key]for key in ('path','sha256','bytes')}
    _fields(session_scope,'records start health ownership source process')
    if not _exact(ref,session_scope['records']):raise ValueError('The operation record belongs to another controller scope.')
    root=Path(runtime_root).resolve(strict=True)
    records=_json(artifact(root,ref));record=_pointer(records,record_reference['pointer'])
    _fields(record,'tool arguments response result');_same(record,'tool','rocq_trace_run')
    _fields(record['arguments'],'from_state command trial')
    _same(record['arguments'],'command',expected_command);_same(record['arguments'],'from_state',expected_source_state)
    _same(record['arguments'],'trial',False);_integer(expected_source_state)
    response_path=artifact(root,_reference(response_reference));raw_path=artifact(root,_reference(raw_reference))
    _same(record,'response',str(response_path))
    result=_response(_json(response_path));_same(record,'result',result)
    if result.get('accepted')is not True:raise ValueError('The enclosing operation was not accepted.')
    _integer(result.get('state_id'))
    if result['state_id']==expected_source_state:raise ValueError('The operation lacks a distinct accepted state.')
    _same(result,'path',str(raw_path));_same(result,'sha256',raw_reference['sha256'])
    _same(_json(raw_path),'accepted',True)
    start_path=artifact(root,_reference(session_scope['start']));health_path=artifact(root,_reference(session_scope['health']))
    ownership=_json(artifact(root,_reference(session_scope['ownership'])))
    source=artifact(root,_reference(session_scope['source']))
    start=_response(_json(start_path));health=_response(_json(health_path))
    _same(records['start'],'response',str(start_path));_same(records['start'],'result',start)
    _same(records['started-health'],'response',str(health_path));_same(records['started-health'],'result',health)
    _same(start,'file',str(source))
    process=session_scope['process'];_fields(process,'pid start_ticks')
    for value in process.values():_integer(value,1)
    if health.get('pet',{}).get('pid')!=process['pid']:
        raise ValueError('The operation health record belongs to another Pet.')
    _same(ownership['owned_closure'],'owned_pet',process)
    if start.get('state_id',-1)>expected_source_state:raise ValueError('The operation predates its accepted session start.')
    return {'command':expected_command,'source_state':expected_source_state,'result_state':result['state_id'],
            'trial':False,'record':record_reference,'response':response_reference,'raw_response':raw_reference,
            'session_scope':session_scope,'association':'sealed controller operation; no SESSION completion claim'}
