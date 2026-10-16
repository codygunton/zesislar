"""Check indexed operations in an actual capture-only SESSION ledger."""
from pathlib import Path
from trace_block_kernel_display import artifact,_json,_fields,_same,_integer
from trace_block_bounded_operation import _response


def _owned(root,path,digest):
    path=Path(path)
    if not path.is_absolute():raise ValueError('The SESSION operation path is not absolute.')
    try:name=path.relative_to(root)
    except ValueError:raise ValueError('The SESSION operation leaves its owned evidence root.')from None
    if '..'in name.parts:raise ValueError('The SESSION operation has an unsupported parent path.')
    current=root
    for part in name.parts:
        current=current/part
        if current.is_symlink():raise ValueError('The SESSION operation path contains a symlink.')
    if not path.is_file():raise ValueError('The SESSION operation path is not a regular file.')
    reference={'path':str(name),'sha256':digest,'bytes':path.stat().st_size}
    return reference,artifact(root,reference)


def session_operation(evidence_root,session_reference,index,*,expected_command,expected_source_state,expected_trial,expected_accepted=True):
    root=Path(evidence_root).resolve(strict=True)
    _integer(expected_source_state)
    if type(expected_accepted)is not bool:raise ValueError('The expected acceptance is not Boolean.')
    if type(expected_trial)is not bool:raise ValueError('The expected trial mode is not Boolean.')
    session=_json(artifact(root,session_reference));operations=session.get('operations')
    if not isinstance(operations,list)or type(index)is not int or index<0 or index>=len(operations):
        raise ValueError('The SESSION operation index is unavailable.')
    process=session.get('ownership',{}).get('pet')
    _fields(process,'pid start_ticks')
    for item in process.values():_integer(item,1)
    def operation(number):
        row=operations[number]
        fields='arguments completed_utc path sha256 started_utc tool'
        _fields(row,fields+(' event_range'if'event_range'in row else''))
        ref,path=_owned(root,row['path'],row['sha256'])
        response=_response(_json(path))
        return row,response,ref
    starts=[n for n,row in enumerate(operations)if row.get('tool')=='rocq_trace_start']
    if len(starts)!=1 or starts[0]>=index:raise ValueError('The operation lacks its unique preceding session start.')
    start_index=starts[0];start,start_response,start_ref=operation(start_index)
    _same(start_response,'file',start['arguments']['file'])
    _same(start_response,'theorem',start['arguments']['theorem'])
    _integer(start_response['state_id'])
    healths=[n for n in range(start_index+1,index)if operations[n].get('tool')=='rocq_health']
    if not healths:raise ValueError('The operation lacks its owned Pet health association.')
    health,health_response,health_ref=operation(healths[0])
    _same(health_response['pet'],'pid',process['pid'])
    states={start_response['state_id']}
    for n in range(start_index+1,index):
        if operations[n].get('tool')!='rocq_trace_run':continue
        previous,result,_=operation(n);arguments=previous['arguments']
        if result.get('accepted')is True and arguments.get('trial')is False:
            _integer(arguments.get('from_state'))
            if arguments.get('from_state')not in states:
                raise ValueError('A preceding operation uses an unrelated source state.')
            _integer(result.get('state_id'));states.add(result['state_id'])
    if expected_source_state not in states:raise ValueError('The selected operation has no accepted same-session source state.')
    row,result,reference=operation(index)
    _same(row,'tool','rocq_trace_run')
    arguments=row['arguments']
    if set(arguments)not in ({'from_state','command','trial'},{'from_state','command','trial','debug','capture_mode'}):
        raise ValueError('The SESSION operation has unsupported arguments.')
    for field,value in [('command',expected_command),('from_state',expected_source_state),('trial',expected_trial)]:_same(arguments,field,value)
    if 'capture_mode'in arguments:_same(arguments,'capture_mode','bounded');_same(arguments,'debug',False)
    if result.get('accepted')is not expected_accepted:raise ValueError('The selected SESSION operation has another acceptance result.')
    _integer(result.get('state_id'))
    raw_reference,raw_path=_owned(root,result['path'],result['sha256'])
    raw=_json(raw_path);_same(raw,'accepted',expected_accepted)
    _same(raw,'retained_state_hash_unchanged',True)
    check=raw.get('retained_state_check');_fields(check,'method before after')
    _same(check,'method','Pet.state_hash');_integer(check['before']);_integer(check['after'])
    if check['before']!=check['after']:raise ValueError('The retained public state hash changed.')
    if (expected_trial or not expected_accepted) and result['state_id']!=expected_source_state:
        raise ValueError('A discarded operation changed its retained state identity.')
    return {'session':dict(session_reference),'operation_index':index,'operation':reference,
        'raw_response':raw_reference,'source_state':expected_source_state,'result_state':result['state_id'],
        'command':expected_command,'trial':expected_trial,'accepted':expected_accepted,'retention_method':'Pet.state_hash','start_operation':start_ref,'health_operation':health_ref,
        'owned_process':process,'session_error':session.get('error'),
        'limit':'This association does not establish session completion or proof closure.'}
