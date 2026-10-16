"""Keep exact ordered hand-trial occurrences in bounded rule points."""
from collections import defaultdict
from collections.abc import Mapping
import re
import hashlib
from trace_block_filtered import typed_guards
from trace_block_kernel_display import _exact, _array


def bounded_guard(client):
    text=typed_guards().get(client)
    if text is None:raise ValueError('The bounded client has no supported typed guard.')
    if text.count('trace_block_ltac1_guard')!=1:raise ValueError('The typed guard bridge is unsupported.')
    return text.replace('trace_block_ltac1_guard','trace_bounded_ltac1_guard')


def _pointer(sequence):return '#/snapshots/event-%08d'%sequence


def _catalog_equal(left,right,before,after):
    """Compare full checked catalogs with exact locally bound sidecar references."""
    if not isinstance(left,Mapping)or not isinstance(right,Mapping):return False
    expected={'schema','complete_sidecar','entries'}
    if set(left)!=expected or set(right)!=expected:return False
    if not _exact(left['schema'],1)or not _exact(right['schema'],1):return False
    if not _array(left['entries'])or not _array(right['entries']):return False
    def compare(a,b):
        if isinstance(a,Mapping)or isinstance(b,Mapping):
            if not isinstance(a,Mapping)or not isinstance(b,Mapping)or set(a)!=set(b):return False
            for key in a:
                if key=='complete_sidecar':
                    if not _exact(a[key],before['complete_sidecar']):return False
                    if not _exact(b[key],after['complete_sidecar']):return False
                elif not compare(a[key],b[key]):return False
            return True
        if _array(a)or _array(b):
            return _array(a)and _array(b)and len(a)==len(b)and all(compare(x,y)for x,y in zip(a,b))
        return _exact(a,b)
    return compare(left,right)


def _group_catalog_binding(row,capture,catalog):
    reference=row['entry_ref']
    if not isinstance(reference,Mapping)or set(reference)!={'catalog_ref','pointer'}:return False
    if not _exact(reference['catalog_ref'],capture['evar_catalog_ref']):return False
    pointer=reference['pointer']
    if not isinstance(pointer,str)or re.fullmatch(r'#/entries/(0|[1-9][0-9]*)',pointer)is None:return False
    entry=catalog['entries'][int(pointer.rsplit('/',1)[1])]
    if not _exact(entry['id'],row['evar'])or type(entry['defined'])is not bool:return False
    if row['status']!=('defined'if entry['defined']else'undefined'):return False
    return _exact(row['body'],entry['body'])


def rollback_equal(before,after,*,before_catalog=None,after_catalog=None):
    """Compare checked state content while retaining each local reference binding.

    Schema2 requires both independently validated catalogs. Event-specific paths
    remain exact within each capture. The comparison retains complete catalog
    content, raw groups, body nodes, state bytes, and printed state.
    """
    try:
        return _rollback_equal(before,after,before_catalog,after_catalog)
    except (KeyError,TypeError,IndexError,ValueError):
        return False


def _rollback_equal(before,after,before_catalog,after_catalog):
    """Compare complete serialized state and independently bound printed fields."""
    version=before.get('schema',1)
    if version!=after.get('schema',1):return False
    if version==2:
        if not _catalog_equal(before_catalog,after_catalog,before,after):return False
        for field in ('group_policy','group_counts'):
            if not _exact(before[field],after[field]):return False
    for field in ('sha256','bytes'):
        if before['complete_sidecar'][field]!=after['complete_sidecar'][field]:return False
    for field in ('fresh_evar_counter','live_goal_ids'):
        if not _exact(before[field],after[field]):return False
    for mode in ('notation','no_notation'):
        for group in ('goals','shelf','given_up'):
            left,right=before[mode][group],after[mode][group]
            if len(left)!=len(right):return False
            for a,b in zip(left,right):
                for key in ('evar','name','conclusion'):
                    if not _exact(a[key],b[key]):return False
                if version==2:
                    for key in ('status','display_ref'):
                        if not _exact(a[key],b[key]):return False
                    if not _group_catalog_binding(a,before,before_catalog):return False
                    if not _group_catalog_binding(b,after,after_catalog):return False
                    if not _exact(a['entry_ref']['pointer'],b['entry_ref']['pointer']):return False
                if len(a['hyps'])!=len(b['hyps']):return False
                for x,y in zip(a['hyps'],b['hyps']):
                    for key in ('names','type','body'):
                        if not _exact(x[key],y[key]):return False
    return True


class BoundedPoints:
    """Accept checked captures and caller-bound operation associations.

    Trial plans are ordered source-bound occurrence lists. Repeated labels do
    not merge. The caller must bind every command to the frozen source.
    """
    def __init__(self,events,captures,descriptors,session_id,operation_for_sequence):
        self.events,self.captures=events,captures
        self.descriptors,self.session_id=descriptors,session_id
        self.operations=operation_for_sequence
        self.points=[];self.residual=None;self.snapshots={}
        groups=defaultdict(list);entries=[];counters={}
        for reference in events.references:
            row=events.read(reference);number=row.get('invocation')
            if row['kind']=='guard-counter':
                if row.get('trial')is not False or type(number)is not int or number<=0:
                    raise ValueError('A bounded counter is not an exact native invocation.')
                client=row.get('client');key=(client,number)
                if key in counters:raise ValueError('A bounded native counter repeats.')
                descriptor=descriptors.get(client)
                if descriptor is None or row.get('rule')!=descriptor['rule']:
                    raise ValueError('The native counter differs from its descriptor.')
                expected=hashlib.sha256(bounded_guard(client).encode()).hexdigest()
                if row.get('guard_hash')!=expected and row.get('classification')!='unknown':
                    raise ValueError('The bounded guard lacks its exact source binding.')
                counters[key]=row
            if number is not None:groups[number].append((reference,row))
            if 'capture'in row:
                if row['sequence']not in captures:raise ValueError('A full event lacks its checked capture.')
                capture=captures[row['sequence']]
                self.snapshots['event-%08d'%row['sequence']]=capture.stable()
            if row['kind']=='native-entry'and row.get('trial')is False:
                client=row.get('rule');key=(client,number)
                if key not in counters or counters[key].get('classification')!='actual-trigger':
                    raise ValueError('A full entry lacks its exact typed trigger.')
                entries.append((reference,row))
            if row['kind']=='checkpoint'and row.get('rule')=='residual'and row.get('trial')is False:
                if self.residual is not None:raise ValueError('The first-residual projection contains multiple residuals.')
                self.residual=dict(captures[row['sequence']].stable(),session_id=session_id,
                    trigger={'kind':'residual','event_sequence':row['sequence']},
                    operation=self._operation(row['sequence']))
        for reference,entry in entries:
            number,client=entry['invocation'],entry['rule'];descriptor=descriptors[client]
            plan=descriptor['trials'];before=captures[entry['sequence']]
            counter=counters[(client,number)]
            goals=counter.get('focused_goals')
            if (not isinstance(goals,list) or any(type(goal)is not int or goal<0 for goal in goals)
                    or(before.capture.get('schema',1)==1 and len(goals)!=len(set(goals)))
                    or goals!=list(before.capture['live_goal_ids'])):
                raise ValueError('The selected capture differs from its typed guard goal identities.')
            if (type(counter.get('fresh_evar_before'))is not int
                    or type(counter.get('fresh_evar_after'))is not int
                    or counter['fresh_evar_before']!=counter['fresh_evar_after']
                    or counter['fresh_evar_before']!=before.capture['fresh_evar_counter']):
                raise ValueError('The selected capture differs from its typed guard fresh counter.')
            point=dict(before.stable(),session_id=session_id,trigger={'kind':'rule-entry',
                'rule':descriptor['rule'],'client':client,'invocation':number,'event_sequence':entry['sequence']},
                hand_call=[],refusal=[],hint_log={'availability':'complete','filter':descriptor['log_filter'],
                'selection':'Invocation-attributed Debug messages and exact listed names. Trial logs remain separate.',
                'events':[]},operation=self._operation(entry['sequence']))
            accepted=None;feedback=[];index=0
            for ref,row in groups[number]:
                kind=row['kind']
                if kind in ('hand-accepted','hand-rollback','hand-refused'):
                    if row.get('rule')!=client:raise ValueError('The hand trial belongs to another client.')
                    if index>=len(plan)and kind!='hand-refused':raise ValueError('An undeclared hand occurrence appears.')
                if kind=='feedback':
                    message={'level':row['level'],'message':events.text_field(ref,'message'),'event_sequence':row['sequence']}
                    if row.get('trial')is True:
                        if index>=len(plan)or row.get('clause')!=plan[index]['clause']:
                            raise ValueError('The trial log lacks exact occurrence attribution.')
                        feedback.append(message)
                    elif row.get('trial')is False:
                        if row['level']=='debug'or any(name in message['message']for name in descriptor['log_filter']):
                            point['hint_log']['events'].append(message)
                    else:raise ValueError('The feedback trial attribution is unavailable.')
                elif kind=='hand-accepted':
                    if accepted is not None or row.get('trial')is not True or row.get('clause')!=plan[index]['clause']:
                        raise ValueError('The accepted event differs from its exact trial occurrence.')
                    accepted=row['sequence']
                elif kind=='hand-rollback':
                    if row.get('trial')is not False or row.get('exact')is not True or row.get('clause')!=plan[index]['clause']:
                        raise ValueError('The rollback lacks exact occurrence attribution.')
                    rollback=captures[row['sequence']]
                    if not rollback_equal(before.capture,rollback.capture,
                        before_catalog=getattr(before,'catalog',None),after_catalog=getattr(rollback,'catalog',None)):raise ValueError('The full rollback differs from the entry state.')
                    command=plan[index]['command'];outcome='accepted'if accepted is not None else'refused'
                    trial={'trial_id':'invocation-%d-occurrence-%d'%(number,index+1),'clause':row['clause'],
                        'command':command,'outcome':outcome,'before':'event-%08d'%entry['sequence'],
                        'after_trial':'event-%08d'%(accepted if accepted is not None else row['sequence']),
                        'rollback':'event-%08d'%row['sequence'],'rollback_equal':True,
                        'rollback_method':'complete-marshal-bytes-and-printed-state','feedback':feedback,
                        'event_sequence':row['sequence'],'operation':self._operation(row['sequence'])}
                    if accepted is None:trial['after_trial_availability']='unavailable: refused discarded branch'
                    trial['commands']=[{'command':command,'before':_pointer(entry['sequence']),
                        'after':_pointer(accepted if accepted is not None else row['sequence']),
                        'outcome':outcome,'refusal':None}]
                    point['hand_call'].append(trial);index+=1;accepted=None;feedback=[]
                elif kind=='hand-refused':
                    if row.get('trial')is not False or not point['hand_call']:
                        raise ValueError('The refusal lacks its exact preceding trial.')
                    trial=point['hand_call'][-1]
                    if trial['clause']!=row.get('clause')or trial['outcome']!='refused'or'message'in trial:
                        raise ValueError('The refusal differs from its exact occurrence.')
                    message=events.text_field(ref,'refusal');trial['message']=message
                    trial['commands'][0]['refusal']=message
                    point['refusal'].append({'hand_call_index':len(point['hand_call'])-1,'clause':trial['clause'],
                        'message':message,'exposure':plan[index-1]['exposure']})
            if accepted is not None or feedback or index!=len(plan):raise ValueError('The point lacks its complete ordered trial plan.')
            if any(t['outcome']=='refused'and'message'not in t for t in point['hand_call']):
                raise ValueError('A refused occurrence lacks its exact message.')
            self.points.append(point)
        self.coverage={'attempted_entries':len(counters),'actual_triggers':sum(v.get('classification')=='actual-trigger'for v in counters.values()),
                       'captured_events':len(entries),'session_and_stream_complete':False}

    def _operation(self,sequence):
        value=self.operations.get(sequence)
        if value is None:raise ValueError('The event lacks its exact enclosing operation association.')
        return value
