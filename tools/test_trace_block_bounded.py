"""Check bounded references and operation joins with synthetic records."""
from pathlib import Path
import copy,hashlib,json,sys,tempfile,unittest
sys.path.insert(0,str(Path(__file__).resolve().parent/'block'))
from trace_block_bounded_points import BoundedPoints,bounded_guard
from trace_block_bounded_operation import checked_operation
from trace_block_bounded_capture import BoundedCapture,pointer
from trace_block_bounded_session import session_operation


class Capture:
    def __init__(self):
        groups={'goals':[],'shelf':[],'given_up':[]}
        self.capture={'complete_sidecar':{'sha256':'a'*64,'bytes':1},'fresh_evar_counter':4,'live_goal_ids':[],
                      'notation':copy.deepcopy(groups),'no_notation':copy.deepcopy(groups)}
    def stable(self):return {'goal':'True','complete_sidecar':self.capture['complete_sidecar']}

class Events:
    def __init__(self,rows):self.rows=rows;self.references=list(range(len(rows)))
    def read(self,reference):return self.rows[reference]
    def text_field(self,reference,field):return self.rows[reference][field]

class PointTests(unittest.TestCase):
    client='Hooks.zesu_conjunct_head_if_enabled'
    def build(self,edit=None):
        c=self.client;guard=hashlib.sha256(bounded_guard(c).encode()).hexdigest()
        rows=[{'kind':'guard-counter','sequence':1,'trial':False,'client':c,'rule':'ConjunctMatch','invocation':1,
               'guard_hash':guard,'classification':'actual-trigger','focused_goals':[],
               'fresh_evar_before':4,'fresh_evar_after':4},
              {'kind':'native-entry','sequence':2,'trial':False,'rule':c,'invocation':1,'capture':{}},
              {'kind':'hand-accepted','sequence':3,'trial':True,'rule':c,'invocation':1,'clause':'whole-rule','capture':{}},
              {'kind':'hand-rollback','sequence':4,'trial':False,'rule':c,'invocation':1,'clause':'whole-rule','exact':True,'capture':{}},
              {'kind':'hand-accepted','sequence':5,'trial':True,'rule':c,'invocation':1,'clause':'whole-rule','capture':{}},
              {'kind':'hand-rollback','sequence':6,'trial':False,'rule':c,'invocation':1,'clause':'whole-rule','exact':True,'capture':{}}]
        captures={n:Capture()for n in range(2,7)}
        descriptors={c:{'rule':'ConjunctMatch','log_filter':[c],'trials':[
            {'clause':'whole-rule','command':'exact_existing_callback','exposure':'not-exposed'}for _ in range(2)]}}
        operations={n:{'same-session':'synthetic'}for n in range(2,7)}
        if edit:edit(rows,captures,descriptors,operations)
        return BoundedPoints(Events(rows),captures,descriptors,'synthetic',operations)
    def reject(self,edit):
        with self.assertRaises(ValueError):self.build(edit)
    def test_duplicate_labels_keep_occurrences(self):
        p=self.build().points[0];self.assertEqual(len(p['hand_call']),2)
        self.assertNotEqual(p['hand_call'][0]['trial_id'],p['hand_call'][1]['trial_id'])
    def test_missing_declared_trial(self):self.reject(lambda r,c,d,o:r.__delitem__(slice(4,None)))
    def test_extra_trial(self):self.reject(lambda r,c,d,o:d[self.client]['trials'].pop())
    def test_wrong_guard(self):self.reject(lambda r,c,d,o:r[0].update(guard_hash='b'*64))
    def test_wrong_guard_goals(self):self.reject(lambda r,c,d,o:r[0].update(focused_goals=[99]))
    def test_wrong_guard_fresh_counter(self):self.reject(lambda r,c,d,o:r[0].update(fresh_evar_before=3,fresh_evar_after=3))
    def test_guard_changed_fresh_counter(self):self.reject(lambda r,c,d,o:r[0].update(fresh_evar_after=5))
    def test_trial_counter(self):self.reject(lambda r,c,d,o:r[0].update(trial=True))
    def test_wrong_trial_client(self):self.reject(lambda r,c,d,o:r[2].update(rule='different'))
    def test_accepted_without_trial(self):self.reject(lambda r,c,d,o:r[2].update(trial=False))
    def test_wrong_rollback(self):self.reject(lambda r,c,d,o:c[4].capture['complete_sidecar'].update(sha256='b'*64))
    def test_unchecked_capture(self):self.reject(lambda r,c,d,o:c.pop(4))
    def test_missing_operation(self):self.reject(lambda r,c,d,o:o.pop(4))
    def test_wrong_clause(self):self.reject(lambda r,c,d,o:r[2].update(clause='other'))
    def test_missing_refusal_message(self):self.reject(lambda r,c,d,o:r.pop(2))
    def test_unknown_guard_client(self):
        with self.assertRaises(ValueError):bounded_guard('Unsupported')



class OperationTests(unittest.TestCase):
 def run_case(self,edit=None,change_refs=None):
  with tempfile.TemporaryDirectory()as directory:
   root=Path(directory)
   def write(name,data):
    p=root/name;p.write_text(json.dumps(data,sort_keys=True)+'\n')
    raw=p.read_bytes();return {'path':name,'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw)}
   source=write('Control.v',{'synthetic':'statement'})
   start={'structuredContent':{'success':True,'state_id':1,'file':str(root/'Control.v')}}
   health={'structuredContent':{'success':True,'pet':{'pid':10}}}
   ownership={'owned_closure':{'owned_pet':{'pid':10,'start_ticks':20}}}
   raw_ref=write('raw.json',{'accepted':True})
   payload={'success':True,'accepted':True,'state_id':4,'path':str(root/'raw.json'),'sha256':raw_ref['sha256']}
   response={'isError':False,'structuredContent':copy.deepcopy(payload)}
   records={'start':{'response':str(root/'start.json'),'result':start['structuredContent']},
    'started-health':{'response':str(root/'health.json'),'result':health['structuredContent']},
    'observed':{'tool':'rocq_trace_run','arguments':{'from_state':2,'command':'idtac.','trial':False},
     'response':str(root/'response.json'),'result':copy.deepcopy(payload)}}
   if edit:edit(records,response,ownership)
   refs={'response_reference':write('response.json',response),'raw_reference':raw_ref}
   record_ref=write('records.json',records)
   refs['record_reference']=dict(record_ref,pointer='#/observed')
   refs['session_scope']={'records':record_ref,'start':write('start.json',start),'health':write('health.json',health),
    'ownership':write('ownership.json',ownership),'source':source,'process':{'pid':10,'start_ticks':20}}
   if change_refs:change_refs(refs)
   return checked_operation(root,expected_command='idtac.',expected_source_state=2,**refs)
 def reject(self,edit=None,change_refs=None):
  with self.assertRaises((ValueError,KeyError)):self.run_case(edit,change_refs)
 def test_valid(self):self.assertEqual(self.run_case()['source_state'],2)
 def test_record_response_substitution(self):self.reject(lambda a,b,c:a['observed'].update(response='other.json'))
 def test_result_path_substitution(self):
  self.reject(lambda a,b,c:(a['observed']['result'].update(path='/foreign/raw.json'),b['structuredContent'].update(path='/foreign/raw.json')))
 def test_missing_pointer(self):self.reject(change_refs=lambda r:r['record_reference'].update(pointer='#/missing'))
 def test_pointer_to_another_record(self):self.reject(change_refs=lambda r:r['record_reference'].update(pointer='#/start'))
 def test_invalid_pointer_escape(self):self.reject(change_refs=lambda r:r['record_reference'].update(pointer='#/observed~2'))
 def test_foreign_records(self):self.reject(change_refs=lambda r:r['session_scope'].update(records=r['response_reference']))
 def test_error_envelope(self):self.reject(lambda a,b,c:b.update(isError=True))
 def test_error_integer_is_not_false(self):self.reject(lambda a,b,c:b.update(isError=0))
 def test_error_null_is_not_false(self):self.reject(lambda a,b,c:b.update(isError=None))
 def test_wrong_command(self):self.reject(lambda a,b,c:a['observed']['arguments'].update(command='assumption.'))
 def test_wrong_source_state(self):self.reject(lambda a,b,c:a['observed']['arguments'].update(from_state=3))
 def test_trial_operation(self):self.reject(lambda a,b,c:a['observed']['arguments'].update(trial=True))
 def test_failed_accepted_response(self):self.reject(lambda a,b,c:b['structuredContent'].update(accepted=False))
 def test_wrong_raw_hash(self):self.reject(change_refs=lambda r:r['raw_reference'].update(sha256='b'*64))
 def test_foreign_pet(self):self.reject(change_refs=lambda r:r['session_scope']['process'].update(pid=11))
 def test_foreign_pet_tick(self):self.reject(change_refs=lambda r:r['session_scope']['process'].update(start_ticks=21))
 def test_foreign_source(self):self.reject(change_refs=lambda r:r['session_scope'].update(source=r['response_reference']))
 def test_parent_path_refused(self):self.reject(change_refs=lambda r:r['response_reference'].update(path='../response.json'))


class ContextTests(unittest.TestCase):
 def run_case(self,filters,edit=None):
  context=[{'name':'h'+str(i),'body':None}for i in range(len(filters))]
  hyps=[{'names':['h'+str(i)],'type':'T'+str(i),'body':None,
    'type_display_ref':pointer('evar/7/hyp/%d/type'%i),'body_display_ref':None}
    for i in reversed(range(len(filters)))if filters[i]]
  goal={'evar':7,'name':None,'conclusion':'P','display_ref':pointer('evar/7/conclusion'),'hyps':hyps}
  capture={mode:{'goals':[copy.deepcopy(goal)],'shelf':[],'given_up':[],'hidden_stack':{}}
           for mode in ['notation','no_notation']}
  instance=BoundedCapture.__new__(BoundedCapture);instance.capture=capture
  instance.by_id={7:{'name':None,'defined':False,'context':context,'filter':filters}}
  instance._display=lambda name,ref,left,right:({'root_id':name}if ref==pointer(name)else self.fail('wrong source index'))
  if edit:edit(capture)
  rows=instance._goals('goals')
  return rows,context
 def test_false_middle_keeps_original_indexes(self):
  rows,context=self.run_case([True,False,True]);self.assertEqual([h['names']for h in rows[0]['hyps']],[['h2'],['h0']]);self.assertEqual(len(context),3)
 def test_all_false(self):self.assertEqual(self.run_case([False,False])[0][0]['hyps'],[])
 def test_false_first(self):self.assertEqual(self.run_case([False,True])[0][0]['hyps'][0]['names'],['h1'])
 def test_false_last(self):self.assertEqual(self.run_case([True,False])[0][0]['hyps'][0]['names'],['h0'])
 def test_all_true_preserves_reverse_order(self):self.assertEqual(self.run_case([True,True])[0][0]['hyps'][0]['names'],['h1'])
 def test_omitted_visible_hyp_rejects(self):
  with self.assertRaises(ValueError):self.run_case([True],lambda c:c['notation']['goals'][0].update(hyps=[]))
 def test_wrong_visible_name_rejects(self):
  with self.assertRaises(ValueError):self.run_case([True],lambda c:c['notation']['goals'][0]['hyps'][0].update(names=['foreign']))


class SessionTests(unittest.TestCase):
 def run_case(self,edit=None,index=2,trial=False,source=1,command='native.'):
  with tempfile.TemporaryDirectory()as directory:
   root=Path(directory);operations=[]
   def save(name,value):
    p=root/name;p.write_text(json.dumps(value,sort_keys=True)+'\n');return p,hashlib.sha256(p.read_bytes()).hexdigest()
   def op(tool,args,payload):
    p,h=save('operation-%d.json'%len(operations),{'isError':False,'structuredContent':payload})
    operations.append({'tool':tool,'arguments':args,'path':str(p),'sha256':h,'started_utc':'start','completed_utc':'end'})
   op('rocq_trace_start',{'file':'Control.v','theorem':'fixture'},{'success':True,'state_id':1,'file':'Control.v','theorem':'fixture'})
   op('rocq_health',{}, {'success':True,'pet':{'pid':10}})
   for label,discard,result_id in [('native.',False,2),('status.',True,2)]:
    p,h=save('capture-%d.json'%len(operations),{'accepted':True,'retained_state_hash_unchanged':True,
       'retained_state_check':{'method':'Pet.state_hash','before':7,'after':7}})
    op('rocq_trace_run',{'from_state':1 if label=='native.'else 2,'command':label,'trial':discard,'debug':False,'capture_mode':'bounded'},
       {'success':True,'accepted':True,'state_id':result_id,'path':str(p),'sha256':h})
   session={'operations':operations,'ownership':{'pet':{'pid':10,'start_ticks':20}},'error':None}
   if edit:edit(root,session)
   p,h=save('SESSION.json',session)
   return session_operation(root,{'path':'SESSION.json','sha256':h,'bytes':p.stat().st_size},index,
       expected_command=command,expected_source_state=source,expected_trial=trial)
 def reject(self,edit=None,**kwargs):
  with self.assertRaises((ValueError,KeyError)):self.run_case(edit,**kwargs)
 def test_committed_at_initial_state(self):self.assertFalse(self.run_case()['trial'])
 def test_discarded_state_stays_retained(self):self.assertTrue(self.run_case(index=3,trial=True,source=2,command='status.')['trial'])
 def test_trial_mode_mismatch(self):self.reject(index=3,trial=False,source=2,command='status.')
 def test_initial_source_mismatch(self):self.reject(source=99)
 def test_command_mismatch(self):self.reject(command='other.')
 def test_index_bool(self):self.reject(index=True)
 def test_index_out_of_range(self):self.reject(index=99)
 def test_foreign_process(self):self.reject(lambda p,s:s['ownership']['pet'].update(pid=11))
 def test_changed_operation_hash(self):self.reject(lambda p,s:s['operations'][2].update(sha256='0'*64))
 def test_foreign_operation_path(self):self.reject(lambda p,s:s['operations'][2].update(path='/foreign/operation.json'))
 def test_wrong_tool(self):self.reject(lambda p,s:s['operations'][2].update(tool='rocq_health'))
 def test_duplicate_start(self):self.reject(lambda p,s:s['operations'][1].update(tool='rocq_trace_start'))
 def test_no_start(self):self.reject(lambda p,s:s['operations'][0].update(tool='other'))
 def test_bad_response_envelope(self):
  def edit(root,session):
   row=session['operations'][2];p=Path(row['path']);v=json.loads(p.read_text());v['isError']=True;p.write_text(json.dumps(v));row['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
  self.reject(edit)
 def test_refused_response(self):
  def edit(root,session):
   row=session['operations'][2];p=Path(row['path']);v=json.loads(p.read_text());v['structuredContent']['accepted']=False;p.write_text(json.dumps(v));row['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
  self.reject(edit)

if __name__=='__main__':unittest.main()
