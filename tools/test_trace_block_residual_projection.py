"""Check synthetic SDK trial associations without executing a proof."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).parent/'block'))
from trace_block_filtered_projection import ProjectionView
from trace_block_seal import file_sha256
from trace_block_stream import build_stream_trace, json_document
import test_trace_block_filtered_projection as projection_fixtures
import test_trace_block_filtered_points as capture_fixture


class ResidualProjectionTests(unittest.TestCase):
    setUp = projection_fixtures.FilteredProjectionTests.setUp
    write = projection_fixtures.FilteredProjectionTests.write
    leaf = projection_fixtures.FilteredProjectionTests.leaf
    index = projection_fixtures.FilteredProjectionTests.index
    envelope = projection_fixtures.FilteredProjectionTests.envelope
    event_row = projection_fixtures.FilteredProjectionTests.event_row
    fixture = projection_fixtures.FilteredProjectionTests.fixture
    view = projection_fixtures.FilteredProjectionTests.view

    def residual_fixture(self, accepted=True):
        request,session=self.fixture(False)
        command='1: exact I.'
        source=self.base/'Unchanged.v';source.write_text('Ltac unchanged := exact I.')
        trial={'name':'whole-rule','rule':'FinishFacts','command':command,
               'command_sha256':hashlib.sha256(command.encode()).hexdigest(),
               'sources':[{'path':str(source),'sha256':file_sha256(source)}], 'exposure':'not-exposed'}
        request['residual_trials']=[trial]
        session['residual_selection']={'scope':'first-focused-leaf','selector':{'kind':'focused-index','value':1},'selected_goal_id':7,'event':session['residual_event'],'captured_current_goals':1}
        capture=capture_fixture.capture()
        capture['show_proof']={'availability':'complete','command':'Show Proof.', 'notation':'fun H => ?Goal','no_notation':'fun H : True => ?Goal'}
        def event(number,after=False):
            value=copy.deepcopy(capture)
            if after:
                value=capture_fixture.capture(True);value['show_proof']=capture['show_proof']
            ref=self.event_row(number,kind='checkpoint',rule='residual',invocation=0,trial=False,capture=value)
            return dict(ref,path=str(self.root/ref['path']))
        before=event(7);after=[event(8,True)]if accepted else [];rollback=event(9)
        checkpoint='all: ltac2:(trace_block_snapshot "residual").'
        executed=command+' '+checkpoint
        state_check={'method':'Pet.state_hash','before':11,'after':11}
        def operation(number,command,discarded,state,accepted=True):
            result={'accepted':accepted,'retained_state_hash_unchanged':True,'retained_state_check':state_check}
            if not accepted:result['message']='Exact synthetic refusal.'
            retained=self.root/('retained-%d.json'%number);retained.write_text(json.dumps(result))
            response={'success':True,'accepted':accepted,'state_id':state,'path':str(retained),'sha256':file_sha256(retained)}
            path=self.root/('sdk-%d.json'%number);path.write_text(json.dumps({'structuredContent':response}))
            session['operations'].append({'tool':'rocq_trace_run','arguments':{'command':command,'trial':discarded,'capture_mode':'bounded','from_state':1 if number==1 else 2},'path':str(path),'sha256':file_sha256(path)})
            return response
        operation(1,checkpoint,False,2)
        result=operation(2,executed,True,2,accepted)
        operation(3,checkpoint,False,3)
        session['residual_trials']=[dict(trial,before=[before],after=after,rollback=[rollback],
            after_availability='captured'if accepted else'not-retained',execution='SDK-discarded',native_entry=False,
            refusal_exposure='not-exposed',executed_command=executed,before_state_id=2,result=result,state_check=state_check)]
        self.save_session(session)
        return request,session

    def save_session(self,session):
        (self.root/'SESSION.json').write_text(json.dumps(session))

    def test_accepted_trial_preserves_full_snapshot_associations(self):
        request,_=self.residual_fixture()
        with self.view(request)as view:
            trace=build_stream_trace(request,view)
            self.assertTrue(trace['completion']['trace_complete'],trace['completion']['reasons'])
            trial=trace['residual']['hand_call'][0]
            self.assertEqual(trial['scope'],'residual-leaf')
            self.assertEqual(trial['selected_goal_id'],7)
            self.assertIn('residual-trial-0:after',trace['snapshots'])
            json.loads(''.join(json_document(trace)))

    def test_refused_partial_state_stays_unavailable(self):
        request,_=self.residual_fixture(False)
        with self.view(request)as view:
            trace=build_stream_trace(request,view)
            self.assertTrue(trace['completion']['trace_complete'],trace['completion']['reasons'])
            trial=trace['residual']['hand_call'][0]
            self.assertEqual(trial['after_trial'],trial['rollback'])
            self.assertIn('unavailable',trial['after_trial_status'])
            self.assertEqual(trace['residual']['refusal'][0]['exposure'],'not-exposed')

    def reject(self,mutation,accepted=True):
        request,session=self.residual_fixture(accepted)
        mutation(request,session)
        self.save_session(session)
        with self.assertRaises((ValueError,KeyError)):
            self.view(request)

    def test_missing_trial_rejects(self):self.reject(lambda q,s:s.update(residual_trials=[]))
    def test_missing_before_rejects(self):self.reject(lambda q,s:s['residual_trials'][0].update(before=[]))
    def test_missing_accepted_after_rejects(self):self.reject(lambda q,s:s['residual_trials'][0].update(after=[]))
    def test_fabricated_refused_after_rejects(self):self.reject(lambda q,s:s['residual_trials'][0].update(after=s['residual_trials'][0]['before']),False)
    def test_wrong_selected_leaf_rejects(self):self.reject(lambda q,s:s['residual_selection'].update(selected_goal_id=8))
    def test_wrong_command_rejects(self):self.reject(lambda q,s:s['residual_trials'][0].update(command='1: idtac.'))
    def test_nontrial_operation_rejects(self):self.reject(lambda q,s:s['operations'][1]['arguments'].update(trial=False))
    def test_wrong_persistent_state_rejects(self):self.reject(lambda q,s:s['operations'][1]['arguments'].update(from_state=99))
    def test_selected_event_substitution_rejects(self):self.reject(lambda q,s:s['residual_selection'].update(event=s['residual_trials'][0]['before'][0]))
    def test_selected_goal_count_rejects(self):self.reject(lambda q,s:s['residual_selection'].update(captured_current_goals=2))
    def test_foreign_operation_path_rejects(self):
        request,session=self.residual_fixture()
        operation=session['operations'][1]
        foreign=self.base/'foreign-operation.json'
        foreign.write_bytes(Path(operation['path']).read_bytes())
        operation.update(path=str(foreign),sha256=file_sha256(foreign))
        self.save_session(session)
        with self.assertRaisesRegex(ValueError,'owned session directory'):self.view(request)
    def test_repeated_capture_rejects(self):self.reject(lambda q,s:s['residual_trials'][0].update(rollback=s['residual_trials'][0]['before']))


if __name__=='__main__':unittest.main()
