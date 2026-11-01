"""Exercise long-check exports without PET, compilation, or admission."""
import ast,asyncio,copy,json,os,stat,sys,tempfile,unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE),str(HERE.parents[1]),str(HERE.parents[2])]
import entry_chain_provider as P

class LongCheckState(unittest.IsolatedAsyncioTestCase):
 def setUp(self):
  temporary=tempfile.TemporaryDirectory();self.addCleanup(temporary.cleanup)
  self.output=Path(temporary.name);self.calls=[]
  def goal(n):return {'info':{'evar':str(n)},'hyps':[{'names':['selector_marker'],'ty':'SelectedRoute','def':'selected_route'}],'ty':'True'}
  self.groups={'goals':[goal(1)],'stack':[[[goal(2)],[goal(3)]]],'shelf':[goal(4)],'given_up':[goal(5)]}
  self.payload=dict(copy.deepcopy(self.groups),kernel_groups=copy.deepcopy(self.groups),
       local_definition_export={'original_state_preserved':True})
  self.export_path=self.output/'complete-goals/state_8.json';P.atomic_json(self.export_path,self.payload)
  self.export=dict(P.binding(self.export_path),success=True,state_id=8)
  self.result={'success':True,'state_id':8,'check_time_ms':60001}
  self.arguments={'from_state':7,'body':'unchanged_search.','timeout':604800}
  self.markers={'native_route':{'path':'unchanged-route','sha256':'a'*64},'phase':'native','native_search':True}
 async def query(self,session,name,arguments):
  self.calls.append((name,arguments));return self.export
 async def capture(self,result=None,observed=90,index=1):
  return await P.retain_long_check(self.query,None,'rocq_check',self.arguments,
     self.result if result is None else result,self.output,index,observed,self.markers)
 def record(self,receipt):return json.loads(Path(receipt['record']['path']).read_text())
 async def test_all_ordinary_and_kernel_groups_and_markers_are_private(self):
  original=copy.deepcopy(self.result);receipt=await self.capture();record=self.record(receipt)
  self.assertTrue(receipt['success']);self.assertTrue(record['complete_state_available'])
  self.assertEqual(self.calls,[('rocq_complete_goals',{'from_state':8})])
  self.assertEqual(record['state_id'],8);self.assertEqual(record['command'],self.arguments)
  self.assertEqual(record['returned_result'],original);self.assertEqual(self.result,original)
  self.assertEqual(record['route_markers'],self.markers)
  state=Path(record['complete_state']['path']);self.assertEqual(json.loads(state.read_text()),self.payload)
  self.assertEqual(record['selector_markers']['state'],P.binding(state))
  for path in [state.parent,state.parent.parent]:self.assertEqual(stat.S_IMODE(path.stat().st_mode),0o700)
  for path in [state,Path(receipt['record']['path'])]:self.assertEqual(stat.S_IMODE(path.stat().st_mode),0o600)
  self.assertNotIn('goals',receipt);self.assertNotIn('returned_result',receipt)
 async def test_exact_sixty_seconds_does_not_export(self):
  self.assertIsNone(await self.capture(dict(self.result,check_time_ms=60000)))
  self.assertFalse((self.output/'long-checks').exists());self.assertEqual(self.calls,[])
 async def test_missing_timing_uses_qualified_observed_rpc_duration(self):
  receipt=await self.capture({'success':True,'state_id':8},observed=61)
  record=self.record(receipt);self.assertIsNone(record['timing']['check_time_ms'])
  self.assertIn('command execution duration unavailable',record['timing']['threshold_basis'])
 async def test_missing_timing_and_short_observation_do_not_invent_duration(self):
  self.assertIsNone(await self.capture({'success':True,'state_id':8},observed=60))
 async def test_no_returned_state_never_queries_the_input(self):
  receipt=await self.capture({'success':False,'last_valid_state_id':7,'check_time_ms':61000})
  self.assertFalse(receipt['success']);self.assertEqual(self.calls,[])
  record=self.record(receipt);self.assertIsNone(record['state_id']);self.assertIn('No input state',record['export_error'])
 async def test_long_qed_no_scope_is_explicit_without_empty_groups(self):
  self.arguments['body']='Qed.'
  result=copy.deepcopy(self.result)
  async def no_scope(*args):raise P.ToolFailure('No proof scope.',{'success':False,'state_id':8,'reason':'no-proof-scope'})
  with patch.object(self,'query',side_effect=no_scope):receipt=await self.capture()
  record=self.record(receipt);self.assertFalse(record['complete_state_available'])
  self.assertEqual(record['export_result']['reason'],'no-proof-scope')
  self.assertEqual(record['returned_result'],result);self.assertEqual(self.result,result)
  self.assertNotIn('complete_state',record);self.assertNotIn('kernel_groups',record)
 async def test_other_export_failure_is_explicit(self):
  async def failure(*args):raise RuntimeError('fixture export failure')
  with patch.object(self,'query',side_effect=failure):receipt=await self.capture()
  self.assertFalse(receipt['success']);self.assertEqual(self.record(receipt)['export_error'],'fixture export failure')
 async def test_wrong_state_refuses_capture(self):
  self.export['state_id']=9;receipt=await self.capture()
  self.assertFalse(receipt['success']);self.assertIn('another returned state',self.record(receipt)['export_error'])
 async def test_changed_export_refuses_capture(self):
  self.export_path.write_text('{}');receipt=await self.capture()
  self.assertFalse(receipt['success']);self.assertIn('changed',self.record(receipt)['export_error'])
 async def test_incomplete_kernel_groups_refuse_capture(self):
  self.payload['kernel_groups']['shelf']=[];P.atomic_json(self.export_path,self.payload)
  self.export.update(P.binding(self.export_path));receipt=await self.capture()
  self.assertFalse(receipt['success']);self.assertIn('goal group',self.record(receipt)['export_error'])
 async def test_restarted_pet_is_not_queried(self):
  receipt=await self.capture(dict(self.result,pet_restarted=True))
  self.assertFalse(receipt['success']);self.assertEqual(self.calls,[])
 async def test_cancelled_export_records_failure_and_preserves_cancellation(self):
  async def cancelled(*args):raise asyncio.CancelledError('fixture cancellation')
  with patch.object(self,'query',side_effect=cancelled):
   with self.assertRaises(asyncio.CancelledError):await self.capture()
  record=json.loads((self.output/'long-checks/call-0001/RESULT.json').read_text())
  self.assertFalse(record['success']);self.assertIn('CancelledError',record['export_error'])
 async def test_private_directory_alias_refuses(self):
  other=self.output/'other';other.mkdir();(self.output/'long-checks').symlink_to(other)
  with self.assertRaises(ValueError):await self.capture()
 async def test_noncheck_does_not_export(self):
  self.assertIsNone(await P.retain_long_check(self.query,None,'rocq_compile_file',self.arguments,
       self.result,self.output,1,90,self.markers));self.assertEqual(self.calls,[])
 async def test_directory_durability_precedes_return(self):
  original=os.fsync;calls=[]
  def synced(fd):calls.append(stat.S_ISDIR(os.fstat(fd).st_mode));return original(fd)
  with patch.object(P.os,'fsync',side_effect=synced):receipt=await self.capture()
  self.assertTrue(receipt['success']);self.assertEqual(sum(calls),3)
 async def test_actual_call_exports_before_return_without_changing_result(self):
  tree=ast.parse(Path(P.__file__).read_text());execute=next(n for n in tree.body if isinstance(n,ast.AsyncFunctionDef) and n.name=='execute')
  function=next(n for n in execute.body if isinstance(n,ast.AsyncFunctionDef) and n.name=='call')
  namespace=dict(vars(P),runtime={'phase':'prerequisites'},calls=[],output=self.output,
                 native_body='zesu_block.',check_operation=lambda *a,**kw:{'success':True})
  exec(compile(ast.Module(body=[function],type_ignores=[]),str(P.__file__),'exec'),namespace)
  observed=[];owner=self
  class Session:
   async def call_tool(self,name,arguments):
    observed.append(name);value=owner.result if name=='rocq_check' else owner.export
    return SimpleNamespace(structuredContent=value,content=[],isError=False,
       model_dump=lambda **kwargs:{'structuredContent':value})
  value=await namespace['call'](Session(),'rocq_check',self.arguments)
  self.assertIs(value,self.result);self.assertEqual(observed,['rocq_check','rocq_complete_goals'])
  self.assertTrue(namespace['calls'][0]['long_check_state']['success'])
  self.assertIn('post_operation_validation',namespace['calls'][0])
  self.assertEqual(self.record(namespace['calls'][0]['long_check_state'])['returned_result'],self.result)

if __name__=='__main__':unittest.main()
