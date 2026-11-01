"""Source-only launcher controls. No native proof or admission runs."""
from pathlib import Path
from unittest.mock import patch
import json,tempfile,unittest
import scratch
import _test_support
ENTRY=Path(json.loads((_test_support.LEGACY/'_build/check-entry-stage1-passfix-ten-runtime-v2/release-v1/RUNTIME.json').read_text())['prepared_workspace'])/'artifacts/default/ZesuSsz/Generated/DecodeItem/Entries.v'
class CacheOptionControls(unittest.TestCase):
 def test_default_remains_confirmation(self):
  with tempfile.TemporaryDirectory() as directory:
   args=_test_support.arguments(['800d6a64',str(ENTRY),'--output',directory+'/out'])
  self.assertEqual(args.cache,'off')
  runtime={'result_cache':{'directory':'/private/cache'},'cache_policy':{'lookup_before_admission':True}}
  scratch.configure_cache(runtime,args.cache)
  self.assertEqual(runtime['result_cache']['purpose'],'confirmation')
  self.assertFalse(runtime['cache_policy']['enabled'])
  self.assertEqual(scratch.runtime_cache_setting(runtime),'off')
 def test_checkpoint_selects_exploration(self):
  with tempfile.TemporaryDirectory() as directory:
   args=_test_support.arguments(['800d6a64',str(ENTRY),'--cache','on','--output',directory+'/out'])
  runtime={'result_cache':{'directory':'/private/cache'},'cache_policy':{'lookup_before_admission':True}}
  scratch.configure_cache(runtime,args.cache)
  self.assertEqual(runtime['result_cache']['purpose'],'exploration')
  self.assertTrue(runtime['cache_policy']['enabled'])
  self.assertTrue(runtime['cache_policy']['lookup_before_admission'])
  self.assertEqual(scratch.runtime_cache_setting(runtime),'on')
 def test_unsupported_cache_option_refuses(self):
  with self.assertRaises(SystemExit):_test_support.arguments(['800d6a64',str(ENTRY),'--cache','perhaps'])
 def test_declaration_cache_refuses(self):
  with self.assertRaises(SystemExit):_test_support.arguments(['800d6a64',str(ENTRY),'--cache','on','--declarations-only'])
 def test_unsupported_runtime_purpose_refuses(self):
  with self.assertRaises(ValueError):scratch.runtime_cache_setting({'result_cache':{'purpose':'perhaps'}})
 def test_summary_reports_requested_cache_mode(self):
  with tempfile.TemporaryDirectory() as directory:
   path=Path(directory);(path/'RESULT.json').write_text('{}')
   result={'status':'infrastructure_failed','cache_status':'fresh'}
   self.assertEqual(scratch.summarize(result,path,'on')['cache'],'on; exploration checkpoint')
   self.assertEqual(scratch.summarize(result,path)['cache'],'off; confirmation rule test')
 def test_execution_environment_and_summary_match(self):
  for setting in ['off','on']:
   with self.subTest(setting=setting),tempfile.TemporaryDirectory() as directory:
    out=Path(directory);native=out/'native';native.mkdir()
    config={'bindings':[],'jobs':[{'key':'prerequisites','ordered_modules':[],'output':str(out/'pre')},{'key':'800d6a64','output':str(native)}],'job_controller':{'path':'unused-controller'},'result_cache':{'directory':'/private/cache'}}
    scratch.configure_cache(config,setting)
    path=out/'RUNTIME.json';path.write_text(json.dumps(config));(out/'INPUTS.json').write_text('{}')
    (native/'RESULT.json').write_text(json.dumps({'status':'infrastructure_failed','error':'Deliberate fixture. No native launch.'}))
    with patch('restart_bindings.verify_restart_runtime'),patch.object(scratch,'check_proof_bindings'),patch.object(scratch.subprocess,'run') as run,patch.dict(scratch.os.environ,{'ZESU_IO':'','ZESU_PROOF_CACHE':'opposite'}):
     self.assertEqual(scratch.execute(path,scratch.digest(path)),2)
    self.assertEqual(run.call_args.kwargs['env']['ZESU_PROOF_CACHE'],setting)
    summary=json.loads((out/'RESULT.json').read_text())
    self.assertEqual(summary['cache'].split(';')[0],setting)
 def test_gate_cannot_opt_into_checkpoint_cache(self):
  with tempfile.TemporaryDirectory() as directory:
   out=Path(directory);config={'bindings':[],'jobs':[{},{}],'result_cache':{'purpose':'exploration'}};path=out/'RUNTIME.json';path.write_text(json.dumps(config))
   with patch('restart_bindings.verify_restart_runtime'),patch.object(scratch,'check_proof_bindings'),patch.object(scratch.subprocess,'run') as run,patch.dict(scratch.os.environ,{'ZESU_IO':'gate'}):
    with self.assertRaisesRegex(ValueError,'gate cannot'):scratch.execute(path,scratch.digest(path))
   run.assert_not_called()
if __name__=='__main__':unittest.main()
