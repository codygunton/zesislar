import json,os,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import end_run_cleanup as C
import scratch
import _test_support


class Cleanup(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
  self.root=Path(self.temp.name)/'run';self.root.mkdir();self.job=self.root/'jobs/native';self.job.mkdir(parents=True)
  self.config={'prepared_workspace':str(self.root/'prepared'),'jobs':[{'key':'native','phase':'native','output':str(self.job)}]}
  self.js(self.root/'RESULT.json',{'status':'open'});self.js(self.job/'RESULT.json',{'status':'native_open'})
  self.js(self.job/'CLOSURE.json',{'all_owned_actors_closed':True,'actors':[],'claim_key':'run'})
  self.js(self.job/'RELEASE.json',{'released':True,'claim_key':'run','bytes':16*1024**3})
  self.js(self.job/'DISPATCH-FINISHED.json',{'result':C.binding(self.job/'RESULT.json')})
 def js(self,p,v):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v));return p
 def file(self,path,size=1_000_000):
  p=Path(path);p.parent.mkdir(parents=True,exist_ok=True)
  with p.open('wb') as f:f.truncate(size)
  return p
 def finish(self):return C.finish(self.config,self.root)
 def test_default_on_retains_evidence_sources_and_small_files(self):
  large=self.file(self.job/'workspace/build/Large.vo')
  kept=[self.file(self.job/('workspace/'+name),size) for name,size in [('Small.vo',999999),('Entries.v',2000000),('STATE.json',2000000),('certificate.md',2000000),('PACKET.bin',2000000)]]
  packet=self.file(self.root/'packets/Evidence.vo',2000000)
  report=self.finish();self.assertEqual(report['status'],'cleaned');self.assertFalse(large.exists())
  self.assertTrue(all(p.exists() for p in kept+[packet]));self.assertIsNone(report['physical_recovery_bytes'])
  self.assertTrue((self.root/'END-RESULT-SEALED.json').exists())
 def test_cleans_both_owned_copy_roots(self):
  a=self.file(self.root/'prepared/artifacts/default/A.vo');b=self.file(self.job/'workspace/artifacts/default/B.cmxs')
  self.assertEqual(self.finish()['removed_count'],2);self.assertFalse(a.exists());self.assertFalse(b.exists())
 def test_reuse_off_preserves_seed_and_readiness(self):
  a=self.file(self.root/'prepared/artifacts/default/A.vo');self.js(self.root/'READINESS.json',{'objects':[C.binding(a)]})
  self.config['end_of_run_cleanup']=C.policy(False);report=self.finish()
  self.assertEqual(report['status'],'disabled');self.assertTrue(a.exists());self.assertTrue((self.root/'READINESS.json').exists())
 def test_failed_or_killed_job_cleans_only_after_seal_and_closure(self):
  for status in ['infrastructure_failed','killed']:
   with self.subTest(status=status):
    self.js(self.root/'RESULT.json',{'status':status});a=self.file(self.job/'workspace/Failed.vo')
    (self.root/'END-CLEANUP.json').unlink(missing_ok=True);(self.root/'END-RESULT-SEALED.json').unlink(missing_ok=True)
    self.assertEqual(self.finish()['status'],'cleaned');self.assertFalse(a.exists())
 def test_kill_before_result_seal_refuses(self):
  a=self.file(self.job/'workspace/A.vo');(self.root/'RESULT.json').unlink()
  self.assertEqual(self.finish()['status'],'refused');self.assertTrue(a.exists())
 def test_missing_release_refuses(self):
  a=self.file(self.job/'workspace/A.vo');(self.job/'RELEASE.json').unlink()
  self.assertEqual(self.finish()['status'],'refused');self.assertTrue(a.exists())
 def test_recorded_active_actor_refuses(self):
  a=self.file(self.job/'workspace/A.vo');self.js(self.job/'CLOSURE.json',{'all_owned_actors_closed':False,'actors':[],'claim_key':'run'})
  self.assertEqual(self.finish()['status'],'refused');self.assertTrue(a.exists())
 def test_live_actor_refuses_even_with_closed_receipt(self):
  a=self.file(self.job/'workspace/A.vo');ticks=int(Path('/proc/self/stat').read_text().rsplit(')',1)[1].split()[19])
  self.js(self.job/'CLOSURE.json',{'all_owned_actors_closed':True,'actors':[{'pid':os.getpid(),'startticks':ticks,'ended':True}],'claim_key':'run'})
  self.assertEqual(self.finish()['status'],'refused');self.assertTrue(a.exists())
 def test_foreign_job_root_refuses_before_deletion(self):
  a=self.file(self.job/'workspace/A.vo');self.config['jobs'][0]['output']=str(self.root.parent/'foreign')
  self.assertEqual(self.finish()['status'],'refused');self.assertTrue(a.exists())
 def test_parent_traversal_refuses(self):
  a=self.file(self.job/'workspace/A.vo');self.config['jobs'][0].update(key='../../foreign',output=str(self.root/'jobs/../../foreign'))
  self.assertEqual(self.finish()['status'],'refused');self.assertTrue(a.exists())
 def test_external_prepared_seed_stays_untouched(self):
  a=self.file(self.root.parent/'seed/A.vo');self.config['prepared_workspace']=str(a.parent)
  report=self.finish();self.assertEqual(report['status'],'cleaned');self.assertTrue(a.exists())
 def test_symlink_copy_root_refuses(self):
  target=self.root.parent/'foreign';target.mkdir();a=self.file(target/'A.vo');(self.job/'workspace').symlink_to(target,target_is_directory=True)
  self.assertEqual(self.finish()['status'],'refused');self.assertTrue(a.exists())
 def test_nested_symlink_is_never_followed(self):
  target=self.root.parent/'foreign';target.mkdir();a=self.file(target/'A.vo');root=self.job/'workspace';root.mkdir();(root/'outside').symlink_to(target,target_is_directory=True)
  self.assertEqual(self.finish()['status'],'cleaned');self.assertTrue(a.exists())
 def test_native_processing_must_finish_before_cleanup(self):
  a=self.file(self.job/'workspace/A.vo');(self.job/'DISPATCH-FINISHED.json').unlink()
  self.assertEqual(self.finish()['status'],'refused');self.assertTrue(a.exists())
 def test_outer_execute_finally_calls_cleanup_on_failure(self):
  runtime=self.root/'RUNTIME.json';self.js(runtime,self.config)
  with patch.object(scratch,'execute_retained',side_effect=KeyboardInterrupt),patch.object(C,'finish',return_value={}) as finish:
   with self.assertRaises(KeyboardInterrupt):scratch.execute(runtime,C.binding(runtime)['sha256'])
  finish.assert_called_once()
 def test_cli_default_and_explicit_off(self):
  entry=self.file(self.root/'Entries.v',0);argv=['800d6960',str(entry),'--output',str(self.root/'new')]
  with patch.object(scratch,'read_bound',return_value={'targets':{},'rows':[{'pc':2148362592,'key':'800d6960'}]}):
   self.assertEqual(_test_support.arguments(argv).end_cleanup,'on')
   self.assertEqual(_test_support.arguments(argv+['--end-cleanup','off']).end_cleanup,'off')

if __name__=='__main__':unittest.main()
