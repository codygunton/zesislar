"""Use disposable processes to test registered controller cancellation."""
from pathlib import Path
import json,os,signal,subprocess,sys,tempfile,time,unittest
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE.parents[2])]
import controller_cleanup as C

class ControllerCleanup(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name)
 def test_failure_closes_registered_child_and_keeps_foreign_process(self):
  foreign=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)'])
  self.addCleanup(foreign.wait)
  self.addCleanup(lambda:foreign.terminate() if foreign.poll() is None else None)
  with self.assertRaisesRegex(RuntimeError,'injected'):
   with C.Supervisor(self.root) as supervisor:
    child=supervisor.launch([sys.executable,'-c','import time;time.sleep(60)'])
    raise RuntimeError('injected controller failure')
  self.assertIsNotNone(child.poll());self.assertIsNone(foreign.poll())
  report=json.loads((self.root/'CONTROLLER-EXIT-CLEANUP.json').read_text())
  self.assertTrue(report['all_registered_children_closed']);self.assertFalse(report['SIGKILL_covered'])
 def test_launch_time_signal_is_deferred_until_identity_registration(self):
  original=C.subprocess.Popen
  def launched(*args,**kwargs):
   process=original(*args,**kwargs);os.kill(os.getpid(),signal.SIGTERM);return process
  with self.assertRaises(SystemExit) as raised:
   with C.Supervisor(self.root) as supervisor:
    with patch.object(C.subprocess,'Popen',side_effect=launched):
     supervisor.launch([sys.executable,'-c','import time;time.sleep(60)'])
  self.assertEqual(raised.exception.code,143)
  report=json.loads((self.root/'CONTROLLER-EXIT-CLEANUP.json').read_text())
  self.assertEqual(len(report['children']),1);self.assertTrue(report['all_registered_children_closed'])
 def test_wrong_actor_identity_cannot_receive_signal(self):
  with C.Supervisor(self.root) as supervisor:
   child=supervisor.launch([sys.executable,'-c','import time;time.sleep(60)'])
   row=supervisor.children[0];process,actor,descriptor=row['process'],row['actor'],row['pidfd']
   with patch.object(C,'live',return_value=False),patch.object(C,'signal_pidfd') as send:
    child.terminate();child.wait();supervisor.cleanup();send.assert_not_called()
 def registration_failure(self, target):
  spawned=[];original=C.subprocess.Popen
  def launched(*a,**kw):
   process=original(*a,**kw);spawned.append(process);return process
  supervisor=C.Supervisor(self.root)
  try:
   with self.assertRaisesRegex(RuntimeError,'unclosed or unknown'):
    with supervisor:
     with patch.object(C.subprocess,'Popen',side_effect=launched),patch.object(C,target,side_effect=OSError('injected registration failure')),patch.object(C,'signal_pidfd') as send:
      try:supervisor.launch([sys.executable,'-c','import time;time.sleep(60)'])
      finally:
       self.assertFalse(C.children_closed());send.assert_not_called()
   report=json.loads((self.root/'CONTROLLER-EXIT-CLEANUP.json').read_text())
   self.assertEqual(len(report['children']),1);self.assertFalse(report['all_registered_children_closed'])
   self.assertFalse(report['children'][0]['authenticated'])
  finally:
   for process in spawned:
    if process.poll() is None:process.terminate()
    process.wait()
 def test_identity_lookup_failure_retains_unknown_child_without_signal(self):self.registration_failure('identity')
 def test_pidfd_open_failure_retains_unknown_child_without_signal(self):self.registration_failure('open_pidfd')
 def test_normal_exit_closes_a_live_registered_child(self):
  with C.Supervisor(self.root) as supervisor:
   child=supervisor.launch([sys.executable,'-c','import time;time.sleep(60)'])
  self.assertIsNotNone(child.poll())
  self.assertTrue(json.loads((self.root/'CONTROLLER-EXIT-CLEANUP.json').read_text())['all_registered_children_closed'])
 def test_normal_completion_keeps_exit_evidence(self):
  with C.Supervisor(self.root):
   result=C.run([sys.executable,'-c','raise SystemExit(7)'])
  self.assertEqual(result.returncode,7)

class ClaimReleaseControls(unittest.TestCase):
 def test_unregistered_spawn_cannot_release_claim(self):
  import entry_chain_run as E
  from memory_policy import apply_job
  from types import SimpleNamespace
  with tempfile.TemporaryDirectory() as folder:
   root=Path(folder);out=root/'job'
   job=apply_job({'phase':'prerequisites','key':'fixture','ordered_modules':[]})
   config={'identity':{'fixture':True},'admission':{},'shared_latch':str(root/'latch')}
   unknown=SimpleNamespace(pid=99999999,poll=lambda:None)
   with patch('restart_bindings.verify_restart_runtime'),patch.object(E,'normalize_cpu'),patch.object(E,'reserve'),patch.object(E,'binding_recheck'),patch.object(E,'stage_job',return_value=({'bindings':[]},root)),patch.object(E,'outer_argv',return_value=['fixture']),patch.object(C,'launch',side_effect=OSError('injected pidfd failure')),patch.object(C,'last_child',return_value=(unknown,None)),patch.object(C,'cleanup',side_effect=RuntimeError('unknown actor')),patch.object(C,'children_closed',return_value=False),patch.object(E,'release') as release,patch.object(E.entry_chain_result,'summarize',return_value={}):
    with self.assertRaisesRegex(RuntimeError,'unknown actor'):E.run_stock_job(config,job,out)
    release.assert_not_called()
   closure=json.loads((out/'CLOSURE.json').read_text())
   self.assertFalse(closure['all_owned_actors_closed'])
   self.assertFalse(closure['actors'][0]['ended'])
   self.assertFalse((out/'RELEASE.json').exists())

if __name__=='__main__':unittest.main()
