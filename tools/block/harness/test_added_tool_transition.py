"""Refresh an old layout twice, then stage current tools without a compiler."""
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch
import json,os,shutil,subprocess,sys,tempfile,unittest
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE),str(HERE.parents[1]),str(HERE.parents[2])]
import clone_copy,harness_commit,restart_bindings as restart,scratch,entry_chain_run
from compiler_snapshot import binding_rows

OLD_LAYOUT=HERE/'test-fixtures/tool-transition/b4ca-TOOL-LAYOUT.json'

class AddedToolTransition(unittest.TestCase):
 def setUp(self):
  temporary=tempfile.TemporaryDirectory(dir=os.environ.get('TMPDIR'))
  self.addCleanup(temporary.cleanup);self.root=Path(temporary.name).resolve()
  self.workspace=self.root/'prepared';self.workspace.mkdir()
  # Materialize a genuine detached predecessor from a tracked old-layout
  # fixture. No historical worktree or agent evidence is a test dependency.
  repository=self.root/'repository';repository.mkdir()
  old_here=repository/'tools/block/harness';old_here.mkdir(parents=True)
  old_layout=json.loads(OLD_LAYOUT.read_text())
  (old_here/'TOOL-LAYOUT.json').write_bytes(OLD_LAYOUT.read_bytes())
  for source in old_layout.values():
   target=old_here/source;target.parent.mkdir(parents=True,exist_ok=True)
   clone_copy.copy2(HERE/source,target)
  def git(*args):
   return subprocess.run(['git','-C',str(repository),*args],check=True,capture_output=True,text=True).stdout.strip()
  git('init','-q');git('config','user.name','Nonproof fixture');git('config','user.email','fixture@example.invalid')
  git('add','tools');git('commit','-qm','Authenticated old-layout fixture')
  self.old=harness_commit.checkout(git('rev-parse','HEAD'),repository)
  self.current={'commit':'nonproof-target-fixture','root':str(HERE.parents[2])}
  real=harness_commit.check
  check=patch('harness_commit.check',side_effect=lambda row:True if row==self.current else real(row))
  check.start();self.addCleanup(check.stop)
  pin=patch('harness_commit.pin',return_value=self.current);pin.start();self.addCleanup(pin.stop)
  old_here=Path(self.old['root'])/'tools/block/harness'
  self.new='block/port_heldout_authority.py'
  self.assertNotIn(self.new,old_layout)
  transitions=[]
  for relative,source in old_layout.items():
   target=self.workspace/'tools'/relative;target.parent.mkdir(parents=True,exist_ok=True)
   clone_copy.copy2(old_here/source,target)
   transitions.append(dict(relative=relative,prepared=restart.binding(target),successor=restart.binding(old_here/source)))
  for name in ['_CoqProject','_RocqProject']:(self.workspace/name).write_text('')
  source=self.workspace/'Control.v';source.write_text('Lemma control : True. Proof. exact I. Qed.\n')
  obj=source.with_suffix('.vo');obj.write_bytes(b'nonproof historical object fixture')
  compiler=self.root/'nonproof-compiler';compiler.write_bytes(b'Nonproof compiler fixture version 1. Never executed.\n')
  jobs=[dict(key='prerequisites',phase='prerequisites',ordered_modules=[],output=str(self.root/'old-jobs/prerequisites')),
        dict(key='control',phase='native',ordered_modules=[],target={'module':'Control'},output=str(self.root/'old-jobs/control'))]
  from memory_policy import apply_job
  jobs=[apply_job(row) for row in jobs]
  self.config=dict(harness=self.old,prepared_workspace=str(self.workspace),prepared_tool_transition=transitions,
   bindings=[restart.binding(source),restart.binding(obj),restart.binding(compiler)]+[row['prepared'] for row in transitions],
   effective_compiler_version={'text':'Nonproof compiler fixture version 1. Never executed.','compiler':restart.binding(compiler)},
   jobs=jobs,proof_runtime={'module_files':{'Control':'Control.v'},'mcp_argv':[sys.executable]},
   cache_producer_files={'implementation':[],'inputs':[],'outputs':[]},cache_attempt={'limits':{'memory_bytes':64*1024**3}},
   admission={'reviewed_helpers':str(old_here/'code/entry_admission')},aggregate_memory_ceiling_bytes=64*1024**3,
   adoption_implementation=restart.binding(old_here/'code/full_chain.py'),
   job_controller=restart.binding(old_here/'code/entry_chain_run.py'),guard_override=restart.binding(old_here/'runtime-tools/resource_guard.sh'),
   guard_override_base=restart.binding(old_here/'runtime-tools/resource_guard.sh'),identity={'fixture':'nonproof'},
   expected_mcp_flags=[],physical_flags=[],guard_helper_paths=[],declarations_only=True)
  self.prior=self.root/'PRIOR.json';scratch.save(self.prior,self.config)
  self.original=[dict(row) for row in self.config['bindings']]
  self.measured=self.root/'MEASUREMENTS.json';scratch.save(self.measured,{'rows':[]})

 def refresh(self,path=None,name='refresh001'):
  path=path or self.prior
  args=[str(path),restart.binding(path)['sha256'],'--completed-stock-measurements',str(self.measured),
        '--harness-commit',self.current['commit'],'--output',str(self.root/name),'--end-cleanup','off']
  # Unit fixtures have no resource admission. The public function still performs
  # all runtime, policy, binding, predecessor, and destination checks.
  with patch('command_scope.require'):
   self.assertEqual(scratch.refresh_memory(args),0)
  result=self.root/name/'RUNTIME.json'
  return result,json.loads(result.read_text())

 def test_two_refreshes_then_actual_stage_job(self):
  first,c=self.refresh();second,c=self.refresh(first,'refresh002')
  self.assertFalse((self.workspace/'tools'/self.new).exists())
  self.assertTrue(restart.verify_restart_runtime(c,HERE))
  for row in self.original:self.assertIn(row,c['bindings']);self.assertEqual(restart.binding(row['path']),row)
  job=deepcopy(c['jobs'][0]);job['policy']={'minimum_claim_bytes':job['claim_bytes'],'physical_fence_bytes':job['physical_fence_bytes'],'memory_job':deepcopy(job)}
  out=self.root/'stage';out.mkdir()
  runtime,workspace=entry_chain_run.stage_job(c,job,out)
  self.assertEqual(runtime['physical_compiler'],c['effective_compiler_version']['compiler'])
  target=workspace/'tools'/self.new
  self.assertEqual(restart.binding(target)['sha256'],restart.binding(HERE/'code/port_heldout_authority.py')['sha256'])
  self.assertNotEqual(target.stat().st_ino,(HERE/'code/port_heldout_authority.py').stat().st_ino)
  self.assertFalse((self.workspace/'tools'/self.new).exists())
  self.assertTrue(all(row in binding_rows(runtime) for row in self.original))
  self.assertEqual(json.loads((out/'COMPILER-IMPORT-CONTROL.json').read_text())['returncode'],0)
  self.assertFalse((out/'STARTED.json').exists());self.assertFalse((out/'native/CALLS.json').exists())

 def test_sealed_seed_refuses_before_any_write(self):
  _,c=self.refresh();c['seed_binding_reference']={'descriptor':{'fixture':True}}
  out=self.root/'sealed-job';out.mkdir()
  before={str(p):restart.binding(p) for p in self.workspace.rglob('*') if p.is_file()}
  with patch('seed_bindings.descriptor',return_value={'sealed_boundary':True}),patch('seed_bindings.validate'):
   with self.assertRaisesRegex(ValueError,'fresh unsealed'):entry_chain_run.stage_job(c,c['jobs'][0],out)
  self.assertEqual(before,{str(p):restart.binding(p) for p in self.workspace.rglob('*') if p.is_file()})
  self.assertEqual(list(out.iterdir()),[])

 def test_deleted_previously_required_tool_refuses(self):
  (self.workspace/'tools/block/binding_cache.py').unlink()
  with self.assertRaises(FileNotFoundError):self.refresh()

 def test_appeared_destination_refuses(self):
  _,c=self.refresh();target=self.workspace/'tools'/self.new
  clone_copy.copy2(HERE/'code/port_heldout_authority.py',target)
  with self.assertRaises(ValueError):restart.verify_restart_runtime(c,HERE)

 def test_appeared_symlink_refuses(self):
  _,c=self.refresh();(self.workspace/'tools'/self.new).symlink_to(self.root/'absent')
  with self.assertRaises(ValueError):restart.verify_restart_runtime(c,HERE)

 def test_prior_runtime_mutation_refuses(self):
  _,c=self.refresh();self.prior.write_text(self.prior.read_text()+' ')
  with self.assertRaisesRegex(ValueError,'predecessor runtime changed'):restart.verify_restart_runtime(c,HERE)

 def test_prior_layout_binding_refuses(self):
  _,c=self.refresh();row=next(row for row in c['prepared_tool_transition'] if row['relative']==self.new)
  row['absent']['layout']['sha256']='0'*64
  with self.assertRaisesRegex(ValueError,'pinned layout'):restart.verify_restart_runtime(c,HERE)

 def test_wrong_successor_refuses(self):
  _,c=self.refresh();row=next(row for row in c['prepared_tool_transition'] if row['relative']==self.new)
  row['successor']['sha256']='0'*64
  with self.assertRaisesRegex(ValueError,'another source'):restart.verify_restart_runtime(c,HERE)

 def test_second_refresh_checks_original_absence(self):
  first,c=self.refresh();(self.workspace/'tools'/self.new).write_bytes(b'new appearance')
  with self.assertRaises(ValueError):self.refresh(first,'refresh002')

 def test_new_job_destination_appearance_refuses(self):
  _,c=self.refresh();copy=self.root/'clone';clone_copy.copytree(self.workspace,copy)
  clone_copy.copy2(HERE/'code/port_heldout_authority.py',copy/'tools'/self.new)
  with self.assertRaisesRegex(ValueError,'appeared in the new job'):restart.install_restart_tools(copy,c,HERE)

 def test_exclusive_publication_refuses_replacement(self):
  target=self.root/'target';target.write_bytes(b'other actor')
  with self.assertRaises(FileExistsError):restart.install_absent(HERE/'code/port_heldout_authority.py',target)
  self.assertEqual(target.read_bytes(),b'other actor')

 def test_removed_layout_entry_stays_historical(self):
  # A removed successor entry must still validate the predecessor file.
  config=deepcopy(self.config);config['harness']=self.current;config['bindings'].append(restart.binding(self.prior))
  layout=json.loads((HERE/'TOOL-LAYOUT.json').read_text());removed=next(iter(layout));layout.pop(removed)
  with patch.object(restart.json,'loads',wraps=json.loads) as loads:
   real=loads._mock_wraps
   loads.side_effect=lambda text,*a,**kw:layout if text==(HERE/'TOOL-LAYOUT.json').read_text() else real(text,*a,**kw)
   rows=restart.prepared_transitions(config,HERE,restart.binding(self.prior))
  self.assertNotIn(removed,{row['relative'] for row in rows})
  old=next(row['prepared'] for row in self.config['prepared_tool_transition'] if row['relative']==removed)
  self.assertEqual(restart.binding(old['path']),old);self.assertIn(old,config['bindings'])

if __name__=='__main__':unittest.main()
