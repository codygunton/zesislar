"""Test reference release and exact restoration without a proof or compiler."""
from pathlib import Path
import ast,copy,gc,json,os,sys,tempfile,unittest,weakref
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE),str(HERE.parent),str(HERE.parents[1])]
import waiting_envelope as W
import binding_cache as B
import proof_bindings as P
import supplier_ready as S
from entry_chain import binding,save
from entry_chain_resources import check_operation,session_validation

class Payload(dict):pass

class WaitingEnvelope(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name).resolve()
 def test_wait_releases_references_and_restores_same_dictionary(self):
  payload=Payload(path='/nonproof',sha256='a'*64);reference=weakref.ref(payload)
  config={'bindings':[payload],'small':{'value':7}};original=copy.deepcopy(config);address=id(config)
  # The expected comparison must not retain the weak-reference fixture object.
  original=json.loads(json.dumps(original));del payload
  with W.compact_wait(self.root,configuration=config) as checkpoint:
   self.assertEqual(id(config),address);self.assertEqual(set(config),{'waiting_envelope'})
   self.assertIsNone(reference());self.assertEqual(Path(checkpoint['path']).stat().st_mode&0o777,0o600)
  self.assertEqual(config,original);self.assertEqual(id(config),address)
 def test_tool_failure_restores_original_before_propagation(self):
  config={'bindings':[{'path':'source','sha256':'b'*64}],'job':'same'};before=copy.deepcopy(config)
  with self.assertRaisesRegex(RuntimeError,'tool failure'):
   with W.compact_wait(self.root,configuration=config):raise RuntimeError('tool failure')
  self.assertEqual(config,before)
 def test_checkpoint_mutation_refuses_restoration(self):
  config={'bindings':[]}
  with self.assertRaisesRegex(ValueError,'identity changed|bytes changed'):
   with W.compact_wait(self.root,configuration=config) as checkpoint:Path(checkpoint['path']).write_text('{}')
  self.assertIn('waiting_envelope',config)
  report=json.loads(Path(checkpoint['path']).with_suffix('.receipt.json').read_text())
  self.assertFalse(report['restored']);self.assertIn('restore_error',report)
 def test_identical_bytes_inode_replacement_refuses(self):
  config={'bindings':[]}
  with self.assertRaisesRegex(ValueError,'identity changed'):
   with W.compact_wait(self.root,configuration=config) as checkpoint:
    path=Path(checkpoint['path']);other=self.root/'replacement';other.write_bytes(path.read_bytes());other.chmod(0o600);os.replace(other,path)
 def test_suspended_dictionary_mutation_refuses(self):
  config={'bindings':[]}
  with self.assertRaisesRegex(ValueError,'suspended dictionary changed'):
   with W.compact_wait(self.root,configuration=config):config['changed']=True
 def test_yielded_reference_cannot_rebind_checkpoint(self):
  config={'bindings':[]}
  with self.assertRaisesRegex(ValueError,'identity changed|bytes changed'):
   with W.compact_wait(self.root,configuration=config) as checkpoint:
    path=Path(checkpoint['path']);path.write_text('{}');checkpoint['sha256']='changed caller reference'
 def test_checkpoint_symlink_refuses(self):
  config={'bindings':[]}
  with self.assertRaisesRegex(ValueError,'private owned file'):
   with W.compact_wait(self.root,configuration=config) as checkpoint:
    source=Path(checkpoint['path']);target=self.root/'other';source.rename(target);source.symlink_to(target)
 def test_checkpoint_mode_change_refuses(self):
  config={'bindings':[]}
  with self.assertRaisesRegex(ValueError,'private owned file'):
   with W.compact_wait(self.root,configuration=config) as checkpoint:Path(checkpoint['path']).chmod(0o644)
 def test_checkpoint_hardlink_refuses(self):
  config={'bindings':[]}
  with self.assertRaisesRegex(ValueError,'private owned file'):
   with W.compact_wait(self.root,configuration=config) as checkpoint:os.link(checkpoint['path'],self.root/'alias')
 def test_different_process_identity_refuses(self):
  config={'bindings':[]}
  with W.compact_wait(self.root,configuration=config) as checkpoint:
   owner={'pid':os.getpid(),'startticks':0,'uid':os.getuid()}
   with self.assertRaisesRegex(ValueError,'another controller'):W.read_checkpoint(checkpoint,owner)
 def test_repeated_dictionary_alias_refuses_before_suspension(self):
  config={'bindings':[]}
  with self.assertRaisesRegex(ValueError,'repeats'):
   with W.compact_wait(self.root,one=config,two=config):pass
  self.assertEqual(config,{'bindings':[]})
 def test_nested_suspension_restores_each_exact_object(self):
  outer={'one':[1,2]};inner={'two':[3,4]}
  with W.compact_wait(self.root,outer=outer):
   with W.compact_wait(self.root,inner=inner):self.assertIn('waiting_envelope',outer)
   self.assertEqual(inner,{'two':[3,4]})
  self.assertEqual(outer,{'one':[1,2]})
 def test_final_full_validation_rejects_source_mutation_after_wait(self):
  source=self.root/'source.v';source.write_text('unchanged fixture')
  runtime={'bindings':[binding(source)]};path=self.root/'RUNTIME.json';save(path,runtime)
  reference=binding(path);runtime.update(runtime_path=str(path),runtime_sha256=reference['sha256'])
  with self.assertRaisesRegex(ValueError,'changed'):
   with session_validation(path,reference['sha256']) as state:
    check_operation(runtime,force_full=True)
    with W.compact_wait(self.root,runtime=runtime):source.write_text('changed fixture')
  self.assertFalse(state.final['success']);self.assertEqual(state.full_attempts,2)
 def test_final_full_validation_runs_after_tool_failure(self):
  source=self.root/'source.v';source.write_text('unchanged fixture')
  runtime={'bindings':[binding(source)]};path=self.root/'RUNTIME.json';save(path,runtime)
  reference=binding(path);runtime.update(runtime_path=str(path),runtime_sha256=reference['sha256'])
  with self.assertRaisesRegex(RuntimeError,'tool failure'):
   with session_validation(path,reference['sha256']) as state:
    check_operation(runtime,force_full=True)
    with W.compact_wait(self.root,runtime=runtime):raise RuntimeError('tool failure')
  self.assertTrue(state.final['success']);self.assertEqual(state.full_attempts,2)
 def test_kernel_branch_retains_original_outer_workspace_cwd(self):
  import entry_chain_run as E
  from types import SimpleNamespace
  outer=self.root/'outer';(outer/'workspace').mkdir(parents=True)
  kernel=outer/'kernel-check';kernel.mkdir()
  save(kernel/'KERNEL-ARGV.json',['nonproof-command'])
  save(kernel/'KERNEL-ENVIRONMENT.json',{})
  runtime={'job_output':str(outer),'bindings':[]};before=copy.deepcopy(runtime)
  tree=ast.parse(Path(E.__file__).read_text())
  function=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='inside')
  branch=next(n for n in ast.walk(function) if isinstance(n,ast.If) and
     any(isinstance(value,ast.Constant) and value.value=='KERNEL-ARGV.json' for value in ast.walk(n.test)))
  observed=[]
  def run(command,**kwargs):
   self.assertEqual(command,['nonproof-command'])
   self.assertEqual(kwargs['cwd'],outer/'workspace')
   self.assertNotEqual(kwargs['cwd'],kernel/'workspace')
   self.assertIn('waiting_envelope',runtime)
   observed.append(kwargs['cwd']);return SimpleNamespace(returncode=0)
  namespace=dict(vars(E),out=kernel,runtime=runtime)
  with patch.dict(os.environ,{'ZESU_AGGREGATE_SLICE':'nonproof-fixture'}),patch.object(E.subprocess,'run',side_effect=run):
   exec(compile(ast.Module(body=branch.body,type_ignores=[]),str(E.__file__),'exec'),namespace)
  self.assertEqual(observed,[outer/'workspace']);self.assertEqual(runtime,before)
 def test_digest_release_keeps_force_hashing_and_counters(self):
  source=self.root/'source';source.write_text('fixture')
  with B.force_hashing(True),patch.object(B,'_persistent') as persistent:
   before=B.COUNTERS['hashes'];first=B.digest(source);self.assertGreater(B.release_process_cache(),0)
   self.assertEqual(B.digest(source),first);persistent.assert_not_called()
   self.assertEqual(B.COUNTERS['hashes']-before,2)
 def test_classification_release_recomputes_exact_rows(self):
  source=self.root/'source.v';source.write_text('fixture');runtime={'bindings':[binding(source)]}
  first=P.proof_rows(runtime);self.assertGreater(P.release_classification_cache(),0)
  self.assertEqual(P.proof_rows(runtime),first)
 def test_supplier_memo_release_drops_optional_references(self):
  payload=Payload(value='fixture');reference=weakref.ref(payload)
  with patch.object(S,'_MEMO',{'fixture':payload}):
   del payload;self.assertEqual(S.release_validation_cache(),1);gc.collect();self.assertIsNone(reference())

if __name__=='__main__':unittest.main()
