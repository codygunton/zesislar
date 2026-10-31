import errno,fcntl,hashlib,os,shutil,struct,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import clone_copy as C


def shared_extents(path):
 buffer=bytearray(32+56*32)
 struct.pack_into('=QQIIII',buffer,0,0,(1<<64)-1,1,0,32,0)
 with Path(path).open('rb') as stream:fcntl.ioctl(stream.fileno(),0xC020660B,buffer,True)
 count=struct.unpack_from('=I',buffer,20)[0]
 return [struct.unpack_from('=QQQ',buffer,32+56*i)+ (struct.unpack_from('=I',buffer,32+56*i+40)[0],) for i in range(count)]


class CloneCopy(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory(prefix='clone-control-',dir=HERE.parent)
  self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name)
  self.source=self.root/'source';self.source.write_bytes(os.urandom(2*1024*1024));self.target=self.root/'target'
 def test_real_clone_preserves_hash_metadata_and_distinct_inode(self):
  self.source.chmod(0o640);os.utime(self.source,ns=(1700000000000000000,1700000001000000000))
  C.copy2(self.source,self.target);a=self.source.stat();b=self.target.stat()
  self.assertEqual(C.digest(self.source),C.digest(self.target));self.assertNotEqual((a.st_dev,a.st_ino),(b.st_dev,b.st_ino))
  self.assertEqual((a.st_mode,a.st_uid,a.st_gid,a.st_mtime_ns),(b.st_mode,b.st_uid,b.st_gid,b.st_mtime_ns))
  self.assertTrue(any(e[3]&0x2000 for e in shared_extents(self.source)))
  self.assertTrue(any(e[3]&0x2000 for e in shared_extents(self.target)))
 def test_both_write_directions_are_isolated(self):
  C.copyfile(self.source,self.target);original=self.source.read_bytes()
  with self.target.open('r+b') as f:f.write(b'CHANGED')
  self.assertEqual(self.source.read_bytes(),original);saved=self.target.read_bytes()
  with self.source.open('r+b') as f:f.write(b'SOURCE!')
  self.assertEqual(self.target.read_bytes(),saved)
 def test_unsupported_clone_refuses_without_data_copy(self):
  self.target.write_bytes(b'old target')
  with patch.object(C.fcntl,'ioctl',side_effect=OSError(errno.EOPNOTSUPP,'unsupported')),patch.object(C.shutil,'copyfile') as fullcopy,patch.object(C.shutil,'copy2') as copy2:
   with self.assertRaises(OSError):C.copy2(self.source,self.target)
  fullcopy.assert_not_called();copy2.assert_not_called();self.assertEqual(self.target.read_bytes(),b'old target')
  self.assertEqual(list(self.root.glob('.*.clone-*')),[])
 def test_cross_filesystem_copy_refuses(self):
  with tempfile.TemporaryDirectory(dir='/dev/shm') as other:
   target=Path(other)/'target'
   with patch.object(C.fcntl,'ioctl') as ioctl:
    with self.assertRaises(OSError) as result:C.copy2(self.source,target)
   self.assertEqual(result.exception.errno,errno.EXDEV);ioctl.assert_not_called();self.assertFalse(target.exists())
 def test_failed_ioctl_never_leaves_partial_destination(self):
  with patch.object(C.fcntl,'ioctl',side_effect=OSError(errno.EXDEV,'cross device')):
   with self.assertRaises(OSError):C.copyfile(self.source,self.target)
  self.assertFalse(self.target.exists());self.assertEqual(list(self.root.glob('.*.clone-*')),[])
 def test_corrupt_clone_refuses_before_publication(self):
  with patch.object(C.fcntl,'ioctl',return_value=0):
   with self.assertRaisesRegex(ValueError,'source bytes'):C.copyfile(self.source,self.target)
  self.assertFalse(self.target.exists())
 def test_same_inode_and_hardlink_refuse(self):
  os.link(self.source,self.target)
  with self.assertRaisesRegex(ValueError,'distinct source inode'):C.copy2(self.source,self.target)
 def test_symbolic_destination_refuses(self):
  self.target.symlink_to(self.source)
  with self.assertRaisesRegex(ValueError,'symbolic link'):C.copy2(self.source,self.target)
 def test_copytree_uses_clones_and_preserves_aliases(self):
  tree=self.root/'tree';tree.mkdir();(tree/'object').write_bytes(self.source.read_bytes());(tree/'alias').symlink_to('object')
  C.copytree(tree,self.root/'copy',symlinks=True)
  self.assertTrue((self.root/'copy/alias').is_symlink());self.assertEqual(C.digest(tree/'object'),C.digest(self.root/'copy/object'))
  self.assertNotEqual((tree/'object').stat().st_ino,(self.root/'copy/object').stat().st_ino)
 def test_copytree_failure_has_no_fallback(self):
  tree=self.root/'tree';tree.mkdir();(tree/'object').write_bytes(b'data')
  with patch.object(C.fcntl,'ioctl',side_effect=OSError(errno.EOPNOTSUPP,'unsupported')):
   with self.assertRaises(shutil.Error):C.copytree(tree,self.root/'copy')
  self.assertFalse((self.root/'copy/object').exists())
 def test_copytree_rejects_arbitrary_copy_function(self):
  with self.assertRaises(TypeError):C.copytree(self.root,self.root/'new',copy_function=shutil.copyfile)
 def test_kernel_recheck_uses_clone_in_owned_workspace(self):
  import kernel_recheck as K
  workspace=self.root/'workspace';(workspace/'Target').mkdir(parents=True);source=workspace/'Target/Native.v';source.write_text('Lemma target : True. Proof. exact I. Qed.\n')
  checker=self.root/'checker';checker.write_text('pinned checker')
  statement='Lemma target : True.';sha=hashlib.sha256(statement.encode()).hexdigest()
  cached={'key':'fixture','result':{'success':True,'status':'passed','native_receipts':{'block':{'compile_file_success':True,'verification_method':'module_m','assumptions':[],'statement_sha256':sha,'statement':statement,'source':str(source),'source_sha256':C.digest(source),'object':str(self.source),'object_sha256':C.digest(self.source)}}}}
  current={'statement_sha256':sha,'source':{'path':str(source),'sha256':C.digest(source)},'workspace':str(workspace),'module':'Fixture.Target.Native','dependency_modules':[],'checker':{'path':str(checker),'sha256':C.digest(checker)},'physical_flags':['-Q',str(workspace),'Fixture']}
  def launch(argv):
   target=Path(argv[-3])/'Native.vo';self.assertEqual(C.digest(target),C.digest(self.source));self.assertNotEqual(target.stat().st_ino,self.source.stat().st_ino)
   return {'returncode':0,'all_owned_actors_closed':True,'claim_released':True,'CPU':{'cpu_seconds':0},'claim_key':'fixture','released_bytes':24*1024**3}
  with patch.object(K.clone_copy,'copy2',wraps=C.copy2) as copied:result=K.verify(cached,current,launch)
  self.assertTrue(result['success'],result);copied.assert_called_once()
 def test_result_cache_clones_artifacts_and_raw_result(self):
  import json,result_cache as R
  state={name:[] for name in ['goals','stack','shelf','given_up']};state['goals']=[{}];state['kernel_groups']={k:v for k,v in state.items()};state_path=self.root/'state.json';state_path.write_text(json.dumps(state))
  result={'phase':'native','success':False,'status':'native_open','normal_tactic_return':True,'proof_finished':False,'block':'fixture','complete_state':{'path':str(state_path),'sha256':C.digest(state_path),'state_source':'successful_command_returned_state'},'group_counts':{'active':1,'focus_frames':0,'frame_goals':0,'shelves':0,'given_up':0}}
  result_path=self.root/'result.json';result_path.write_text(json.dumps(result));key=R.build_key({},lambda value:{'block':'fixture','key_function':'clone-test.v1'})
  with patch.dict(os.environ,{'ZESU_PROOF_CACHE':'on','ZESU_IO':'batch'}),patch.object(C.fcntl,'ioctl',wraps=fcntl.ioctl) as ioctl:
   record=R.store(self.root/'cache',key,result_path,[{'path':str(self.source),'sha256':C.digest(self.source)}])
  self.assertEqual(record['cache_status'],'stored');self.assertGreaterEqual(ioctl.call_count,3)
  target=self.root/'cache'/key['sha256']/'files'/C.digest(self.source);self.assertEqual(C.digest(target),C.digest(self.source));self.assertNotEqual(target.stat().st_ino,self.source.stat().st_ino)
 def test_production_callers_have_no_stdlib_data_copy(self):
  import ast
  found=[]
  for path in [HERE/'scratch.py',*(HERE/'code').glob('*.py')]:
   for node in ast.walk(ast.parse(path.read_text())):
    if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute) and isinstance(node.func.value,ast.Name) and node.func.value.id=='shutil' and node.func.attr in {'copy','copy2','copyfile','copytree','copyfileobj'}:
     if path.name!='clone_copy.py':found.append((path.name,node.lineno))
  self.assertEqual(found,[])

if __name__=='__main__':unittest.main()
