"""Check native verification contexts with authenticated nonproof compiler data."""
from copy import deepcopy
from pathlib import Path
import hashlib,json,sys,tempfile,unittest

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE),str(HERE.parent),str(HERE.parents[1])]
import compiler_snapshot as C
import scratch_statement as S
import test_compiler_snapshot as fixtures
from entry_chain import binding,save

RECORD=('Record Control := { value : nat }.\n'
        'Definition holds (x : Control) := True.\n'
        'Ltac zesu_block := exact I.\n'
        'Lemma DesignedBoundary_Control (x : Control) : holds x.\n'
        'Proof.\nzesu_block.\nQed.\n')
IMPORTED=('Require Import Fixture.Base.\n'
          'Lemma DesignedBoundary_Control : True.\n'
          'Proof.\nzesu_block.\nQed.\n')


class CompiledVerification(unittest.TestCase):
 accept_output=fixtures.CompilerSnapshotTests.accept_output

 def setUp(self):
  temporary=tempfile.TemporaryDirectory();self.addCleanup(temporary.cleanup)
  self.root=Path(temporary.name).resolve()
  self.library=self.root/'library';self.library.mkdir()
  self.compiler=self.root/'switch/bin/coqc';self.compiler.parent.mkdir(parents=True)
  self.compiler.write_text('Nonexecutable compiler fixture. No compiler runs.\n')
  self.path=self.root/'RUNTIME.json';self.source=self.library/'Control.v'

 def prepare(self,text=RECORD):
  self.source.write_text(text);self.specification=S.source_statement(self.source)
  self.target={'module':'Fixture.Control','source_sha256':binding(self.source)['sha256'],
               'statement_sha256':hashlib.sha256(self.specification['statement'].encode()).hexdigest()}
  self.runtime={'physical_compiler':binding(self.compiler),'physical_flags':['-Q',str(self.library),'Fixture'],
                'bindings':[binding(self.source),binding(self.compiler)],'job_output':str(self.root),
                'module_files':{'Fixture.Control':'library/Control.v'}}
  save(self.path,self.runtime);self.reference=binding(self.path)
  self.runtime.update(runtime_path=str(self.path),runtime_sha256=self.reference['sha256'])
  snapshot=C.publish(self.runtime,lambda:None,self.root/'SNAPSHOT.json',compiler=self.compiler,environment={})
  self.manager=C.OutputReceipts(C.read(snapshot,self.reference),snapshot)
  self.obj=self.source.with_suffix('.vo');self.obj.write_text('Authenticated nonproof object fixture.\n')
  self.receipt=self.accept_output(self.manager,self.obj)

 def payload(self,**changes):
  arguments=dict(runtime=self.runtime,target=self.target,source=self.source,
                 specification=self.specification,name='check_exact_control',workspace=self.root,
                 manager=self.manager,receipt=self.receipt)
  arguments.update(changes)
  return S.compiled_verification(**arguments)

 def test_inline_record_uses_one_compiled_identity_in_both_contexts(self):
  self.prepare();before=self.source.read_bytes();p=self.payload()
  expected=self.specification['statement'].replace('DesignedBoundary_Control','check_exact_control',1)
  self.assertEqual(p['problem_statement'],'Require Import Fixture.Control.\n'+expected)
  self.assertEqual(p['proof'],p['problem_statement']+'Proof. apply Fixture.Control.DesignedBoundary_Control. Qed.\n')
  self.assertNotIn('Record ',p['problem_statement']+p['proof'])
  self.assertEqual(p['context']['accepted_compilation'],self.receipt)
  self.assertEqual(self.source.read_bytes(),before)

 def test_imported_production_style_declaration_keeps_exact_statement(self):
  self.prepare(IMPORTED);p=self.payload()
  expected=self.specification['statement'].replace('DesignedBoundary_Control','check_exact_control',1)
  self.assertEqual(p['problem_statement'],'Require Import Fixture.Control.\n'+expected)
  self.assertEqual(p['context']['source'],binding(self.source))
  self.assertEqual(p['context']['object'],binding(self.obj))
  self.assertEqual(p['context']['compiler'],binding(self.compiler))

 def test_changed_declaration_refuses(self):
  self.prepare();spec=deepcopy(self.specification);spec['statement']=spec['statement'].replace('holds x','False')
  with self.assertRaisesRegex(ValueError,'declaration changed'):self.payload(specification=spec)

 def test_changed_statement_binding_refuses(self):
  self.prepare();target=dict(self.target,statement_sha256='0'*64)
  with self.assertRaisesRegex(ValueError,'declaration changed'):self.payload(target=target)

 def test_changed_source_binding_refuses(self):
  self.prepare();target=dict(self.target,source_sha256='0'*64)
  with self.assertRaisesRegex(ValueError,'source or compiler bytes'):self.payload(target=target)

 def test_changed_source_refuses(self):
  self.prepare();self.source.write_text(RECORD.replace('holds x','True'))
  with self.assertRaisesRegex(ValueError,'declaration changed'):self.payload()

 def test_changed_object_refuses(self):
  self.prepare();self.obj.write_text('Changed object fixture.\n')
  with self.assertRaises(ValueError):self.payload()

 def test_wrong_object_receipt_refuses(self):
  self.prepare();wrong=dict(self.receipt,path=str(self.root/'OTHER.json'))
  with self.assertRaisesRegex(ValueError,'accepted compilation receipt'):self.payload(receipt=wrong)

 def test_changed_receipt_refuses(self):
  self.prepare();Path(self.receipt['path']).write_text('{}')
  with self.assertRaises(ValueError):self.payload()

 def test_changed_compiler_refuses(self):
  self.prepare();self.compiler.write_text('Changed compiler fixture.\n')
  with self.assertRaisesRegex(ValueError,'source or compiler bytes'):self.payload()

 def test_wrong_compiler_binding_refuses(self):
  self.prepare();runtime=dict(self.runtime,physical_compiler=dict(binding(self.compiler),sha256='0'*64))
  with self.assertRaisesRegex(ValueError,'compiler or producer'):self.payload(runtime=runtime)

 def test_wrong_runtime_receipt_refuses(self):
  self.prepare();runtime=dict(self.runtime,runtime_sha256='0'*64)
  with self.assertRaisesRegex(ValueError,'compiler or producer'):self.payload(runtime=runtime)

 def test_missing_accepted_receipt_refuses(self):
  self.prepare()
  for changes in [dict(receipt=None),dict(manager=None)]:
   with self.subTest(changes=changes),self.assertRaisesRegex(ValueError,'accepted compilation receipt'):
    self.payload(**changes)

 def test_foreign_module_source_refuses(self):
  self.prepare();runtime=dict(self.runtime,module_files={'Fixture.Control':'library/Other.v'})
  with self.assertRaisesRegex(ValueError,'module mapping'):self.payload(runtime=runtime)

 def test_invalid_module_and_problem_names_refuse(self):
  self.prepare()
  for changes in [dict(target=dict(self.target,module='Fixture.Control. Abort')),dict(name='bad. Qed')]:
   with self.subTest(changes=changes),self.assertRaisesRegex(ValueError,'name is invalid'):
    self.payload(**changes)

 def test_local_syntax_refuses_instead_of_dropping_context(self):
  self.prepare('Local Notation token := nat.\n'+RECORD)
  with self.assertRaisesRegex(ValueError,'unsupported local syntax'):self.payload()

 def test_section_context_refuses_instead_of_generalizing_implicitly(self):
  self.prepare('Section ContextControl.\nContext (n : nat).\n'+RECORD+'End ContextControl.\n')
  with self.assertRaisesRegex(ValueError,'unsupported local syntax'):self.payload()

 def test_current_flags_must_match_successful_receipt(self):
  self.prepare();runtime=dict(self.runtime,physical_flags=self.runtime['physical_flags']+['-q'])
  with self.assertRaisesRegex(ValueError,'producer or compiler'):self.payload(runtime=runtime)


if __name__=='__main__':unittest.main()
