"""Check session validation with tiny data files and no proof processes."""
import asyncio
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE),str(HERE.parent),str(HERE.parents[1])]
import entry_chain_resources as R
import entry_chain_provider as P
from entry_chain import binding


class SessionValidationTests(unittest.TestCase):
    def setUp(self):
        self.temporary=tempfile.TemporaryDirectory();self.addCleanup(self.temporary.cleanup)
        self.root=Path(self.temporary.name);self.source=self.root/'fixture.v'
        self.source.write_text('Nonproof test input.\n')
        self.path=self.root/'RUNTIME.json'
        self.path.write_text(json.dumps({'bindings':[binding(self.source)]})+'\n')
        self.expected=binding(self.path)['sha256']
        self.runtime=json.loads(self.path.read_text())
        self.runtime.update(runtime_path=str(self.path),runtime_sha256=self.expected)
        self.real=R.check_proof_bindings

    def session(self):
        return R.session_validation(self.path,self.expected)

    def check(self,**kwargs):
        return R.check_operation(self.runtime,**kwargs)

    def test_unchanged_RPC_checks_reuse_start_validation_and_finish_fully(self):
        with patch.object(R,'check_proof_bindings',wraps=self.real) as validate:
            with self.session() as state:
                self.assertTrue(self.check(force_full=True)['source_bindings_checked'])
                for _ in range(12):
                    report=self.check()
                    self.assertTrue(report['validation_reused'])
                    self.assertFalse(report['source_bindings_checked'])
                    self.assertEqual(report['proof_bindings_checked'],0)
                    self.assertEqual(report['cached_proof_bindings'],1)
                self.assertEqual(validate.call_count,1)
            self.assertEqual(validate.call_count,2)
        self.assertEqual(state.full_completed,2)
        self.assertEqual(state.reused,12)
        self.assertTrue(state.final['success'])

    def test_other_process_style_checks_still_validate_each_operation(self):
        with patch.object(R,'check_proof_bindings',wraps=self.real) as validate:
            self.check();self.check()
        self.assertEqual(validate.call_count,2)

    def test_reused_seed_counts_do_not_claim_new_validation_work(self):
        work={'proof_bindings_checked':1,'shared_seed_files_checked':10,'cell_delta_files_checked':2}
        with patch.object(R,'check_proof_bindings',return_value=work):
            with self.session():
                self.check();report=self.check()
                for name in ['proof_bindings_checked','shared_seed_files_checked','cell_delta_files_checked']:
                    self.assertEqual(report[name],0)
                self.assertEqual(report['cached_shared_seed_files_checked'],10)
                self.assertEqual(report['cached_cell_delta_files_checked'],2)

    def test_separate_sessions_do_not_share_validation(self):
        with patch.object(R,'check_proof_bindings',wraps=self.real) as validate:
            with self.session() as first:self.assertFalse(self.check()['validation_reused'])
            with self.session() as second:self.assertFalse(self.check()['validation_reused'])
        self.assertIsNot(first,second);self.assertEqual(validate.call_count,4)
        self.assertEqual(first.full_completed,2);self.assertEqual(second.full_completed,2)

    def test_a_separate_process_has_no_parent_session_cache(self):
        code='''from pathlib import Path
import json,sys
h=Path(sys.argv[3]);sys.path[:0]=[str(h/'code'),str(h),str(h.parent),str(h.parents[1])]
import entry_chain_resources as R
path=Path(sys.argv[1]);expected=sys.argv[2]
r=json.loads(path.read_text());r.update(runtime_path=str(path),runtime_sha256=expected)
assert R._SESSION_VALIDATION.get() is None
assert not R.check_operation(r)['validation_reused']
with R.session_validation(path,expected) as state:
 assert not R.check_operation(r)['validation_reused']
print(json.dumps(state.report()))
'''
        with self.session() as parent:
            self.check()
            result=subprocess.run([sys.executable,'-B','-c',code,str(self.path),self.expected,str(HERE)],
                                  capture_output=True,text=True,check=True)
            child=json.loads(result.stdout)
            self.assertEqual(parent.full_completed,1)
            self.assertEqual(child['full_validations_completed'],2)
            self.assertEqual(child['reused_operation_checks'],0)
        self.assertEqual(parent.full_completed,2)

    def test_inherited_fork_cannot_reuse_parent_validation(self):
        with self.session():
            self.check();reader,writer=os.pipe();pid=os.fork()
            if pid==0:
                os.close(reader)
                try:
                    try:self.check()
                    except ValueError as error:
                        os.write(writer,str(error).encode());os._exit(0)
                    os._exit(1)
                except BaseException:os._exit(2)
            os.close(writer)
            try:message=os.read(reader,1024).decode()
            finally:os.close(reader)
            _,status=os.waitpid(pid,0)
            self.assertEqual(os.waitstatus_to_exitcode(status),0)
            self.assertIn('another process',message)

    def test_failed_initial_validation_never_creates_a_cache_hit(self):
        self.source.write_text('Changed required input.\n')
        with patch.object(R,'check_proof_bindings',wraps=self.real) as validate:
            with self.assertRaises(ValueError):
                with self.session() as state:self.check(force_full=True)
        self.assertEqual(validate.call_count,2)
        self.assertEqual(state.reused,0);self.assertEqual(state.full_completed,0)
        self.assertFalse(state.final['success'])

    def test_touch_and_permission_changes_force_full_validation(self):
        with patch.object(R,'check_proof_bindings',wraps=self.real) as validate:
            with self.session():
                self.check();self.path.chmod(0o400)
                self.assertFalse(self.check()['validation_reused'])
                stamp=self.path.stat();os.utime(self.path,ns=(stamp.st_atime_ns,stamp.st_mtime_ns+1000))
                self.assertFalse(self.check()['validation_reused'])
        self.assertEqual(validate.call_count,4)

    def test_identical_byte_replacement_forces_full_validation(self):
        with patch.object(R,'check_proof_bindings',wraps=self.real) as validate:
            with self.session():
                self.check();replacement=self.root/'replacement'
                replacement.write_bytes(self.path.read_bytes());replacement.replace(self.path)
                self.assertFalse(self.check()['validation_reused'])
        self.assertEqual(validate.call_count,3)

    def test_same_size_write_with_restored_mtime_refuses(self):
        with self.assertRaisesRegex(ValueError,'runtime bytes changed'):
            with self.session() as state:
                self.check();before=self.path.stat();raw=self.path.read_bytes()
                self.path.write_bytes(raw.replace(b'bindings',b'Bindings',1))
                os.utime(self.path,ns=(before.st_atime_ns,before.st_mtime_ns))
                self.check()
        self.assertFalse(state.final['success'])

    def test_changed_byte_replacement_refuses(self):
        with self.assertRaisesRegex(ValueError,'runtime bytes changed'):
            with self.session():
                self.check();replacement=self.root/'replacement'
                replacement.write_bytes(self.path.read_bytes()+b' ');replacement.replace(self.path)
                self.check()

    def test_symlink_retarget_forces_full_validation(self):
        link=self.root/'runtime-link';link.symlink_to(self.path)
        runtime=dict(self.runtime,runtime_path=str(link))
        with patch.object(R,'check_proof_bindings',wraps=self.real) as validate:
            with R.session_validation(link,self.expected):
                R.check_operation(runtime);other=self.root/'other-runtime'
                other.write_bytes(self.path.read_bytes());link.unlink();link.symlink_to(other)
                self.assertFalse(R.check_operation(runtime)['validation_reused'])
        self.assertEqual(validate.call_count,3)

    def test_change_during_full_validation_refuses_and_does_not_cache(self):
        def changed(runtime,**kwargs):
            work=self.real(runtime,**kwargs)
            stamp=self.path.stat();os.utime(self.path,ns=(stamp.st_atime_ns,stamp.st_mtime_ns+1000))
            return work
        with patch.object(R,'check_proof_bindings',side_effect=changed):
            with self.assertRaisesRegex(ValueError,'during full validation'):
                with self.session() as state:self.check()
        self.assertIsNone(state.work);self.assertEqual(state.full_completed,0)

    def test_change_during_cheap_identity_check_refuses(self):
        state=R.SessionValidation(self.path,self.expected)
        state.check(self.path,self.expected,lambda:{'proof_bindings_checked':1})
        old=state.identity()
        with patch.object(state,'identity',side_effect=[old,('changed',old)]):
            with self.assertRaisesRegex(ValueError,'identity check'):
                state.check(self.path,self.expected,lambda:self.fail('A cheap hit unexpectedly validated.'))
        self.assertIsNone(state.work)

    def test_another_runtime_envelope_cannot_reuse_the_session(self):
        with self.assertRaisesRegex(ValueError,'another runtime envelope'):
            with self.session():
                self.check();R.check_operation(dict(self.runtime,runtime_path=str(self.root/'other')))

    def test_body_failure_still_forces_final_validation(self):
        with patch.object(R,'check_proof_bindings',wraps=self.real) as validate:
            with self.assertRaisesRegex(RuntimeError,'RPC fixture failed'):
                with self.session() as state:
                    self.check();raise RuntimeError('RPC fixture failed')
        self.assertEqual(validate.call_count,2);self.assertTrue(state.final['success'])

    def test_final_validation_detects_changed_proof_inputs(self):
        with self.assertRaises(ValueError):
            with self.session() as state:
                self.check();self.source.write_text('Changed between RPCs.\n')
                self.assertTrue(self.check()['validation_reused'])
        self.assertFalse(state.final['success'])

    def test_context_is_reset_after_failure(self):
        with self.assertRaises(RuntimeError):
            with self.session():self.check();raise RuntimeError('fixture')
        with patch.object(R,'check_proof_bindings',wraps=self.real) as validate:self.check()
        self.assertEqual(validate.call_count,1)

    def test_provider_completion_receipts_follow_final_validation(self):
        @P.validated_session
        async def fixture(request):
            self.check();self.check()
        request={'runtime':str(self.path),'runtime_sha256':self.expected,'output':str(self.root)}
        asyncio.run(fixture(request))
        report=json.loads((self.root/'SESSION-VALIDATION.json').read_text())
        self.assertTrue(report['final_validation']['success'])
        self.assertEqual(report['full_validations_completed'],2)
        self.assertTrue((self.root/'TRANSPORT-CLOSED.json').exists())

    def test_provider_failure_retains_final_validation_receipt(self):
        @P.validated_session
        async def fixture(request):
            self.check();raise P.ToolFailure('RPC fixture failed',{'success':False})
        request={'runtime':str(self.path),'runtime_sha256':self.expected,'output':str(self.root)}
        with self.assertRaisesRegex(P.ToolFailure,'RPC fixture failed'):asyncio.run(fixture(request))
        report=json.loads((self.root/'SESSION-VALIDATION.json').read_text())
        self.assertTrue(report['final_validation']['success'])
        self.assertFalse((self.root/'TRANSPORT-CLOSED.json').exists())

    def test_failed_final_validation_never_publishes_completion(self):
        @P.validated_session
        async def fixture(request):
            self.check();self.source.write_text('Changed required input.\n')
        request={'runtime':str(self.path),'runtime_sha256':self.expected,'output':str(self.root)}
        with self.assertRaises(ValueError):asyncio.run(fixture(request))
        report=json.loads((self.root/'SESSION-VALIDATION.json').read_text())
        self.assertFalse(report['final_validation']['success'])
        self.assertFalse((self.root/'TRANSPORT-CLOSED.json').exists())


if __name__=='__main__':unittest.main()
