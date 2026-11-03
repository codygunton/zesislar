"""Authenticate role exits and preserve payload behavior without a compiler."""
from copy import deepcopy
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import admission_memory as M
import role_peaks as P
import scope_bookings as S
from entry_chain import binding, save
import test_owned_guard_scope as Fixtures


class RolePeaks(unittest.TestCase):
    def setUp(self):
        f = Fixtures.OwnedGuardScope(); f.setUp(); self.addCleanup(f.doCleanups)
        self.f = f
        self.root_owner = f.data['entry_pilot_outside_owners'][f.key]
        harness = f.root/'harness'
        controller = harness/'tools/block/harness/code/entry_chain_run.py'
        controller.parent.mkdir(parents=True); controller.write_text('fixture controller')
        authority = harness/'tools/block/harness/policies/CONTROLLER-PEAK-OBSERVATIONS.json'
        authority.parent.mkdir(parents=True); authority.write_bytes(Path(S.AUTHORITY['path']).read_bytes())
        self.runtime = {'harness': {'root': str(harness), 'commit': 'fixture'},
            'declarations_only': True, 'phase': 'prerequisites', 'declaration_checks': [],
            'control_session': None, 'native_route': None, 'job_output': str(f.out),
            'canonical_admission': {'physical_fence_bytes': 64*M.GIB}}
        runtime_path=f.out/'RUNTIME.json'; save(runtime_path,self.runtime)
        self.command=[sys.executable,'-B',str(controller),'--inside',str(f.out)]
        with patch.object(P,'last_peak',return_value=None):
            self.selected=S.measured_descriptor(self.runtime)
        self.environment={'ZESU_CONTROLLER_ROLE':P.ROLES[0],
            'ZESU_CONTROLLER_AUTHORITY_SHA256':S.AUTHORITY['sha256'],
            'ZESU_MODULE_CLAIM_BYTES':str(M.GIB)}
        S._peak_context(binding(runtime_path),self.selected,P.ROLES[0],self.environment,self.command)
        config=dict(self.runtime,job_controller=binding(controller),jobs=[
            {'key':'block','output':str(f.out),'phase':'prerequisites'}])
        config_path=f.root/'CONFIG.json';save(config_path,config)
        f.process(self.root_owner,1,['python',str(controller),str(config_path),binding(config_path)['sha256'],'block',str(f.out)],'/outside')
        f.argv=['bash',str(f.guard),'scope-exec',str(f.marker),'--',*self.command]
        f.process(f.actor,14,f.argv,str(f.leaf.relative_to(f.reader.root)))
        f.data.update(shell_claim_owners={M.shell_key(f.marker):{
            'owner':f.owner,'generation':f.generation,'marker':str(f.marker),
            'guard_source':f.source}}, claim_locations={f.key:{'kind':'entry','owner':self.root_owner,'output_path':str(f.out)}})
        f.data['fixed_claims'][M.shell_key(f.marker)]=M.GIB
        f.ledger.write_text(json.dumps(f.data))
        M.mark_shell(f.marker,ledger=f.ledger,reader=f.reader);f.post_exec()
        (f.leaf/'memory.max').write_text(str(64*M.GIB))
        (f.leaf/'memory.swap.max').write_text('0')
        (f.leaf/'memory.peak').write_text(str(3*M.GIB))
        self.payload={'pid':16,'startticks':106}
        f.process(self.payload,15,['payload'],str(f.leaf.relative_to(f.reader.root)))
        path=f.proc/'16/stat';path.write_text(path.read_text().replace('(process) S','(process) Z'))

    def begin(self):
        with patch.object(P,'identity',return_value=self.f.actor),patch('harness_commit.check'):
            return P.begin(self.f.marker,self.command,ledger=self.f.ledger,reader=self.f.reader,environment=self.environment)

    def closed(self, code=0):
        f=self.f;start=self.begin();reference=P.finish(start,self.payload,code)
        data=json.loads(f.ledger.read_text());key=M.shell_key(f.marker)
        data['fixed_claims'][key]=0
        data['shell_releases']={key:{'owner':f.owner,'marker':str(f.marker)}}
        f.ledger.write_text(json.dumps(data));f.marker.unlink()
        for actor in (f.owner,f.actor):
            path=f.proc/str(actor['pid'])/'stat'
            path.write_text(path.read_text().replace('(process) S','(process) Z'))
        for path in f.leaf.iterdir():path.unlink()
        f.leaf.rmdir()
        return reference

    def test_real_guard_identity_records_exit_then_requires_exact_release(self):
        start=self.begin();ref=P.finish(start,self.payload,7)
        self.assertIsNone(P.last_peak(P.ROLES[0],'declarations-serial',ledger=self.f.ledger,reader=self.f.reader))
        self.assertEqual(json.loads(Path(ref['path']).read_text())['returncode'],7)

    def test_released_peak_pins_role_kind_and_nonzero_exit(self):
        ref=self.closed(code=9)
        self.assertEqual(P.last_peak(P.ROLES[0],'declarations-serial',ledger=self.f.ledger,reader=self.f.reader),(ref,3*M.GIB))
        for role,kind in [(P.ROLES[1],'declarations-serial'),(P.ROLES[0],'declarations-dag')]:
            self.assertIsNone(P.last_peak(role,kind,ledger=self.f.ledger,reader=self.f.reader))

    def test_signal_exit_is_recorded_but_cannot_size_a_new_role(self):
        reference=self.closed(code=-signal.SIGTERM)
        self.assertEqual(json.loads(Path(reference['path']).read_text())['returncode'],-signal.SIGTERM)
        self.assertIsNone(P.last_peak(P.ROLES[0],'declarations-serial',ledger=self.f.ledger,reader=self.f.reader))
        with self.assertRaisesRegex(ValueError,'normal status'):
            P.recorded_peak(reference,P.ROLES[0],'declarations-serial',ledger=self.f.ledger,reader=self.f.reader)

    def test_changed_document_owner_or_release_keeps_default(self):
        ref=self.closed();f=self.f
        original=f.ledger.read_text();data=json.loads(original)
        key=M.shell_key(f.marker)
        for mutation in ('owner','release','claim'):
            changed=deepcopy(data)
            if mutation=='owner':changed['shell_claim_owners'][key]['owner']['startticks']=999
            elif mutation=='release':changed['shell_releases'][key]['marker']='different'
            else:changed['fixed_claims'][key]=M.GIB
            f.ledger.write_text(json.dumps(changed))
            self.assertIsNone(P.last_peak(P.ROLES[0],'declarations-serial',ledger=f.ledger,reader=f.reader))
        f.ledger.write_text(original)
        Path(ref['path']).write_text('{}')
        self.assertIsNone(P.last_peak(P.ROLES[0],'declarations-serial',ledger=f.ledger,reader=f.reader))
        with self.assertRaises(ValueError):P.recorded_peak(ref,P.ROLES[0],'declarations-serial',ledger=f.ledger,reader=f.reader)

    def test_changed_runtime_role_payload_or_fence_refuses_before_execution(self):
        for key,value in [('ZESU_CONTROLLER_ROLE',P.ROLES[1]),('ZESU_CONTROLLER_RUN_KIND','declarations-dag'),('ZESU_MODULE_CLAIM_BYTES','1')]:
            original=self.environment.copy();self.environment[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):self.begin()
            self.environment=original
        (self.f.leaf/'memory.max').write_text(str(32*M.GIB))
        with self.assertRaisesRegex(ValueError,'fence'):self.begin()

    def test_mcp_payload_requires_exact_relay_owner_pipe_and_server(self):
        f=self.f;parent={'pid':21,'startticks':121}
        f.process(parent,11,['relay'],str(f.group.relative_to(f.reader.root)))
        f.process(f.owner,21,['guard','scope'],str(f.group.relative_to(f.reader.root)))
        read_fd,write_fd=os.pipe();self.addCleanup(os.close,read_fd);self.addCleanup(os.close,write_fd)
        fd_path=f.proc/'21/fd';fd_path.mkdir()
        (fd_path/'7').symlink_to('/proc/'+str(os.getpid())+'/fd/'+str(read_fd))
        info=os.fstat(read_fd);relay='/pinned/relay.py'
        runtime=dict(self.runtime,prepared_workspace=str(f.root),mcp_argv=[sys.executable,relay,'scope','--guard',str(f.guard),'--receipt','/receipt','--',sys.executable,'/server.py'])
        command=[sys.executable,relay,'enter','21','121','7',str(info.st_dev),str(info.st_ino),'--',sys.executable,'/server.py']
        P._payload(command,{'role':P.ROLES[1]},runtime,f.reader,f.owner)
        changed=command.copy();changed[-1]='/other-server.py'
        with self.assertRaisesRegex(ValueError,'payload changed'):
            P._payload(changed,{'role':P.ROLES[1]},runtime,f.reader,f.owner)
        changed=command.copy();changed[7]=str(info.st_ino+1)
        with self.assertRaisesRegex(ValueError,'pipe owner changed'):
            P._payload(changed,{'role':P.ROLES[1]},runtime,f.reader,f.owner)

    def test_peak_reader_keeps_defaults_without_evidence_and_pins_selection(self):
        with patch.object(P,'last_peak',return_value=None):
            selection=S.measured_descriptor(self.runtime)
        self.assertEqual(selection['client_claim_bytes'],M.GIB)
        self.assertEqual(selection['mcp_claim_bytes'],24964177920)
        with patch.object(P,'last_peak',return_value=({'path':'p','sha256':'s'},10*M.GIB)):
            selection=S.measured_descriptor(self.runtime)
        self.assertEqual(selection['client_claim_bytes'],15*M.GIB)
        with patch.object(P,'recorded_peak',return_value={'memory_peak_bytes':10*M.GIB}):
            self.assertEqual(S.validate_booking(self.runtime,None,selection),selection)
        selection['run_kind']='declarations-dag'
        with self.assertRaises(ValueError):S.validate_booking(self.runtime,None,selection)


class PayloadBehavior(unittest.TestCase):
    def run_supervisor(self, source):
        here=Path(__file__).resolve().parent
        roots=[str(path) for path in (here/'code',here,here.parent,here.parents[1])]
        script='import sys;sys.path[:0]='+repr(roots)+';import role_peaks as P;sys.exit(P.run_payload([sys.executable,"-c",'+repr(source)+'],on_exit=lambda actor,code:None))'
        environment=dict(os.environ)
        environment.pop('PYTHONPATH',None)
        return subprocess.run([sys.executable,'-c',script],input='input-data',text=True,capture_output=True,timeout=8,env=environment)

    def test_fixture_imports_without_inherited_pythonpath(self):
        with patch.dict(os.environ,{'PYTHONPATH':'/unrelated-source'}):
            result=self.run_supervisor('import os;assert "PYTHONPATH" not in os.environ;print("clean-import")')
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertEqual(result.stdout,'clean-import\n')

    def test_stdio_and_nonzero_exit_stay_exact(self):
        result=self.run_supervisor('import sys;print(sys.stdin.read());print("error-data",file=sys.stderr);sys.exit(7)')
        self.assertEqual(result.returncode,7);self.assertEqual(result.stdout,'input-data\n');self.assertEqual(result.stderr,'error-data\n')

    def test_payload_signal_status_stays_exact(self):
        result=self.run_supervisor('import os,signal;os.kill(os.getpid(),signal.SIGTERM)')
        self.assertEqual(result.returncode,128+signal.SIGTERM)

    def test_incomplete_cleanup_keeps_status_and_grants_no_peak(self):
        with patch.object(P,'_group_members',return_value=[1]),patch.object(P.time,'monotonic',side_effect=iter(range(0,100,2))),patch.object(P.os,'killpg'):
            recorded=[]
            self.assertEqual(P.run_payload([sys.executable,'-c','import sys;sys.exit(7)'],on_exit=lambda *row:recorded.append(row)),7)
            self.assertEqual(recorded,[])

    def test_descendant_cannot_survive_completed_payload(self):
        result=self.run_supervisor('import subprocess,sys;child=subprocess.Popen([sys.executable,"-c","import time;time.sleep(60)"]);print(child.pid,flush=True)')
        self.assertEqual(result.returncode,0,result.stderr)
        pid=int(result.stdout.strip())
        try:
            state=(Path('/proc')/str(pid)/'stat').read_text().rsplit(')',1)[1].split()[0]
        except FileNotFoundError:state='gone'
        self.assertIn(state,('gone','Z','X'))


if __name__=='__main__':unittest.main()
