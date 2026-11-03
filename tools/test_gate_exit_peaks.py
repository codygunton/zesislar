"""Reject incomplete gate exits and use the last exact workload measurement."""
from copy import deepcopy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import gate_exit_peaks as P
from block.harness.code.entry_chain import binding, save
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent/'block/harness'))
import test_admission_memory as Fixtures


class GatePeaks(unittest.TestCase):
    def setUp(self):
        f=Fixtures.ScopeTests();f.setUp();self.addCleanup(f.doCleanups);self.f=f
        self.guard=f.root/'public/resource_guard.sh';self.guard.parent.mkdir()
        self.guard.write_bytes((Path(__file__).parent/'resource_guard.sh').read_bytes());self.guard.chmod(0o700)
        self.source=f.reader.guard_source(str(self.guard),binding(self.guard)['sha256'])
        self.limit=120*P.GIB
        for name,value in [('memory.max',self.limit),('memory.swap.max',0),('memory.peak',2*P.GIB)]:
            (f.group/name).write_text(str(value))
        self.request={'policy':{'physical_fence_bytes':self.limit,'claim_key':'gate','claim_bytes':9*P.GIB},
            'owner':f.owner,'guard_source':self.source,'target':'check-fast',
            'command':['make','--no-print-directory','_check-fast'],'code_identity':{'workload':'exact'}}
        self.measurement=P.sample(f.group,self.request,f.actor,reader=f.reader)
        self.batch={'actors':[f.actor], 'aggregate_paths':[str(f.group)]}
        self.ledger={'fixed_claims':{'gate':0},'correctness_gate_owners':{'gate':f.owner},
            'correctness_gate_releases':{'gate':{'released':True,'bytes':9*P.GIB,'owner':f.owner}}}
        save(f.out/'REQUEST.json',self.request)
        save(f.out/'RESULT.json',{'success':True,'exit_code':0,'completed_ns':1,
            'aggregate_peak_bytes':2*P.GIB,'guard_exit':self.measurement,'code_identity_after':self.request['code_identity']})
        save(f.out/'CLOSURE.json',{'all_owned_actors_closed':True,'batch':self.batch})
        self.ledger['correctness_gate_releases']['gate']['receipt_sha256']=binding(f.out/'REQUEST.json')['sha256']
        P.endorse(f.out,self.request,self.ledger,closed=True)
        for path in f.group.iterdir():path.unlink()
        f.group.rmdir()

    def select(self, ledger=None, **kw):
        return P.latest(self.ledger if ledger is None else ledger,'check-fast',self.request['command'],self.limit,
            self.request['code_identity'],closed=lambda batch:True,guard_reader=self.f.reader,**kw)

    def test_released_guard_peak_uses_formula_and_keeps_fence(self):
        selected=self.select()
        self.assertEqual(selected['claim_bytes'],3*P.GIB)
        self.assertEqual(selected['physical_fence_bytes'],120*P.GIB)
        self.assertEqual(selected['reason'],'last_released_guard_gate_peak')

    def test_latest_matching_peak_wins_instead_of_family_maximum(self):
        old=deepcopy(self.ledger['gate_exit_peaks'][0]);old['result']={'path':'/absent','sha256':'0'*64}
        self.ledger['gate_exit_peaks'].insert(0,old)
        self.assertIsNotNone(self.select())
        self.ledger['gate_exit_peaks'].append(old)
        self.assertIsNone(self.select())

    def test_changed_owner_release_claim_guard_and_receipt_keep_default(self):
        data=deepcopy(self.ledger)
        data['gate_exit_peaks'][0]['result']['sha256']='0'*64
        self.assertIsNone(self.select(data))
        for case in ('owner','release','claim','guard'):
            data=deepcopy(self.ledger)
            if case=='owner':data['correctness_gate_owners']['gate']['startticks']=999
            elif case=='release':data['correctness_gate_releases']['gate']['bytes']=1
            elif case=='claim':data['fixed_claims']['gate']=1
            elif case=='guard':self.guard.write_text('changed')
            else:data['gate_exit_peaks'][0]['result']['sha256']='0'*64
            with self.subTest(case=case):self.assertIsNone(self.select(data))

    def test_other_kind_command_fence_or_workload_does_not_match(self):
        for target,command,limit,identity in [('check-iris',self.request['command'],self.limit,self.request['code_identity']),
                ('check-fast',['make','changed'],self.limit,self.request['code_identity']),
                ('check-fast',self.request['command'],64*P.GIB,self.request['code_identity']),
                ('check-fast',self.request['command'],self.limit,{'workload':'other'})]:
            with self.subTest(target=target,command=command,limit=limit,identity=identity):
                self.assertIsNone(P.latest(self.ledger,target,command,limit,identity,closed=lambda batch:True,guard_reader=self.f.reader))

    def test_live_owner_or_aggregate_cannot_authorize_reuse(self):
        self.assertIsNone(P.latest(self.ledger,'check-fast',self.request['command'],self.limit,
            self.request['code_identity'],closed=lambda batch:False,guard_reader=self.f.reader))
        self.f.group.mkdir()
        self.assertIsNone(self.select())

    def test_changed_post_execution_workload_cannot_authorize_sizing(self):
        result=json.loads((self.f.out/'RESULT.json').read_text())
        result['code_identity_after']={'workload':'changed'}
        save(self.f.out/'RESULT.json',result)
        with self.assertRaisesRegex(ValueError,'released measurement'):
            P.endorse(self.f.out,self.request,self.ledger,closed=True)
        self.assertIsNone(self.select())

    def test_failed_gate_cannot_create_an_endorsement(self):
        result=json.loads((self.f.out/'RESULT.json').read_text());result.update(success=False,exit_code=1)
        save(self.f.out/'RESULT.json',result)
        with self.assertRaisesRegex(ValueError,'released measurement'):
            P.endorse(self.f.out,self.request,self.ledger,closed=True)


class WorkloadIdentity(unittest.TestCase):
    def test_revision_and_prose_changes_do_not_change_workload_identity(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary)
            subprocess.run(['git','init','-q',str(root)],check=True)
            (root/'Proof.v').write_text('Definition value := 1.')
            (root/'README.md').write_text('Original prose')
            (root/'compiler').write_text('exact toolchain')
            subprocess.run(['git','-C',str(root),'add','.'],check=True)
            with patch.object(P,'toolchain',return_value={'compiler':binding(root/'compiler')}):
                first=P.code_identity(root)
                (root/'README.md').write_text('Changed prose')
                self.assertEqual(P.code_identity(root),first)
                (root/'Proof.v').write_text('Definition value := 2.')
                self.assertNotEqual(P.code_identity(root),first)


class ToolchainIdentity(unittest.TestCase):
    def test_makefile_switch_selects_both_actual_binaries(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary)
            for name in ('opam','coqc','dune'):(root/name).write_text(name)
            with patch.dict(os.environ,{'OPAM_SWITCH':'/exact/switch'}),patch.object(P.shutil,'which',return_value=str(root/'opam')),patch.object(P.subprocess,'check_output',return_value=str(root/'coqc')+'\n'+str(root/'dune')+'\n') as query:
                selected=P.toolchain()
                self.assertEqual(selected['coqc'],binding(root/'coqc'))
                self.assertEqual(selected['dune'],binding(root/'dune'))
                self.assertIn('--switch=/exact/switch',query.call_args.args[0])
                self.assertTrue(query.call_args.kwargs['text'])


if __name__=='__main__':unittest.main()
