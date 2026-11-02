"""Authenticate a one-GiB controller under its unchanged canonical root booking."""
import hashlib
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import admission_memory as M
import scope_bookings as S
from entry_chain import binding
import test_early_canonical_aggregate as Fixtures


class ControllerAssociationTests(unittest.TestCase):
    def setUp(self):
        self.f=Fixtures.EarlyCanonicalAggregate();self.f.setUp();self.addCleanup(self.f.doCleanups)
        f=self.f
        self.root=f.root/'harness'
        self.controller=self.root/'tools/block/harness/code/entry_chain_run.py'
        self.controller.parent.mkdir(parents=True);self.controller.write_text('Nonproof controller fixture.\n')
        authority=self.root/'tools/block/harness/policies/CONTROLLER-PEAK-OBSERVATIONS.json'
        authority.parent.mkdir(parents=True);authority.write_bytes(Path(S.AUTHORITY['path']).read_bytes())
        self.config={'harness':{'root':str(self.root)},'declarations_only':True,
            'control_session':None,'declaration_checks':[],'native_route':None,
            'job_controller':binding(self.controller),'jobs':[{'key':f.owner['block'],
                'phase':'prerequisites','output':str(f.out),'claim_bytes':64*M.GIB}]}
        self.path=f.root/'CONFIG.json'
        f.command=[str(self.controller) if x=='/tools/entry_chain_run.py' else x for x in f.command]
        f.wrapper=[str(self.controller) if x=='/tools/entry_chain_run.py' else x for x in f.wrapper]
        f.process(f.batch,11,f.wrapper,'/outside')
        f.process(f.creator,12,['bash',*f.command],'/outside')
        f.process(f.pending,15,['bash',*f.command[4:]],str(f.group.relative_to(f.reader.root)))
        self.persist()
        f.fields['memory_claim_bytes']=str(M.GIB);f.save_token()
        self.addCleanup(patch.stopall)
        patch('harness_commit.check',return_value=None).start()

    def persist(self, *, descriptor=None):
        f=self.f
        self.path.write_text(json.dumps(self.config))
        digest=hashlib.sha256(self.path.read_bytes()).hexdigest()
        f.process(f.owner,1,['python','-B',str(self.controller),str(self.path),digest,
                             f.owner['block'],str(f.out)],'/outside')
        selected=S.descriptor(self.config,self.config['jobs'][0]) if descriptor is None else descriptor
        f.write(f.out/'LAUNCH.json',{'owner':f.owner,'argv':f.command,'controller_booking':selected})

    def test_one_gib_client_shares_the_exact_64_gib_root(self):
        f=self.f
        sample=f.observation();self.assertTrue(sample['verified'],sample)
        new=f.reader.shell(f.token,owner=f.pending)
        result=M.projection(f.data,{f.key:64*M.GIB},M.GIB,200*M.GIB,reader=f.reader,
                            new_observation=new,pending_shell=(f.marker,f.token))
        self.assertTrue(result['fits'])
        self.assertEqual(result['accounted_active_bytes'],64*M.GIB)
        self.assertEqual(f.data['fixed_claims'][f.key],64*M.GIB)

    def test_unbound_configuration_hash_refuses(self):
        self.path.write_text(self.path.read_text()+'\n')
        self.f.assert_refused()

    def test_changed_role_descriptor_refuses(self):
        selected=S.descriptor(self.config,self.config['jobs'][0])
        selected['allowed_tools'].append('rocq_start')
        self.persist(descriptor=selected)
        self.f.assert_refused()

    def test_control_session_cannot_borrow_the_small_client_role(self):
        self.config['control_session']={}
        self.persist()
        self.f.assert_refused()

    def test_changed_root_booking_refuses_the_association(self):
        self.config['jobs'][0]['claim_bytes']=32*M.GIB
        self.persist()
        self.f.assert_refused()

    def test_changed_controller_source_refuses(self):
        self.controller.write_text('Changed nonproof controller fixture.\n')
        self.f.assert_refused()


if __name__=='__main__':unittest.main()
