"""Nonproof tests for verified reservation credit and both admission limits."""
import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'code'))
import admission_memory as M


class ArithmeticTests(unittest.TestCase):
    def sample(self, scope='/scope/a', device=1, inode=2, live=40):
        return dict(verified=True, scope=scope, device=device, inode=inode, live_bytes=live)

    def evaluate(self, claims, new, available, **kwargs):
        return M.evaluate(claims, new, available, slice_max_bytes=1000, headroom_bytes=20, **kwargs)

    def test_live_memory_does_not_count_twice(self):
        r=self.evaluate({'active':60}, 20, 100, observations={'active':self.sample()})
        self.assertTrue(r['fits'])
        self.assertEqual((r['unrealized_claim_bytes'],r['requested_unrealized_bytes'],r['requested_total_bytes']),(20,40,80))

    def test_unknown_and_unreadable_scopes_keep_full_claim(self):
        for observations in ({}, {'active':dict(verified=False,live_bytes=60)}):
            r=self.evaluate({'active':60},20,100,observations=observations)
            self.assertFalse(r['fits']);self.assertEqual(r['credited_live_bytes'],0)

    def test_credit_never_exceeds_claim(self):
        r=self.evaluate({'active':60},10,100,observations={'active':self.sample(live=200)})
        self.assertEqual(r['unrealized_claim_bytes'],0)

    def test_seventy_percent_boundary_is_exact(self):
        self.assertTrue(self.evaluate({'unknown':50},20,100)['fits'])
        self.assertFalse(self.evaluate({'unknown':50},21,100)['fits'])

    def test_slice_cap_uses_full_claims_and_fixed_headroom(self):
        r=self.evaluate({'active':970},11,10000,observations={'active':self.sample(live=970)})
        self.assertFalse(r['fits']);self.assertEqual(r['slice_claim_cap_bytes'],980)
        self.assertTrue(self.evaluate({'active':970},10,10000)['fits'])

    def test_overlapping_or_duplicate_scopes_lose_all_credit(self):
        for right in [self.sample(), self.sample('/scope/a/child',inode=3),self.sample('/scope/b')]:
            r=self.evaluate({'a':40,'b':40},1,100,observations={'a':self.sample(), 'b':right})
            self.assertEqual(r['credited_live_bytes'],0);self.assertFalse(r['fits'])

    def test_disjoint_scopes_keep_credit(self):
        r=self.evaluate({'a':40,'b':40},1,100,observations={'a':self.sample(), 'b':self.sample('/scope/b',inode=3)})
        self.assertEqual(r['credited_live_bytes'],80);self.assertTrue(r['fits'])

    def test_negative_boolean_and_invalid_observations_refuse(self):
        for claims,new,free in [({'x':-1},0,1),({'x':True},0,1),({},True,1),({},0,-1)]:
            with self.assertRaises(ValueError):self.evaluate(claims,new,free)
        with self.assertRaises(ValueError):self.evaluate({'x':2},0,1,observations={'x':self.sample(live=-1)})


class ScopeTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name);self.proc=self.root/'proc';self.proc.mkdir()
        self.reader=M.ScopeReader(proc=self.proc,cgroup_root=self.root/'cgroup')
        self.parent=self.reader.parent;self.parent.mkdir(parents=True)
        (self.parent/'memory.max').write_text(str(M.SLICE_MAX_BYTES))
        (self.parent/'memory.swap.max').write_text('0')
        self.owner=dict(pid=11,startticks=101,token='token',block='block')
        self.batch=dict(pid=12,startticks=102)
        self.actor=dict(pid=13,startticks=103)
        self.out=self.root/'output';self.out.mkdir()
        self.group=self.parent/f'zesuworkloads-aggregate{os.getuid()}p12r1.slice';self.group.mkdir()
        (self.group/'memory.current').write_text('40')
        self.key='EntryChain_block_token'
        self.process(self.owner,1,['python','/tools/entry_chain_run.py','runtime','hash','block',str(self.out)],'/outside')
        self.process(self.batch,11,['guard','batch'],'/outside')
        self.process(self.actor,1,['python','/tools/entry_chain_run.py','--inside',str(self.out)],str(self.group.relative_to(self.reader.root)))
        self.write(self.out/'STARTED.json',{'owner':self.owner})
        self.write(self.out/'BATCH-PROCESS.json',self.batch)
        info=self.group.stat()
        self.bound=dict(aggregate_path=str(self.group),aggregate_device=info.st_dev,aggregate_inode=info.st_ino,inside_pid=13,inside_startticks=103)
        self.write(self.out/'BATCH-IDENTITY.json',self.bound)
        self.data={'entry_pilot_outside_owners':{self.key:self.owner},'fixed_claims':{self.key:60}}

    def write(self,path,value):path.write_text(json.dumps(value))

    def process(self,actor,parent,argv,group):
        p=self.proc/str(actor['pid']);p.mkdir(exist_ok=True)
        fields=['S',str(parent)]+['0']*17+[str(actor['startticks'])]
        (p/'stat').write_text(f"{actor['pid']} (process) "+' '.join(fields))
        (p/'cmdline').write_bytes(('\0'.join(argv)+'\0').encode())
        (p/'cgroup').write_text('0::/'+group.lstrip('/')+'\n')

    def observation(self):return self.reader.claim(self.data,self.key)

    def test_retained_entry_uses_token_and_child_aggregate_not_owner_scope(self):
        row=self.observation();self.assertTrue(row['verified'],row)
        self.assertEqual(row['live_bytes'],40)
        r=M.projection(self.data,{self.key:60},20,100,reader=self.reader)
        self.assertTrue(r['fits']);self.assertEqual(r['admission_pool'],'canonical')

    def test_registry_wrapper_may_parent_the_aggregate_creator(self):
        group=self.parent/f'zesuworkloads-aggregate{os.getuid()}p14r1.slice'
        self.group.rename(group);self.group=group
        self.process(dict(pid=14,startticks=104),12,['guard','batch'],'/outside')
        self.bound.update(aggregate_path=str(group))
        self.write(self.out/'BATCH-IDENTITY.json',self.bound)
        self.process(self.actor,1,['python','/tools/entry_chain_run.py','--inside',str(self.out)],str(group.relative_to(self.reader.root)))
        self.assertTrue(self.observation()['verified'])
        self.process(dict(pid=14,startticks=104),999,['guard','batch'],'/outside')
        self.assertFalse(self.observation()['verified'])

    def test_new_location_still_requires_exact_existing_owner(self):
        self.data['claim_locations']={self.key:dict(kind='entry',owner=self.owner,output_path=str(self.out))}
        self.assertTrue(self.observation()['verified'])
        self.data['claim_locations'][self.key]['owner']=dict(self.owner,token='wrong')
        self.assertFalse(self.observation()['verified'])

    def test_reused_pid_and_wrong_batch_parent_refuse_credit(self):
        for actor,parent in [(dict(self.batch,startticks=999),11),(self.batch,999)]:
            self.process(actor,parent,['guard'],'/outside')
            self.assertFalse(self.observation()['verified'])

    def test_wrong_token_inside_output_inode_or_membership_refuses(self):
        for mutation in ['token','output','inode','membership']:
            with self.subTest(mutation=mutation):
                original=copy.deepcopy(self.data)
                if mutation=='token':self.data['entry_pilot_outside_owners'][self.key]['token']='wrong'
                elif mutation=='output':self.process(self.actor,1,['python','/tools/entry_chain_run.py','--inside','other'],'/outside')
                elif mutation=='inode':self.write(self.out/'BATCH-IDENTITY.json',dict(self.bound,aggregate_inode=0))
                else:(self.proc/'13/cgroup').write_text('0::/outside\n')
                self.assertFalse(self.observation()['verified'])
                self.data=original;self.write(self.out/'BATCH-IDENTITY.json',self.bound)
                self.process(self.actor,1,['python','/tools/entry_chain_run.py','--inside',str(self.out)],str(self.group.relative_to(self.reader.root)))

    def test_unreadable_counter_or_unowned_receipt_keeps_full_claim(self):
        (self.group/'memory.current').unlink();self.assertFalse(self.observation()['verified'])
        (self.group/'memory.current').write_text('40')
        (self.out/'STARTED.json').chmod(0o666);self.assertFalse(self.observation()['verified'])

    def test_unknown_pending_and_legacy_claims_have_no_credit(self):
        r=M.projection({}, {'legacy:x':60},20,100,reader=self.reader)
        self.assertFalse(r['fits']);self.assertEqual(r['credited_live_bytes'],0)

    def test_changed_or_unreadable_slice_refuses_admission(self):
        for content in ['max','123']:
            (self.parent/'memory.max').write_text(content)
            r=M.projection(self.data,{self.key:60},0,100,reader=self.reader)
            self.assertFalse(r['fits']);self.assertEqual(r['slice_max_bytes'],0)
        (self.parent/'memory.max').unlink();self.assertEqual(self.reader.slice_max(),0)

    def test_duplicate_real_claim_scope_cannot_double_credit(self):
        another='EntryChain_other_second'
        second=dict(self.owner,block='other',token='second')
        self.data['entry_pilot_outside_owners'][another]=second
        self.data['claim_locations']={another:dict(kind='entry',owner=second,output_path=str(self.out))}
        r=M.projection(self.data,{self.key:60,another:60},0,100,reader=self.reader)
        # The second claim cannot pass the first claim's STARTED token.
        self.assertFalse(r['claim_observations'][another]['verified'])
        self.assertFalse(r['fits'])

    def test_counter_sampling_rechecks_process_and_cgroup_identity(self):
        actual=self.reader.directory
        calls=[]
        def changed(path):
            result=actual(path);calls.append(path)
            return (result[0],result[1]+1) if len(calls)>1 else result
        with patch.object(self.reader,'directory',side_effect=changed):
            self.assertFalse(self.observation()['verified'])

    def test_reused_aggregate_creator_pid_during_sampling_loses_credit(self):
        self.process(self.batch,11,['guard','batch'],'/outside')
        original=Path.read_text
        def changed(path,*args,**kwargs):
            value=original(path,*args,**kwargs)
            if path == self.group/'memory.current':
                self.process(dict(self.batch,startticks=999),11,['other'],'/outside')
            return value
        with patch.object(Path,'read_text',changed):
            self.assertFalse(self.observation()['verified'])

    def test_gate_retained_run_binds_request_and_batch(self):
        owner=dict(pid=11,startticks=101,run_id='gate-test')
        self.write(self.out/'REQUEST.json',dict(owner=owner,policy={'claim_key':'gate'}))
        self.write(self.out/'BATCH.json',dict(actors=[self.actor],aggregate_paths=[str(self.group)]))
        self.process(self.actor,1,['python','/tools/correctness_gate.py','inside',str(self.out)],str(self.group.relative_to(self.reader.root)))
        data={'correctness_gate_owners':{'gate':owner},'claim_locations':{'gate':dict(owner=owner,kind='gate',output_path=str(self.out))}}
        self.assertTrue(self.reader.claim(data,'gate')['verified'])
        self.write(self.out/'REQUEST.json',dict(owner=owner,policy={'claim_key':'other'}))
        self.assertFalse(self.reader.claim(data,'gate')['verified'])

    def test_compiler_leaf_binds_owner_and_child_start(self):
        leaf=self.group/'zesudet-coqc-11-1.scope';leaf.mkdir();(leaf/'memory.current').write_text('12')
        self.process(self.owner,12,['compiler wrapper'],'/outside')
        self.process(self.actor,1,['coqc'],str(leaf.relative_to(self.reader.root)))
        marker=self.root/'11.random';marker.write_text(f'13\nowner_start=101\nchild_start=103\naggregate={self.group.name}\n')
        (self.proc/'13/environ').write_bytes(f'ZESU_COQC_SCOPE={marker}\0ZESU_COQC_RESERVATION={marker}\0'.encode())
        self.assertTrue(self.reader.compiler(marker)['verified'])
        (self.proc/'13/environ').write_bytes(b'ZESU_COQC_SCOPE=other\0ZESU_COQC_RESERVATION=other\0')
        self.assertFalse(self.reader.compiler(marker)['verified'])
        marker.write_text(f'13\naggregate={self.group.name}\n')
        self.assertFalse(self.reader.compiler(marker)['verified'])


if __name__=='__main__':unittest.main()
