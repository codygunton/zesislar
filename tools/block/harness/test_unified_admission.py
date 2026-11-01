"""Temporary-ledger controls. These controls start no proof or compiler."""
import json
import hashlib
from pathlib import Path
import sys
import threading
import unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE/'code'),str(HERE.parents[1])]
import admission_memory as M
import test_admission_memory as Fixtures
import correctness_gate as G


class UnifiedAdmission(unittest.TestCase):
    write=Fixtures.ScopeTests.write
    process=Fixtures.ScopeTests.process

    def setUp(self):
        Fixtures.ScopeTests.setUp(self)
        self.tokens=self.root/'tokens';self.tokens.mkdir()
        self.ledger=self.root/'LEDGER.json'
        self.environment=patch.dict(M.os.environ,{'ZESU_GATE_LOCK':str(self.root/'gate.lock')})
        self.environment.start();self.addCleanup(self.environment.stop)
        self.data['shell_marker_directory']=str(self.tokens)
        self.data['fixed_claims']={}
        self.save(self.data)
        self.pending={'pid':14,'startticks':104}
        self.process(self.pending,12,['guard','scope'],str(self.group.relative_to(self.reader.root)))
        (self.group/'cgroup.events').write_text('populated 1\n')
        (self.group/'memory.max').write_text(str(64*M.GIB))
        (self.group/'memory.swap.max').write_text('0')
        self.marker=self.tokens/'14.fixture-generation-1234'

    def save(self,data):self.ledger.write_text(json.dumps(data))
    def read(self):return json.loads(self.ledger.read_text())

    def token(self,name='replacement',amount=64*M.GIB,fence=64*M.GIB):
        p=self.root/name
        generation='second-generation-1234' if name=='second' else 'fixture-generation-1234'
        p.write_text('confirmed\nwriter=\naggregate='+self.group.name+
                     f'\nmemory_claim_bytes={amount}\nmemory_fence_bytes={fence}\nowner_start=104\nreservation_generation={generation}\n')
        p.chmod(0o600)
        return p

    def confirm(self,amount=64*M.GIB,marker=None,replacement=None):
        return M.confirm_shell(marker or self.marker,replacement or self.token(amount=amount),
                               amount,200*M.GIB,ledger=self.ledger,reader=self.reader)

    def test_unverified_aggregate_flag_cannot_collapse_two_bookings(self):
        observation={'verified':False,'aggregate_verified':True,'scope':'/untrusted',
                     'device':1,'inode':2,'live_bytes':64*M.GIB}
        result=M.evaluate({'first':64*M.GIB,'second':64*M.GIB},0,100*M.GIB,
                          observations={'first':observation,'second':observation},
                          slice_max_bytes=M.SLICE_MAX_BYTES)
        self.assertEqual(result['active_claim_bytes'],128*M.GIB)
        self.assertEqual(result['accounted_active_bytes'],128*M.GIB)
        self.assertEqual(result['credited_live_bytes'],0)
        self.assertFalse(result['fits'])

    def test_pending_nested_tokens_charge_one_approved_booking(self):
        self.assertTrue(self.confirm()['fits'])
        other=self.tokens/'14.second-generation-1234'
        self.assertTrue(self.confirm(marker=other,replacement=self.token('second'))['fits'])
        data=self.read()
        r=M.projection(data,M.ledger_claims(data),0,200*M.GIB,reader=self.reader)
        self.assertEqual(r['active_claim_bytes'],64*M.GIB)
        self.assertEqual(r['raw_claim_bytes'],128*M.GIB)
        self.assertEqual(len(data['shell_claim_owners']),2)

    def test_measured_booking_stays_below_fence(self):
        self.assertTrue(self.confirm(amount=24*M.GIB)['fits'])
        data=self.read()
        r=M.projection(data,M.ledger_claims(data),0,200*M.GIB,reader=self.reader)
        self.assertEqual(r['active_claim_bytes'],24*M.GIB)

    def test_canonical_booking_blocks_shell_confirmation(self):
        data=self.read();data['fixed_claims']['canonical']=100*M.GIB;self.save(data)
        self.assertFalse(self.confirm()['fits'])
        self.assertFalse(self.marker.exists())
        self.assertNotIn(M.shell_key(self.marker),self.read()['fixed_claims'])

    def canonical(self,key,amount):
        policy={'ledger':str(self.ledger),'lock':str(self.ledger.with_suffix('.lock')),
                'claim_key':key,'claim_bytes':amount}
        def projection(data,claims,new,free):
            return M.projection(data,claims,new,free,reader=self.reader)
        class Refused(Exception):pass
        def stop(_):raise Refused()
        with patch.object(G,'projection',projection):
            try:
                return G.reserve(policy,{'pid':999,'startticks':999},self.root/(key+'.json'),
                                 available=lambda:200*M.GIB,pause=stop)
            except Refused:return {'admitted':False}

    def test_shell_booking_blocks_actual_canonical_reserve(self):
        self.assertTrue(self.confirm()['fits'])
        self.assertFalse(self.canonical('gate',100*M.GIB)['admitted'])
        self.assertNotIn('gate',self.read()['fixed_claims'])

    def test_parallel_cross_route_transactions_cannot_both_admit(self):
        barrier=threading.Barrier(2);results=[];errors=[]
        replacement=self.token()
        def shell():
            try:barrier.wait();results.append(self.confirm(replacement=replacement)['fits'])
            except BaseException as e:errors.append(e)
        def canonical():
            try:barrier.wait();results.append(self.canonical('gate',100*M.GIB)['admitted'])
            except BaseException as e:errors.append(e)
        threads=[threading.Thread(target=shell),threading.Thread(target=canonical)]
        for t in threads:t.start()
        for t in threads:t.join()
        self.assertEqual(errors,[])
        self.assertEqual(sorted(results),[False,True])

    def test_marker_publication_failure_retains_full_booking(self):
        replace=M.os.replace
        def fail(source,target):
            if Path(target)==self.marker:raise OSError('injected token publication failure')
            return replace(source,target)
        with patch.object(M.os,'replace',fail):
            with self.assertRaises(OSError):self.confirm()
        self.assertFalse(self.marker.exists())
        data=self.read()
        self.assertEqual(data['fixed_claims'][M.shell_key(self.marker)],64*M.GIB)
        r=M.projection(data,M.ledger_claims(data),0,200*M.GIB,reader=self.reader)
        self.assertEqual(r['accounted_active_bytes'],64*M.GIB)

    def test_unreadable_owner_prevents_grouping(self):
        self.assertTrue(self.confirm()['fits'])
        (self.proc/'14/stat').write_text('14 (reused) S 12 '+'0 '*17+'999')
        data=self.read()
        r=M.projection(data,M.ledger_claims(data),0,200*M.GIB,reader=self.reader)
        self.assertEqual(r['credited_live_bytes'],0)
        self.assertEqual(r['accounted_active_bytes'],64*M.GIB)

    def test_legacy_marker_is_visible_without_mutation(self):
        replacement=self.token();replacement.rename(self.marker)
        before=self.marker.read_bytes();ledger=self.ledger.read_bytes()
        r=M.current_projection(100*M.GIB,200*M.GIB,ledger=self.ledger,reader=self.reader)
        self.assertFalse(r['fits'])
        self.assertEqual(self.marker.read_bytes(),before)
        self.assertEqual(self.ledger.read_bytes(),ledger)

    def test_request_and_token_booking_must_match(self):
        with self.assertRaisesRegex(ValueError,'effective token booking'):
            self.confirm(replacement=self.token(amount=24*M.GIB))
        self.assertFalse(self.marker.exists())

    def test_pending_release_retains_aggregate_booking_until_closed(self):
        self.assertTrue(self.confirm()['fits'])
        self.assertTrue(M.release_shell(self.marker,ledger=self.ledger,reader=self.reader))
        data=self.read()
        self.assertEqual(data['fixed_claims'][M.shell_key(self.marker)],0)
        r=M.projection(data,M.ledger_claims(data),0,200*M.GIB,reader=self.reader)
        self.assertEqual(r['accounted_active_bytes'],64*M.GIB)
        (self.group/'cgroup.events').write_text('populated 0\n')
        r=M.projection(data,M.ledger_claims(data),0,200*M.GIB,reader=self.reader)
        self.assertEqual(r['accounted_active_bytes'],0)

    def test_growth_preserves_token_identity_and_exact_release(self):
        self.assertTrue(self.confirm()['fits'])
        identity=self.reader.file_identity(self.marker.lstat())
        original=self.marker.read_bytes()
        for amount in (80*M.GIB,32*M.GIB):
            M.refresh_shell_growth([{'reservation':str(self.marker),'claim_bytes':amount}],
                                   ledger=self.ledger,reader=self.reader)
            self.assertEqual(self.reader.file_identity(self.marker.lstat()),identity)
            self.assertEqual(self.marker.read_bytes(),original)
        self.assertEqual(M.read_shell_bookings(ledger=self.ledger)[str(self.marker)],80*M.GIB)
        self.assertTrue(M.release_shell(self.marker,ledger=self.ledger,reader=self.reader))
        data=self.read()
        self.assertEqual(data['fixed_claims'][M.shell_key(self.marker)],0)
        result=M.projection(data,M.ledger_claims(data),0,200*M.GIB,reader=self.reader)
        self.assertEqual(result['accounted_active_bytes'],80*M.GIB)

    def test_stale_token_cannot_publish_growth(self):
        self.assertTrue(self.confirm()['fits'])
        original=self.marker.read_bytes()
        other=self.root/'changed-token';other.write_bytes(original);other.replace(self.marker)
        with self.assertRaisesRegex(ValueError,'authenticated shell token'):
            M.refresh_shell_growth([{'reservation':str(self.marker),'claim_bytes':80*M.GIB}],
                                   ledger=self.ledger,reader=self.reader)
        self.assertEqual(self.read()['fixed_claims'][M.shell_key(self.marker)],64*M.GIB)

    def test_unknown_legacy_release_preserves_marker(self):
        self.token().rename(self.marker)
        original=self.marker.read_bytes();ledger=self.ledger.read_bytes()
        with self.assertRaisesRegex(ValueError,'authenticated aggregate closure'):
            M.release_shell(self.marker,ledger=self.ledger,reader=self.reader)
        self.assertEqual(self.marker.read_bytes(),original)
        self.assertEqual(self.ledger.read_bytes(),ledger)

    def test_exact_closed_legacy_hold_authorizes_reclamation(self):
        self.token().rename(self.marker)
        info=self.group.stat();data=self.read()
        data['legacy_aggregate_holds']={'protected':{'aggregate':{
            'scope':str(self.group),'device':info.st_dev,'inode':info.st_ino},'fallback_bytes':64*M.GIB}}
        self.save(data)
        (self.group/'cgroup.events').write_text('populated 0\n')
        self.assertTrue(M.release_shell(self.marker,ledger=self.ledger,reader=self.reader))
        self.assertFalse(self.marker.exists())
        self.assertIn(M.shell_key(self.marker),self.read()['legacy_shell_releases'])

    def rollout_writer(self,mode='batch'):
        source=self.root/'resource_guard.sh';source.write_text('# Nonproof fixture.\n')
        owner=self.batch if mode=='batch' else self.pending
        argv=['bash',str(source),mode,'fixture','--',str(source),'scope','client','--','true']
        self.process(owner,11 if mode=='batch' else 12,argv,
                     '/outside' if mode=='batch' else str(self.group.relative_to(self.reader.root)))
        (self.proc/'14/environ').write_bytes(f'ZESU_AGGREGATE_SLICE={self.group.name}\0'.encode())
        self.token().rename(self.marker)
        return {'owner':dict(owner),'token_owner':dict(self.pending),'argv':argv,
                'source':{'path':str(source),'sha256':hashlib.sha256(source.read_bytes()).hexdigest()},
                'marker':str(self.marker)}

    def test_batch_rollout_binds_distinct_creator_and_token_owner(self):
        writer=self.rollout_writer()
        result=M.prepare_legacy_rollout(self.read(),[writer],reader=self.reader)
        hold=next(iter(result['legacy_aggregate_holds'].values()))
        self.assertEqual(hold['writer'],self.batch)
        self.assertEqual(hold['token_owner'],self.pending)
        self.assertEqual(hold['fallback_bytes'],64*M.GIB)

    def test_scope_rollout_keeps_its_exact_token_owner(self):
        writer=self.rollout_writer('scope')
        result=M.prepare_legacy_rollout(self.read(),[writer],reader=self.reader)
        hold=next(iter(result['legacy_aggregate_holds'].values()))
        self.assertEqual(hold['writer'],hold['token_owner'])

    def test_batch_rollout_refuses_foreign_aggregate_token(self):
        writer=self.rollout_writer()
        creator={'pid':21,'startticks':201}
        other=self.reader.parent/f'zesuworkloads-aggregate{self.reader.uid}p21r1.slice';other.mkdir()
        for name,value in [('memory.current','10'),('memory.max',str(64*M.GIB)),('memory.swap.max','0')]:
            (other/name).write_text(value)
        self.process(creator,11,['guard','batch'],'/outside')
        self.process(self.pending,21,['guard','scope'],str(other.relative_to(self.reader.root)))
        self.marker.write_text(self.marker.read_text().replace(self.group.name,other.name))
        with self.assertRaisesRegex(ValueError,'exact aggregate'):
            M.prepare_legacy_rollout(self.read(),[writer],reader=self.reader)

    def test_batch_rollout_refuses_reused_creator_pid(self):
        writer=self.rollout_writer();writer['owner']['startticks']=999
        with self.assertRaisesRegex(ValueError,'process identity changed'):
            M.prepare_legacy_rollout(self.read(),[writer],reader=self.reader)

    def test_rollout_token_filename_binds_owner_pid_despite_equal_startticks(self):
        writer=self.rollout_writer();other={'pid':15,'startticks':104}
        self.process(other,12,['guard','scope'],str(self.group.relative_to(self.reader.root)))
        writer['token_owner']=other
        with self.assertRaisesRegex(ValueError,'filename names another owner'):
            M.prepare_legacy_rollout(self.read(),[writer],reader=self.reader)

    def test_scope_rollout_cannot_borrow_another_token_owner(self):
        writer=self.rollout_writer('scope');writer['token_owner']=dict(self.batch)
        with self.assertRaisesRegex(ValueError,'another token owner'):
            M.prepare_legacy_rollout(self.read(),[writer],reader=self.reader)


if __name__=='__main__':unittest.main()
