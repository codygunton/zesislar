"""Nonproof tests for verified reservation credit and both admission limits."""
import copy
import io
from contextlib import redirect_stderr
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

    def test_live_usage_above_booking_refuses_at_slice_cap(self):
        r=self.evaluate({'active':60},11,10000,observations={'active':self.sample(live=970)})
        self.assertFalse(r['fits'])
        self.assertEqual(r['active_claim_bytes'],60)
        self.assertEqual(r['accounted_active_bytes'],970)
        self.assertEqual(r['live_over_booking_bytes'],910)
        self.assertEqual(r['requested_total_bytes'],981)
        self.assertEqual(r['unrealized_claim_bytes'],0)
        self.assertTrue(self.evaluate({'active':60},10,10000,
            observations={'active':self.sample(live=970)})['fits'])

    def test_booking_remains_floor_for_verified_live_usage(self):
        r=self.evaluate({'active':60},20,100,observations={'active':self.sample(live=40)})
        self.assertEqual(r['accounted_active_bytes'],60)
        self.assertEqual(r['live_over_booking_bytes'],0)
        self.assertEqual(r['claim_observations']['active']['accounted_bytes'],60)
        self.assertTrue(r['fits'])

    def test_unverified_over_booking_value_cannot_change_accounting(self):
        r=self.evaluate({'active':60},20,100,
            observations={'active':dict(verified=False,live_bytes=10000)})
        self.assertEqual(r['accounted_active_bytes'],60)
        self.assertEqual(r['credited_live_bytes'],0)
        self.assertFalse(r['fits'])

    def test_conflicting_scopes_keep_overage_without_credit(self):
        r=self.evaluate({'a':40,'b':40},1,100,
            observations={'a':self.sample(live=200), 'b':self.sample(live=200)})
        self.assertEqual(r['accounted_active_bytes'],400)
        self.assertEqual(r['credited_live_bytes'],0)
        self.assertFalse(r['fits'])

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

    def test_duplicate_zero_sample_also_invalidates_the_other_credit(self):
        r=self.evaluate({'a':40,'b':40},1,100,observations={
            'a':self.sample(live=0),'b':self.sample(live=40)})
        self.assertEqual(r['credited_live_bytes'],0)
        self.assertFalse(r['fits'])

    def test_disjoint_scopes_keep_credit(self):
        r=self.evaluate({'a':40,'b':40},1,100,observations={'a':self.sample(), 'b':self.sample('/scope/b',inode=3)})
        self.assertEqual(r['credited_live_bytes'],80);self.assertTrue(r['fits'])

    def test_negative_boolean_and_invalid_observations_refuse(self):
        for claims,new,free in [({'x':-1},0,1),({'x':True},0,1),({},True,1),({},0,-1)]:
            with self.assertRaises(ValueError):self.evaluate(claims,new,free)
        with self.assertRaises(ValueError):self.evaluate({'x':2},0,1,observations={'x':self.sample(live=-1)})


class LiveAdmissionTests(unittest.TestCase):
    def decide(self, request=8 * M.GIB, live=None, age=0, maximum=M.SLICE_MAX_BYTES,
               sample_maximum=None, available=200 * M.GIB):
        class Reader:
            def claim(self, data, key):
                return {'verified': False}
            def slice_max(self):
                return maximum
            def slice_sample(self):
                return {'sampled_monotonic_ns': 20_000_000_000 - age,
                        'live_bytes': maximum // 2 - request if live is None else live,
                        'slice_max_bytes': maximum if sample_maximum is None else sample_maximum,
                        'scope': '/owned/slice', 'device': 1, 'inode': 2}
        self.log = io.StringIO()
        with patch.object(M.time, 'monotonic_ns', return_value=20_000_000_000), redirect_stderr(self.log):
            return M.projection({}, {'booked': 200 * M.GIB}, request, available, reader=Reader())

    def test_exact_half_cap_and_eight_gib_boundary_use_live_path(self):
        result = self.decide()
        self.assertTrue(result['fits'])
        self.assertEqual(result['admission_basis'], 'live_memory')
        self.assertEqual(result['active_claim_bytes'], 200 * M.GIB)
        self.assertEqual(result['claim_observations']['booked']['verified'], False)
        self.assertIn('live_bytes=', self.log.getvalue())
        self.assertIn('request_bytes=8589934592', self.log.getvalue())
        self.assertIn('booked_bytes=214748364800', self.log.getvalue())

    def test_default_sixteen_gib_ceiling_and_configured_boundary(self):
        with patch.dict(os.environ, {}, clear=True):
            self.assertTrue(self.decide(request=16*M.GIB)['fits'])
            self.assertFalse(self.decide(request=16*M.GIB+1)['fits'])
        with patch.dict(os.environ, {'ZESU_LIVE_REQUEST_LIMIT_GIB':'8'}):
            self.assertTrue(self.decide(request=8*M.GIB)['fits'])
            self.assertFalse(self.decide(request=8*M.GIB+1)['fits'])
        with patch.dict(os.environ, {'ZESU_LIVE_REQUEST_LIMIT_GIB':'20'}):
            self.assertTrue(self.decide(request=20*M.GIB)['fits'])

    def test_invalid_live_ceiling_keeps_booking_and_all_claims(self):
        for value in ('0','-1',str(M.SLICE_MAX_BYTES // M.GIB + 1),'1.5','invalid',''):
            with self.subTest(value=value),patch.dict(os.environ, {'ZESU_LIVE_REQUEST_LIMIT_GIB':value}):
                result=self.decide(request=M.GIB)
                self.assertFalse(result['fits'])
                self.assertEqual(result['admission_basis'],'booking')
                self.assertEqual(result['active_claim_bytes'],200*M.GIB)

    def test_sixteen_gib_still_requires_fresh_anon_and_half_slice(self):
        self.assertFalse(self.decide(request=16*M.GIB,age=10_000_000_001)['fits'])
        self.assertFalse(self.decide(request=16*M.GIB,live=M.SLICE_MAX_BYTES//2-16*M.GIB+1)['fits'])

    def test_one_byte_above_half_cap_falls_back_to_booking(self):
        result = self.decide(live=M.SLICE_MAX_BYTES // 2 - 8 * M.GIB + 1)
        self.assertFalse(result['fits'])
        self.assertEqual(result['admission_basis'], 'booking')

    def test_larger_and_zero_requests_keep_booking(self):
        for request in (0, 16 * M.GIB + 1, 64 * M.GIB):
            with self.subTest(request=request):
                result = self.decide(request=request, live=0)
                self.assertFalse(result['fits'])
                self.assertEqual(result['admission_basis'], 'booking')
                self.assertNotIn('live_memory_sample', result)

    def test_ten_second_boundary_is_exact_and_future_samples_refuse(self):
        self.assertTrue(self.decide(age=10_000_000_000)['fits'])
        for age in (10_000_000_001, -1):
            self.assertFalse(self.decide(age=age)['fits'])

    def test_missing_unreadable_or_changed_slice_sample_uses_booking(self):
        base = M.evaluate({'old': 200 * M.GIB}, M.GIB, 200 * M.GIB,
                          slice_max_bytes=M.SLICE_MAX_BYTES)
        for reader in (object(), unittest.mock.Mock(slice_sample=unittest.mock.Mock(side_effect=OSError))):
            self.assertFalse(M.live_memory_admission(dict(base), reader)['fits'])
        self.assertFalse(self.decide(sample_maximum=0)['fits'])
        self.assertFalse(self.decide(sample_maximum=M.SLICE_MAX_BYTES - 1)['fits'])
        self.assertFalse(self.decide(maximum=0, live=0)['fits'])
        self.assertFalse(self.decide(live=-1)['fits'])

    def test_memavailable_remains_an_independent_limit(self):
        self.assertFalse(self.decide(live=0, available=M.GIB)['fits'])

    def test_old_reader_and_booking_success_remain_supported(self):
        class Reader:
            def claim(self, data, key): return {'verified': False}
            def slice_max(self): return M.SLICE_MAX_BYTES
        result = M.projection({}, {}, M.GIB, 200 * M.GIB, reader=Reader())
        self.assertTrue(result['fits'])
        self.assertEqual(result['admission_basis'], 'booking')


class WaiterTests(unittest.TestCase):
    """A large request that waits past the bound is admitted before newer small ones."""

    HALF = M.SLICE_MAX_BYTES // 2
    LIVE_OWNERS = {('gate', 1), ('small', 1)}

    class Reader:
        def __init__(self, test): self.test = test
        def claim(self, data, key): return {'verified': False}
        def slice_max(self): return M.SLICE_MAX_BYTES
        def slice_sample(self):
            return {'sampled_monotonic_ns': 20_000_000_000, 'live_bytes': self.test.live,
                    'slice_max_bytes': M.SLICE_MAX_BYTES, 'scope': '/owned/slice', 'device': 1, 'inode': 2}
        def process(self, actor):
            if (actor['pid'], actor['startticks']) not in WaiterTests.LIVE_OWNERS:
                raise ValueError('dead')
            return 1

    def setUp(self):
        self.data, self.live, self.now = {}, self.HALF - 6 * M.GIB, 1_000_000_000_000
        env = patch.dict(os.environ, {'ZESU_ADMISSION_WAIT_BOUND_S': '300'})
        env.start(); self.addCleanup(env.stop)

    def decide(self, request, requester, booked=200 * M.GIB, available=200 * M.GIB):
        self.log = io.StringIO()
        with patch.object(M.time, 'monotonic_ns', return_value=20_000_000_000), \
                patch.object(M.time, 'time_ns', return_value=self.now), redirect_stderr(self.log):
            return M.projection(self.data, {'booked': booked}, request, available,
                                reader=self.Reader(self), requester=requester)

    def gate_poll(self):
        result = self.decide(32 * M.GIB, 'gate')
        if result['fits']:
            M.clear_waiter(self.data, 'gate')
        else:
            M.record_waiter(self.data, 'gate', 32 * M.GIB, {'pid': 'gate', 'startticks': 1}, self.now)
        return result['fits']

    def test_small_request_passes_without_a_large_waiter(self):
        result = self.decide(4 * M.GIB, 'small')
        self.assertTrue(result['fits'])
        self.assertEqual((result['admission_basis'], result['waiter_reserved_bytes']), ('live_memory', 0))

    def test_waiting_32_gib_claim_is_admitted_while_4_gib_requests_keep_arriving(self):
        admitted_small, gate_step = [], None
        for step in range(30):
            self.live -= 4 * M.GIB              # one running 4 GiB job ends each minute
            if self.decide(4 * M.GIB, 'small')['fits']:
                self.live += 4 * M.GIB          # one new 4 GiB request arrives each minute
                admitted_small.append(step)
            if self.gate_poll():
                gate_step = step
                break
            self.now += 60_000_000_000
        # The small requests always pass on live memory; once aged, the large claim
        # passes too, on live memory up to the slice maximum less the headroom.
        self.assertEqual(admitted_small, list(range(6)))
        self.assertEqual(gate_step, 5)
        self.assertNotIn('gate', self.data.get(M.WAITERS, {}))

    def test_a_waiter_that_live_memory_cannot_admit_does_not_freeze_small_requests(self):
        cap = M.SLICE_MAX_BYTES - M.HEADROOM_BYTES
        booked, available = cap - 10 * M.GIB, 400 * M.GIB
        self.live = cap - 25 * M.GIB          # the waiter needs live + 32 GiB <= cap
        M.record_waiter(self.data, 'gate', 32 * M.GIB, {'pid': 'gate', 'startticks': 1}, self.now)
        self.assertTrue(self.decide(4 * M.GIB, 'small', booked, available)['fits'])
        self.now += 300_000_000_000           # aged: the waiter reserves its bytes on bookings only
        small = self.decide(4 * M.GIB, 'small', booked, available)
        self.assertEqual((small['fits'], small['waiter_reserved_bytes']), (False, 32 * M.GIB))
        self.assertFalse(self.decide(32 * M.GIB, 'gate', booked, available)['fits'])
        self.live = self.HALF - 10 * M.GIB    # on live memory a small request passes beside the waiter
        self.assertEqual(self.decide(4 * M.GIB, 'small')['admission_basis'], 'live_memory')
        self.live = cap - 25 * M.GIB
        self.now += 900_000_000_000           # after the second bound the waiter stops blocking
        small = self.decide(4 * M.GIB, 'small', booked, available)
        self.assertEqual((small['fits'], small['waiter_reserved_bytes']), (True, 0))
        self.assertIn('admission waiter gate', self.log.getvalue())
        self.assertIn('gate', self.data[M.WAITERS])      # it keeps its place
        self.live = cap - 40 * M.GIB          # memory frees: the waiter is admitted
        result = self.decide(32 * M.GIB, 'gate', booked, available)
        self.assertEqual((result['fits'], result['admission_basis']), (True, 'live_memory'))

    def test_young_dead_or_smaller_waiters_reserve_nothing(self):
        M.record_waiter(self.data, 'gate', 32 * M.GIB, {'pid': 'gate', 'startticks': 1}, self.now)
        self.now += 60_000_000_000
        self.assertEqual(self.decide(4 * M.GIB, 'small')['waiter_reserved_bytes'], 0)
        self.now += 300_000_000_000
        self.assertEqual(self.decide(4 * M.GIB, 'small')['waiter_reserved_bytes'], 32 * M.GIB)
        self.assertEqual(self.decide(64 * M.GIB, 'larger')['waiter_reserved_bytes'], 0)
        self.data[M.WAITERS]['gate']['owner'] = {'pid': 'gone', 'startticks': 1}
        self.assertEqual(self.decide(4 * M.GIB, 'small')['waiter_reserved_bytes'], 0)
        self.assertNotIn('gate', self.data[M.WAITERS])

    def test_only_the_head_of_the_waiter_queue_reserves(self):
        for index, size in enumerate((8, 6, 12)):
            M.record_waiter(self.data, f'w{index}', size * M.GIB, {'pid': 'gate', 'startticks': 1},
                            self.now + index)
        self.now += 400_000_000_000
        self.assertEqual(self.decide(2 * M.GIB, 'small')['waiter_reserved_bytes'], 8 * M.GIB)
        self.assertEqual(self.decide(7 * M.GIB, 'small')['waiter_reserved_bytes'], 8 * M.GIB)
        self.assertEqual(self.decide(10 * M.GIB, 'small')['waiter_reserved_bytes'], 12 * M.GIB)

    def test_an_aged_waiter_keeps_its_first_refusal_time(self):
        owner = {'pid': 'gate', 'startticks': 1}
        self.assertTrue(M.record_waiter(self.data, 'gate', 32 * M.GIB, owner, 1))
        self.assertFalse(M.record_waiter(self.data, 'gate', 32 * M.GIB, owner, 2))
        self.assertEqual(self.data[M.WAITERS]['gate']['since_ns'], 1)


GIB = M.GIB


class RegionReleaseTests(unittest.TestCase):
    """A recorded region release stands when its receipt was deleted, not when it changed."""

    def test_deleted_receipt_keeps_the_release(self):
        with tempfile.TemporaryDirectory() as directory:
            receipt = Path(directory) / 'REPORT.json'
            receipt.write_text('{"released": true}\n')
            import hashlib
            data = {'fixed_claims': {'a': 5}, 'region_claims': {'6ae0': 17 * GIB},
                    'released_region_claims': {'6ae0': {'bytes': 17 * GIB, 'receipt': str(receipt),
                                                        'sha256': hashlib.sha256(receipt.read_bytes()).hexdigest()}}}
            self.assertEqual(M.ledger_claims(data), {'a': 5})
            receipt.unlink()
            warnings = io.StringIO()
            with redirect_stderr(warnings):
                self.assertEqual(M.ledger_claims(data), {'a': 5})
            self.assertIn('region release 6ae0: receipt', warnings.getvalue())
            receipt.write_text('{"released": false}\n')
            self.assertEqual(M.ledger_claims(data), {'a': 5, 'legacy:6ae0': 17 * GIB})


class RetainedHoldTests(unittest.TestCase):
    """A batch hold books live anonymous use plus its running compiles."""

    AGGREGATE = '/cg/zesuworkloads-aggregate1000p1r1.slice'

    class Reader:
        def __init__(self, anon, aggregate):
            self.anon, self.aggregate = anon, aggregate
        def claim(self, data, key, **options):
            return {'verified': True, 'aggregate_verified': True, 'scope': self.aggregate,
                    'device': 1, 'inode': 2, 'live_bytes': GIB}
        def residual(self, bound):
            row = dict(bound, verified=True, aggregate_verified=True, live_bytes=20 * GIB)
            if self.anon is not None:
                row['anon_bytes'] = self.anon
            return row
        def slice_max(self):
            return M.SLICE_MAX_BYTES
        def slice_sample(self):
            raise OSError('no live sample in this fixture')

    def ledger(self):
        aggregate = {'scope': self.AGGREGATE, 'device': 1, 'inode': 2}
        return {'fixed_claims': {'shell:running': 2 * GIB, 'shell:ended': 0},
                'shell_aggregate_holds': {'shell-aggregate:x': {'aggregate': aggregate,
                                                                'fallback_bytes': 16 * GIB}}}

    def test_batch_with_one_ended_and_one_running_compile(self):
        data = self.ledger()
        result = M.projection(data, M.ledger_claims(data), GIB, 10**13,
                              reader=self.Reader(3 * GIB, self.AGGREGATE))
        # The running compile's 2 GiB claim plus the aggregate's anonymous memory
        # outside it (3 GiB live less its 1 GiB), not the 16 GiB the ended compile
        # once booked. The shared aggregate and its compile count each byte once.
        self.assertEqual(result['active_claim_bytes'], 4 * GIB)

    def test_ledger_total_is_live_claims_plus_unspent_aggregate(self):
        aggregate = {'scope': self.AGGREGATE, 'device': 1, 'inode': 2}
        claims = {'shell:a': 4 * GIB, 'shell:b': 6 * GIB}
        data = {'fixed_claims': dict(claims),
                'shell_aggregate_holds': {'shell-aggregate:x': {'aggregate': aggregate,
                                                                'fallback_bytes': 32 * GIB}}}
        for anon, unspent in ((2 * GIB, 0), (5 * GIB, 3 * GIB)):
            with self.subTest(anon=anon):
                result = M.projection(data, M.ledger_claims(data), GIB, 10**13,
                                      reader=self.Reader(anon, self.AGGREGATE))
                # Each running compile shows 1 GiB live inside the aggregate.
                self.assertEqual(result['active_claim_bytes'], sum(claims.values()) + unspent)

    def test_hold_without_anonymous_sample_keeps_its_fallback(self):
        data = self.ledger()
        result = M.projection(data, M.ledger_claims(data), GIB, 10**13,
                              reader=self.Reader(None, self.AGGREGATE))
        self.assertEqual(result['active_claim_bytes'], 16 * GIB)

    def test_hold_never_books_above_its_fallback(self):
        data = self.ledger()
        result = M.projection(data, M.ledger_claims(data), GIB, 10**13,
                              reader=self.Reader(40 * GIB, self.AGGREGATE))
        self.assertEqual(result['active_claim_bytes'], 16 * GIB)


class GateCompileSumTests(unittest.TestCase):
    """A measured gate books its own claim plus its running compiles."""

    AGGREGATE = '/cg/zesuworkloads-aggregate1000p7r1.slice'

    class Reader(RetainedHoldTests.Reader):
        pass

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def marker(self, name, claim, fence=16 * GIB):
        path = self.root / name
        path.write_text(f'1234\nwriter=\naggregate=x\nmemory_claim_bytes={claim}\nmemory_fence_bytes={fence}\n')
        return {'marker': str(path)}

    def ledger(self, compiles, gate=GIB, cold=47 * GIB):
        data = {'fixed_claims': {'CorrectnessGate_g': gate},
                'correctness_gate_cold_claims': {'CorrectnessGate_g': cold} if cold else {},
                'shell_claim_owners': {}}
        for index, claim in enumerate(compiles):
            key = f'shell:{index}'
            data['fixed_claims'][key] = claim
            data['shell_claim_owners'][key] = self.marker(f'm{index}', claim)
        return data

    def booked(self, data, new=GIB, available=10**13):
        return M.projection(data, M.ledger_claims(data), new, available,
                            reader=self.Reader(None, self.AGGREGATE))

    def test_cached_gate_books_its_own_claim_plus_running_compiles(self):
        result = self.booked(self.ledger([GIB, GIB]))
        self.assertEqual(result['active_claim_bytes'], 3 * GIB)

    def test_an_unmeasured_compile_adds_its_fence_but_no_floor(self):
        # One running compile is unmeasured (booked at its 16 GiB fence). Its
        # fence bounds it, so the gate no longer jumps to its 47 GiB basis.
        result = self.booked(self.ledger([GIB, 16 * GIB]))
        self.assertEqual(result['active_claim_bytes'], 18 * GIB)
        many = self.booked(self.ledger([16 * GIB] * 4))
        self.assertEqual(many['active_claim_bytes'], GIB + 64 * GIB)

    def test_measured_compiles_together_book_at_most_the_gate_basis(self):
        # Ten measured compiles at 8 GiB each sum to 81 GiB; their peaks do not
        # coincide, and the measured whole-gate basis is 47 GiB.
        result = self.booked(self.ledger([8 * GIB] * 10))
        self.assertEqual(result['active_claim_bytes'], 47 * GIB)
        # An unmeasured compile raises the cap by its own fence booking.
        mixed = self.booked(self.ledger([8 * GIB] * 10 + [16 * GIB]))
        self.assertEqual(mixed['active_claim_bytes'], 63 * GIB)

    def test_a_gate_never_books_above_its_aggregate_fence(self):
        data = self.ledger([16 * GIB] * 4)
        data['claim_fences'] = {'CorrectnessGate_g': {'owner': {}, 'physical_fence_bytes': 40 * GIB}}
        self.assertEqual(self.booked(data)['active_claim_bytes'], 40 * GIB)

    def test_compile_joining_a_gate_adds_to_its_sum(self):
        data = self.ledger([GIB])
        joining = {'verified': True, 'aggregate_verified': True, 'scope': self.AGGREGATE,
                   'device': 1, 'inode': 2, 'live_bytes': 0}
        result = M.projection(data, M.ledger_claims(data), 2 * GIB, 10**13,
                              reader=self.Reader(None, self.AGGREGATE), new_observation=joining)
        self.assertEqual(result['active_claim_bytes'], 4 * GIB)

    def test_unmeasured_gate_keeps_the_max_rule(self):
        result = self.booked(self.ledger([GIB, GIB], gate=47 * GIB, cold=None))
        self.assertEqual(result['active_claim_bytes'], 47 * GIB)

    def test_gate_sum_above_the_slice_cap_waits_for_admission(self):
        result = self.booked(self.ledger([16 * GIB] * (M.SLICE_MAX_BYTES // (16 * GIB) + 1)))
        self.assertGreater(result['active_claim_bytes'], result['slice_claim_cap_bytes'])
        self.assertFalse(result['fits'])


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

    def test_slice_sample_reads_exact_owned_parent_and_preserves_fences(self):
        (self.parent/'memory.current').write_text(str(M.SLICE_MAX_BYTES))
        (self.parent/'memory.stat').write_text('anon 1234\nfile 999999999\n')
        sample = self.reader.slice_sample()
        self.assertEqual(sample['live_bytes'], 1234)
        self.assertEqual(sample['counter'], 'memory.stat:anon')
        self.assertEqual(sample['scope'], str(self.parent))
        self.assertEqual(sample['slice_max_bytes'], M.SLICE_MAX_BYTES)
        self.assertEqual((self.parent/'memory.max').read_text(), str(M.SLICE_MAX_BYTES))
        self.assertEqual((self.parent/'memory.swap.max').read_text(), '0')
        (self.parent/'memory.swap.max').write_text('1')
        with self.assertRaises(ValueError): self.reader.slice_sample()

    def test_residual_reports_anonymous_memory_apart_from_page_cache(self):
        (self.group/'cgroup.events').write_text('populated 1\n')
        (self.group/'memory.current').write_text(str(30*M.GIB))
        (self.group/'memory.stat').write_text(f'anon {3*M.GIB}\nfile {27*M.GIB}\n')
        info=self.group.stat()
        row=self.reader.residual(dict(scope=str(self.group),device=info.st_dev,inode=info.st_ino))
        self.assertEqual((row['live_bytes'],row['anon_bytes']),(30*M.GIB,3*M.GIB))

    def test_prune_drops_only_removed_aggregate_holds(self):
        (self.group/'cgroup.events').write_text('populated 1\n')
        info=self.group.stat()
        live=dict(scope=str(self.group),device=info.st_dev,inode=info.st_ino)
        gone=dict(scope=str(self.parent/f'zesuworkloads-aggregate{os.getuid()}p99r1.slice'),device=1,inode=2)
        alien=dict(scope=str(self.root/'elsewhere.slice'),device=1,inode=2)
        data={'shell_aggregate_holds':{k:{'aggregate':v,'fallback_bytes':7}
              for k,v in (('live',live),('gone',gone),('alien',alien))}}
        M.prune_closed_aggregate_holds(data,self.reader)
        # A removed owned aggregate is closed; a live or unverifiable one keeps its booking.
        self.assertEqual(set(data['shell_aggregate_holds']),{'live','alien'})
        claims=M.projection(data,{},1,10**12,reader=self.reader)
        self.assertGreaterEqual(claims['raw_claim_bytes'],7)

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


class WorkloadParentTests(unittest.TestCase):
    def test_parent_fence_follows_the_account_limit(self):
        with tempfile.TemporaryDirectory() as temp:
            account = Path(temp) / 'user.slice' / 'user-1000.slice'
            self.assertEqual(M.workload_parent_bytes(temp, uid=1000), 160 * M.GIB)
            account.mkdir(parents=True)
            for account_gib, parent_gib in ((200, 160), (210, 170), (235, 175)):
                (account / 'memory.max').write_text(f'{account_gib * M.GIB}\n')
                self.assertEqual(M.workload_parent_bytes(temp, uid=1000), parent_gib * M.GIB)
            (account / 'memory.max').write_text('max\n')
            self.assertEqual(M.workload_parent_bytes(temp, uid=1000), 160 * M.GIB)


if __name__=='__main__':unittest.main()
