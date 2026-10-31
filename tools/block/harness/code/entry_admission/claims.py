"""Root reservations. Never reduce or release a claim."""
from pathlib import Path
import time
from io_helpers import read, sha, atomic_json, locked, memory_available

LEDGER = Path('/home/cody/zesislar/_build/agents/worker-build-2/native-region-release-v1/LEDGER.json')
LOCK = LEDGER.with_name('LEDGER.lock')
INITIAL = 64 * 1024**3
ALLOWANCE = 2 * 1024**3


def active_claims(data, legacy):
    result = dict(data['fixed_claims'])
    if any(type(v) is not int or v < 0 for v in result.values()):
        raise ValueError('invalid-fixed-claim')
    for name,amount in data.get('region_claims', {}).items():
        if type(amount) is not int or amount < 0:
            raise ValueError('invalid-legacy-claim')
        release = data.get('released_region_claims', {}).get(name)
        bound = legacy.get(name)
        if bound is not None:
            if release != bound or bound['bytes'] != amount or sha(bound['receipt']) != bound['sha256']:
                raise ValueError('changed-root-legacy-release')
        else:
            # An unbound release cannot remove an old reservation.
            result['legacy:'+name] = amount
    return result


def requested_claim(aggregate_kib):
    if type(aggregate_kib) is not int or aggregate_kib < 0:
        raise ValueError('invalid-aggregate-VmHWM')
    return max(INITIAL, aggregate_kib * 1536 + ALLOWANCE)


def latch(path, reason, detail):
    if not Path(path).exists():
        atomic_json(path, {'time_ns':time.time_ns(),'reason':reason,'detail':detail,
                          'healthy_jobs_not_cancelled':True,'automatic_release':False})


def reserve(key, legacy, receipt, latch_path, *, ledger=LEDGER, lock=LOCK, available=memory_available,
            physical_fence_bytes=None):
    if physical_fence_bytes != INITIAL:
        raise ValueError("The legacy caller lacks the reviewed 64 GiB aggregate policy.")
    with locked(ledger,lock):
        if Path(latch_path).exists():
            raise ValueError('shared-dispatch-latch-is-set')
        data = read(ledger)
        claims = active_claims(data,legacy)
        if data['fixed_claims'].get(key,0):
            raise ValueError('claim-already-assigned')
        free = available()
        record = {'time_ns':time.time_ns(),'claim':key,'initial_bytes':INITIAL,
            'active_claims':claims,'total_before_bytes':sum(claims.values()),
            'requested_total_bytes':sum(claims.values())+INITIAL,
            'MemAvailable_bytes':free,'budget_bytes':free*7//10,
            'admitted':sum(claims.values())+INITIAL <= free*7//10,'automatic_release':False}
        if record['admitted']:
            data['fixed_claims'][key] = INITIAL
            data.setdefault('s1_row5_admissions',{})[key] = record
            atomic_json(ledger,data)
        record['ledger_sha256'] = sha(ledger)
        atomic_json(receipt,record)
        return record


def grow(key, aggregate_kib, owner, legacy, receipt, latch_path, *,
         ledger=LEDGER, lock=LOCK, available=memory_available):
    with locked(ledger,lock):
        data = read(ledger)
        current = data['fixed_claims'].get(key,0)
        if type(current) is not int or current < INITIAL:
            raise ValueError('live-claim-is-not-assigned')
        claims = active_claims(data,legacy)
        desired = max(current,requested_claim(aggregate_kib))
        free = available()
        total = sum(claims.values())-current+desired
        record = {'time_ns':time.time_ns(),'owner':owner,'claim':key,
            'previous_bytes':current,'requested_bytes':desired,'aggregate_live_VmHWM_KiB':aggregate_kib,
            'client_allowance_bytes':ALLOWANCE,'MemAvailable_bytes':free,'budget_bytes':free*7//10,
            'requested_total_bytes':total,'changed':desired>current,
            'budget_exceeded':total>free*7//10,'committed':False,
            'automatic_stop':False,'automatic_release':False}
        try:
            if desired > current:
                # Account the observation even when the fresh budget is exceeded.
                data['fixed_claims'][key] = desired
                data.setdefault('s1_row5_growth',{})[key] = dict(record,committed=True)
                atomic_json(ledger,data)
            record['committed'] = True
            record['ledger_sha256'] = sha(ledger)
            atomic_json(receipt,record)
        except BaseException as error:
            record['commit_error'] = repr(error)
            atomic_json(Path(receipt).with_name('GROWTH-COMMIT-FAILURE.json'),record)
            latch(latch_path,'growth-commit-failed',record)
            raise
        if record['changed'] and record['budget_exceeded']:
            latch(latch_path,'growth-exceeds-budget',record)
        return record


def assigned_budget(key, legacy, *, ledger=LEDGER, lock=LOCK, available=memory_available):
    with locked(ledger,lock):
        data = read(ledger)
        claims = active_claims(data,legacy)
        if data['fixed_claims'].get(key,0) < INITIAL:
            raise ValueError('assigned-claim-is-absent')
        free = available()
        return {'time_ns':time.time_ns(),'claim':key,'assigned_bytes':data['fixed_claims'][key],
                'active_claims':claims,'budget_bytes':free*7//10,
                'MemAvailable_bytes':free,'total_bytes':sum(claims.values()),
                'fits':sum(claims.values()) <= free*7//10}
