"""Check fresh inputs before admission and keep cache verdicts separate."""
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path


SELECTED_BLOCKS = frozenset(['800d6960', '800d69d8', '800d6a00', '800d6a14',
                            '800d6a64', '800d6ab4', '800d69e0', '800d6a6c',
                            '800d6a08', '800d6aa8'])


def save(path, value):
    path = Path(path)
    path.write_text(json.dumps(value, indent=2) + '\n')


def binding(path):
    path = Path(path)
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def select(jobs):
    if len(jobs) != 10 or {job['key'] for job in jobs} != SELECTED_BLOCKS:
        raise ValueError('The Stage1 job set differs from the released ten blocks.')
    if any(job['phase'] != 'native' for job in jobs):
        raise ValueError('The selected Stage1 set contains a non-native job.')
    return jobs


def annotate_native_return(result, calls_binding, native_route=None):
    """Read the actual native response. Do not infer a return from exit status."""
    path = Path(calls_binding['path'])
    if binding(path)['sha256'] != calls_binding['sha256']:
        raise ValueError('The retained native call log changed.')
    calls = json.loads(path.read_text())
    from native_route import authority_body
    expected_body=authority_body(native_route) if native_route else 'zesu_block.'
    native = [row for row in calls if row['tool'] == 'rocq_check'
              and row['arguments'].get('body') == expected_body]
    if len(native) != 1:
        raise ValueError('A cache observation requires one exact native tactic call.')
    returned = native[0].get('result', {})
    normal = returned.get('success') is True and not returned.get('pet_restarted') and not returned.get('restarted')
    result = deepcopy(result)
    result.update(normal_tactic_return=bool(normal), proof_finished=returned.get('proof_finished'),
                  native_calls=calls_binding)
    if result.get('status') == 'native_open':
        if not normal or returned.get('proof_finished') is not False:
            raise ValueError('The open verdict has no normal unfinished native return.')
        state_id = returned.get('state_id')
        exports = [row for row in calls if row['tool'] == 'rocq_complete_goals'
                   and row['arguments'].get('from_state') == state_id
                   and row.get('result', {}).get('success') is True]
        if state_id is None or not exports or result.get('complete_state', {}).get('state_source') != 'successful_command_returned_state':
            raise ValueError('The open verdict lacks a complete returned-state export.')
    return result


def retain_hit(out, cached, verification=None):
    """Reuse the verdict. Do not authorize a cached object for a new proof."""
    out = Path(out)
    result = deepcopy(cached['result'])
    prior_cpu = result.get('CPU')
    prior_peak = result.get('aggregate_peak_bytes')
    physical = (verification or {}).get('physical_receipt')
    if result.get('status') == 'passed':
        if not physical or not physical.get('all_owned_actors_closed') or not physical.get('claim_released') or physical.get('CPU') is None:
            raise ValueError('The closed-hit kernel check lacks costs or physical closure.')
    kernel_cpu = physical['CPU'] if physical else {'cpu_seconds': 0, 'scope': 'No fresh proof search.'}
    cache_status = 'cached open (not re-run)' if result.get('status') == 'native_open' else 'cached'
    result.update(cache_status=cache_status, historical_CPU=prior_cpu,
                  historical_peak_bytes=prior_peak,
                  CPU=kernel_cpu,
                  aggregate_peak_bytes=None, aggregate_peak_KiB=None,
                  final_memory_accounting_available=False,
                  object_reuse_authorized=False, proof_accepted_by_Root=False,
                  fresh_proof_calls=0, fresh_search_CPU_seconds=0,
                  kernel_recheck=verification)
    if result.get('status') == 'native_open':
        result['cached_residual_scope'] = 'Diagnostic only. No proof-state continuation is authorized.'
        result['cache_verdict'] = 'cached open (not re-run)'
    else:
        if verification is None or verification.get('success') is not True:
            raise ValueError('A closed cache hit has no successful current kernel re-check.')
        result['cache_verdict'] = 'cached closed (kernel re-checked)'
    save(out / 'CACHE-HIT.json', {'cache_status': cache_status, 'manifest': binding(cached['manifest']),
                                 'canonical_claim_created': verification is not None,
                                 'kernel_recheck': verification, 'proof_calls': 0})
    save(out / 'CLOSURE.json', {'all_owned_actors_closed': True, 'owned_proof_actors': [],
                              'canonical_claim_created': verification is not None,
                              'kernel_recheck': verification,
                              'basis': 'No proof search ran. Any kernel-check closure is retained separately.'})
    save(out / 'RELEASE.json', {'released': True, 'never_admitted': verification is None,
                              'kernel_recheck': verification, 'bytes': 0 if physical is None else physical['released_bytes'],
                              'claim_key': None if physical is None else physical['claim_key']})
    save(out / 'RESULT.json', result)
    return result


def dispatch(*, block, out, prepared, collector, cache, key_builder, reserve,
             execute, close, release, artifacts, verify_closed=None, purpose='exploration'):
    """Run at most one native attempt. Callbacks use the stock lifecycle.

    prepared contains the fresh collection report. No historical key enters
    this function. execute() must start its all-exit watcher before yielding.
    close() must retain exact actor and aggregate closure before release().
    """
    if block not in SELECTED_BLOCKS:
        raise ValueError('The block is outside the released Stage1 set.')
    out = Path(out)
    if (out / 'RESULT.json').exists():
        raise ValueError('The attempt already has a result. The adapter refuses replay.')
    if prepared['input']['block'] != block:
        raise ValueError('The collected key input names another block.')
    collector.revalidate(prepared)
    key = key_builder(prepared['input'])
    save(out / 'CACHE-KEY.json', key)
    # Lookup precedes every canonical admission. Corruption propagates.
    defects, verifications = [], []
    def on_defect(record):
        defects.append(record)
        save(out / ('CACHE-DEFECT-%03d.json' % len(defects)), record)
    def verifier(hit):
        if verify_closed is None:
            raise ValueError('Closed cache reuse requires a current kernel verifier.')
        receipt = verify_closed(hit)
        verifications.append(receipt)
        return receipt
    enabled = (purpose == 'exploration' and os.environ.get('ZESU_PROOF_CACHE') != 'off'
               and os.environ.get('ZESU_IO') != 'gate')
    cached = cache.lookup(key, verify_closed=verifier if verify_closed is not None else None,
                          on_defect=on_defect, purpose=purpose) if enabled else None
    if any(row.get('physical_receipt') and
           (not row['physical_receipt'].get('all_owned_actors_closed') or not row['physical_receipt'].get('claim_released'))
           for row in verifications):
        raise RuntimeError('The kernel-check lifecycle remains open. Fresh execution is held.')
    if cached is not None:
        return retain_hit(out, cached, verifications[-1] if verifications else None)
    save(out / 'CACHE-MISS.json', {'cache_status': 'fresh' if enabled else 'off',
                                 'historical_seeding': False, 'purpose': purpose})
    admitted = False
    result = None
    try:
        reserve(recheck=lambda: collector.revalidate(prepared))
        admitted = True
        collector.revalidate(prepared)
        result = execute(prepared['execution_environment'])
    finally:
        if admitted:
            closure = close()
            if not closure['all_owned_actors_closed']:
                raise RuntimeError('The owned proof actors remain live. The claim remains assigned.')
            release(closure)
    result = deepcopy(result)
    result['cache_status'] = 'fresh' if enabled else 'off'
    result['cache_defect'] = bool(defects)
    save(out / 'RESULT.json', result)
    if enabled and result.get('status') in {'passed', 'native_open'}:
        # The cache validates normal returns, exact complete groups, and
        # all required closed-proof receipts. The store remains fresh.
        stored = cache.store(key, out / 'RESULT.json', artifacts(), purpose=purpose)
        save(out / 'CACHE-STORE.json', {'stored': True, 'cache_status': 'fresh',
                                      'receipt': stored,
                                      'historical_CPU_added': False})
    else:
        save(out / 'CACHE-STORE.json', {'stored': False, 'cache_status': 'fresh',
                                      'reason': 'Caching is off or no completed native verdict exists.'})
    return result
