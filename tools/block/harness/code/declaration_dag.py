"""Schedule independent declarations before serialized receipt publication.

The caller authenticates the graph, resource weights, and canonical admission.
Workers produce private artifacts. Only the controller publishes their receipts.
"""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import threading


GIB = 1024 ** 3
CLAIM_BYTES = 64 * GIB
MAXIMUM_WORKERS = 48


def _positive(value, label):
    if type(value) is not int or value <= 0:
        raise ValueError('The declaration ' + label + ' must be a positive integer.')
    return value


def validate(ordered, edges, weights, completed, protected):
    """Require a complete topological plan before dispatching any compiler."""
    if (not isinstance(ordered, list) or not ordered or
            any(not isinstance(name, str) or not name for name in ordered) or
            len(set(ordered)) != len(ordered)):
        raise ValueError('The declaration order must contain distinct module names.')
    positions = {name: index for index, name in enumerate(ordered)}
    if set(weights) != set(ordered):
        raise ValueError('The declaration weights must cover the exact order.')
    if set(completed) & positions.keys() or not set(protected) <= positions.keys():
        raise ValueError('The declaration completion or protected set is invalid.')
    for name, weight in weights.items():
        if _positive(weight, 'module weight') >= CLAIM_BYTES:
            raise ValueError('One declaration cannot fit below the aggregate booking: ' + name)
    dependencies = {name: set() for name in ordered}
    for edge in edges:
        name, dependency = edge['from'], edge['to']
        if name not in positions:
            continue
        if dependency in positions:
            if positions[dependency] >= positions[name]:
                raise ValueError('The declaration order is not topological: ' + name)
        elif dependency not in completed:
            raise ValueError('A declaration import lacks an accepted object: ' + dependency)
        dependencies[name].add(dependency)
    return dependencies


def execute(ordered, edges, weights, *, completed=(), protected=(),
            claim_bytes, fence_bytes, available_bytes, compile_private,
            publish, compile_protected, checkpoint=lambda value: None,
            maximum_workers=MAXIMUM_WORKERS):
    """Drain healthy workers after failure. Publish before releasing each weight."""
    if claim_bytes != CLAIM_BYTES or fence_bytes != CLAIM_BYTES:
        raise ValueError('Parallel declarations require the fixed 64/64 GiB policy.')
    count = min(_positive(maximum_workers, 'worker count'), MAXIMUM_WORKERS)
    completed, protected = set(completed), set(protected)
    dependencies = validate(ordered, edges, weights, completed, protected)
    pending = set(ordered)
    active, receipts, failures = {}, {}, []
    halt = threading.Event()
    peak_workers = peak_weight = 0
    protected_active = None

    def report():
        running = list(active.values()) + ([protected_active] if protected_active else [])
        checkpoint({'pending': [name for name in ordered if name in pending],
                    'active': sorted(running),
                    'accepted': list(receipts), 'failures': list(failures),
                    'running_weight_bytes': sum(weights[name] for name in running),
                    'claim_bytes': CLAIM_BYTES, 'maximum_workers': count})

    def worker(name):
        if halt.is_set():
            raise RuntimeError('A declaration did not start after another worker failed.')
        try:
            return compile_private(name)
        except BaseException:
            halt.set()
            raise

    def accept(name, artifact):
        # The provider validates and publishes on this controller thread only.
        receipt = publish(name, artifact)
        if not isinstance(receipt, dict) or set(receipt) != {'path', 'sha256'}:
            raise ValueError('A declaration publication lacks its bound accepted receipt.')
        receipts[name] = receipt
        completed.add(name)

    report()
    with ThreadPoolExecutor(max_workers=count) as pool:
        while pending or active:
            if not failures and not halt.is_set():
                # No later module can cross an unfinished protected MCP barrier.
                barrier = next((name for name in ordered if name in protected and name in pending), None)
                boundary = ordered.index(barrier) if barrier is not None else len(ordered)
                before = [name for name in ordered[:boundary] if name in pending]
                if barrier is not None and not before and not active:
                    try:
                        available = _positive(available_bytes(), 'available memory')
                        if weights[barrier] > min(CLAIM_BYTES - 1, 7 * available // 10):
                            raise ValueError('The protected declaration exceeds the current memory budget.')
                        protected_active = barrier
                        peak_workers = max(peak_workers, 1)
                        peak_weight = max(peak_weight, weights[barrier])
                        report()
                        artifact = compile_protected(barrier)
                        accept(barrier, artifact)
                        pending.remove(barrier)
                    except Exception as error:
                        failures.append({'module': barrier, 'error': str(error)})
                        halt.set()
                    finally:
                        protected_active = None
                    report()
                    continue
                ready = [name for name in before if dependencies[name] <= completed]
                for name in ready:
                    if len(active) >= count or halt.is_set():
                        break
                    available = _positive(available_bytes(), 'available memory')
                    budget = min(CLAIM_BYTES - 1, 7 * available // 10)
                    running = sum(weights[module] for module in active.values())
                    if running + weights[name] > budget:
                        continue
                    pending.remove(name)
                    active[pool.submit(worker, name)] = name
                    peak_workers = max(peak_workers, len(active))
                    peak_weight = max(peak_weight, running + weights[name])
                if pending and not active and not failures:
                    failures.append({'error': 'No ready declaration fits the current memory budget.'})
                    halt.set()
                report()
            if not active:
                break
            finished, _ = wait(active, return_when=FIRST_COMPLETED)
            for future in finished:
                name = active[future]
                try:
                    accept(name, future.result())
                except Exception as error:
                    failures.append({'module': name, 'error': str(error)})
                    halt.set()
                finally:
                    # Keep the weight until compilation, closure, and publication finish.
                    active.pop(future)
            report()
    result = {'schema': 'entry-chain.declaration-dag-result.v1', 'receipts': receipts,
              'failures': failures, 'pending': [name for name in ordered if name in pending],
              'peak_workers': peak_workers, 'peak_weight_bytes': peak_weight,
              'claim_bytes': CLAIM_BYTES, 'fence_bytes': CLAIM_BYTES}
    if failures:
        error = RuntimeError('The declaration DAG stopped after a failed dispatch or publication.')
        error.result = result
        raise error
    return result
