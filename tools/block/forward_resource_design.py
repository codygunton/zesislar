"""Check inherited ownership after each instruction of symbolic CFG traversal."""
from dataclasses import replace

from forward_design import evaluate_function
from forward_resources import _Facts, apply_owned_writes, render_resource_boundary
from symbolic_state import Expr, MemoryRegion, MemoryWrite, SymbolicState


def _state_from_result(record):
    """Decode only an in-process traversal result, never an initial state file."""
    memory = []
    for region in record['memory']:
        length = region.get('length')
        memory.append(MemoryRegion(Expr.from_dict(region['base']),
            tuple(Expr.from_dict(value) for value in region.get('bytes', [])),
            Expr.from_dict(region['byte_array']) if 'byte_array' in region else None,
            Expr.from_dict(length) if isinstance(length, dict) else length,
            region.get('uninitialized', False), region.get('ownership_id'), region.get('minimum_length', 0)))
    writes = [MemoryWrite(Expr.from_dict(write['address']), Expr.from_dict(write['value']), write['size'],
                          write['mapped'], Expr.from_dict(write['result']) if 'result' in write else None,
                          write.get('event_id'), write.get('provenance'), write.get('ownership_id'))
              for write in record['writes']]
    return SymbolicState({key: Expr.from_dict(value) for key, value in record['registers'].items()}, memory,
                         [Expr.from_dict(value) for value in record['conditions']], list(record['reports']), writes,
                         record['endianness'], record['trace_count'],
                         {key: Expr.from_dict(value) for key, value in record.get('retained_registers', {}).items()},
                         list(record.get('memory_disjoint', [])),
                         list(record['register_writes']) if 'register_writes' in record else None)


def _prepare_state(state, seed):
    known = _Facts(state.conditions, seed.facts)
    state.memory_disjoint = [(fact['terms']['left'], fact['terms']['right'])
                             for fact in known.available('disjoint_ranges')]
    owned = {resource.id: resource for resource in seed.resources}
    state.memory = [replace(region, minimum_length=known.lower_bound(owned[region.ownership_id])[0])
                    if region.ownership_id in owned else region for region in state.memory]


def evaluate_owned_function(function, traces, initial_seeds, *, vocabulary, max_paths=4096):
    """Stop a block before another instruction when ownership checks fail.

    Each seed carries public source ownership or an explicit handwritten cut.
    The value traversal retains the same CFG cuts and concrete-PC routing.
    """
    seeds = {int(pc, 0) if isinstance(pc, str) else pc: seed for pc, seed in initial_seeds.items()}
    initial = {}
    for pc, seed in seeds.items():
        state = seed.state.copy()
        _prepare_state(state, seed)
        initial[pc] = state

    def check(state, *, seed_pc, **context):
        seed = seeds[seed_pc]
        _prepare_state(state, seed)
        result = apply_owned_writes(seed.resources, state.writes, conditions=state.conditions,
                                    facts=seed.facts, endianness=state.endianness)
        if result.status != 'complete':
            return result.to_dict()
        owners = {transition['write_index']: transition['resource_id'] for transition in result.transitions}
        state.writes = [replace(write, ownership_id=owners[index]) for index, write in enumerate(state.writes)]
        rendered = render_resource_boundary(seed.ownership, result, state, vocabulary=vocabulary)
        if rendered['block_status'] != 'completed':
            return rendered
        return None

    report = evaluate_function(function, traces, initial, max_paths=max_paths, check_state=check)
    report['resource_layer_schema'] = 'owned-resources.v1'
    for boundary in report['boundaries']:
        for alternative in boundary['alternatives']:
            seed = seeds[int(alternative['seed_pc'], 0)]
            state = _state_from_result(alternative['state'])
            result = apply_owned_writes(seed.resources, state.writes, conditions=state.conditions,
                                        facts=seed.facts, endianness=state.endianness)
            alternative['resource_boundary'] = render_resource_boundary(seed.ownership, result, state,
                                                                        vocabulary=vocabulary)
    return report


def prepare_literal_entry_helpers(report, interfaces, *, register_ownership, enabled=False):
    """Prepare rule (d) without changing generated entries or enabling the rule."""
    from entry_helper_resources import prepare_function_entry_helpers
    return prepare_function_entry_helpers(report, interfaces,
        register_ownership=register_ownership, enabled=enabled)
