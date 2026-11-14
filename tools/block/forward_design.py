#!/usr/bin/env python3
"""Propagate untrusted symbolic states through straight-line CFG blocks.

Only caller-supplied entry states and explicit cut seeds start execution.
Incoming states never cross a join or loop head. A separate source pass may
generalize them and supply an explicit generated seed on a later round.
"""
from collections import deque
from dataclasses import dataclass
import re

try:
    from .symbolic_state import SymbolicState, evaluate_trace, parse_trace
    from .boundary_guards import annotate_reaching_stops
except ImportError:
    from symbolic_state import SymbolicState, evaluate_trace, parse_trace
    from boundary_guards import annotate_reaching_stops


GPR = re.compile(r'x(?:[0-9]|[12][0-9]|3[01])\Z')


def _pc(value):
    return int(value, 0) if isinstance(value, str) else int(value)


def _name(value):
    return value[1:-1] if isinstance(value, str) and value.startswith('|') else value


def _footprint(events, universe):
    """Compute reads before writes and writes on every syntactic trace path."""
    uses, written = set(), set()
    for event in events:
        if not isinstance(event, list) or not event:
            return universe, set()
        kind, *args = event
        def expression_reads(raw):
            if not isinstance(raw, list) or not raw:
                return set()
            name = _name(raw[0]) if isinstance(raw[0], str) else None
            direct = {name} if isinstance(name, str) and GPR.fullmatch(name) else set()
            return direct | set().union(*(expression_reads(child) for child in raw))
        # A write destination is not an expression read. Its value can still
        # read that register, as in a self update.
        expressions = args[1:] if kind == 'write-reg' else args
        uses.update(expression_reads(expressions) - written)
        if kind == 'cases':
            if len(args) < 2:
                return universe, set()
            branches = []
            for trace in args[1:]:
                if not isinstance(trace, list) or not trace or trace[0] != 'trace':
                    return universe, set()
                branch_uses, branch_written = _footprint(trace[1:], universe)
                uses.update(branch_uses - written)
                branches.append(branch_written)
            written.update(set.intersection(*branches))
        elif kind in ('read-reg', 'assume-reg', 'write-reg') and args:
            name = _name(args[0])
            if isinstance(name, str) and GPR.fullmatch(name):
                if kind == 'write-reg':
                    written.add(name)
                elif name not in written:
                    uses.add(name)
        elif kind not in {'declare-const', 'define-const', 'define-enum', 'assert',
                          'assume', 'cycle', 'branch-address', 'read-mem', 'write-mem'}:
            return universe, set()
    return uses, written


def _liveness(blocks, instructions, traces, initial_states):
    universe = {name for state in initial_states.values() for name in state.registers if GPR.fullmatch(name)}
    parsed = {}
    for pc, source in traces.items():
        try:
            parsed[pc] = parse_trace(source)[1:]
        except ValueError:
            parsed[pc] = None
        # Include every syntactic register name before conservative fallback.
        def registers(value):
            if not isinstance(value, list):
                return
            if value and value[0] in ('read-reg', 'write-reg', 'assume-reg') and len(value) > 1:
                name = _name(value[1])
                if isinstance(name, str) and GPR.fullmatch(name):
                    universe.add(name)
            for child in value:
                if isinstance(child, list):
                    registers(child)
        registers(parsed[pc])
    uses, writes = {}, {}
    for pc in blocks:
        uses[pc], writes[pc] = set(), set()
        for instruction in instructions[pc]:
            events = parsed.get(instruction)
            read, written = _footprint(events, universe) if events is not None else (universe, set())
            uses[pc].update(read - writes[pc])
            writes[pc].update(written)
    live = {pc: set() for pc in blocks}
    changed = True
    while changed:
        changed = False
        for pc, block in reversed(list(blocks.items())):
            outgoing = set().union(*(live[target] for target in block['successors'] if target in blocks))
            current = uses[pc] | (outgoing - writes[pc])
            if current != live[pc]:
                live[pc], changed = current, True
    return live


def _project(state, live):
    result = state.copy()
    result.retained_registers.update(state.registers)
    result.registers = {name: value for name, value in result.registers.items()
                        if not GPR.fullmatch(name) or name in live}
    return result


def source_liveness(function, traces, initial_states):
    """Compute conservative source reads without executing any trace path.

    Following successors beyond a cut can retain extra values. It cannot mark
    a value dead merely because the first chosen path did not read it.
    """
    blocks = {_pc(block['start']): {**block, 'successors': [_pc(pc) for pc in block['successors']]}
              for block in function['blocks']}
    rows = [_pc(row['pc']) for row in function['rows']]
    instructions = {pc: [at for at in rows if pc <= at < _pc(block['end'])] for pc, block in blocks.items()}
    if (len(blocks) != len(function['blocks']) or len(set(rows)) != len(rows)
            or any(not selected or selected[0] != pc for pc, selected in instructions.items())
            or sorted(at for selected in instructions.values() for at in selected) != sorted(rows)):
        raise ValueError('The liveness source has an incomplete or overlapping CFG')
    traces = {_pc(pc): source for pc, source in traces.items()}
    return {pc: sorted(registers) for pc, registers in _liveness(blocks, instructions, traces, initial_states).items()}


@dataclass
class _Work:
    block_pc: int
    seed_pc: int
    state: SymbolicState
    path: tuple = ()
    visited: tuple = ()
    entry: int = 0


def _entry_slots(blocks, boundaries, cuts, duplicated):
    """Group each slot block's alternatives into entry slots, one per incoming edge.

    A duplicated join and every non-cut block after it carry slots. A slot's key is
    its predecessor block and, when that block carries slots too, the predecessor slot
    its paths continue from; alternatives that split inside a block share a slot.
    """
    carrying, pending = set(), list(duplicated)
    while pending:
        pc = pending.pop()
        if pc not in carrying:
            carrying.add(pc)
            pending.extend(target for target in blocks[pc]['successors'] if target in blocks and target not in cuts)
    slot_of = {}

    def slots(pc):
        if pc not in slot_of:
            rows, index = [], {}
            for number, alternative in enumerate(boundaries[pc]['alternatives']):
                predecessor = _pc(alternative['predecessor_pc'])
                key = (predecessor, slots(predecessor)[alternative['predecessor_alternative']]
                       if predecessor in carrying else None)
                if key not in index:
                    index[key] = len(rows)
                    rows.append({'predecessor_pc': hex(key[0]), 'predecessor_slot': key[1], 'alternatives': []})
                rows[index[key]]['alternatives'].append(number)
            boundaries[pc]['slots'] = rows
            slot_of[pc] = {number: slot for slot, row in enumerate(rows) for number in row['alternatives']}
        return slot_of[pc]

    for pc in sorted(carrying):
        slots(pc)


def evaluate_function(function, traces, initial_states, *, max_paths=4096, check_state=None,
                      generated_seeds=None, duplicated_joins=()):
    """Return a complete boundary inventory and explicit propagation stops.

    max_paths bounds the total leaf alternatives created during this traversal.
    Infeasible and stopped alternatives count toward the same explicit budget.
    Each boundary lists, as reaching_stops, the stops that dropped a path whose
    block can reach it; a renderer refuses a boundary with any such stop.

    Each pc in duplicated_joins is a join that is not a cut: every incoming path
    continues through it, and its block, with the non-cut blocks after it, records
    one entry slot per incoming edge (`slots`). Their alternatives name the
    alternative they continue from (`predecessor_alternative`).
    """
    if isinstance(max_paths, bool) or not isinstance(max_paths, int) or max_paths < 1:
        raise ValueError('The path limit must be a positive integer')
    entry, end = _pc(function['entry']), _pc(function['end'])
    rows = {_pc(row['pc']): row for row in function['rows']}
    if len(rows) != len(function['rows']):
        raise ValueError('The CFG contains duplicate instruction PCs')
    blocks = {}
    for block in sorted(function['blocks'], key=lambda row: _pc(row['start'])):
        pc, stop = _pc(block['start']), _pc(block['end'])
        if pc in blocks or stop <= pc:
            raise ValueError('The CFG contains a duplicate or empty block')
        blocks[pc] = {'end': stop, 'successors': sorted({_pc(target) for target in block['successors']})}
    if entry not in blocks:
        raise ValueError('The function entry is not a block start')
    instructions, assigned = {}, set()
    for pc, block in blocks.items():
        selected = sorted(at for at in rows if pc <= at < block['end'])
        if not selected or selected[0] != pc or assigned.intersection(selected):
            raise ValueError('The CFG has an empty, overlapping, or incomplete block')
        instructions[pc] = selected
        assigned.update(selected)
    if assigned != set(rows):
        raise ValueError('The CFG leaves instructions outside its blocks')
    predecessors = {pc: set() for pc in blocks}
    for pc, block in blocks.items():
        for target in block['successors']:
            if target in predecessors:
                predecessors[target].add(pc)
    loop_heads = {_pc(loop['minimum_pc']) for loop in function.get('loops', [])}
    if not loop_heads.issubset(blocks):
        raise ValueError('A loop head is not a block start')
    # A call ends its block; its callee runs outside the function. The return
    # site is a cut: a path continues there only from a call-return seed.
    calls = {}
    for call in function.get('calls', []):
        if call.get('kind') == 'tail':
            # A tail jump leaves the function; its block is an exit, not a call.
            continue
        site = _pc(call['pc'])
        block = next((pc for pc, row in blocks.items() if pc <= site < row['end']), None)
        if block is None or instructions[block][-1] != site or blocks[block]['successors'] != [site + 4]:
            raise ValueError('A call does not end its block with the return site as its successor')
        calls[block] = {'call_pc': site, 'callee_pc': _pc(call['target']), 'return_pc': site + 4}
    return_sites = {row['return_pc'] for row in calls.values()}
    cuts = {}
    for pc in blocks:
        reasons = set()
        if pc in loop_heads:
            reasons.add('loop_head')
        if len(predecessors[pc]) > 1:
            reasons.add('join')
        if pc in return_sites:
            reasons.add('call_return')
        if reasons:
            cuts[pc] = reasons
    duplicated = {_pc(pc) for pc in duplicated_joins}
    if any(cuts.get(pc) != {'join'} for pc in duplicated):
        raise ValueError('A duplicated join must be a join and nothing else')
    for pc in duplicated:
        del cuts[pc]
    seeds = {_pc(pc): state for pc, state in initial_states.items()}
    generated_seeds = {_pc(pc): kind for pc, kind in (generated_seeds or {}).items()}
    if any(pc not in seeds or pc not in cuts or kind not in {'join', 'loop_head', 'call_return'}
           or (kind == 'call_return') != (pc in return_sites)
           for pc, kind in generated_seeds.items()):
        raise ValueError('A generated seed must name an explicit join, loop head, or call return site')
    if len(seeds) != len(initial_states) or any(pc != entry and pc not in cuts for pc in seeds):
        raise ValueError('An initial state must belong to the function entry or a handwritten cut')
    if any(not isinstance(state, SymbolicState) for state in seeds.values()):
        raise ValueError('Every initial state must be an explicit SymbolicState')
    traces = {_pc(pc): source for pc, source in traces.items()}
    live = _liveness(blocks, instructions, traces, seeds)
    boundaries = {pc: {'pc': hex(pc), 'status': ('generated_' + generated_seeds[pc]) if pc in generated_seeds
                       else 'handwritten_cut' if pc in cuts else 'unreachable',
                       'alternatives': []} for pc in blocks}
    result = {'schema': 'block-forward-states.v1',
              'function': {'name': function['name'], 'entry': hex(entry), 'end': hex(end)},
              'boundaries': list(boundaries.values()),
              'cuts': [{'pc': hex(pc), 'reason': reason} for pc, reasons in sorted(cuts.items())
                       for reason in sorted(reasons)], 'stops': [], 'reports': [], 'exits': []}
    if calls:
        result['calls'] = [{'block_pc': hex(block), **{key: hex(value) for key, value in row.items()}}
                           for block, row in sorted(calls.items())]
    returns = {_pc(pc) for pc in function.get('returns', [])}
    pending = deque()
    paths_created = 0

    def stop(reason, work, instruction_pc=None, state=None, path=None, **details):
        item = {'reason': reason, 'block_pc': hex(work.block_pc), 'instruction_pc':
                hex(instruction_pc) if instruction_pc is not None else None,
                'seed_pc': hex(work.seed_pc), 'path': list(work.path if path is None else path), **details}
        if state is not None:
            item['state'] = state.to_dict()
        result['stops'].append(item)

    def boundary(pc, state, work, predecessor):
        projected = _project(state, live[pc])
        boundaries[pc]['alternatives'].append({'predecessor_pc': hex(predecessor) if predecessor is not None else None,
                                              'seed_pc': hex(work.seed_pc), 'state': projected.to_dict(),
                                              'path': list(work.path),
                                              'back_edge': pc in loop_heads and predecessor is not None
                                              and (pc == work.seed_pc or pc in work.visited),
                                              **({'predecessor_alternative': work.entry}
                                                 if duplicated and predecessor is not None else {})})
        if pc not in cuts:
            boundaries[pc]['status'] = 'generated'
        return projected, len(boundaries[pc]['alternatives']) - 1

    for pc, state in sorted(seeds.items()):
        work = _Work(pc, pc, state.copy())
        if paths_created == max_paths:
            stop('path_limit', work, state=state, max_paths=max_paths, discarded_alternatives=1)
            continue
        paths_created += 1
        work.state, work.entry = boundary(pc, state, work, None)
        pending.append(work)
    while pending:
        work = pending.popleft()
        if work.block_pc in work.visited:
            stop('cycle_without_cut', work, state=work.state)
            continue
        states = [(work.state, work.path)]
        for at in instructions[work.block_pc]:
            following = []
            for state, prefix in states:
                actual = state.registers.get('PC')
                if actual is None or actual.op != 'bits':
                    stop('unknown_pc', work, at, state, prefix, stage='instruction_entry',
                         actual_pc=actual.to_dict() if actual else None, expected_pc=hex(at))
                    continue
                if actual.value != at:
                    stop('intermediate_pc_mismatch', work, at, state, prefix,
                         actual_pc=hex(actual.value), expected_pc=hex(at))
                    continue
                if at not in traces:
                    stop('missing_trace', work, at, state, prefix)
                    continue
                try:
                    available = max_paths - paths_created + 1
                    alternatives = evaluate_trace(traces[at], state, instruction_index=at, max_paths=available)
                except ValueError as error:
                    stop('invalid_trace', work, at, state, prefix, detail=str(error))
                    continue
                paths_created += max(0, sum(alt.status != 'path_limit' for alt in alternatives)-1)
                for alternative in alternatives:
                    path = prefix + alternative.path
                    for report in alternative.state.reports[len(state.reports):]:
                        report = dict(report)
                        report['path'] = list(prefix + tuple(report['path']))
                        result['reports'].append({'block_pc': hex(work.block_pc), 'seed_pc': hex(work.seed_pc), **report})
                    if alternative.status != 'complete':
                        details = {}
                        if alternative.status == 'path_limit':
                            report = alternative.state.reports[-1]
                            details = {'max_paths': max_paths,
                                       'discarded_alternatives': report['discarded_alternatives']}
                        stop(alternative.status, work, at, alternative.state, path,
                             unsupported_event=alternative.unsupported_event, event_index=alternative.event_index,
                             **details)
                        continue
                    if check_state is not None:
                        decision = check_state(alternative.state, seed_pc=work.seed_pc,
                                               block_pc=work.block_pc, instruction_pc=at, path=path)
                        if decision is not None:
                            stop('state_check', work, at, alternative.state, path, detail=decision)
                            continue
                    following.append((alternative.state, path))
            states = following
            if not states:
                break
        for state, path in states:
            actual = state.registers.get('PC')
            routed = _Work(work.block_pc, work.seed_pc, state, path, work.visited + (work.block_pc,), work.entry)
            if (actual is not None and actual.op != 'bits' and not blocks[work.block_pc]['successors']
                    and instructions[work.block_pc][-1] in returns):
                # A CFG return site leaves the function; its exit is not a dropped path.
                result['exits'].append({'kind': 'function_return', 'block_pc': hex(work.block_pc),
                                        'instruction_pc': hex(instructions[work.block_pc][-1]),
                                        'seed_pc': hex(work.seed_pc), 'target': actual.to_dict(),
                                        'path': list(path), 'state': state.to_dict()})
                continue
            if actual is None or actual.op != 'bits':
                stop('unknown_pc', routed, instructions[work.block_pc][-1], state,
                     stage='block_exit', actual_pc=actual.to_dict() if actual else None)
                continue
            target = actual.value
            call = calls.get(work.block_pc)
            if call is not None and target == call['callee_pc']:
                # The callee summary continues this path at the return site.
                stop('call_boundary', routed, call['call_pc'], state, target_pc=hex(call['return_pc']),
                     callee_pc=hex(target))
                continue
            if target not in blocks[work.block_pc]['successors'] or target not in blocks:
                stop('outside_pc', routed, instructions[work.block_pc][-1], state,
                     actual_pc=hex(target), allowed_successors=[hex(pc) for pc in blocks[work.block_pc]['successors']])
                continue
            projected, index = boundary(target, state, routed, work.block_pc)
            if target in cuts:
                stop('handwritten_cut', routed, instructions[work.block_pc][-1], state,
                     target_pc=hex(target), cut_reasons=sorted(cuts[target]))
                continue
            pending.append(_Work(target, work.seed_pc, projected, path, routed.visited, index))
    if duplicated:
        result['duplicated_joins'] = [hex(pc) for pc in sorted(duplicated)]
        _entry_slots(blocks, boundaries, cuts, duplicated)
    return annotate_reaching_stops(result, function)
