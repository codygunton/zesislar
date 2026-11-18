#!/usr/bin/env python3
"""Propagate untrusted symbolic states through straight-line CFG blocks.

Only caller-supplied entry states and handwritten cut seeds start execution.
Incoming states never cross a join or loop head. The pass never generalizes them.
"""
from collections import deque
from dataclasses import dataclass
import re

try:
    from .symbolic_state import SymbolicState, evaluate_trace, parse_trace
except ImportError:
    from symbolic_state import SymbolicState, evaluate_trace, parse_trace


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
        uses.update(expression_reads(args) - written)
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


@dataclass
class _Work:
    block_pc: int
    seed_pc: int
    state: SymbolicState
    path: tuple = ()
    visited: tuple = ()


def evaluate_function(function, traces, initial_states, *, max_paths=4096, check_state=None):
    """Return a complete boundary inventory and explicit propagation stops.

    max_paths bounds the total leaf alternatives created during this traversal.
    Infeasible and stopped alternatives count toward the same explicit budget.
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
    cuts = {}
    for pc in blocks:
        reasons = set()
        if pc in loop_heads:
            reasons.add('loop_head')
        if len(predecessors[pc]) > 1:
            reasons.add('join')
        if reasons:
            cuts[pc] = reasons
    seeds = {_pc(pc): state for pc, state in initial_states.items()}
    if len(seeds) != len(initial_states) or any(pc != entry and pc not in cuts for pc in seeds):
        raise ValueError('An initial state must belong to the function entry or a handwritten cut')
    if any(not isinstance(state, SymbolicState) for state in seeds.values()):
        raise ValueError('Every initial state must be an explicit SymbolicState')
    traces = {_pc(pc): source for pc, source in traces.items()}
    live = _liveness(blocks, instructions, traces, seeds)
    boundaries = {pc: {'pc': hex(pc), 'status': 'handwritten_cut' if pc in cuts else 'unreachable',
                       'alternatives': []} for pc in blocks}
    result = {'schema': 'block-forward-states.v1',
              'function': {'name': function['name'], 'entry': hex(entry), 'end': hex(end)},
              'boundaries': list(boundaries.values()),
              'cuts': [{'pc': hex(pc), 'reason': reason} for pc, reasons in sorted(cuts.items())
                       for reason in sorted(reasons)], 'stops': [], 'reports': []}
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
                                              'path': list(work.path)})
        if pc not in cuts:
            boundaries[pc]['status'] = 'generated'
        return projected

    for pc, state in sorted(seeds.items()):
        work = _Work(pc, pc, state.copy())
        if paths_created == max_paths:
            stop('path_limit', work, state=state, max_paths=max_paths, discarded_alternatives=1)
            continue
        paths_created += 1
        work.state = boundary(pc, state, work, None)
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
            routed = _Work(work.block_pc, work.seed_pc, state, path, work.visited + (work.block_pc,))
            if actual is None or actual.op != 'bits':
                stop('unknown_pc', routed, instructions[work.block_pc][-1], state,
                     stage='block_exit', actual_pc=actual.to_dict() if actual else None)
                continue
            target = actual.value
            if target not in blocks[work.block_pc]['successors'] or target not in blocks:
                stop('outside_pc', routed, instructions[work.block_pc][-1], state,
                     actual_pc=hex(target), allowed_successors=[hex(pc) for pc in blocks[work.block_pc]['successors']])
                continue
            projected = boundary(target, state, routed, work.block_pc)
            if target in cuts:
                stop('handwritten_cut', routed, instructions[work.block_pc][-1], state,
                     target_pc=hex(target), cut_reasons=sorted(cuts[target]))
                continue
            pending.append(_Work(target, work.seed_pc, projected, path, routed.visited))
    return result
