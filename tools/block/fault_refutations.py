"""Retain candidate exception exits as obligations, never as successors."""
from copy import deepcopy
from pathlib import Path
import hashlib
import json
from symbolic_state import parse_trace


def _hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _name(value):
    return value[1:-1] if isinstance(value, str) and value.startswith('|') else value


def selected_events(source, branch_path):
    """Resolve one complete source path without choosing a branch."""
    parsed = parse_trace(source)
    remaining = iter(branch_path)
    records = []
    def visit(events, prefix):
        for index, event in enumerate(events):
            address = prefix + (index,)
            if not isinstance(event, list) or not event:
                raise ValueError('A source event is malformed.')
            if event[0] == 'cases':
                try:
                    chosen = next(remaining)
                except StopIteration as error:
                    raise ValueError('The complete branch path is missing a choice.') from error
                children = event[2:]
                if type(chosen) is not int or not 0 <= chosen < len(children):
                    raise ValueError('The complete branch path has an invalid choice.')
                child = children[chosen]
                if not child or child[0] != 'trace':
                    raise ValueError('A source branch has no trace.')
                visit(child[1:], address + (2 + chosen,))
            else:
                records.append({'raw_path': list(address), 'event': deepcopy(event),
                    'segment_initial': index == 0})
    visit(parsed[1:], ())
    try:
        next(remaining)
    except StopIteration:
        return records
    raise ValueError('The complete branch path contains extra choices.')


def classify_exception_exit(source, branch_path, final_state):
    """Return only a structural candidate. This function proves no refutation."""
    pc = final_state.registers.get('PC')
    if pc is None or pc.op != 'bits' or pc.value != 0:
        return None
    events = selected_events(source, branch_path)
    writes = [row for row in events if row['event'][0] == 'write-reg']
    pc_writes = [row for row in writes if _name(row['event'][1]) == 'PC']
    if not pc_writes:
        return None
    terminal = pc_writes[-1]
    raw = terminal['event'][3]
    if not isinstance(raw, str) or not raw.startswith(('#x', '#b')) or int(raw[2:], 16 if raw.startswith('#x') else 2):
        return None
    roots = {_name(row['event'][1]) for row in writes}
    groups = ({'mcause', 'mepc', 'mtval'}, {'scause', 'sepc', 'stval'})
    if 'cur_privilege' not in roots or not any(group <= roots for group in groups):
        return None
    return {'terminal_pc_event': terminal,
        'exception_writes': [row for row in writes if _name(row['event'][1]) in set.union(*groups) | {'cur_privilege'}],
        'events': events}


def make_fault_obligation(source, alternative, *, source_scope, rocq_trace, incoming_state, resource_origin):
    """Keep raw guards as metadata until their exact Rocq projection is checked."""
    if alternative.status != 'complete':
        return None
    candidate = classify_exception_exit(source, alternative.path, alternative.state)
    if candidate is None:
        return None
    if not isinstance(source_scope, dict) or not source_scope:
        raise ValueError('A fault obligation needs its exact incoming source scope.')
    if not {'path', 'sha256'} <= set(rocq_trace):
        raise ValueError('A fault obligation needs the bound Rocq trace.')
    if not isinstance(resource_origin, dict) or not resource_origin:
        raise ValueError('The original resource source is required.')
    guards = [row for row in candidate['events'] if row['event'][0] in {'assert', 'assume'}]
    typed_hash = _hash({key: value.to_dict() for key, value in incoming_state.registers.items()})
    resource_hash = _hash({'origin': resource_origin, 'incoming_state': incoming_state.to_dict()})
    identity = {'source_scope': source_scope, 'raw_trace_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'branch_path': list(alternative.path), 'terminal_pc_event': candidate['terminal_pc_event'],
        'typed_substitution_hash': typed_hash, 'incoming_resource_context_hash': resource_hash}
    return {'schema': 'source-fault-refutation.v1', 'id': _hash(identity), **identity,
        'status': 'open', 'successor_allowed': False, 'block_open': True,
        'entry_case_id': source_scope.get('entry_case_id'),
        'incoming_source_scope_hash': _hash(source_scope),
        'resource_context': {'origin': deepcopy(resource_origin),
            'incoming_state': incoming_state.to_dict(),
            'projection_status': 'pending',
            'post_exception_state_is_handoff': False},
        'proof': {'status': 'open', 'supporting_components': []},
        'rocq_trace': deepcopy(rocq_trace), 'candidate_basis': 'Exact exception-register writes and terminal zero-PC write.',
        'exception_writes': candidate['exception_writes'], 'raw_guard_metadata': guards,
        'untrusted_valuation_conditions': [condition.to_dict() for condition in alternative.state.conditions],
        'untrusted_exception_reports': deepcopy(alternative.state.reports[len(incoming_state.reports):]),
        'proof_premises_added': [], 'required_rocq_guard_projection': True,
        'required_refutation': 'Refute this exact reachable Rocq path from the original entry resources and immutable entry case.',
        'untrusted_post_exception_state_sha256': _hash(alternative.state.to_dict())}


def record_obligation(report, block_pc, obligation):
    """An unresolved obligation keeps its block open."""
    if (obligation['status'] != 'open' or obligation['successor_allowed'] is not False
            or obligation.get('proof', {}).get('status') != 'open'):
        raise ValueError('Only pending non-successor obligations use this interface.')
    bucket = 'case_refutations' if obligation.get('source_leaf_kind') == 'incompatible_normal_path' else 'fault_refutations'
    report.setdefault(bucket, []).append(deepcopy(obligation))
    status = report.setdefault('block_refutation_status', {}).setdefault(str(block_pc),
        {'status': 'open', 'required': 0, 'discharged': 0})
    status['required'] += 1
    status['status'] = 'open'


class FaultObligationContext:
    """Bind obligations to original resources and one immutable entry case."""
    def __init__(self, *, entry_source, public_seed, source_function, rocq_traces,
                 owned_seeds, entry_case=None):
        self.entry_source = deepcopy(entry_source)
        self.public_seed = deepcopy(public_seed)
        self.source_function = deepcopy(source_function)
        self.rocq_traces = deepcopy(rocq_traces)
        self.owned_seeds = owned_seeds
        self.entry_case = deepcopy(entry_case)
        if entry_case is not None:
            if entry_case.get('source_function') != source_function:
                raise ValueError('The entry case belongs to another source function.')
            if entry_case['entry'] != entry_source or entry_case.get('entry_body_changed') is not False:
                raise ValueError('The case changed its original entry source.')
            if entry_case.get('state_conditions_added') or entry_case.get('branch_filtering_enabled'):
                raise ValueError('Unproved entry-case conditions cannot select a branch.')

    def validate_function(self, function):
        path = Path(self.source_function['path'])
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != self.source_function['sha256']:
            raise ValueError('The bound source function changed.')
        inventory = json.loads(data)
        if function not in inventory.get('functions', []):
            raise ValueError('Fault obligations belong to another source function.')

    def __call__(self, alternative, *, source, incoming_state, seed_pc, block_pc,
                 instruction_pc, prefix):
        if alternative.status != 'complete':
            return None
        if instruction_pc not in self.rocq_traces:
            raise ValueError('The source instruction has no bound Rocq trace.')
        seed = self.owned_seeds[seed_pc]
        case_id = self.entry_case['id'] if self.entry_case else None
        scope = {'entry_case_id': case_id, 'entry': self.entry_source,
            'public_seed': self.public_seed, 'source_function': self.source_function,
            'entry_case_context_hash': _hash(self.entry_case) if self.entry_case is not None else None,
            'seed_pc': hex(seed_pc), 'block_pc': hex(block_pc),
            'originating_instruction_pc': hex(instruction_pc),
            'incoming_path': list(prefix),
            'original_branch_path': list(prefix + alternative.path)}
        origin = {'entry': self.entry_source, 'public_seed': self.public_seed,
            'ownership': deepcopy(seed.ownership),
            'resource_ids': [resource.id for resource in seed.resources],
            'incoming_resource_projection_status': 'pending'}
        return make_fault_obligation(source, alternative, source_scope=scope,
            rocq_trace=self.rocq_traces[instruction_pc], incoming_state=incoming_state,
            resource_origin=origin)
