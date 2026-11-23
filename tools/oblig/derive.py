#!/usr/bin/env python3
"""Turn every generator stop and refusal of one function into a typed request (plan A6).

    derive.py --function F --run RUN [--symbol SYMBOL] [--round N] [--cfg CFG]
              [--inputs DIR --bank DIR | --render DIR]

Each call writes one round, `RUN/round-<n>/` (the next free n unless --round is given), because
`tools/block/render_function.sh` skips a step whose output exists:

  round-<n>/derived/LIVE.json             live registers per block (forward pass, else the CFG)
  round-<n>/derived/FRAME.json            every stack slot read or written: size, first writer
  round-<n>/derived/JOIN-STATEMENTS.json  per join outside a loop cut: the disjunction of its incoming states
  round-<n>/derived/CALLEES.json          each call with the callee's proved_functions.json row
  round-<n>/derived/CONTRACT-SKELETON.v   argument registers, pointer ranges, layouts; meaning open
  round-<n>/derived/REQUESTS.json         one row per open request, plus the refusals no request answers

Round 1 runs no forward pass: it issues every request the control-flow graph alone fixes (the
contract, one loop assertion per loop cut, one premise per callee without a registry row, one call
row per call). A later round compiles the annotation file to the function profile
(`annotations.py compile`), runs `render_function.sh` into `round-<n>/render/` (or reads an
existing run dir given by --render), and adds the requests of its stops and refusals.
A request whose id an annotation row answers (`request`) is not issued again.
No model is called; no proof runs here.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/block'))

from loop_structure import block_successors, dominators, loop_heads as natural_loop_heads  # noqa: E402

CFG = ROOT / 'build/stock-zisk/cfg.json'
REGISTRY = ROOT / 'ZesuSsz/Contracts/proved_functions.json'
FUNCTIONS = ROOT / 'tools/block/functions'
KINDS = ('contract', 'callee_premise', 'loop_assertion', 'join_assertion', 'access_placement', 'call_row',
         'predicate')
CFG_KINDS = ('contract', 'callee_premise', 'loop_assertion', 'call_row')
RAM = ('0xa0000000', '0xc0000000')
# Forward-pass stops that drop no path (boundary_guards.PASSING_STOPS).
PASSING_STOPS = frozenset({'handwritten_cut', 'infeasible', 'call_boundary'})
STOP_KINDS = {'state_check': 'access_placement', 'unsupported': 'access_placement',
              'cycle_without_cut': 'loop_assertion', 'path_limit': 'join_assertion'}
# Stops that no annotation answers: an input of the run is missing or broken.
INPUT_STOPS = frozenset({'missing_trace', 'invalid_trace'})
MEMORY_REPORTS = ('unknown_memory_bound', 'unknown_memory_read', 'ambiguous_memory_alias',
                  'unknown_memory_mapping')

ABI = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6',
       'a7', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
ARGUMENT_REGISTERS = ['x%d' % n for n in range(10, 18)]
CALLER_SAVED = ['x1', 'x5', 'x6', 'x7', *ARGUMENT_REGISTERS, 'x28', 'x29', 'x30', 'x31']
CALLEE_SAVED = ['x2', 'x8', 'x9', *['x%d' % n for n in range(18, 28)]]
R_TYPE = {'add', 'sub', 'and', 'or', 'xor', 'sll', 'srl', 'sra', 'slt', 'sltu', 'addw', 'subw', 'sllw', 'srlw',
          'sraw', 'mul', 'mulh', 'mulhu', 'mulhsu', 'mulw', 'div', 'divu', 'rem', 'remu', 'divw', 'divuw', 'remw',
          'remuw'}
NO_SOURCE = {'lui', 'auipc'}


def register_name(name):
    """`xN` for an ABI or `xN` register name."""
    if re.fullmatch(r'x\d+', name):
        return name
    if name == 'fp':
        return 'x8'
    return 'x%d' % ABI.index(name)


def offset(pc, base):
    return '+' + hex(pc - base)


def case(pc, base):
    return format(pc - base, '04x')


def request_id(function, kind, pc, base):
    return '%s/decision/%s-%s' % (function, kind, case(pc, base))


def load_json(path):
    return json.loads(Path(path).read_text())


def load_cfg_function(cfg, symbol):
    rows = [row for row in load_json(cfg)['functions'] if row['name'] == symbol]
    if len(rows) != 1:
        raise SystemExit('derive: the CFG %s has %d functions named %s' % (cfg, len(rows), symbol))
    return rows[0]


def registry_rows(path=REGISTRY):
    return {row['symbol']: row for row in load_json(path)['functions'] if row.get('symbol')}


def symbol_names():
    from function_profiles import symbol_table
    names = {}
    for name, address in symbol_table().items():
        names.setdefault(address, name)
    return names


# ---------------------------------------------------------------- CFG facts

def cut_heads(function):
    """{loop cut pc: note}: every natural loop head and every target of a CFG backward edge.

    A backward-edge target that dominates no source of its edge is not a natural loop head;
    the generator's `loop_heads` omits it, so its cut needs a hand `loop_heads` row."""
    natural = natural_loop_heads(function)
    heads = {pc: None for pc in natural}
    successors = block_successors(function)
    starts = sorted(successors)
    dom = dominators(successors, int(function['entry']))
    for loop in function.get('loops', []):
        for edge in loop.get('backward_edges', []):
            target, source = int(edge['to'], 0), int(edge['from'], 0)
            if target in heads:
                continue
            block = max(start for start in starts if start <= source)
            heads[target] = ('the backward edge from %s does not make it a natural loop head (it %s its source '
                             'block); tools/block/loop_structure.loop_heads omits it, so the cut needs a hand '
                             '`loop_heads` row' % (offset(source, int(function['entry'])),
                                                   'dominates' if target in dom.get(block, ()) else
                                                   'does not dominate'))
    return dict(sorted(heads.items()))


def predecessors(function):
    result = {int(block['start']): set() for block in function['blocks']}
    for block in function['blocks']:
        for target in block['successors']:
            if int(target) in result:
                result[int(target)].add(int(block['start']))
    return result


def cfg_joins(function, cuts):
    return sorted(pc for pc, rows in predecessors(function).items() if len(rows) > 1 and pc not in cuts)


def calls_of(function):
    return [call for call in function.get('calls', []) if call.get('kind') in ('call', 'tail')]


def callees(function, registry, names):
    base = int(function['entry'])
    rows = []
    for call in calls_of(function):
        target = int(call['target'])
        symbol = names.get(target)
        entry = registry.get(symbol)
        rows.append({'call_site': offset(int(call['pc']), base), 'kind': call['kind'],
                     'callee': symbol, 'callee_pc': (symbol + '+0x0') if symbol else None,
                     'status': entry['status'] if entry else None,
                     'registry': {key: entry[key] for key in ('function', 'status', 'interface', 'call_spec')
                                  if key in entry} if entry else None})
    return rows


def row_uses_defs(row, defined=frozenset()):
    """(uses, defs) of one CFG row. A call reads the argument registers its own block set before
    it (`defined`): the callee's arity is not in the CFG, and a register passed through unchanged
    from the entry is missed. A return reads the result and callee-saved registers."""
    rd = 'x%d' % row['rd'] if row.get('rd') else None
    rs1 = 'x%d' % row['rs1'] if row.get('rs1') else None
    rs2 = 'x%d' % row['rs2'] if row.get('rs2') else None
    kind, mnemonic = row['kind'], row['mnemonic']
    if kind == 'call':
        return {rs1, 'x2', *(set(ARGUMENT_REGISTERS) & set(defined))} - {None}, set(CALLER_SAVED)
    if kind == 'return':
        return {rs1, 'x10', 'x11', *CALLEE_SAVED} - {None}, set()
    if kind in ('store', 'branch'):
        return {rs1, rs2} - {None}, set()
    if kind == 'load':
        return {rs1} - {None}, {rd} - {None}
    if kind == 'jump':
        return ({rs1} - {None} if mnemonic == 'jalr' else set()), {rd} - {None}
    if mnemonic in NO_SOURCE:
        return set(), {rd} - {None}
    return ({rs1, rs2} if mnemonic in R_TYPE else {rs1}) - {None}, {rd} - {None}


def cfg_liveness(function):
    """{block pc: sorted live-in registers}, by backward dataflow over the CFG rows."""
    rows = {int(row['pc']): row for row in function['rows']}
    blocks = {int(block['start']): block for block in function['blocks']}
    summary = {}
    for start, block in blocks.items():
        uses, defs = set(), set()
        for pc in sorted(pc for pc in rows if start <= pc < int(block['end'])):
            used, defined = row_uses_defs(rows[pc], defs)
            uses |= used - defs
            defs |= defined
        summary[start] = (uses, defs)
    live = {start: set() for start in blocks}
    changed = True
    while changed:
        changed = False
        for start in sorted(blocks, reverse=True):
            out = set().union(*(live.get(int(target), set()) for target in blocks[start]['successors']))
            uses, defs = summary[start]
            new = uses | (out - defs)
            if new != live[start]:
                live[start], changed = new, True
    return {start: sorted(registers, key=lambda name: int(name[1:])) for start, registers in live.items()}


def reverse_postorder(function):
    successors = block_successors(function)
    order, seen = [], set()

    def visit(pc):
        seen.add(pc)
        for child in successors.get(pc, []):
            if child not in seen and child in successors:
                visit(child)
        order.append(pc)
    sys.setrecursionlimit(max(10000, sys.getrecursionlimit()))
    visit(int(function['entry']))
    rest = [pc for pc in sorted(successors) if pc not in seen]
    return list(reversed(order)) + rest


def frame_slots(function):
    """Every stack slot the CFG's address analysis names, keyed by its offset from the entry sp."""
    base = int(function['entry'])
    rows = {int(row['pc']): row for row in function['rows']}
    blocks = {int(block['start']): int(block['end']) for block in function['blocks']}
    slots = {}
    for start in reverse_postorder(function):
        for pc in sorted(pc for pc in rows if start <= pc < blocks[start]):
            row = rows[pc]
            analysis = row.get('address_analysis')
            if not (isinstance(analysis, list) and analysis and analysis[0] == 'stack'):
                continue
            slot = slots.setdefault(analysis[1], {'offset': analysis[1], 'size': row.get('width'), 'reads': [],
                                                  'writes': [], 'first_writer': None})
            slot['size'] = max(slot['size'] or 0, row.get('width') or 0)
            if row['kind'] == 'store':
                slot['writes'].append(offset(pc, base))
                slot['first_writer'] = slot['first_writer'] or offset(pc, base)
            else:
                slot['reads'].append(offset(pc, base))
    frame = next((-row['imm'] for row in function['rows'] if row['mnemonic'] == 'addi' and row.get('rd') == 2
                  and row.get('rs1') == 2 and row.get('imm', 0) < 0), 0)
    return {'frame_bytes': frame, 'offset_base': 'entry sp',
            'slots': [slots[key] for key in sorted(slots)]}


# ---------------------------------------------------------------- forward-pass facts

def _expr(value):
    from symbolic_state import Expr
    return Expr.from_dict(value)


def alternative_statement(alternative, live):
    """The Coq conjunction of one incoming state: its path conditions and its live register values."""
    state = alternative['state']
    parts = ['%s = true' % _expr(condition).coq() for condition in state.get('conditions', [])]
    for register in live:
        if register in state.get('registers', {}):
            parts.append('machine_%s = %s' % (register, _expr(state['registers'][register]).coq()))
    return ' /\\ '.join('(' + part + ')' for part in parts) or 'True'


def join_statements(forward, function, cuts, live):
    base = int(function['entry'])
    boundaries = {int(row['pc'], 0): row for row in forward.get('boundaries', [])} if forward else {}
    rows = []
    for pc in cfg_joins(function, cuts):
        registers = live.get(pc, [])
        row = {'pc': offset(pc, base), 'registers': registers, 'alternatives': None, 'statement': None,
               'exact': False}
        boundary = boundaries.get(pc)
        if boundary is not None:
            incoming = [alt for alt in boundary['alternatives'] if alt.get('predecessor_pc') is not None]
            row['alternatives'] = []
            texts = []
            for alternative in incoming:
                item = {'predecessor': offset(int(alternative['predecessor_pc'], 0), base),
                        'seed': offset(int(alternative['seed_pc'], 0), base), 'path': alternative.get('path')}
                try:
                    item['statement'] = alternative_statement(alternative, registers)
                    texts.append(item['statement'])
                except ValueError as error:
                    item['unrenderable'] = str(error)
                row['alternatives'].append(item)
            stops = boundary.get('reaching_stops', [])
            row['reaching_stops'] = len(stops)
            row['exact'] = bool(incoming) and len(texts) == len(incoming) and not stops
            if row['exact']:
                row['statement'] = ' \\/ '.join('(' + text + ')' for text in texts)
        rows.append(row)
    return rows


def placement_proposal(stop, base):
    """The access an unknown read names, as a placement row, when its address is an owned array's
    base plus a symbolic index; else None."""
    from symbolic_state import _addends, operation
    state = stop.get('state') or {}
    addresses = [report['address'] for report in state.get('reports', [])
                 if report.get('kind') in MEMORY_REPORTS and 'address' in report]
    if not addresses:
        return None
    address = _expr(addresses[-1])
    terms, constant = _addends(address)
    found = []
    for region in state.get('memory', []):
        if 'byte_array' not in region:
            continue
        region_base = _expr(region['base'])
        base_terms, base_constant = _addends(region_base)
        rest = list(terms)
        if any(term not in rest or rest.remove(term) for term in base_terms) or not rest:
            continue
        index = rest[0]
        for term in rest[1:]:
            index = operation('bvadd', index, term)
        try:
            found.append({'array': _expr(region['byte_array']).coq(), 'index': index.coq(), 'scale': 1,
                          'offset': (constant - base_constant) % (1 << 64)})
        except ValueError:
            continue
    if len(found) > 1:
        # Several owned arrays share the address's symbolic base (a header below its data): the one the
        # symbolic index starts at, when it is the only one.
        found = [row for row in found if row['offset'] == 0]
    if len(found) != 1:
        return None
    pc = int(stop['instruction_pc'], 0)
    return {'at': {'pc': offset(pc, base), 'boundary': 'access'}, 'binders': [], 'resources': [], 'facts': [],
            'placement': found[0]}


# ---------------------------------------------------------------- requests

def new_request(function_name, kind, pc, base, reason, needs=(), source=None, proposal=None):
    return {'id': request_id(function_name, kind, pc, base), 'kind': kind, 'pc': offset(pc, base),
            'reason': reason, 'needs': list(needs), 'derivable': proposal is not None, 'proposal': proposal,
            'sources': [source] if source else []}


def add(requests, row):
    """Add a request; a second row with the same id adds its sources and count only."""
    existing = requests.get(row['id'])
    if existing is None:
        requests[row['id']] = dict(row, count=1)
        return
    existing['count'] += 1
    existing['sources'].extend(source for source in row['sources'] if source not in existing['sources'])
    if existing['proposal'] is None and row['proposal'] is not None:
        existing['proposal'], existing['derivable'] = row['proposal'], True


def cfg_requests(function, function_name, registry, names):
    """Every request the control-flow graph alone fixes (round 1)."""
    base = int(function['entry'])
    requests = {}
    add(requests, new_request(function_name, 'contract', base, base,
                              'the function has no contract: entry and exit resources, outcome, frame and bound',
                              needs=['CONTRACT-SKELETON.v'], source='cfg:entry'))
    for pc, note in cut_heads(function).items():
        add(requests, new_request(function_name, 'loop_assertion', pc, base,
                                  'loop cut: the forward pass needs the assertion that holds at every visit',
                                  needs=[note] if note else [], source='cfg:loop_head'))
    premised = set()
    for call in calls_of(function):
        pc, target = int(call['pc']), int(call['target'])
        symbol = names.get(target)
        entry = registry.get(symbol)
        needs = ['callee %s: %s' % (symbol, 'registry row %s (%s)' % (entry['function'], entry['status'])
                                    if entry else 'no registry row')]
        if entry and entry.get('interface'):
            needs.append('interface %s' % entry['interface'])
        add(requests, new_request(function_name, 'call_row', pc, base,
                                  'call design row: spec, arrays and return facts of the call at %s'
                                  % offset(pc, base), needs=needs, source='cfg:call'))
        if entry is None and target not in premised:
            premised.add(target)
            add(requests, new_request(function_name, 'callee_premise', pc, base,
                                      'callee %s has no row in proved_functions.json' % symbol,
                                      needs=['call spec in the form of memcpyCallPremise'], source='cfg:call'))
    return requests


FIRST_STOP = re.compile(r'the first is (\w+) in block (0x[0-9a-f]+) at (0x[0-9a-f]+|None)')


def classify_stop(reason):
    return STOP_KINDS.get(reason, 'predicate')


def render_requests(run, function, function_name, cuts, statements):
    """(requests, refusals without a request) from one render_function.sh run dir."""
    base = int(function['entry'])
    end = int(function['end'])
    joins = {int(row['pc'], 0) + base: row for row in statements}
    preds = predecessors(function)
    requests, unhandled = {}, []
    forward_path = run / 'forward/FORWARD.json'
    forward = load_json(forward_path) if forward_path.exists() else None

    def join_request(pc, reason, source):
        row = joins.get(pc)
        proposal = None
        if row is not None and row['exact']:
            proposal = {'at': {'pc': offset(pc, base), 'boundary': 'join'},
                        'binders': [{'name': 'machine_' + register, 'register': register}
                                    for register in row['registers']],
                        'resources': [], 'facts': [{'coq': row['statement'], 'role': 'fact'}]}
        add(requests, new_request(function_name, 'join_assertion', pc, base, reason,
                                  needs=[] if proposal else ['the join statement of its incoming states'],
                                  source=source, proposal=proposal))

    def stop_request(reason, pc, block, detail, source, stop=None):
        if reason in INPUT_STOPS:
            unhandled.append({'source': source, 'reason': reason, 'pc': offset(pc, base), 'detail': detail})
            return
        kind = classify_stop(reason)
        if kind in ('join_assertion', 'loop_assertion') and block is not None:
            pc = block
        proposal = placement_proposal(stop, base) if kind == 'access_placement' and stop else None
        if kind == 'join_assertion':
            join_request(pc, 'forward stop %s: %s' % (reason, detail), source)
            return
        add(requests, new_request(function_name, kind, pc, base, 'forward stop %s: %s' % (reason, detail),
                                  source=source, proposal=proposal))

    if forward is not None:
        for stop in forward.get('stops', []):
            reason = stop['reason']
            if reason in PASSING_STOPS:
                continue
            actual = stop.get('actual_pc')
            if reason in ('intermediate_pc_mismatch', 'outside_pc') and isinstance(actual, str) \
                    and not base <= int(actual, 0) < end:
                continue   # a fault arm leaves the function (boundary_guards.leaves_function)
            at = stop.get('instruction_pc') or stop['block_pc']
            detail = stop.get('unsupported_event') or stop.get('detail') or ''
            if isinstance(detail, dict):
                reports = detail.get('reports') or []
                detail = '; '.join(str(row.get('detail', row.get('kind'))) for row in reports[:2]) or \
                    str(detail.get('status', ''))
            stop_request(reason, int(at, 0), int(stop['block_pc'], 0), str(detail)[:400],
                         'forward/FORWARD.json#stops', stop)
    joins_path = run / 'forward/JOINS.json'
    if joins_path.exists():
        for site, reason in load_json(joins_path).get('refusals', {}).items():
            pc = int(site, 0)
            source = 'forward/JOINS.json#refusals/' + site
            if reason.startswith('call boundary refused:'):
                add(requests, new_request(function_name, 'call_row', pc - 4, base, reason, source=source))
            elif reason.startswith('tail call refused:') or reason.startswith('a tail call'):
                add(requests, new_request(function_name, 'call_row', pc, base, reason, source=source))
            elif reason.startswith('loop head seed refused'):
                add(requests, new_request(function_name, 'loop_assertion', pc, base, reason, source=source))
            elif reason in ('no path reaches the call', 'no incoming edge', 'no path reaches the tail call'):
                unhandled.append({'source': source, 'reason': reason, 'pc': offset(pc, base)})
            elif reason.startswith('incomplete call block'):
                continue   # the stop that makes it incomplete is its own request
            else:
                join_request(pc, reason, source)
    designs_path = run / 'forward/LOOP-DESIGNS.json'
    if designs_path.exists():
        for head, reason in load_json(designs_path).get('refusals', {}).items():
            add(requests, new_request(function_name, 'loop_assertion', int(head, 0), base,
                                      'loop design inference refused: ' + reason,
                                      source='forward/LOOP-DESIGNS.json#refusals/' + head))
    result_path = run / 'render/RESULT.json'
    if not result_path.exists():
        log = run / 'render.log'
        unhandled.append({'source': 'render/RESULT.json', 'reason': 'no render result',
                          'detail': log.read_text()[-600:] if log.exists() else None})
        return requests, unhandled
    for row in load_json(result_path).get('cases', []):
        status = row.get('status', '')
        if not status.startswith('refused_'):
            continue
        source = 'render/RESULT.json#' + str(row.get('pc'))
        detail = '; '.join(str(report.get('detail')) for report in row.get('reports', []))[:600]
        pc = int(row['pc'], 0) if str(row.get('pc', '')).startswith('0x') else None
        if pc is None:
            # A function-return or tail package: its design row answers it.
            unhandled.append({'source': source, 'reason': status, 'detail': detail})
            continue
        if status == 'refused_incomplete_boundary':
            if pc in cuts:
                add(requests, new_request(function_name, 'loop_assertion', pc, base,
                                          'incomplete loop-head boundary: ' + detail, source=source))
            elif len(preds.get(pc, ())) > 1:
                join_request(pc, 'incomplete join boundary: ' + detail, source)
            else:
                first = FIRST_STOP.search(detail)
                if first is None:
                    unhandled.append({'source': source, 'reason': status, 'pc': offset(pc, base), 'detail': detail})
                    continue
                at = first[3] if first[3] != 'None' else first[2]
                stop_request(first[1], int(at, 0), int(first[2], 0), detail, source)
        elif status == 'refused_mixed_roots':
            join_request(pc, 'edges from different roots: ' + detail, source)
        elif status == 'refused_no_loop_head_row':
            add(requests, new_request(function_name, 'loop_assertion', pc, base,
                                      'no loop-head row: ' + detail, source=source))
        else:
            # refused_no_alternatives, refused_boundary and others: no annotation answers them.
            unhandled.append({'source': source, 'reason': status, 'pc': offset(pc, base), 'detail': detail})
    return requests, unhandled


# ---------------------------------------------------------------- answers already given

def annotation_path(function_name):
    return FUNCTIONS / (function_name + '.annotations.json')


def answered_ids(function_name, profile, function, registry, names):
    """Request ids that an annotation row or the hand profile already answers."""
    base = int(function['entry'])
    answered = set()
    path = annotation_path(function_name)
    if path.exists():
        answered.update(row['request'] for row in load_json(path).get('rows', []) if row.get('request'))
    if profile is not None:
        def pc_of(text):
            """The pc of a `+0xOFFSET` key of the function itself; None for another symbol's key."""
            return base + int(text[1:], 16) if text.startswith('+0x') else None
        for design in profile.get('loop_designs', []):
            at = pc_of(design['head'])
            if at is not None:
                answered.add(request_id(function_name, 'loop_assertion', at, base))
        for call in profile.get('calls', []):
            at = pc_of(call['call_site_pc'])
            if at is not None:
                answered.add(request_id(function_name, 'call_row', at, base))
        if profile.get('domain_component'):
            answered.add(request_id(function_name, 'contract', base, base))
    for call in calls_of(function):
        if names.get(int(call['target'])) in registry:
            answered.add(request_id(function_name, 'callee_premise', int(call['pc']), base))
    return answered


# ---------------------------------------------------------------- contract skeleton

def hint_parameters(hints, base):
    """[(name, register, type)] of the function's own parameters (hint pack LOCATIONS.json) at its entry:
    a parameter in a register, or one passed by reference at [register + 0] (its type gains a `*`)."""
    path = hints / 'LOCATIONS.json'
    if not path.exists():
        return None
    rows = []
    for variable in load_json(path).get('variables', []):
        if variable.get('kind') != 'param' or len(variable.get('scope', [])) != 1:
            continue
        register, kind = None, variable.get('type')
        for item in variable.get('ranges', []):
            location = item.get('location') or {}
            if int(str(item.get('start', '+0x1')).lstrip('+'), 16) != 0:
                continue
            if location.get('kind') == 'register':
                register = register_name(location['register'])
            elif location.get('kind') == 'memory' and location.get('offset') == 0 and location.get('base'):
                register, kind = register_name(location['base']), '*' + (kind or '?')
        rows.append((variable['name'], register, kind))
    return rows


def type_key(name, table):
    """The TYPES.json key of a type name, stripping pointer and array prefixes until one matches."""
    while name:
        if name in table:
            return name
        stripped = re.sub(r'^(\*|\[\d*\]|const )', '', name)
        if stripped == name:
            return None
        name = stripped
    return None


def layout_lines(hints, types):
    path = hints / 'TYPES.json'
    if not path.exists():
        return []
    table = load_json(path).get('types', {})
    lines, seen = [], set()
    pending = list(types)
    while pending:
        name = type_key(pending.pop(0) or '', table)
        if name is None or name in seen:
            continue
        seen.add(name)
        row = table[name]
        lines.append('   %s (%s, %s bytes)' % (name, row.get('kind'), row.get('byte_size')))
        for member in row.get('members', []):
            lines.append('     +%s %s : %s (%s bytes)' % (member.get('offset'), member.get('name'),
                                                       member.get('type'), member.get('size')))
            pending.append(member.get('type'))
    return lines


def pointer_registers(function, live_in):
    """Argument registers that a load or store of the entry block uses as its base before redefining it."""
    rows = sorted(function['rows'], key=lambda row: int(row['pc']))
    entry = next(block for block in function['blocks'] if int(block['start']) == int(function['entry']))
    defined, pointers = set(), set()
    for row in rows:
        if not int(entry['start']) <= int(row['pc']) < int(entry['end']):
            continue
        if row['kind'] in ('load', 'store') and row.get('rs1'):
            base = 'x%d' % row['rs1']
            if base in live_in and base not in defined:
                pointers.add(base)
        _, defs = row_uses_defs(row)
        defined |= defs
    return pointers


def contract_skeleton(function, function_name, live, hints):
    base = int(function['entry'])
    name = function_name[0].upper() + function_name[1:]
    live_in = [register for register in live.get(base, []) if register in ARGUMENT_REGISTERS]
    parameters = hint_parameters(hints, base) if hints is not None else None
    pointers = pointer_registers(function, live_in)
    fields = []
    for register in live_in:
        hint = next((row for row in parameters or [] if row[1] == register), None)
        pointer = register in pointers or bool(hint and hint[2] and hint[2][:1] in '*[')
        fields.append((register, hint[0] if hint else None, hint[2] if hint else None, pointer))
    lines = ['(* Contract skeleton of %s: input for the contract decision (plan A6), not a statement.' % function['name'],
             '   Generated by tools/oblig/derive.py from the CFG%s. The meaning is left open. *)'
             % (' and the hint pack' if parameters is not None else ' (no hint pack in the run dir)'),
             'From Coq Require Import ZArith.',
             'Local Open Scope Z_scope.', '']
    lines.append('(* Argument registers live at the entry, with the hint pack\'s parameter and type:')
    for register, variable, kind, pointer in fields:
        lines.append('   %s %s%s%s' % (register, variable or '-', ' : ' + kind if kind else '',
                                     ' (pointer: read through)' if pointer else ''))
    lines.append('   Frame: %d bytes. *)' % frame_slots(function)['frame_bytes'])
    layouts = layout_lines(hints, [kind for _, _, kind, _ in fields if kind]) if hints is not None else []
    if layouts:
        lines += ['(* Structure layouts (offset member : type):', *layouts, '*)']
    lines += ['', 'Record %sArgs := {' % name]
    lines += ['  %sArg_%s : Z;' % (function_name, variable or register)
              for register, variable, _, _ in fields]
    lines += ['}.', '']
    ranges = ['(%s <= %sArg_%s args < %s)' % (RAM[0], function_name, variable or register, RAM[1])
              for register, variable, _, pointer in fields if pointer]
    ranges += ['(0 <= %sArg_%s args < 2 ^ 64)' % (function_name, variable or register)
               for register, variable, _, pointer in fields if not pointer]
    lines.append('Definition %sArgumentRanges (args : %sArgs) : Prop :=' % (function_name, name))
    lines.append('  ' + (' /\\\n  '.join(ranges) if ranges else 'True') + '.')
    return '\n'.join(lines) + '\n'


# ---------------------------------------------------------------- driver

def next_round(run):
    taken = [int(path.name.split('-')[1]) for path in run.glob('round-*') if path.name.split('-')[1].isdigit()]
    return max(taken, default=0) + 1


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_profile_data(function_name):
    path = FUNCTIONS / (function_name + '.json')
    return load_json(path) if path.exists() else None


def run_render(function_name, inputs, bank, render, log):
    path = annotation_path(function_name)
    if path.exists():
        subprocess.run([sys.executable, str(Path(__file__).with_name('annotations.py')), 'compile',
                        '--function', function_name], check=True)
    with open(log, 'w') as stream:
        result = subprocess.run(['bash', str(ROOT / 'tools/block/render_function.sh'), function_name, str(inputs),
                                 str(render), str(bank)], cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    return result.returncode


def derive(function_name, run, *, symbol=None, round_number=None, cfg=CFG, inputs=None, bank=None, render=None,
           registry_path=REGISTRY, names=None):
    run = Path(run)
    profile = load_profile_data(function_name)
    annotations = load_json(annotation_path(function_name)) if annotation_path(function_name).exists() else None
    symbol = symbol or (profile or {}).get('symbol') or (annotations or {}).get('symbol')
    if not symbol:
        raise SystemExit('derive: no symbol for %s (no profile, no annotation file; pass --symbol)' % function_name)
    function = load_cfg_function(cfg, symbol)
    base = int(function['entry'])
    registry = registry_rows(registry_path)
    names = symbol_names() if names is None else names
    round_number = round_number or next_round(run)
    directory = run / ('round-%d' % round_number)
    derived = directory / 'derived'
    derived.mkdir(parents=True, exist_ok=False)
    render_status = None
    if render is None and round_number > 1 and inputs is not None and bank is not None:
        render = directory / 'render'
        render_status = run_render(function_name, inputs, bank, render, directory / 'render.log')
    cuts = cut_heads(function)
    forward = load_json(Path(render) / 'forward/FORWARD.json') \
        if render is not None and (Path(render) / 'forward/FORWARD.json').exists() else None
    if forward is not None and forward.get('liveness'):
        live = {int(pc, 0): registers for pc, registers in forward['liveness'].items()}
        live_source = 'forward/FORWARD.json#liveness'
    else:
        live, live_source = cfg_liveness(function), 'cfg'
    statements = join_statements(forward, function, cuts, live)
    requests = cfg_requests(function, function_name, registry, names)
    unhandled = []
    if render is not None:
        found, unhandled = render_requests(Path(render), function, function_name, cuts, statements)
        for row in found.values():
            for _ in range(row.pop('count')):
                add(requests, dict(row, sources=list(row['sources'])))
    answered = answered_ids(function_name, profile, function, registry, names)
    open_rows = [row for key, row in sorted(requests.items()) if key not in answered]
    hints = run / 'hints'
    common = {'function': function_name, 'symbol': symbol, 'round': round_number,
              'cfg': {'path': str(Path(cfg).resolve().relative_to(ROOT)) if Path(cfg).resolve().is_relative_to(ROOT)
                      else str(cfg), 'sha256': sha256(cfg)}}
    files = {
        'LIVE.json': {**common, 'source': live_source,
                      'live_in': {offset(pc, base): registers for pc, registers in sorted(live.items())}},
        'FRAME.json': {**common, **frame_slots(function)},
        'JOIN-STATEMENTS.json': {**common, 'source': 'forward/FORWARD.json' if forward else None, 'joins': statements},
        'CALLEES.json': {**common, 'calls': callees(function, registry, names)},
        'REQUESTS.json': {**common, 'schema': 'oblig-requests/1', 'render': str(render) if render else None,
                          'render_exit': render_status,
                          'counts': {kind: sum(row['kind'] == kind for row in open_rows) for kind in KINDS},
                          'answered': sorted(answered & set(requests)),
                          'requests': open_rows, 'refusals_without_request': unhandled},
    }
    for name, data in files.items():
        (derived / name).write_text(json.dumps(data, indent=1, ensure_ascii=False) + '\n')
    (derived / 'CONTRACT-SKELETON.v').write_text(
        contract_skeleton(function, function_name, live, hints if hints.is_dir() else None))
    return files['REQUESTS.json']


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--function', required=True, help='region name (tools/block/functions/<F>.json)')
    parser.add_argument('--run', required=True, type=Path, help='run dir, e.g. _build/agents/aa/<F>')
    parser.add_argument('--symbol', help='ELF symbol, when neither a profile nor an annotation file names it')
    parser.add_argument('--round', type=int, dest='round_number')
    parser.add_argument('--cfg', type=Path, default=CFG)
    parser.add_argument('--inputs', type=Path, help='render inputs (render_function.sh INPUTS)')
    parser.add_argument('--bank', type=Path, help='kept bench bank (render_function.sh BANK)')
    parser.add_argument('--render', type=Path, help='derive from an existing render_function.sh run dir')
    options = parser.parse_args()
    if (options.inputs is None) != (options.bank is None):
        parser.error('--inputs and --bank go together')
    result = derive(options.function, options.run, symbol=options.symbol, round_number=options.round_number,
                    cfg=options.cfg, inputs=options.inputs, bank=options.bank, render=options.render)
    print(json.dumps({'round': result['round'], 'counts': result['counts'],
                      'refusals_without_request': len(result['refusals_without_request'])}))


if __name__ == '__main__':
    main()
