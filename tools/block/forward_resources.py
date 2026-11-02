#!/usr/bin/env python3
"""Preserve source ownership and account for every symbolic memory write.

Ownership comes only from input resources. Address bounds never create ownership.
The source adapter must establish fractions and permissions before stores proceed.
"""
from dataclasses import dataclass, field
import hashlib
import json
from pathlib import Path
import re

try:
    from .entry_seed import _code_mask
    from .symbolic_state import Expr, MemoryWrite, _offset, bits, operation
except ImportError:
    from entry_seed import _code_mask
    from symbolic_state import Expr, MemoryWrite, _offset, bits, operation


def _strip_enclosure(text):
    text = text.strip()
    if text.endswith('%I'):
        text = text[:-2].rstrip()
    while text.startswith('(') and text.endswith(')'):
        mask, depth, enclosing = _code_mask(text), 0, True
        for index, char in enumerate(mask):
            if char == '(':
                depth += 1
            elif char == ')':
                depth -= 1
                if depth == 0 and index != len(mask)-1:
                    enclosing = False
                    break
        if not enclosing:
            break
        text = text[1:-1].strip()
    return text


def _top_positions(text, token):
    mask, depth = _code_mask(text), 0
    array_stars = {match.end()-1 for match in re.finditer(r'↦ₘ(?:\{[^}]*\})?∗', mask)}
    for index, char in enumerate(mask):
        if char in '([{⌜':
            depth += 1
        elif char in ')]}⌝':
            depth -= 1
        elif char == token and depth == 0 and index not in array_stars:
            yield index


def parse_source_ownership(body, *, provenance):
    """Retain the exact source vocabulary without guessing hidden resources.

    Fractions stay as source text. This parser assigns no write permissions.
    Leading existential declarations remain in their original order.
    """
    body = _code_mask(body, mask_strings=False).strip()
    body = _strip_enclosure(body)
    prefixes = []
    while body.startswith('∃'):
        comma = next(_top_positions(body, ','), None)
        if comma is None:
            raise ValueError('The existential declaration has no body')
        prefixes.append(body[:comma+1])
        body = _strip_enclosure(body[comma+1:])
    positions = [-1, *_top_positions(body, '∗'), len(body)]
    components = []
    for index, (left, right) in enumerate(zip(positions, positions[1:])):
        source = body[left+1:right].strip()
        if not source:
            raise ValueError('The source contains an empty resource')
        record = {'id': f'resource_{index}', 'source': source, 'provenance': dict(provenance)}
        classified = _strip_enclosure(source)
        arrows = list(_top_positions(classified, '↦'))
        memory = re.fullmatch(r'(?P<address>.*?)\s*↦ₘ(?P<fraction>\{[^}]*\})?(?P<operator>∗|\?)\s*(?P<value>.+)', classified, re.S) if len(arrows) == 1 else None
        register = re.fullmatch(r'"(?P<name>[^"\n]+)"\s*↦ᵣ(?P<fraction>\{[^}]*\})?\s*(?P<value>.+)', classified, re.S) if len(arrows) == 1 else None
        if memory:
            record.update(kind='byte_array' if memory['operator'] == '∗' else 'unknown_byte_array',
                          address_z=memory['address'].strip(), fraction=memory['fraction'],
                          writable=None)
            record['value' if memory['operator'] == '∗' else 'length'] = memory['value'].strip()
        elif register:
            record.update(kind='register', name=register['name'], value=register['value'].strip(),
                          fraction=register['fraction'])
        else:
            record.update(kind='opaque')
        components.append(record)
    return {'schema': 'source-ownership.v1', 'existential_prefixes': prefixes,
            'components': components, 'provenance': dict(provenance)}


def ownership_from_assertion_tree(tree, *, provenance):
    """Preserve an explicit public seed's separation and existential scopes."""
    components, binders = [], []
    def visit(node, path=(), scope=()):
        kind = node['kind']
        if kind == 'sep':
            return {'kind': 'sep', 'left': visit(node['left'], path+(0,), scope),
                    'right': visit(node['right'], path+(1,), scope)}
        if kind == 'exists':
            local = list(node['binders'])
            for binder in local:
                binders.append({**binder, 'scope': list(path)})
            children = [visit(child, path+(index,), scope+(path,))
                        for index, child in enumerate(node['components'])]
            return {'kind': 'exists', 'binders': local, 'scope': list(path),
                    'body': {'kind': 'sep_list', 'children': children}}
        resource_id = node['id']
        if kind == 'register':
            if 'original_component' in node:
                source = node['original_component']
            else:
                fraction = '{' + node['fraction_coq'] + '}' if 'fraction_coq' in node else ''
                source = f'"{node["register"]}" ↦ᵣ{fraction} RVal_Bits ({node["value_coq"]})'
        elif kind in ('byte_array', 'uninitialized_memory'):
            source = node['original_component']
        elif kind == 'pure':
            source = '⌜' + node['coq'] + '⌝'
        else:
            source = node['coq']
        parsed = parse_source_ownership(source, provenance={**provenance, 'ast_path': list(path)})
        if len(parsed['components']) != 1 or parsed['existential_prefixes']:
            raise ValueError('A public seed component has an unsupported nested scope')
        component = parsed['components'][0]
        component.update(id=resource_id, scope=[list(item) for item in scope], seed_component=node)
        components.append(component)
        return {'kind': 'component', 'id': resource_id}
    preserved = visit(tree)
    if len({component['id'] for component in components}) != len(components):
        raise ValueError('The public seed repeats an ownership ID')
    return {'schema': 'source-ownership.v1', 'existential_prefixes': [], 'tree': preserved,
            'binders': binders, 'components': components, 'provenance': dict(provenance)}


def _render_tree(tree, sources):
    if tree['kind'] == 'component':
        return sources[tree['id']]
    if tree['kind'] == 'sep':
        return '(' + _render_tree(tree['left'], sources) + ' ∗ ' + _render_tree(tree['right'], sources) + ')'
    if tree['kind'] == 'sep_list':
        return '(' + ' ∗ '.join(_render_tree(child, sources) for child in tree['children']) + ')'
    if tree['kind'] == 'exists':
        binders = ' '.join(f'({binder["name"]} : {binder["type"]})' for binder in tree['binders'])
        return '(∃ ' + binders + ', ' + _render_tree(tree['body'], sources) + ')'
    raise ValueError('The assertion tree kind is unsupported')


def _scoped_coq(expr, aliases):
    if expr.op == 'unknown_input' and expr in aliases:
        return aliases[expr]
    def replace(term):
        if term in aliases:
            return Expr('input', width=term.width, value=aliases[term])
        return Expr(term.op, tuple(replace(arg) for arg in term.args), term.width, term.value)
    return replace(expr).coq()


@dataclass(frozen=True)
class OwnedBytes:
    id: str
    base: Expr
    address_z: str
    byte_array: Expr | None
    length: Expr | int
    writable: bool | None
    fraction: str | None
    component: dict
    provenance: dict
    element_bits: int | None = None

    def to_dict(self):
        return {'id': self.id, 'base': self.base.to_dict(), 'address_z': self.address_z,
                'byte_array': self.byte_array.to_dict() if self.byte_array is not None else None,
                'length': self.length.to_dict() if isinstance(self.length, Expr) else self.length,
                'writable': self.writable, 'fraction': self.fraction,
                'component': self.component, 'provenance': self.provenance,
                'element_bits': self.element_bits}


def _contains(expr, needle):
    return expr == needle or any(_contains(arg, needle) for arg in expr.args)


class _Facts:
    def __init__(self, conditions, facts):
        self.conditions, self.explicit, self.substitutions = [], list(facts), {}
        def collect(condition):
            if condition.op == 'and':
                for child in condition.args:
                    collect(child)
            else:
                self.conditions.append(condition)
        for condition in conditions:
            collect(condition)
        for condition in self.conditions:
            if condition.op == '=' and len(condition.args) == 2:
                left, right = condition.args
                if left.op not in ('input', 'unknown_input'):
                    left, right = right, left
                if left.op in ('input', 'unknown_input') and left != right and not _contains(right, left):
                    self.substitutions[left] = right
        for fact in self.explicit:
            if not isinstance(fact, dict) or not fact.get('origin') or not fact.get('fact_id'):
                raise ValueError('An ownership fact must include source provenance')
            if fact.get('status') not in ('supplied', 'derived-by-pass', 'required-unavailable'):
                raise ValueError('The ownership fact status is unsupported')
            if fact.get('kind') not in ('address_equality', 'bounds', 'nonwrap', 'disjoint_ranges', 'permission', 'element_lookup'):
                raise ValueError('The ownership fact kind is unsupported')
            if not isinstance(fact.get('terms'), dict):
                raise ValueError('An ownership fact needs typed terms')

    def available(self, kind):
        return [fact for fact in self.explicit if fact['kind'] == kind and fact['status'] != 'required-unavailable']

    def canonical(self, expr, seen=frozenset()):
        if expr in seen:
            return expr
        if expr in self.substitutions:
            return self.canonical(self.substitutions[expr], seen | {expr})
        if not expr.args:
            return expr
        return operation(expr.op, *(self.canonical(arg, seen | {expr}) for arg in expr.args),
                         width=expr.width, value=expr.value)

    def offset(self, address, base):
        for fact in self.available('address_equality'):
            terms = fact['terms']
            if not {'address', 'base', 'index'}.issubset(terms):
                continue
            if terms['address'] == address and terms['base'] == base:
                offset = terms['index']
                if isinstance(offset, bool) or not isinstance(offset, int) or offset < 0:
                    raise ValueError('A relative offset must be a nonnegative integer')
                return offset, {'kind': 'source_fact', 'fact_id': fact['fact_id'], 'origin': fact['origin']}
        offset = _offset(self.canonical(address), self.canonical(base))
        if offset is not None:
            return offset, {'kind': 'affine_identity',
                            'conditions': [condition.to_dict() for condition in self.conditions if condition.op == '=']}
        return None, None

    def lower_bound(self, resource):
        length = resource.length
        if isinstance(length, int):
            return length, {'kind': 'source_length', 'resource_id': resource.id}
        length = self.canonical(length)
        if length.op == 'bits':
            return length.value, {'kind': 'constant_length'}
        lower, evidence = 0, None
        views = {length}
        for fact in self.available('bounds'):
            if fact['terms'].get('resource_id') == resource.id and 'length_view' in fact['terms']:
                views.add(self.canonical(Expr.from_dict(fact['terms']['length_view'])))
        for fact in self.available('bounds'):
            terms = fact['terms']
            if not {'resource_id', 'index', 'count'}.issubset(terms):
                continue
            minimum = terms['index'] + terms['count']
            if terms['resource_id'] == resource.id and minimum > lower:
                lower, evidence = minimum, {'kind': 'source_fact', 'fact_id': fact['fact_id'], 'origin': fact['origin']}
        for condition in self.conditions:
            if condition.op == 'not' and condition.args[0].op == '=':
                left, right = map(self.canonical, condition.args[0].args)
                if (left in views and right.op == 'bits' and right.value == 0) or (right in views and left.op == 'bits' and left.value == 0):
                    if lower < 1:
                        lower, evidence = 1, {'kind': 'path_condition', 'condition': condition.to_dict()}
                continue
            if condition.op not in ('bvule', 'bvult', 'bvuge', 'bvugt', 'bvsle', 'bvslt', 'bvsge', 'bvsgt'):
                continue
            left, right = map(self.canonical, condition.args)
            if condition.op.endswith(('le', 'lt')):
                left, right = right, left
            if left not in views or right.op != 'bits':
                continue
            if condition.op.startswith('bvs') and right.value >= 1 << (right.width-1):
                continue
            minimum = right.value + int(condition.op.endswith(('lt', 'gt')))
            if minimum > lower:
                lower, evidence = minimum, {'kind': 'path_condition', 'condition': condition.to_dict()}
        return lower, evidence

    def disjoint(self, first, second):
        return any({fact['terms']['left'], fact['terms']['right']} == {first, second}
                   for fact in self.available('disjoint_ranges'))

    def nonwrap(self, resource):
        for fact in self.available('nonwrap'):
            if fact['terms']['resource_id'] == resource.id:
                return {'kind': 'source_fact', 'fact_id': fact['fact_id'], 'origin': fact['origin']}
        if resource.base.op == 'bits' and isinstance(resource.length, int):
            if 0 <= resource.base.value and resource.base.value+resource.length <= 1 << resource.base.width:
                return {'kind': 'constant_nonwrap'}
        return None

    def permission(self, resource):
        # A Boolean flag and mapped=true cannot establish write permission.
        if resource.writable is not True or resource.fraction is None:
            return None
        if re.fullmatch(r'DfracOwn\s+(?:1(?:%Qp)?|\(1(?:%Qp)?\))', _strip_enclosure(resource.fraction)) is None:
            return None
        for fact in self.available('permission'):
            if fact['terms'].get('resource_id') == resource.id and fact['terms'].get('fraction') == resource.fraction:
                return {'kind': 'source_fact', 'fact_id': fact['fact_id'], 'origin': fact['origin']}
        return None


@dataclass
class ResourceResult:
    resources: list
    writes: list
    status: str = 'complete'
    processed_writes: int = 0
    updates: dict = field(default_factory=dict)
    reports: list = field(default_factory=list)
    transitions: list = field(default_factory=list)

    def to_dict(self):
        return {'schema': 'owned-write-images.v1', 'status': self.status,
                'block_status': 'completed' if self.status == 'complete' else 'stopped',
                'resources': [{**resource.to_dict(), 'status': 'updated' if self.updates[resource.id] else 'preserved'}
                              for resource in self.resources],
                'writes': [write.to_dict() for write in self.writes],
                'processed_writes': self.processed_writes,
                'updates': {key: [{'offset': offset, **record} for offset, record in sorted(updates.items())]
                            for key, updates in self.updates.items()}, 'reports': self.reports,
                'transitions': self.transitions,
                'processed_prefix': {'write_count': self.processed_writes, 'transitions': self.transitions},
                'blocked_event': {'write': self.writes[self.processed_writes].to_dict(),
                                  'report': self.reports[-1]} if self.status != 'complete' else None}


def apply_owned_writes(resources, writes, *, conditions=(), facts=(), endianness='little'):
    """Merge stores into inherited ownership. Retain stopped and pending stores.

    The caller must bind endianness to the pinned state convention.
    This version accepts only the pinned little-endian convention.
    """
    resources, writes = list(resources), list(writes)
    if endianness != 'little':
        raise ValueError('The ownership layer requires the pinned little-endian convention')
    if len({resource.id for resource in resources}) != len(resources):
        raise ValueError('The ownership records repeat a resource ID')
    if any(not isinstance(write, MemoryWrite) for write in writes):
        raise ValueError('Every write must be a symbolic MemoryWrite')
    result = ResourceResult(resources, writes, updates={resource.id: {} for resource in resources})
    known = _Facts(conditions, facts)

    def halt(reason, index, write, **details):
        result.status = 'stopped'
        result.reports.append({'kind': reason, 'write_index': index,
                               'address': write.address.to_dict(), **details})
        return result

    for index, write in enumerate(writes):
        candidates, relations = [], []
        for resource in resources:
            offset, relation = known.offset(write.address, resource.base)
            relations.append((resource, offset))
            if offset is not None:
                bound, evidence = known.lower_bound(resource)
                if offset+write.size <= bound:
                    candidates.append((resource, offset, relation, evidence))
        if not candidates:
            return halt('unknown_write_owner' if all(offset is None for _, offset in relations)
                        else 'unknown_write_bounds', index, write)
        if len(candidates) != 1:
            return halt('ambiguous_write_owner', index, write,
                        resource_ids=[resource.id for resource, *_ in candidates])
        owner, offset, relation, bound = candidates[0]
        for other, other_offset in relations:
            if other.id == owner.id or known.disjoint(owner.id, other.id):
                continue
            # A lower bound cannot establish that a second resource ends here.
            exact_length = other.length if isinstance(other.length, int) else None
            if isinstance(other.length, Expr) and other.length.op == 'bits':
                exact_length = other.length.value
            reverse, _ = known.offset(other.base, write.address)
            if other_offset is None or exact_length is None or other_offset < exact_length or (reverse is not None and reverse < write.size):
                return halt('ambiguous_write_alias', index, write, resource_ids=[owner.id, other.id])
        if owner.writable is not True:
            return halt('write_permission_denied' if owner.writable is False else 'unknown_write_permission',
                        index, write, resource_id=owner.id, fraction=owner.fraction)
        permission = known.permission(owner)
        if permission is None:
            return halt('unknown_write_permission', index, write, resource_id=owner.id, fraction=owner.fraction)
        nonwrap = known.nonwrap(owner)
        if nonwrap is None:
            return halt('unknown_write_nonwrap', index, write, resource_id=owner.id)
        if owner.element_bits != 8:
            return halt('unknown_byte_element_type', index, write, resource_id=owner.id)
        if write.size not in (1, 2, 4, 8):
            return halt('unsupported_write_size', index, write)
        if write.value.width != write.size*8:
            return halt('write_width_mismatch', index, write)
        for byte in range(write.size):
            value = operation('extract', write.value, width=8, value=byte*8)
            result.updates[owner.id][offset+byte] = {'value': value.to_dict(), 'write_index': index,
                                                   'offset_justification': relation,
                                                   'bound_justification': bound}
        result.transitions.append({'write_index': index, 'resource_id': owner.id, 'offset': offset,
                                   'offset_justification': relation, 'bound_justification': bound,
                                   'nonwrap_justification': nonwrap, 'permission_justification': permission})
        result.processed_writes += 1
    return result


def load_resource_vocabulary(path, expected_sha256):
    """Read source rules. Never read their capture-membership attachments."""
    data = Path(path).read_bytes()
    if hashlib.sha256(data).hexdigest() != expected_sha256:
        raise ValueError('The resource vocabulary hash differs from the frozen boundary')
    packet = json.loads(data)
    checked = {}
    for row in packet.get('rows', []):
        for binding in row.get('source_bindings', []):
            source = binding['path']
            if source not in checked:
                checked[source] = hashlib.sha256(Path(source).read_bytes()).hexdigest()
            if checked[source] != binding['sha256']:
                raise ValueError('The resource helper source changed: ' + source)
    return {'input_sha256': expected_sha256, 'source_vocabulary': packet['source_vocabulary'],
            'source_bindings': checked,
            'rows': [{key: value for key, value in row.items() if key != 'capture_membership'}
                     for row in packet['rows']]}


def _complete_cell_image(resource, image, transitions, aliases, vocabulary):
    """Use the bound two-word row only for the exact final full-cell image."""
    rows = [row for row in vocabulary.get('rows', []) if row.get('kind') == 'two_word_stack_frame']
    if not rows:
        return None
    if len(rows) != 1:
        raise ValueError('The memory vocabulary repeats its two-word row')
    row = rows[0]
    if not row.get('source_bindings') or row.get('helper', {}).get('arguments') != [
            'a : Z', 'low : bv 64', 'high : bv 64']:
        raise ValueError('The two-word memory row has an unsupported source interface')
    length = resource.length.value if isinstance(resource.length, Expr) and resource.length.op == 'bits' else resource.length
    if type(length) is not int or set(image) != set(range(length)):
        return None
    # Transitions retain source order. The final image selects the last write.
    cells = []
    cursor = 0
    while cursor < length:
        choices = [(write, offset) for write, offset in transitions
                   if offset == cursor and write.value.width == 64 and write.size * 8 == write.value.width
                   and offset + write.size <= length
                   and all(image[offset + byte]['value'] == operation('extract', write.value,
                           width=8, value=byte*8).to_dict() for byte in range(write.size))]
        if not choices:
            return None
        write, offset = choices[-1]
        cells.append(write)
        cursor += write.size
    if len(cells) != 2 or cells[0].size != cells[1].size:
        return None
    chunks = [f'(bv_to_little_endian (Z.of_nat {write.size}%nat) 8%N '
              f'(bv_unsigned {_scoped_coq(write.value, aliases)}))' for write in cells]
    return '(' + ' ++ '.join(chunks) + ')'


def _memory_source(resource, image, transitions, aliases, vocabulary):
    """Use the existing whole-array splice and uninitialized-span vocabulary."""
    if not image:
        return resource.component['source']
    fraction = resource.fraction
    if not fraction:
        raise ValueError('The resource has no inherited memory fraction')
    if resource.byte_array is not None:
        value = _scoped_coq(resource.byte_array, aliases)
        for write, offset in transitions:
            stored = _scoped_coq(write.value, aliases)
            value = (f'(Coq.Init.Datatypes.app (take {offset}%nat {value}) '
                     f'(Coq.Init.Datatypes.app (bv_to_little_endian (Z.of_nat {write.size}%nat) 8%N '
                     f'(bv_unsigned ({stored} : bv {write.value.width}%N))) '
                     f'(drop (Nat.add {offset}%nat {write.size}%nat) {value})))')
        return f'({resource.address_z}) ↦ₘ{{{fraction}}}∗ ({value})'
    complete = _complete_cell_image(resource, image, transitions, aliases, vocabulary)
    if complete is not None:
        return f'({resource.address_z}) ↦ₘ{{{fraction}}}∗ {complete}'
    # An uninitialized span has no old byte values. Render only written bytes.
    positions, parts, cursor = sorted(image), [], 0
    runs = []
    for position in positions:
        if not runs or position != runs[-1][-1]+1:
            runs.append([])
        runs[-1].append(position)
    for run in runs:
        start = run[0]
        if cursor < start:
            address = resource.address_z if cursor == 0 else f'Z.add ({resource.address_z}) {cursor}%Z'
            parts.append(f'({address}) ↦ₘ{{{fraction}}}? {start-cursor}%Z')
        address = resource.address_z if start == 0 else f'Z.add ({resource.address_z}) {start}%Z'
        values = '(@Coq.Init.Datatypes.nil (bv 8%N))'
        for position in reversed(run):
            value = _scoped_coq(Expr.from_dict(image[position]['value']), aliases)
            values = f'(Coq.Init.Datatypes.cons ({value} : bv 8%N) {values})'
        parts.append(f'({address}) ↦ₘ{{{fraction}}}∗ ({values})')
        cursor = run[-1]+1
    length = resource.length.value if isinstance(resource.length, Expr) and resource.length.op == 'bits' else resource.length
    if isinstance(length, int):
        if cursor < length:
            parts.append(f'(Z.add ({resource.address_z}) {cursor}%Z) ↦ₘ{{{fraction}}}? {length-cursor}%Z')
    else:
        original = resource.component.get('length')
        if not isinstance(original, str):
            raise ValueError('The uninitialized span has no original length term')
        parts.append(f'(Z.add ({resource.address_z}) {cursor}%Z) ↦ₘ{{{fraction}}}? '
                     f'(Z.sub ({original}) {cursor}%Z)')
    return '(' + ' ∗ '.join(parts) + ')'


def render_resource_boundary(ownership, result, final_state, *, retained_registers=None, vocabulary):
    """Render source ownership only after the complete ordered write set succeeds.

    retained_registers must contain actual final values before liveness projection.
    A missing projected value stops rendering. Original seed values cannot fill it.
    """
    output = {'schema': 'resource-boundary.v1', 'block_status': 'stopped', 'components': [],
              'reports': list(result.reports), 'write_accounting': result.to_dict(),
              'vocabulary_sha256': vocabulary['input_sha256']}
    if result.status != 'complete' or result.processed_writes != len(result.writes):
        return output
    resources = {resource.id: resource for resource in result.resources}
    registers = dict(final_state.retained_registers)
    registers.update(retained_registers or {})
    registers.update(final_state.registers)
    rendered, seen = [], set()
    for component in ownership['components']:
        resource_id = component['id']
        aliases = {Expr.from_dict(binder['expression']): binder['name'] for binder in ownership.get('binders', [])
                   if 'expression' in binder and binder['scope'] in component.get('scope', [])}
        try:
            if component['kind'] in ('byte_array', 'unknown_byte_array'):
                if resource_id not in resources:
                    raise ValueError('The source memory resource has no ownership record')
                resource = resources[resource_id]
                transitions = [(result.writes[step['write_index']], step['offset'])
                               for step in result.transitions if step['resource_id'] == resource_id]
                source = _memory_source(resource, result.updates[resource_id], transitions, aliases, vocabulary)
                seen.add(resource_id)
            elif component['kind'] == 'register':
                name = component['name']
                if name not in registers:
                    raise ValueError('The owned register has no retained final value: ' + name)
                value = registers[name]
                if not component['value'].startswith('RVal_Bits ') or value.width is None:
                    raise ValueError('The owned register value shape is unsupported: ' + name)
                fraction = component.get('fraction') or ''
                source = f'"{name}" ↦ᵣ{fraction} RVal_Bits ({_scoped_coq(value, aliases)} : bv {value.width}%N)'
            else:
                source = component['source']
            rendered.append({'id': resource_id, 'source': source, 'provenance': component['provenance']})
        except (ValueError, KeyError) as error:
            output['reports'].append({'kind': 'resource_render_stop', 'resource_id': resource_id, 'detail': str(error)})
            return output
    if seen != set(resources):
        output['reports'].append({'kind': 'resource_render_stop', 'detail': 'An ownership ID has no original source component'})
        return output
    output.update(block_status='completed', components=rendered,
                  existential_prefixes=ownership['existential_prefixes'],
                  path_conditions=[condition.to_dict() for condition in final_state.conditions],
                  imports=vocabulary['source_vocabulary']['imports'])
    if 'tree' in ownership:
        output['tree'] = ownership['tree']
        output['body'] = _render_tree(ownership['tree'], {record['id']: record['source'] for record in rendered})
        output['body_kind'] = 'resource_assertion'
    return output
