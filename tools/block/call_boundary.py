"""Continue the forward pass across a call from the callee's machine_call spec.

A call ends its block, and every path that reaches it stops there as a
`call_boundary` stop. call_return_seed merges those call-site states and
applies the callee summary to make the seed of the return site:

* general registers: machine_call_ret returns x2, x8, x9 and x18-x27
  unchanged; every other general register returns an arbitrary word, which
  becomes a fresh binder;
* system registers: exact shapes return unchanged; a mask or bits shape
  returns a fresh value (with its mask fact);
* memory: an array that the spec returns under its own pre binder is the
  caller's resource unchanged; an array that it returns under a post binder
  replaces the caller's bytes at that argument with a fresh owned array; the
  callee frame comes back uninitialized;
* pure facts: the spec's pre-fact (which the caller proves at the call) and
  its post-fact, under one existential for each pre binder that no caller
  resource fixes.

The callee summary comes from the spec's source text. The call design row
names the spec, binds each spec array to its argument and the caller value
of an array that the callee keeps, and states the output length with its
source. Generic code names no address. No proof runs.
"""
from dataclasses import replace
from pathlib import Path
import hashlib
import json
import re

from entry_seed import definition_body
from forward_resources import _strip_enclosure, _top_positions, apply_owned_writes, render_resource_boundary
from forward_resource_design import _state_from_result
from resource_seed import seed_owned_resources
from source_domain import substitute
from symbolic_state import Expr, _offset, bits, input_expr, operation

PRESERVED = ['x2', 'x8', 'x9'] + ['x%d' % number for number in range(18, 28)]
ARGUMENTS = ['x%d' % number for number in range(10, 18)]
GPR = re.compile(r'x(?:[0-9]|[12][0-9]|3[01])\Z')
PREFIX = 'call_'


class CallRefused(ValueError):
    """The call-return seed cannot be built from these inputs."""


def _split(text, token):
    positions = [-1, *_top_positions(text, token), len(text)]
    return [text[left + 1:right].strip() for left, right in zip(positions, positions[1:])]


def _binders(prefix):
    """Parse `∃ (a b : T) (c : U),` or `∃ a : T,` into ordered (name, type) pairs."""
    text = prefix.strip()[1:].rstrip(',').strip()
    groups = re.findall(r'\(([^():]+):([^()]+)\)', text) if text.startswith('(') else [tuple(text.split(':', 1))]
    return [(name, kind.strip()) for names, kind in groups for name in names.split()]


def parse_machine_call_spec(source, name):
    """Read the callee summary from `machine_call MAP STACK (fun argv sp RET => ...)`."""
    body = _strip_enclosure(re.sub(r'%I\s*$', '', definition_body(source, name).strip()))
    body = _strip_enclosure(re.sub(r'%I\s*$', '', body))
    match = re.match(r'machine_call\s+(\S+)\s+(\S+)\s+', body)
    if match is None:
        raise CallRefused('The callee spec is not a machine_call: ' + name)
    lam = _strip_enclosure(body[match.end():])
    head = re.match(r'fun\s+(\w+)\s+(\w+)\s+(\w+)\s*=>\s*', lam)
    if head is None:
        raise CallRefused('The machine_call body is not fun argv sp RET => ...')
    argv, sp, ret = head.groups()

    def assertion(text):
        text = _strip_enclosure(text.strip())
        binders = []
        while text.startswith('∃'):
            comma = next(_top_positions(text, ','))
            binders += _binders(text[:comma + 1])
            text = _strip_enclosure(text[comma + 1:])
        return binders, _split(text, '∗')

    pre_binders, pre = assertion(lam[head.end():])
    if not pre[-1].startswith(ret + ' '):
        raise CallRefused('The machine_call body does not end in its return continuation.')
    post_lam = _strip_enclosure(pre[-1][len(ret):])
    post_head = re.match(r'fun\s+_\s*=>\s*', post_lam)
    if post_head is None:
        raise CallRefused('The return continuation does not ignore the returned registers.')
    post_binders, post = assertion(post_lam[post_head.end():])
    if post[-1] != 'True':
        raise CallRefused('The return assertion does not end in True.')
    names = {'argv': argv, 'sp': sp}

    def classify(parts):
        rows = {'registers': [], 'collections': [], 'arrays': [], 'facts': []}
        for part in parts:
            array = re.fullmatch(r'bv_unsigned\s+\(' + argv + r'\s+!!!\s+(\d+)%nat\)\s+↦ₘ∗\s+(\w+)', part)
            register = re.fullmatch(r'"(\w+)"\s+↦ᵣ\s+RVal_Bits\s+(\w+)', part)
            if array:
                rows['arrays'].append({'argument': int(array[1]), 'binder': array[2]})
            elif register:
                rows['registers'].append({'register': register[1], 'binder': register[2]})
            elif part.startswith('reg_col'):
                rows['collections'].append(part)
            elif part.startswith('⌜') and part.endswith('⌝'):
                rows['facts'].append(part[1:-1].strip())
            elif part != 'True' and not part.startswith(ret + ' '):
                raise CallRefused('The callee spec has an unsupported resource: ' + part)
        return rows

    return {'map': match[1], 'stack': match[2], 'names': names, 'pre_binders': pre_binders,
            'post_binders': post_binders, 'pre': classify(pre), 'post': classify(post)}


def _groups(text, start):
    """Yield (begin, end) of top-level argument tokens from start: a paren group or a word."""
    position = start
    while position < len(text):
        while position < len(text) and text[position].isspace():
            position += 1
        if position >= len(text) or text[position] in ')]':
            return
        if text[position] in '([':
            depth, begin = 0, position
            while True:
                depth += text[position] in '(['
                depth -= text[position] in ')]'
                position += 1
                if depth == 0:
                    break
            yield begin, position
        else:
            match = re.match(r"[\w'.!%]+", text[position:])
            if not match:
                return
            yield position, position + match.end()
            position += match.end()


def _local_definitions(source, names):
    """Return {name: (parameters, body)} for spec-file definitions the facts use."""
    result = {}
    for name in names:
        match = re.search(r'\bDefinition\s+' + re.escape(name) + r'\b', source)
        if match is None:
            continue
        header = source[match.end():source.index(':=', match.end())]
        parameters = []
        for begin, end in _groups(header, 0):
            group = header[begin:end]
            if not group.startswith('('):
                break
            names_part = group[1:-1].split(':', 1)[0]
            parameters += names_part.split()
        body = definition_body(source, name).strip()
        result[name] = (parameters, body)
    return result


def _unfold(fact, definitions):
    """Replace each application of a spec-local definition by its instantiated body."""
    for name, (parameters, body) in definitions.items():
        while True:
            match = re.search(r'(?<![\w.])' + re.escape(name) + r'\b', fact)
            if match is None:
                break
            arguments = list(_groups(fact, match.end()))[:len(parameters)]
            if len(arguments) != len(parameters):
                raise CallRefused('A spec-local definition is not fully applied: ' + name)
            values = {parameter: fact[begin:end] for parameter, (begin, end) in zip(parameters, arguments)}
            fact = fact[:match.start()] + '(' + substitute(body, values) + ')' + fact[arguments[-1][1]:]
    return fact


RETURN_WORD = re.compile(r'\{word:([A-Za-z_][A-Za-z0-9_]*):([0-9]+)\}')


def _return_fact(text, fresh):
    """A design return fact with `{word:BINDER:OFFSET}` rendered as the 64-bit little-endian
    load of the callee's output array BINDER at byte OFFSET, in the forward pass's form, so
    the fact names the same terms as the caller's loads."""
    def word(match):
        array = input_expr(fresh[match.group(1)], None)
        chunks = [Expr('array_byte', (array,), 8, int(match.group(2)) + index) for index in range(8)]
        result = chunks[-1]
        for chunk in reversed(chunks[:-1]):
            result = operation('concat', result, chunk)
        return _coq(result)
    return RETURN_WORD.sub(word, text)


def _word_chunks(image, key, start, end):
    """Render a fully written span as the caller's stores, in decodeItem's frame form:
    `bv_to_little_endian (Z.of_nat n) 8 (bv_unsigned v) ++ ...`, so a later load of a
    stored word reads the word back. Return None unless the stores tile the span."""
    stores = [(image.writes[step['write_index']], step['offset']) for step in image.transitions
              if step['resource_id'] == key]
    chunks, cursor = [], start
    while cursor < end:
        choices = [(write, offset) for write, offset in stores if offset == cursor
                   and offset + write.size <= end and write.size * 8 == write.value.width
                   and all(image.updates[key][offset + byte]['value'] ==
                           operation('extract', write.value, width=8, value=8 * byte).to_dict()
                           for byte in range(write.size))]
        if not choices:
            return None
        write, offset = choices[-1]
        chunks.append('(bv_to_little_endian (Z.of_nat %d%%nat) 8%%N (bv_unsigned (%s : bv %d%%N)))'
                      % (write.size, _coq(write.value), write.value.width))
        cursor += write.size
    return '(' + ' ++ '.join(chunks) + ')'


def _merge_call_sites(edges):
    """One call-site state: equal values stay; a register that differs becomes a binder."""
    states = [_state_from_result(edge['state']) for edge in edges]
    first = states[0]
    if any([write.to_dict() for write in state.writes] != [write.to_dict() for write in first.writes]
           for state in states[1:]):
        raise CallRefused('The call-site paths hold different memory writes.')
    for state in states:
        # Liveness projection keeps dead values only as retained registers.
        state.registers = {**state.retained_registers, **state.registers}
    merged = first.copy()
    widened = []
    for key, value in first.registers.items():
        if any(state.registers.get(key) != value for state in states[1:]):
            if not GPR.fullmatch(key):
                raise CallRefused('The call-site paths hold different system state: ' + key)
            merged.registers[key] = input_expr(PREFIX + 'site_' + key, value.width)
            widened.append(key)
    merged.conditions = [condition for condition in first.conditions
                         if all(condition in state.conditions for state in states[1:])]
    return merged, widened


def _coq(value):
    return value.coq()


def _inputs(value):
    own = [str(value.value)] if value.op == 'input' else []
    return own + [name for child in value.args for name in _inputs(child)]


def _atoms(text):
    return set(re.findall(r"(?<![\w'.])[A-Za-z_][\w']*", re.sub(r'"[^"]*"', '', text)))


def call_return_seed(edges, *, call, function_root, root_seed, shapes, vocabulary, constants=None):
    """Return the OwnedSeed of a call's return site and a report of what it carries."""
    if not edges:
        raise CallRefused('No path reaches the call site.')
    source_path = Path(function_root) / call['spec_source']
    spec_text = source_path.read_text()
    spec = parse_machine_call_spec(spec_text, call['spec'])
    state, widened = _merge_call_sites(edges)
    return_pc = int(call['return_site_pc'], 0)
    ownership = root_seed.ownership
    image = apply_owned_writes(root_seed.resources, state.writes, conditions=state.conditions,
                               facts=root_seed.facts, endianness=state.endianness)
    if image.status != 'complete':
        raise CallRefused('The call-site writes have no complete owned image.')
    resources = {resource.id: resource for resource in image.resources}
    values = {'sp': state.registers['x2'],
              'argv': ['(' + _coq(state.registers[name]) + ')' for name in ARGUMENTS]}

    # Spec arrays: the caller resource at each argument.
    design = {row['binder']: row for row in call['arrays']}
    pre_arrays = {row['binder']: row for row in spec['pre']['arrays']}
    post_arrays = {row['binder']: row for row in spec['post']['arrays']}
    if set(design) != set(pre_arrays):
        raise CallRefused('The call design binds other arrays than the spec: ' + ', '.join(sorted(design)))
    instantiation, splits, kept = {}, {}, set()
    for binder, row in pre_arrays.items():
        argument = row['argument']
        if design[binder]['argument'] != argument:
            raise CallRefused('The call design moves the spec array ' + binder)
        address = state.registers[ARGUMENTS[argument]]
        returned = [post for post in post_arrays.values() if post['argument'] == argument]
        if len(returned) != 1:
            raise CallRefused('The spec does not return its array at argument ' + str(argument))
        if returned[0]['binder'] == binder:
            # The callee keeps these bytes: the design names the caller value.
            instantiation[binder] = design[binder]['caller_value']
            owner = [resource for resource in resources.values()
                     if resource.byte_array is not None and resource.byte_array.value == design[binder]['caller_value']]
            if len(owner) != 1 or image.updates[owner[0].id]:
                raise CallRefused('The kept array has no unchanged caller resource: ' + binder)
            kept.add(owner[0].id)
            continue
        # The callee replaces these bytes: find the caller resource by offset.
        found = [(resource, _offset(address, resource.base)) for resource in resources.values()]
        found = [(resource, offset) for resource, offset in found if offset is not None
                 and 0 <= offset and isinstance(resource.length, int)
                 and offset + design[binder]['length'] <= resource.length]
        if len(found) != 1:
            raise CallRefused('The replaced array has no unique caller resource: ' + binder)
        resource, offset = found[0]
        splits[resource.id] = {'offset': offset, 'length': design[binder]['length'],
                               'pre': binder, 'post': returned[0]['binder']}
        instantiation[binder] = None  # an existential of the carried facts
    # The callee frame: (sp - STACK) ↦ₘ? STACK, returned uninitialized.
    stack = constants.get(spec['stack'], {}).get('value') if constants else None
    stack = stack if stack is not None else call['stack_bytes']
    frame_address = operation('bvsub', state.registers['x2'], bits(stack, 64))
    frames = [resource for resource in resources.values()
              if _offset(frame_address, resource.base) == 0 and resource.byte_array is None
              and resource.length == stack]
    if len(frames) != 1:
        raise CallRefused('The caller owns no uninitialized callee frame of ' + str(stack) + ' bytes.')
    callee_frame = frames[0].id

    # Registers the spec keeps (zisk_input_end): their binder is the caller value.
    for row in spec['pre']['registers']:
        if row not in spec['post']['registers']:
            raise CallRefused('The spec does not return its register ' + row['register'])
        instantiation[row['binder']] = '(' + _coq(state.registers[row['register']]) + ')'
    post_binder_names = [name for name, _ in spec['post_binders']]
    fresh = {name: PREFIX + name for name in post_binder_names}

    # The seed's general registers.
    registers, binders = {}, []
    for component in ownership['components']:
        if component['kind'] != 'register':
            continue
        name = component['name']
        if name in PRESERVED:
            registers[name] = state.registers[name]
        else:
            registers[name] = input_expr(PREFIX + name, 64)
            binders.append({'name': PREFIX + name, 'type': 'bv 64',
                            'expression': input_expr(PREFIX + name, 64).to_dict()})
    # System registers: a mask or bits shape comes back as a new value. It keeps
    # the seed's scoped symbol, so every call-site fact on the old value is dropped
    # and only the shape's mask fact is stated again.
    system_conditions, renewed = [], set()
    for row in shapes['rows']:
        if row['shape'] == 'exact':
            continue
        symbol = Expr.from_dict(row['symbol'])
        registers[row['key']] = symbol
        renewed.add(symbol.value)
        if row['shape'] == 'mask':
            system_conditions.append(operation('=', operation('bvand', symbol, Expr.from_dict(row['mask'])),
                                               Expr.from_dict(row['expected'])))
    state.conditions = [condition for condition in state.conditions if not renewed & set(_inputs(condition))]

    # The carried facts.
    def instantiate(fact, outer):
        mapping = {spec['names']['argv']: '[' + '; '.join(values['argv']) + ']',
                   spec['names']['sp']: '(' + _coq(values['sp']) + ')'}
        mapping.update({name: value for name, value in instantiation.items() if value is not None})
        mapping.update({name: value for name, value in fresh.items()})
        mapping.update(outer)
        return substitute(fact, mapping)
    existential = [(name, kind) for name, kind in spec['pre_binders'] if instantiation.get(name, '') is None]
    # A definition of the spec file is unfolded: the entry cannot import the spec module.
    raw = spec['pre']['facts'] + spec['post']['facts']
    local = _local_definitions(spec_text, sorted(_atoms(' '.join(raw)) - {call['spec']}))
    facts = [instantiate(_unfold(fact, local), {}) for fact in raw]
    # A call argument that nothing else in the seed mentions (an entry witness, or
    # a call-site register that the paths disagree on) is closed inside the facts.
    elsewhere = set(_atoms(' '.join(_coq(value) for key, value in registers.items() if GPR.fullmatch(key))))
    candidates = {binder['name']: binder['type'] for binder in ownership['binders']}
    candidates.update({PREFIX + 'site_' + key: 'bv 64' for key in widened})
    inner = [(name, kind) for name, kind in candidates.items()
             if name in _atoms(' '.join(facts)) and name not in elsewhere]
    existential = inner + existential
    telescope = ' '.join('(%s : %s)' % (name, kind) for name, kind in existential)
    carried = '∃ ' + telescope + ', ' + ' /\\ '.join('(' + fact + ')' for fact in facts) if existential \
        else ' /\\ '.join('(' + fact + ')' for fact in facts)

    # The seed's ownership tree.
    rendered = render_resource_boundary(ownership, image, state, vocabulary=vocabulary)
    if rendered['block_status'] != 'completed':
        raise CallRefused('The call-site state does not render.')
    current = {row['id']: row['source'] for row in rendered['components']}
    nodes, regions, extra_facts = [], {}, []
    for component in ownership['components']:
        key, kind = component['id'], component['kind']
        node = dict(component['seed_component'])
        if kind == 'register':
            node.update(original_component='"%s" ↦ᵣ RVal_Bits %s' % (component['name'], _coq(registers[component['name']])),
                        value_coq=_coq(registers[component['name']]))
            node.pop('symbolic_witness', None)
            if registers[component['name']].op == 'input' and registers[component['name']].value.startswith(PREFIX):
                node['symbolic_witness'] = registers[component['name']].value
        elif key == callee_frame:
            pass
        elif key in splits:
            resource, split = resources[key], splits[key]
            pieces = [(0, split['offset']), (split['offset'], split['offset'] + split['length']),
                      (split['offset'] + split['length'], resource.length)]
            updates = image.updates[key]
            for index, (start, end) in enumerate(pieces):
                if start == end:
                    continue
                piece_id = key if index == 0 else key + ('_call_output' if index == 1 else '_call_after')
                address = '(' + resource.address_z + ' + ' + str(start) + ')' if start else resource.address_z
                written = [offset for offset in range(start, end) if offset in updates]
                if index == 1:
                    value = fresh[split['post']]
                    nodes.append({'kind': 'byte_array', 'id': piece_id, 'original_component':
                                  '%s ↦ₘ∗ %s' % (address, value), 'address_z': address,
                                  'byte_array_expr': input_expr(value, None).to_dict(), 'element_bits': 8,
                                  # The rendered length fact fixes this length.
                                  'length_original_coq': str(split['length'])})
                    extra_facts.append({'resource_id': piece_id, 'count': split['length'],
                                        'coq': '(List.length %s = %d)%%nat' % (value, split['length'])})
                elif not written:
                    nodes.append({'kind': 'uninitialized_memory', 'id': piece_id, 'original_component':
                                  '%s ↦ₘ? %d' % (address, end - start), 'address_z': address,
                                  'length_original_coq': str(end - start)})
                elif len(written) == end - start:
                    known = tuple(Expr.from_dict(updates[offset]['value']) for offset in range(start, end))
                    value = _word_chunks(image, key, start, end) or \
                        '[' + '; '.join(_coq(byte) for byte in known) + ']'
                    nodes.append({'kind': 'byte_array', 'id': piece_id, 'original_component':
                                  '%s ↦ₘ∗ %s' % (address, value), 'address_z': address,
                                  'byte_array_expr': input_expr(value, None).to_dict(), 'element_bits': 8,
                                  'length_original_coq': str(end - start)})
                    regions[piece_id] = known
                else:
                    raise CallRefused('A caller span next to the callee output is partly written: ' + key)
            continue
        elif kind in ('byte_array', 'unknown_byte_array') and image.updates[key]:
            raise CallRefused('A caller array that the callee does not name holds a write: ' + key)
        nodes.append(node)
    terminal = next(index for index, node in enumerate(nodes) if node.get('coq') == 'True')
    nodes[terminal:terminal] = [
        {'kind': 'opaque', 'id': row['resource_id'] + '_length', 'coq': '⌜' + row['coq'] + '⌝'}
        for row in extra_facts] + [{'kind': 'opaque', 'id': 'call_facts', 'coq': '⌜' + carried + '⌝'}] + [
        {'kind': 'opaque', 'id': 'call_return_fact_%d' % index, 'coq': '⌜' + _return_fact(row['coq'], fresh) + '⌝'}
        for index, row in enumerate(call.get('return_facts', []))]
    post_types = dict(spec['post_binders'])
    for split in splits.values():
        binders.append({'name': fresh[split['post']], 'type': post_types[split['post']],
                        'expression': input_expr(fresh[split['post']], None).to_dict()})
    # Root binders that the seed still mentions (entry witnesses passed as arguments).
    text = ' '.join([node.get('original_component', node.get('coq', '')) for node in nodes
                     if node.get('id') != 'call_facts']
                    + [name for value in registers.values() for name in _inputs(value)]
                    + [name for condition in state.conditions for name in _inputs(condition)])
    names = {binder['name'] for binder in binders}
    for binder in ownership['binders']:
        if binder['name'] in _atoms(text) and binder['name'] not in names:
            binders.append({key: value for key, value in binder.items() if key != 'scope'})
            names.add(binder['name'])
    for key in widened:
        name = PREFIX + 'site_' + key
        if name in _atoms(text) and name not in names:
            binders.append({'name': name, 'type': 'bv 64', 'expression': input_expr(name, 64).to_dict()})

    tree = {'kind': 'exists', 'binders': binders, 'components': nodes}
    public = {'schema': 'h1-public-entry-seed.v1', 'function': call.get('function'),
              'entry_pc': hex(return_pc), 'assertion_tree': tree,
              'source_bindings': [{'path': str(source_path),
                                   'sha256': hashlib.sha256(source_path.read_bytes()).hexdigest()}]}
    public['_input_sha256'] = hashlib.sha256(json.dumps(public, sort_keys=True).encode()).hexdigest()
    # Facts: copy root facts; a split resource's facts hold for each of its pieces.
    copied = []
    for fact in root_seed.facts:
        terms = fact.get('terms', {})
        ids = {terms.get('left'), terms.get('right'), terms.get('resource_id')} - {None}
        if fact['kind'] in ('permission', 'nonwrap') or fact['fact_id'].endswith(':separation'):
            continue
        copied.append(fact)
        for key in ids & set(splits):
            for piece in (key + '_call_output', key + '_call_after'):
                clone = json.loads(json.dumps(fact))
                for field in ('left', 'right', 'resource_id'):
                    if clone['terms'].get(field) == key:
                        clone['terms'][field] = piece
                clone['fact_id'] += ':' + piece
                copied.append(clone)
    for row in extra_facts:
        copied.append({'fact_id': row['resource_id'] + ':length', 'kind': 'bounds', 'status': 'supplied',
                       'terms': {'resource_id': row['resource_id'], 'index': 0, 'count': row['count'],
                                 'coq_statement': row['coq']},
                       'origin': {'call_design': call['call_site_pc'], 'source': call['output_length_source']}})
    seed = seed_owned_resources(public, entry_pc=return_pc, vocabulary=vocabulary, constants=constants or {},
                                facts=copied)
    seed.state.registers.update(registers)
    for name, value in state.registers.items():
        if not GPR.fullmatch(name) and name not in registers and name != 'PC':
            seed.state.registers[name] = value
    seed.state.retained_registers = dict(seed.state.registers)
    seed.state.conditions = list(state.conditions) + system_conditions
    seed.state.memory = [replace(region, bytes=regions.get(region.ownership_id, region.bytes))
                         for region in seed.state.memory]
    seed.join_kind = 'call_return'
    report = {'call_site_pc': call['call_site_pc'], 'return_site_pc': call['return_site_pc'],
              'spec': call['spec_module'] + '.' + call['spec'], 'edges': len(edges),
              'widened_call_site_registers': widened, 'replaced': splits, 'kept': sorted(kept),
              'callee_frame': callee_frame, 'carried_fact': carried,
              'havoc_registers': [binder['name'] for binder in binders if binder['name'].startswith(PREFIX + 'x')]}
    return seed, public, report
