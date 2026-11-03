"""Authenticate typed witness inputs against their complete source rows."""
import hashlib
import json
from pathlib import Path

from symbolic_state import Expr, parse_trace


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def bound_json(binding):
    if set(binding) != {'path', 'sha256'}:
        raise ValueError('A source binding needs an exact path and hash.')
    data = Path(binding['path']).read_bytes()
    if hashlib.sha256(data).hexdigest() != binding['sha256']:
        raise ValueError('The bound witness source changed.')
    return json.loads(data)


def pointer(document, path):
    if not isinstance(path, str) or not path.startswith('/'):
        raise ValueError('A source witness needs an exact JSON pointer.')
    for item in path[1:].split('/'):
        key = item.replace('~1', '/').replace('~0', '~')
        document = document[int(key)] if isinstance(document, list) else document[key]
    return document


def _expressions(value):
    if isinstance(value, Expr):
        yield value
        for arg in value.args:
            yield from _expressions(arg)
    elif isinstance(value, dict):
        for item in value.values():
            yield from _expressions(item)
    elif isinstance(value, (tuple, list)):
        for item in value:
            yield from _expressions(item)


def _declarations(node):
    if isinstance(node, list):
        if node[:1] == ['declare-const']:
            yield node
        for item in node:
            yield from _declarations(item)


def record_trace_origins(state, source, *, instruction_pc, seed_pc):
    """Record declaration locations without changing values or path facts."""
    declarations = list(_declarations(parse_trace(source)))
    expressions = {digest(x.to_dict()): x for x in _expressions(
        [state.registers, state.conditions, state.retained_registers])
        if x.op == 'local' and str(x.value).startswith(str(state.trace_count) + ':')}
    for expression in expressions.values():
        name = str(expression.value).split(':', 1)[1]
        matches = [d for d in declarations if d[1] == name]
        if len(matches) != 1:
            raise ValueError('A source local has an ambiguous declaration: ' + name)
        expected = ['_', 'BitVec', str(expression.width)] if expression.width is not None else 'Bool'
        if matches[0][2] != expected:
            raise ValueError('A source local differs from its declaration type.')
        origin = {'kind': 'source_witness_origin', 'symbol': expression.to_dict(),
                  'instruction_pc': hex(instruction_pc), 'seed_pc': hex(seed_pc),
                  'trace_count': state.trace_count, 'declaration': name,
                  'declaration_type': matches[0][2],
                  'raw_trace_sha256': hashlib.sha256(source.encode()).hexdigest()}
        if origin not in state.reports:
            state.reports.append(origin)


def authenticate_sources(binders, bindings, context):
    """Resolve source slots; never obtain a value from a target equality."""
    required = {'report', 'pointer', 'owner_sha256', 'source_declaration', 'target_declaration'}
    if not required <= set(context) or set(context) - required - {'trace_index', 'trace_pointer', 'target_key_declaration'}:
        raise ValueError('Typed source witnesses need a complete source context.')
    from witness_data import _source_declaration, _result_type, declared_witness_slots
    source_declaration = context['source_declaration']
    target_declaration = context['target_declaration']
    for declaration in [source_declaration, target_declaration]:
        _source_declaration(declaration)
    source_kind = _result_type(_source_declaration(source_declaration))
    if not source_kind or source_kind[0].rsplit('.', 1)[-1] != 'iProp':
        raise ValueError('The source owner must be an assertion definition.')
    if source_declaration == target_declaration:
        raise ValueError('A target declaration cannot authenticate its own witnesses.')
    source_slots = declared_witness_slots(Path(source_declaration['path']).read_text(), source_declaration['declaration'])['declared']
    report = bound_json(context['report'])
    if report.get('schema') != 'block-forward-states.v1':
        raise ValueError('Typed witnesses require an authenticated forward report.')
    row = pointer(report, context['pointer'])
    if not isinstance(row, dict) or not {'state', 'resource_boundary'} <= row.keys():
        raise ValueError('A witness source must be a forward alternative.')
    owner = row['resource_boundary']
    if owner.get('block_status') != 'completed' or digest(owner) != context['owner_sha256']:
        raise ValueError('The complete source owner differs from its binding.')
    from forward_resources import parse_source_ownership
    from forward_witnesses import _check_forward_owner
    resources = []
    for component in owner['components']:
        source = component['source']
        if source.startswith('reg_col '):
            resources.append({'kind': 'register_collection', 'value': source[len('reg_col '):]})
        else:
            parsed = parse_source_ownership(source, provenance=component.get('provenance', {}))['components']
            for resource in parsed:
                if resource['kind'] == 'register':
                    resources.append(resource)
                elif resource['kind'] == 'byte_array':
                    if resource.get('fraction') is not None:
                        from check_data_only_lemmas import rocq_tokens
                        if [token for token, _ in rocq_tokens(resource['fraction'])] != ['{', 'DfracOwn', '1', '}']:
                            raise ValueError('The source array has an unsupported fraction.')
                    resources.append(dict(resource, address=resource['address_z']))
                elif source == 'K':
                    resources.append({'kind': 'owned_parameter', 'name': 'K'})
    _check_forward_owner({'resources': resources}, source_declaration)
    trace_row = row
    if 'trace_pointer' in context:
        trace_row = pointer(report, context['trace_pointer'])
        source_pc = row['state']['registers']['PC']
        if (source_pc.get('op') != 'bits' or trace_row.get('predecessor_pc') != hex(source_pc['value'])
                or trace_row.get('seed_pc') != row.get('seed_pc')
                or trace_row['path'][:len(row['path'])] != row['path']):
            raise ValueError('The declaration row belongs to another source edge.')
    if set(bindings) - {b['name'] for b in binders}:
        raise ValueError('The source mapping has extra witness slots.')
    result = {}
    for binder in binders:
        name = binder['name']
        if name not in bindings:
            continue
        binding = bindings[name]
        if set(binding) != {'kind', 'pointer'} or binding['kind'] not in {'existential', 'source_existential', 'trace_local'}:
            raise ValueError('A witness needs a source existential or source declaration.')
        if binding['kind'] == 'source_existential':
            if not binding['pointer'].startswith('/declared/'):
                raise ValueError('A source existential needs its declaration scope.')
            value = pointer({'declared': source_slots}, binding['pointer'])
            if value['name'] != name or value['type'] != binder['type']:
                raise ValueError('The source existential has a different name or type.')
            identity = {'kind': 'source_existential', 'declaration': source_declaration,
                        'slot': binding['pointer'], 'owner': context['owner_sha256']}
        else:
            value = pointer(trace_row if binding['kind'] == 'trace_local' else row, binding['pointer'])
        if binding['kind'] == 'existential':
            if not binding['pointer'].startswith('/resource_boundary/tree/'):
                raise ValueError('An existential witness has no owned source scope.')
            if value.get('name') != name or value.get('type') != binder['type']:
                raise ValueError('The source existential has a different name or type.')
            identity = {'kind': 'existential', 'source': context['report'],
                        'row': context['pointer'], 'scope': binding['pointer'], 'owner': context['owner_sha256']}
        elif binding['kind'] == 'trace_local':
            if not binding['pointer'].startswith('/state/reports/') or value.get('kind') != 'source_witness_origin':
                raise ValueError('A trace witness has no source declaration record.')
            symbol = value['symbol']
            expected_name = 'forward_witness_' + digest(symbol)[:16]
            expected_type = 'bool' if symbol.get('width') is None else 'bv ' + str(symbol['width'])
            if expected_name != name or expected_type != binder['type']:
                raise ValueError('The source declaration has a different slot identity or type.')
            if symbol.get('op') != 'local' or symbol['value'] != str(value['trace_count']) + ':' + value['declaration']:
                raise ValueError('The source declaration identity is inconsistent.')
            if 'trace_pointer' in context and not row['state']['trace_count'] < value['trace_count'] <= trace_row['state']['trace_count']:
                raise ValueError('The source declaration is outside the owned source edge.')
            matching = [r for r in trace_row['state']['reports'] if r.get('kind') == 'source_witness_origin'
                        and r.get('symbol') == symbol]
            if len(matching) != 1:
                raise ValueError('The source declaration projection is ambiguous.')
            if 'trace_index' not in context:
                raise ValueError('A source declaration needs its authenticated trace index.')
            index = bound_json(context['trace_index'])
            traces = [t for t in index['instruction_pairs'] if t['pc'] == value['instruction_pc']]
            if len(traces) != 1:
                raise ValueError('The source instruction trace is ambiguous or missing.')
            trace = traces[0]
            for artifact in ['raw', 'rocq']:
                raw = Path(trace[artifact]['path']).read_bytes()
                if hashlib.sha256(raw).hexdigest() != trace[artifact]['sha256']:
                    raise ValueError('The source instruction artifact changed.')
            raw = Path(trace['raw']['path']).read_text()
            declarations = [d for d in _declarations(parse_trace(raw)) if d[1] == value['declaration']]
            if (trace['raw']['sha256'] != value['raw_trace_sha256'] or len(declarations) != 1
                    or declarations[0][2] != value['declaration_type']):
                raise ValueError('The source declaration differs from its trace artifact.')
            identity = {'kind': 'trace_local', 'pc': value['instruction_pc'],
                        'trace_sha256': value['raw_trace_sha256'], 'declaration': value['declaration'],
                        'rocq_trace_sha256': trace['rocq']['sha256']}
        key = digest(identity)
        result[name] = {'kind': 'source_value', 'source_key': key, 'type': binder['type'],
                        'origin': identity, 'source_pointer': binding['pointer']}
    return result


def owned_register_bindings(context):
    """Select only direct, unique target binders with source-owned registers."""
    from forward_witnesses import _register_owners, _source_definition
    from witness_data import declared_witness_slots, _unwrap
    from join_generalize import REGISTER

    source = context['source_declaration']
    target = context['target_declaration']
    source_registers = _register_owners(_source_definition(source))
    target_registers = _register_owners(_source_definition(target))
    report = bound_json(context['report'])
    row = pointer(report, context['pointer'])
    target_row = pointer(report, context.get('trace_pointer', context['pointer']))
    result = {}
    for slot in declared_witness_slots(Path(target['path']).read_text(), target['declaration'])['remaining']:
        kind = slot['type'].split()
        if len(kind) != 2 or kind[0] != 'bv' or not kind[1].isdigit():
            continue
        candidates = []
        for register, value in target_registers:
            plain = _unwrap(value)
            if plain[1:2] == [':']:
                plain = plain[:1]
            if plain == [slot['name']]:
                candidates.append(register)
        if not candidates:
            continue
        if len(candidates) != 1 or not REGISTER.fullmatch(candidates[0]):
            raise ValueError('A target witness has ambiguous register ownership.')
        register = candidates[0]
        if sum(name == register for name, _ in source_registers) != 1:
            raise ValueError('The source does not own the target witness register.')
        width = int(kind[1])
        for state in [row['state'], target_row['state']]:
            value = state.get('registers', {}).get(register, state.get('retained_registers', {}).get(register))
            if value is None or value.get('width') != width:
                raise ValueError('The owned witness register has a different source width.')
        result[slot['name']] = (register, width)
    return result


def derive_source_plan(context, *, register_bindings=None, allow_owned_registers=False):
    """Use exact source names and declaration records, not target equations."""
    from witness_data import _source_declaration, declared_witness_slots
    from join_generalize import witness_plan

    source = context['source_declaration']
    target = context['target_declaration']
    for declaration in [source, target]:
        _source_declaration(declaration)
    source_layout = declared_witness_slots(Path(source['path']).read_text(), source['declaration'])
    target_layout = declared_witness_slots(Path(target['path']).read_text(), target['declaration'])
    source_slots = source_layout['declared']
    report = bound_json(context['report'])
    row = pointer(report, context.get('trace_pointer', context['pointer']))
    bindings = {}
    registers = register_bindings or {}
    if allow_owned_registers:
        checked = owned_register_bindings(context)
        if any(checked.get(name) != value for name, value in registers.items()):
            raise ValueError('A supplied register input differs from its owned source.')
        registers = checked
    for slot in target_layout['remaining']:
        matches = [i for i, candidate in enumerate(source_slots) if candidate == slot]
        if len(matches) == 1:
            bindings[slot['name']] = {'kind': 'source_existential', 'pointer': '/declared/' + str(matches[0])}
            continue
        origins = [i for i, origin in enumerate(row['state']['reports'])
                   if origin.get('kind') == 'source_witness_origin'
                   and 'forward_witness_' + digest(origin['symbol'])[:16] == slot['name']]
        if len(origins) == 1:
            bindings[slot['name']] = {'kind': 'trace_local', 'pointer': '/state/reports/' + str(origins[0])}
        elif len(origins) > 1:
            raise ValueError('The source declaration projection is ambiguous: ' + slot['name'])
        elif slot['name'] not in registers:
            raise ValueError('The source has no authenticated value for ' + slot['name'] + ' : ' + slot['type'])
    registers = {name: value for name, value in registers.items() if name not in bindings}
    return witness_plan(target_layout['remaining'], register_bindings=registers,
                        source_bindings=bindings, source_context=context)


def derive_runtime_source_plan(context, authority, *, allow_owned_registers=False):
    """Extend a checked used-slot plan without dropping runtime existentials."""
    from witness_data import runtime_witness_slots
    if bound_json(authority).get('schema') != 'zesu.witness-runtime-slot-correction.v1':
        raise ValueError('The full runtime path needs its bound slot authority.')
    plan = derive_source_plan(context, allow_owned_registers=allow_owned_registers)
    slots = runtime_witness_slots(context['target_declaration'])
    used = {row['binder']: row for row in plan['ordered_witnesses']}
    witnesses = []
    for slot in slots:
        if slot['vacuous']:
            witnesses.append({'binder': slot['name'], 'type': slot['type'],
                              'vacuous': True, 'fixed_inhabitant': slot['value_rule']['term']})
        else:
            witnesses.append(dict(used[slot['name']], type=slot['type']))
    return dict(plan, ordered_binders=[slot['name'] for slot in slots],
                ordered_witnesses=witnesses,
                runtime_slots={'authority': authority, 'slots': slots})


def render_source_mapping(plan, *, name, target_application, source_application,
                          parameters, source_parameters, module_header=None):
    """Emit value mappings and capture declarations, never proof scripts."""
    from render_support import expression, identifier
    from witness_data import declared_witness_slots, product, runtime_witness_slots

    if plan.get('schema') != 'source.join-witness-plan.v2':
        raise ValueError('A typed mapping needs the authenticated source plan.')
    context = plan['source_context']
    target = context['target_declaration']
    layout = declared_witness_slots(Path(target['path']).read_text(), target['declaration'])
    runtime = plan.get('runtime_slots')
    if runtime is not None:
        if bound_json(runtime['authority']).get('schema') != 'zesu.witness-runtime-slot-correction.v1':
            raise ValueError('The full runtime path needs its bound slot authority.')
        expected_slots = runtime_witness_slots(target)
        if runtime.get('slots') != expected_slots:
            raise ValueError('The runtime slot identities or vacuous flags changed.')
    slots = layout['declared'] if runtime is not None else layout['remaining']
    input_slots = layout['remaining']
    if plan['ordered_binders'] != [slot['name'] for slot in slots]:
        raise ValueError('The source mapping changes declaration order.')
    witnesses = plan.get('ordered_witnesses', [])
    if (len(witnesses) != len(slots) or
            any(witness.get('binder') != slot['name'] or witness.get('type', slot['type']) != slot['type']
                for witness, slot in zip(witnesses, slots))):
        raise ValueError('The source mapping changes witness order, count, or types.')
    # Recheck bound bytes and slot identities at the actual emission boundary.
    sources = authenticate_sources(input_slots, plan['source_bindings'], context)
    registers = owned_register_bindings(context) if any(slot['name'] not in sources for slot in input_slots) else {}
    name = identifier(name, 'typed source mapping name')
    target_application = expression(target_application, 'mapping target application')
    source_application = expression(source_application, 'mapping source application')
    from entry_bindings import declared_binders, normalize_type
    from forward_witnesses import _application_arguments
    from witness_data import _source_declaration
    applications = {}
    for role, application, declaration in [
            ('source', source_application, context['source_declaration']),
            ('target', target_application, context.get('target_key_declaration', target))]:
        _source_declaration(declaration)
        head, arguments = _application_arguments(application)
        if head.rsplit('.', 1)[-1] != declaration['declaration']:
            raise ValueError('The mapping application has a different declaration head.')
        signature = declared_binders(Path(declaration['path']).read_text(), declaration['declaration'])
        if len(signature) != len(arguments):
            raise ValueError('The mapping application has a different parameter count.')
        applications[role] = {slot['name']: (normalize_type(slot['type']), normalize_type(argument))
                              for slot, argument in zip(signature, arguments)}
    for shared in applications['source'].keys() & applications['target'].keys():
        if applications['source'][shared] != applications['target'][shared]:
            raise ValueError('A shared source parameter has conflicting types or values.')
    if 'target_key_declaration' in context:
        from witness_data import _source_definition
        from check_data_only_lemmas import rocq_tokens
        key_declaration = context['target_key_declaration']
        key_signature = declared_binders(Path(key_declaration['path']).read_text(), key_declaration['declaration'])
        layout_signature = declared_binders(Path(target['path']).read_text(), target['declaration'])
        key_parameters = {slot['name']: slot['type'] for slot in key_signature}
        if any(key_parameters.get(slot['name']) != slot['type'] for slot in layout_signature):
            raise ValueError('The target wrapper changes telescope parameters.')
        remaining = [slot for slot in key_signature if slot['name'] not in {s['name'] for s in layout_signature}]
        if remaining != [{'name': 'K', 'type': 'iProp Sigma'}]:
            raise ValueError('The target wrapper needs one unchanged continuation.')
        body = _source_definition(key_declaration)
        reduced = [token for token in body if token not in {'(', ')', '%', 'I'}]
        expected = [target['declaration']] + [slot['name'] for slot in layout_signature] + ['∗', 'K']
        if reduced != expected:
            raise ValueError('The target wrapper does not preserve the exact telescope and continuation.')
    names = {}
    def telescope(values):
        result = ''
        for value in values:
            key = identifier(value['name'], 'source mapping parameter')
            kind = expression(value['type'], 'source mapping parameter type')
            if key in names and names[key] != kind:
                raise ValueError('A source mapping parameter has conflicting types.')
            names[key] = kind
            result += ' (' + key + ' : ' + kind + ')'
        return result
    typed = telescope(parameters)
    source_typed = telescope(source_parameters)
    types = [slot['type'] for slot in slots]
    kind = product(types)
    input_kind = product([slot['type'] for slot in input_slots])
    arguments = ''.join(' (' + parameter['name'] + ')' for parameter in parameters)
    data_name = name + '_data'
    source_head = _application_arguments(source_application)[0]
    target_head = _application_arguments(target_application)[0]
    opacity = 'Global Typeclasses Opaque ' + source_head + ' ' + target_head + '.\n'
    data_expression = 'source_values'
    if runtime is not None:
        local_names = []
        reserved = set(names) | {'source_values'}
        for index in range(len(input_slots)):
            local = 'captured_slot_' + str(index)
            while local in reserved:
                local += '_'
            reserved.add(local)
            local_names.append(local)
        values = {slot['name']: local for slot, local in zip(input_slots, local_names)}
        data_expression = 'tt'
        by_binder = {row['binder']: row for row in witnesses}
        for slot in reversed(runtime['slots']):
            if slot['vacuous']:
                witness = by_binder[slot['name']]
                if (witness.get('vacuous') is not True or
                        witness.get('fixed_inhabitant') != slot['value_rule']['term']):
                    raise ValueError('A vacuous slot changed its authorized fixed inhabitant.')
                value = '(' + slot['value_rule']['term'] + ')'
            else:
                if by_binder[slot['name']].get('vacuous') or 'fixed_inhabitant' in by_binder[slot['name']]:
                    raise ValueError('A used slot cannot receive a fixed inhabitant.')
                value = values[slot['name']]
            data_expression = '(' + value + ', ' + data_expression + ')'
        if local_names:
            pattern = 'tt'
            for local in reversed(local_names):
                pattern = '(' + local + ', ' + pattern + ')'
            data_expression = "let '" + pattern + ' := source_values in ' + data_expression
    source = opacity + ('Definition ' + data_name + ' `{!islaG Sigma} `{!threadG}' + typed +
              ' (source_values : ' + input_kind + ') : ' + kind + ' := ' + data_expression + '.\n')
    inputs = []
    by_name = {w['binder']: w for w in plan['ordered_witnesses']}
    for slot in input_slots:
        bound = slot['name']
        if bound in sources:
            if by_name[bound].get('source_key') != sources[bound]['source_key']:
                raise ValueError('The emitted source mapping changed a slot identity.')
            inputs.append('(ZesuSourceValue (' + slot['type'] + ') "' + sources[bound]['source_key'] + '")')
        else:
            from symbolic_state import input_expr
            if bound not in registers:
                raise ValueError('The source mapping has no checked owned-register input.')
            register, width = registers[bound]
            if by_name[bound].get('expression') != input_expr(bound, width).to_dict():
                raise ValueError('The emitted register mapping changes its source witness.')
            inputs.append('(ZesuSourceRegister ' + str(width) + '%N "' + register + '")')
    input_term = 'ZesuSourceUnit'
    for item in reversed(inputs):
        input_term = '(ZesuSourcePair ' + item + ' ' + input_term + ')'
    source += '#[export] Instance ' + name + '_enabled : ZesuStepSourceWitnesses := I.\n'
    source += ('#[export] Instance ' + name + ' `{!islaG Sigma} `{!threadG}' + typed + ' :\n'
               '  ZesuEntrySourceWitnessMapping (' + target_application + ') (' + input_kind + ') (' + kind + ') :=\n'
               '  {| zesu_source_witness_input := ' + input_term + ';\n'
               '     zesu_source_witness_mapping := ' + data_name + arguments + ' |}.\n')
    declaration = context['source_declaration']
    source_slots = declared_witness_slots(Path(declaration['path']).read_text(), declaration['declaration'])['declared']
    selected = {plan['source_bindings'][n]['pointer']: value['source_key']
                for n, value in sources.items() if value['origin']['kind'] == 'source_existential'}
    owner_plan = 'ZesuSourceOwnerEnd'
    for i in range(len(source_slots) - 1, -1, -1):
        slot = source_slots[i]
        key = selected.get('/declared/' + str(i))
        option = '(Some "' + key + '")' if key is not None else 'None'
        owner_plan = '(ZesuSourceOwnerSlot (' + slot['type'] + ') ' + option + ' ' + owner_plan + ')'
    source += ('#[export] Instance ' + name + '_owner `{!islaG Sigma} `{!threadG}' + source_typed + ' :\n'
               '  ZesuSourceOwner (' + source_application + ') ' + owner_plan + ' :=\n'
               '  {| zesu_source_owner_original := ' + source_application + ';\n'
               '     zesu_source_owner_original_eq := eq_refl |}.\n')
    emitted = set()
    for value in sources.values():
        origin = value['origin']
        if origin['kind'] != 'trace_local':
            continue
        key = value['source_key']
        if key in emitted:
            raise ValueError('The mapping repeats a source declaration key.')
        emitted.add(key)
        pc = int(origin['pc'], 0)
        variable = origin['declaration']
        if not variable.startswith('v') or not variable[1:].isdigit():
            raise ValueError('A trace declaration needs its numeric source identity.')
        width = value['type'].split()
        if len(width) != 2 or width[0] != 'bv' or not width[1].isdigit():
            raise ValueError('The declaration reader currently supports bitvector sources.')
        source += ('#[export] Instance ' + name + '_declaration_' + str(len(emitted)) + ' :\n'
                   '  ZesuSourceDeclaration (BV 64%N ' + str(pc) + '%Z) ' + variable[1:] + '%Z ' +
                   width[1] + '%N "' + key + '" := I.\n')
    # Metadata is separate from the unchanged ordinary-product mapping.
    # Hash the complete mapping fragment before these records to avoid self-reference.
    mapping_sha256 = hashlib.sha256(source.encode()).hexdigest()
    def profile(values, name_key):
        result = 'ZesuWitnessProfileEnd'
        for slot in reversed(values):
            label = identifier(slot[name_key], 'witness profile name')
            result = ('(ZesuWitnessProfileSlot "' + label + '" (' + slot['type'] + ') ' + result + ')')
        return result
    expected_profile = profile(slots, 'name')
    emitted_slots = [dict(witness, type=slot['type']) for witness, slot in zip(witnesses, slots)]
    emitted_profile = profile(emitted_slots, 'binder')
    source += ('#[export] Instance ' + name + '_source_profile `{!islaG Sigma} `{!threadG}' + typed + ' :\n'
               '  ZesuEntryWitnessSourceProfile (' + target_application + ') (' + kind + ') :=\n'
               '  {| zesu_source_profile_declaration := "' + target['sha256'] + '";\n'
               '     zesu_source_profile_slots := ' + expected_profile + ' |}.\n')
    source += ('#[export] Instance ' + name + '_data_profile `{!islaG Sigma} `{!threadG}' + typed + ' :\n'
               '  ZesuEntryWitnessDataProfile (' + target_application + ') (' + kind + ') :=\n'
               '  {| zesu_data_profile_declaration := "' + target['sha256'] + '";\n'
               '     zesu_data_profile_mapping := "' + mapping_sha256 + '";\n'
               '     zesu_data_profile_slots := ' + emitted_profile + ' |}.\n')
    module_source = None
    if module_header is not None:
        # Keep the caller's complete import order. Add the direct metadata
        # dependency beside the existing source-reader dependency.
        anchor = 'Require Import ZesuSsz.Automation.SourceWitnessInputs.\n'
        dependency = 'Require Import ZesuSsz.Automation.EntryWitnessProfile.\n'
        if module_header.count(anchor) != 1:
            raise ValueError('The mapping header needs one source-reader import.')
        if dependency not in module_header:
            module_header = module_header.replace(anchor, anchor + dependency)
        module_source = module_header + source
    return {'source': source, 'module_source': module_source, 'plan': plan, 'declaration_order': slots,
            'profile_binding': {'declaration': target,
                                'key_declaration': context.get('target_key_declaration', target),
                                'mapping_fragment_sha256': mapping_sha256,
                                'source_slots': slots,
                                'data_slots': [{'name': w['binder'], 'type': w['type']} for w in emitted_slots],
                                'names_from_authenticated_source': True,
                                'runtime_names_recovered': False},
            'internal_order': list(reversed(slots)), 'proof_scripts_emitted': False,
            'capture_uses_source_locations': True,
            'runtime_slot_binding': runtime}
