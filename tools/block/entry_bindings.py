"""Bind source signatures and retain application-local JSON variables."""
from pathlib import Path
from copy import deepcopy
import importlib.util
import hashlib
import re

from entry_schema import FIELDS, contract_fields, source_module, verify_sources
from trace_registers import tokens
from function_names import FunctionNames


def normalize_type(value):
    return ' '.join(tokens(value))


def declared_binders(source, declaration):
    sequence = tokens(source)
    definitions = [index for index, value in enumerate(sequence[:-1])
                   if value == 'Definition' and sequence[index + 1] == declaration]
    if len(definitions) != 1:
        raise ValueError('The source does not contain one unambiguous Definition ' + declaration)
    index = definitions[0] + 2
    result = []
    while index < len(sequence):
        value = sequence[index]
        if value in (':', ':=') or (value == ':' and sequence[index + 1:index + 2] == ['=']):
            return result
        if value == '`':
            index += 1
            if sequence[index] != '{':
                raise ValueError('The Definition has an unsupported context binder')
        if sequence[index] == '{':
            # The schema omits the existing Iris context binders.
            end = index + 1
            depth = 1
            while end < len(sequence) and depth:
                depth += (sequence[end] == '{') - (sequence[end] == '}')
                end += 1
            if depth:
                raise ValueError('The Definition has an unfinished context binder')
            context = sequence[index + 1:end - 1]
            if context not in (['!', 'islaG', 'Sigma'], ['!', 'threadG']):
                raise ValueError('The Definition has an unsupported implicit binder')
            index = end
            continue
        if sequence[index] != '(':
            raise ValueError('The Definition has an unsupported explicit binder')
        start = index + 1
        depth = 1
        index += 1
        while index < len(sequence) and depth:
            depth += (sequence[index] == '(') - (sequence[index] == ')')
            index += 1
        if depth:
            raise ValueError('The Definition has an unfinished binder')
        binder = sequence[start:index - 1]
        if ':' not in binder:
            raise ValueError('The explicit binder has no type')
        colon = binder.index(':')
        names, type_tokens = binder[:colon], binder[colon + 1:]
        if not names or not type_tokens or any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", name) for name in names):
            raise ValueError('The explicit binder has an unsupported shape')
        result.extend({'name': name, 'type': ' '.join(type_tokens)} for name in names)
    raise ValueError('The Definition has no result type')


def check_binders(block, root):
    fields = contract_fields(block)
    if fields is None:
        raise ValueError('The design row lacks all five executable entry fields')
    root = verify_sources(fields, root)
    declared = None
    for key in ('entry_definition', 'resource_predicate'):
        name = fields[key]
        owners = [path for path in fields['source_hashes'] if path.endswith('.v')
                  and name.startswith(source_module(path) + '.')]
        if not owners:
            raise ValueError('The source hashes do not bind ' + name)
        owner = max(owners, key=lambda path: len(source_module(path)))
        # Nested module declarations need a namespace-aware check before use.
        if name != source_module(owner) + '.' + name.rsplit('.', 1)[-1]:
            raise ValueError('The Definition uses an unsupported nested module namespace')
        binders = declared_binders((Path(root)/owner).read_text(), name.rsplit('.', 1)[-1])
        # JSON binders are table universals, not Definition parameters.
        # The kernel checks each ordered argument against the declared type.
        if len(fields['arguments']) != len(binders):
            raise ValueError('The ordered argument count does not match the source Definition: ' + name)
        declared = binders
    return declared


def validate_design(design, root):
    """Require complete, source-bound declarations for every designed row."""
    errors = {}
    for index, row in enumerate(design['blocks']):
        try:
            check_binders(row, root)
        except (ValueError, OSError) as error:
            errors[str(row.get('entry_pc', row.get('entry_definition', index)))] = str(error)
    if errors:
        raise ValueError('The executable design has invalid source bindings: ' +
                         '; '.join(pc + ': ' + reason for pc, reason in errors.items()))
    return len(design['blocks'])


def _rendered_producer(root):
    """Load the workspace producer after the table module initializes."""
    path = Path(root) / 'ZesuSsz/Evidence/generate_block_design.py'
    spec = importlib.util.spec_from_file_location('_entry_design_producer', path)
    producer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(producer)
    # The producer adds this workspace's tools/block directory to sys.path.
    import render_support
    if Path(render_support.__file__).resolve() != (Path(root)/'tools/block/render_support.py').resolve():
        raise ValueError('The entry renderer comes from a different workspace')
    return producer, render_support


def rendered_entry_views(design, root, *, name_prefix="decodeItem"):
    """Keep input prerequisites separate from fresh declaration applications."""
    names = FunctionNames(name_prefix)
    primary = design['blocks']
    supported = [row for row in primary if 'support' in row]
    table = deepcopy(design)
    applications = deepcopy(design)
    mapping, input_hashes, output_hashes = {}, {}, {}

    def collect(target, hashes):
        for path, sha in hashes.items():
            if path in target and target[path] != sha:
                raise ValueError('The entry bindings contain different source hashes: ' + path)
            target[path] = sha

    if not supported:
        for row in primary:
            fields = contract_fields(row)
            if fields:
                collect(input_hashes, fields['source_hashes'])
        return dict(table_design=table, application_design=applications, name_mapping=mapping,
                    input_source_hashes=input_hashes, output_source_hashes=output_hashes,
                    primary_count=len(primary), auxiliary_count=0)

    producer, renderer = _rendered_producer(root)
    for path, source in renderer.render_support(design, root, name_prefix=name_prefix).items():
        output = Path(root)/path
        expected = source.encode('utf-8')
        if not output.is_file() or output.read_bytes() != expected:
            raise ValueError('The generated support output is stale: ' + str(path))
        output_hashes[str(path)] = hashlib.sha256(expected).hexdigest()
    originals = renderer.support_declarations(design)
    fresh = producer.verify_rendered_entries(design, root, name_prefix=name_prefix)
    if len(originals) != len(fresh):
        raise ValueError('The rendered declaration inventory has missing or unused bindings')
    replacements = {}
    generated = f'ZesuSsz/Generated/{names.module}/Entries.v'
    generated_module = source_module(generated)
    output_names = set()
    for original, bound in zip(originals, fresh):
        fields = contract_fields(original)
        current = contract_fields(bound)
        old = fields['entry_definition']
        expected_name = generated_module + '.' + old.rsplit('.', 1)[-1]
        if old in replacements or expected_name in output_names:
            raise ValueError('The rendered declaration inventory contains duplicate bindings')
        expected = deepcopy(original)
        expected.update(entry_definition=expected_name, resource_predicate=expected_name,
                        source_hashes=current['source_hashes'])
        if (fields['resource_predicate'] != old or bound != expected or
                set(current['source_hashes']) != {generated}):
            raise ValueError('The rendered declaration binding differs from its ordered input: ' + old)
        # Old labels remain prerequisites, but only fresh declarations need to exist.
        verify_sources(fields, root)
        check_binders(bound, root)
        collect(input_hashes, fields['source_hashes'])
        collect(output_hashes, current['source_hashes'])
        mapping[old] = expected_name
        output_names.add(expected_name)
        replacements[old] = deepcopy(bound)

    def promoted(row):
        result = deepcopy(row)
        if 'support' in row:
            old = contract_fields(row)['entry_definition']
            if old not in replacements:
                raise ValueError('The primary entry has no rendered binding: ' + old)
            result.update(contract_fields(replacements[old]))
        else:
            check_binders(row, root)
            collect(input_hashes, contract_fields(row)['source_hashes'])
        for edge in result.get('incoming_edges', []):
            if 'resource_alternative' in edge:
                old = edge['resource_alternative']
                if 'support' in row:
                    if old not in mapping:
                        raise ValueError('The resource alternative has no rendered binding: ' + old)
                    edge['resource_alternative'] = mapping[old]
        return result

    table['blocks'] = [promoted(row) for row in primary]
    # Keep the producer's order, including before/after auxiliary declarations.
    applications['blocks'] = [promoted(row) for row in originals]
    applications['blocks'].extend(promoted(row) for row in primary if 'support' not in row)
    primary_names = [row['entry_definition'] for row in supported]
    if len(set(primary_names)) != len(primary_names):
        raise ValueError('The primary entry inventory contains duplicate bindings')
    if not set(primary_names).issubset(replacements):
        raise ValueError('The primary entry inventory has missing bindings')
    for group in (design.get('support', {}), design.get('support', {}).get('bootstrap', {})):
        if group.get('source_hashes'):
            verify_sources(group, root)
            collect(input_hashes, group['source_hashes'])
    if set(input_hashes) & set(output_hashes):
        raise ValueError('A generated output cannot be an entry input prerequisite')
    validate_design(table, root)
    validate_design(applications, root)
    return dict(table_design=table, application_design=applications, name_mapping=mapping,
                input_source_hashes=input_hashes, output_source_hashes=output_hashes,
                primary_count=len(primary), auxiliary_count=len(originals)-len(supported))


def application_source(design, *, name_prefix="decodeItem"):
    """Render type queries for the unchanged, ordered JSON applications."""
    FunctionNames(name_prefix)
    modules = ['ZesuSsz.Automation.All', 'isla.riscv64.riscv64', 'SailStdpp.MachineWord']
    if name_prefix == 'decodeItem':
        modules.append('ZesuSsz.Contracts.RlpDecodeItemContract')
    for row in design['blocks']:
        fields = contract_fields(row)
        modules.extend(source_module(path) for path in fields['source_hashes'] if path.endswith('.v'))
    lines = ['Require Import ' + module + '.' for module in dict.fromkeys(modules)]
    for index, row in enumerate(design['blocks']):
        fields = contract_fields(row)
        lines.extend([f'Section entry_application_{index}.',
                      'Context `{!islaG Sigma} `{!threadG}.'])
        for binder in fields['binders']:
            lines.append(f"Context ({binder['name']} : {binder['type']}).")
        arguments = ''.join(' (' + value + ')' for value in fields['arguments'])
        for name in dict.fromkeys((fields['entry_definition'], fields['resource_predicate'])):
            lines.append('Check (' + name + arguments + ' : iProp Sigma).')
        lines.append(f'End entry_application_{index}.')
    return '\n'.join(lines) + '\n'
