"""Bind source signatures and retain application-local JSON variables."""
from pathlib import Path
import re

from entry_schema import contract_fields, source_module, verify_sources
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
    for row in design['blocks']:
        try:
            check_binders(row, root)
        except (ValueError, OSError) as error:
            errors[row['entry_pc']] = str(error)
    if errors:
        raise ValueError('The executable design has invalid source bindings: ' +
                         '; '.join(pc + ': ' + reason for pc, reason in errors.items()))
    return len(design['blocks'])


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
