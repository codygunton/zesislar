"""Bind an unused declaration origin to its consumed register expression.

The records select source values. They add no logical source facts.
The supported expression language contains equality, bitwise AND, fields,
and closed bitvector literals. Other expressions refuse.
"""
import hashlib
import json
from pathlib import Path
import re

from check_data_only_lemmas import rocq_commands, rocq_tokens
from symbolic_state import parse_trace
from witness_data import _words


def _text(binding):
    if set(binding) != {"path", "sha256"}:
        raise ValueError("A register origin needs an exact artifact binding.")
    raw = Path(binding["path"]).read_bytes()
    if hashlib.sha256(raw).hexdigest() != binding["sha256"]:
        raise ValueError("The register-origin artifact changed.")
    return raw.decode()


def _field(node):
    if not (isinstance(node, list) and len(node) == 2 and
            isinstance(node[0], str) and node[0].startswith("|")):
        return None
    if not (isinstance(node[1], list) and len(node[1]) == 1):
        raise ValueError("The source register accessor is unsupported.")
    accessor = node[1][0]
    if not (isinstance(accessor, list) and len(accessor) == 3 and
            accessor[:2] == ["_", "field"]):
        raise ValueError("The source register field is unsupported.")
    names = [node[0], accessor[2]]
    if any(not isinstance(n, str) or not re.fullmatch(r"\|[A-Za-z_][A-Za-z_0-9]*\|", n)
           for n in names):
        raise ValueError("The source register or field name is unsupported.")
    return tuple(n[1:-1] for n in names)


def _fields(node):
    selected = _field(node)
    if selected is not None:
        return [(node, selected)]
    if isinstance(node, list):
        return [row for child in node for row in _fields(child)]
    return []


def _replace(node, old, new):
    if node == old:
        return new
    return [_replace(child, old, new) for child in node] if isinstance(node, list) else node


def _render(node):
    selected = _field(node)
    if selected is not None:
        register, field = selected
        return 'AExp_Val (AVal_Var ' + json.dumps(register) + ' [Field ' + json.dumps(field) + ']) Mk_annot'
    if isinstance(node, str) and re.fullmatch(r"#(?:x[0-9a-fA-F]+|b[01]+)", node):
        radix = 16 if node[1] == 'x' else 2
        width = len(node[2:]) * (4 if radix == 16 else 1)
        return f'AExp_Val (AVal_Bits (BV {width}%N 0x{int(node[2:], radix):x}%Z)) Mk_annot'
    if isinstance(node, list) and len(node) == 3 and node[0] == '=':
        return 'AExp_Binop (Eq) (' + _render(node[1]) + ') (' + _render(node[2]) + ') Mk_annot'
    if isinstance(node, list) and len(node) == 3 and node[0] == 'bvand':
        return 'AExp_Manyop (Bvmanyarith Bvand) [' + _render(node[1]) + '; ' + _render(node[2]) + '] Mk_annot'
    raise ValueError("The source register guard is unsupported.")


def _tokens(text):
    return [token for token in _words(rocq_tokens(text)) if token not in {'(', ')'}]


def translate_unused_declaration(raw_binding, rocq_binding, *, pc, declaration, width, source_key):
    """Return authenticated register-read metadata. Emit no proof or value."""
    if type(width) is not int or width <= 0:
        raise ValueError("The source width must be a closed positive integer.")
    if not isinstance(source_key, str) or not re.fullmatch(r'[0-9a-f]{64}', source_key):
        raise ValueError("The source register key is not authenticated.")
    if not isinstance(declaration, str) or not re.fullmatch(r'v[0-9]+', declaration):
        raise ValueError("The source declaration is unsupported.")
    if type(pc) is not int or pc < 0:
        raise ValueError("The source PC must be a closed nonnegative integer.")
    raw, consumed = _text(raw_binding), _text(rocq_binding)
    identity = {'kind': 'trace_local', 'pc': hex(pc),
                'trace_sha256': raw_binding['sha256'], 'declaration': declaration,
                'rocq_trace_sha256': rocq_binding['sha256']}
    expected_key = hashlib.sha256(json.dumps(identity, sort_keys=True,
        separators=(',', ':')).encode()).hexdigest()
    if source_key != expected_key:
        raise ValueError("The register origin changes the authenticated source key.")
    events = parse_trace(raw)
    if not isinstance(events, list) or events[:1] != ['trace']:
        raise ValueError("The raw origin needs one source trace.")
    expected = ['declare-const', declaration, ['_', 'BitVec', str(width)]]
    positions = [i for i, event in enumerate(events) if event == expected]
    declarations = [event for event in events if isinstance(event, list) and
                    event[:2] == ['declare-const', declaration]]
    if len(positions) != 1 or len(declarations) != 1:
        raise ValueError("The raw declaration is missing or ambiguous.")
    index = positions[0]
    if index + 2 >= len(events) or events[index + 1][:1] != ['assume'] or events[index + 2][:1] != ['assert']:
        raise ValueError("The declaration has no adjacent source guard pair.")
    assume, asserted = events[index + 1], events[index + 2]
    if len(assume) != 2 or len(asserted) != 2:
        raise ValueError("The source guard pair is unsupported.")
    fields = _fields(assume[1])
    if len(fields) != 1:
        raise ValueError("The source register projection is ambiguous.")
    field_node, (register, field) = fields[0]
    if _replace(assume[1], field_node, declaration) != asserted[1]:
        raise ValueError("The source assertion does not identify the register guard.")
    definitions = [row for row in rocq_commands(consumed) if _words(row)[:2] == ['Definition', f'a{pc:x}']]
    if len(definitions) != 1:
        raise ValueError("The consumed instruction definition is missing or ambiguous.")
    words = _words(definitions[0])
    if ':=' not in words:
        raise ValueError("The consumed instruction has no trace body.")
    body = [token for token in words[words.index(':=') + 1:] if token not in {'(', ')'}]
    variable = declaration[1:]
    if any(body[i:i + 2] == ['Val_Symbolic', variable] for i in range(len(body))):
        raise ValueError("The declaration is used by the consumed trace.")
    declare = _tokens(f'Smt (DeclareConst {variable}%Z (Ty_BitVec {width}%N)) Mk_annot :t:')
    starts = [i for i in range(len(body)) if body[i:i + len(declare)] == declare]
    if len(starts) != 1:
        raise ValueError("The consumed declaration is missing or ambiguous.")
    next_event = _tokens('Assume (' + _render(assume[1]) + ') Mk_annot :t:')
    start = starts[0] + len(declare)
    if body[start:start + len(next_event)] != next_event:
        raise ValueError("The consumed register guard differs from its raw source.")
    return {'schema': 'source.register-origin.v1', 'pc': pc, 'declaration': declaration,
            'width': width, 'register': register, 'field': field, 'source_key': source_key,
            'raw': dict(raw_binding), 'rocq': dict(rocq_binding),
            'raw_assume': assume[1], 'raw_assert': asserted[1],
            'declaration_unused': True, 'values_selected': False,
            'proof_scripts_emitted': False}


def render_register_origin(record):
    """Render source registrations. Recheck both artifacts before emission."""
    expected = translate_unused_declaration(record['raw'], record['rocq'],
        pc=record['pc'], declaration=record['declaration'], width=record['width'],
        source_key=record['source_key'])
    if record != expected:
        raise ValueError("The register-origin record differs from its source.")
    suffix = record['source_key'][:16]
    pc, variable, width = record['pc'], int(record['declaration'][1:]), record['width']
    register, field, key = (json.dumps(record[name]) for name in ('register', 'field', 'source_key'))
    return ('Require Import ZesuSsz.Automation.SourceRegisterCapture196.\n'
            f'#[local] Instance source_unused_{suffix} :\n'
            f'  ZesuSourceUnusedDeclaration (BV 64%N {pc}%Z) {variable}%Z {width}%N := I.\n'
            f'#[local] Instance source_register_{suffix} :\n'
            f'  ZesuSourceRegisterRead (BV 64%N {pc}%Z) {register} {field} {width}%N {key} := I.\n')
