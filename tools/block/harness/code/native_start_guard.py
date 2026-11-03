"""Bind the requested theorem and compare its initial kernel state."""
from pathlib import Path
import hashlib
import json

from residual.modules import parse_module
from check_data_only_lemmas import rocq_commands, rocq_tokens
from entry_pilot_checker import complete_groups


def theorem_span(source, statement, name):
    source = Path(source)
    text = source.read_text()
    proofs = [proof for proof in parse_module(source) if proof.name == name]
    if len(proofs) != 1 or proofs[0].inline:
        raise ValueError('The requested theorem name is ambiguous or inline.')
    proof = proofs[0]
    lines = text.splitlines(keepends=True)
    start = sum(map(len, lines[:proof.declaration_line]))
    end = start + len(statement)
    if text[start:end] != statement:
        raise ValueError('The requested theorem span differs from its authenticated statement.')
    commands = [command for command in rocq_commands(text) if command and command[0][1] == start]
    if len(commands) != 1:
        raise ValueError('The requested theorem declaration is ambiguous.')
    last, offset = commands[0][-1]
    tail = offset + len(last)
    stop = rocq_tokens(text[tail:])[0]
    if stop[0] != '.' or text[start:tail + stop[1] + 1] != statement.rstrip():
        raise ValueError('The requested theorem span is not one complete declaration.')
    if lines[proof.proof_line].strip() != 'Proof.':
        raise ValueError('The requested theorem lacks its separate Proof sentence.')
    return {'name': name, 'source': {'path': str(source),
                'sha256': hashlib.sha256(source.read_bytes()).hexdigest()},
            'statement_sha256': hashlib.sha256(statement.encode()).hexdigest(),
            'declaration_start_byte': len(text[:start].encode()),
            'declaration_end_byte': len(text[:end].encode()),
            'proof_line': proof.proof_line, 'proof_character': len('Proof.') - 1}


def initial_kernel_goal(export):
    groups = complete_groups(export)
    if (len(groups['goals']) != 1 or
            any(groups[key] for key in ('stack', 'shelf', 'given_up'))):
        raise ValueError('The initial kernel state must contain exactly one active goal.')
    goal = groups['goals'][0]
    if not isinstance(goal.get('ty'), str) or not isinstance(goal.get('hyps'), list):
        raise ValueError('The initial kernel target or ordered context is malformed.')
    # Goal IDs can differ between independent starts. Keep every context field.
    return {'ty': goal['ty'], 'hyps': goal['hyps']}


def compare_initial(actual, reference):
    current = initial_kernel_goal(actual)
    expected = initial_kernel_goal(reference)
    if current != expected:
        raise ValueError('The initial kernel target or ordered context differs from the requested theorem.')
    return {'matched': True, 'actual_export': actual, 'reference_export': reference,
            'kernel_target_sha256': hashlib.sha256(current['ty'].encode()).hexdigest(),
            'ordered_context_sha256': hashlib.sha256(json.dumps(current['hyps'], sort_keys=True).encode()).hexdigest()}
