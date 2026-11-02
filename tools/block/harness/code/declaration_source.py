"""Classify direct and local-alias native calls in declaration proof bodies."""
from check_data_only_lemmas import IDENTIFIER, rocq_commands, rocq_tokens, top_level_positions


PROOF_DECLARATIONS = {'Goal', 'Lemma', 'Theorem', 'Fact', 'Remark', 'Corollary',
                      'Proposition', 'Example', 'Definition', 'Let', 'Instance'}
PROOF_ENDS = {'Qed', 'Defined', 'Admitted', 'Abort', 'Save'}
QUERIES = {'Check', 'Print', 'Locate', 'About', 'Search'}


def _command_head(values):
    """Remove locality and attributes without removing the command body."""
    position = 0
    while position < len(values):
        if values[position] in {'Local', 'Global'}:
            position += 1
        elif values[position:position + 2] == ['#', '[']:
            position += 2
            depth = 1
            while depth:
                if values[position] == '[':
                    depth += 1
                elif values[position] == ']':
                    depth -= 1
                position += 1
        else:
            break
    return values[position:]


def _references(values):
    return {value.rsplit('.', 1)[-1] for value in values
            if IDENTIFIER.fullmatch(value) is not None}


def _aliases(definitions, seeds):
    result = set(seeds)
    while True:
        expanded = result | {name for name, references in definitions.items()
                             if references & result}
        if expanded == result:
            return result
        result = expanded


def contains_native_proof(text):
    """Reject opaque execution rather than infer arbitrary Ltac semantics.

    Local aliases are conservative across scopes and redefinitions. Imported
    aliases require the Rocq environment and are outside this lexical check.
    """
    tokens = rocq_tokens(text)
    commands = rocq_commands(text)
    if tokens and tokens[-1][0] != '.':
        raise ValueError('The declaration source has an unfinished command.')
    definitions, opaque, ambiguous = {}, set(), []
    in_proof, ltac2_mode = False, False
    for command in commands:
        values = _command_head([token for token, _ in command])
        if not values:
            raise ValueError('The declaration source has an empty command.')
        references = _references(values)
        native = _aliases(definitions, {'zesu_block'})
        if values[0] in {'Ltac', 'Ltac2'} and values[1:2] != ['Eval']:
            assignments = top_level_positions(values, {':='})
            if (len(values) < 4 or not assignments or assignments[0] < 2 or
                    assignments[0] == len(values) - 1):
                raise ValueError('The declaration source has a malformed Ltac definition.')
            header, body = values[1:assignments[0]], values[assignments[0] + 1:]
            external = header[:2] == ['@', 'external']
            while header and header[0] in {'rec', 'mutable'}:
                header = header[1:]
            name = header[2] if external else header[0]
            if IDENTIFIER.fullmatch(name) is None:
                raise ValueError('The tactic declaration has an unsupported name.')
            name = name.rsplit('.', 1)[-1]
            used = _references(body)
            function = (header[0] not in {'Set', 'Notation', 'Type'} and
                        (len(header) > 1 and header[1] != ':' or body[:1] == ['fun']))
            if values[0] == 'Ltac2' and not (function or external) and used & native:
                raise ValueError('A Ltac2 initializer has an opaque native reference.')
            definitions.setdefault(name, set()).update(used)
            if values[0] == 'Ltac2' or 'ltac2' in used:
                opaque.add(name)
            if top_level_positions(body, {'with'}):
                ambiguous.append(used)
            continue
        native = _aliases(definitions, {'zesu_block'})
        if values[0] in PROOF_ENDS:
            in_proof = False
            continue
        if values[:4] == ['Set', 'Default', 'Proof', 'Mode']:
            ltac2_mode = values[4:] == ['"Ltac2"']
            continue
        inline = bool(references & {'ltac', 'ltac2'})
        evaluation = values[:2] == ['Ltac2', 'Eval']
        if inline or evaluation:
            if references & native:
                return True
            if ('ltac2' in references or evaluation or
                    references & _aliases(definitions, opaque)):
                raise ValueError('Opaque Ltac2 execution requires a Rocq environment.')
        if values[0] in QUERIES:
            continue
        if values[0] in PROOF_DECLARATIONS:
            in_proof = not top_level_positions(values, {':='})
            continue
        if values[:2] == ['Next', 'Obligation']:
            in_proof = True
            continue
        if values[0] == 'Proof':
            in_proof = True
        if in_proof:
            if references & native:
                return True
            if any(used & native for used in ambiguous):
                raise ValueError('A local native alias has ambiguous tactic bindings.')
            if ltac2_mode or references & _aliases(definitions, opaque):
                raise ValueError('Opaque tactic execution requires a Rocq environment.')
        elif references & native and values[0] not in QUERIES:
            raise ValueError('A native reference has an unsupported execution context.')
    if in_proof:
        raise ValueError('The declaration source leaves a proof open.')
    return False
