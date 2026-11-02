"""Permit native entry-point declarations while refusing calls and aliases."""
from check_data_only_lemmas import rocq_commands, rocq_tokens, top_level_positions


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


def contains_native_proof(text):
    """Exempt only Ltac1 declarations of the native entry point itself."""
    tokens = rocq_tokens(text)
    commands = rocq_commands(text)
    if tokens and tokens[-1][0] != '.':
        raise ValueError('The declaration source has an unfinished command.')
    for command in commands:
        values = _command_head([token for token, _ in command])
        if not values:
            raise ValueError('The declaration source has an empty command.')
        if values[0] in {'Ltac', 'Ltac2'} and values[1:2] != ['Eval']:
            assignments = top_level_positions(values, {':='})
            if (len(values) < 4 or not assignments or assignments[0] < 2 or
                    assignments[0] == len(values) - 1):
                raise ValueError('The declaration source has a malformed Ltac definition.')
            if (values[0:2] == ['Ltac', 'zesu_block'] and
                    not top_level_positions(values, {'with'})):
                continue
        if any(token.rsplit('.', 1)[-1] == 'zesu_block' for token in values):
            return True
    return False
