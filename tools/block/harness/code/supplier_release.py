"""Release a changed supplier only with an unchanged activation control."""
from entry_chain import read_bound, check_bindings
from entry_pilot_checker import complete_groups
from pathlib import Path
from check_data_only_lemmas import rocq_commands


def validate(record):
    required = {'module', 'activation_command', 'before', 'after'}
    if set(record) != required:
        raise ValueError('The supplier lacks its complete activation evidence.')
    # This gate concerns the shared public search path. Class-only controls
    # and declaration imports do not establish that path's activation.
    if record['activation_command'] not in {'zesu_block.','zesu_finish.','Hooks.zesu_liAStep.','ZesuSsz.Automation.Hooks.zesu_liAStep.'}:
        raise ValueError('The supplier control does not execute the public block tactic.')
    before, after = record['before'], record['after']
    if before['control_source']['sha256'] != after['control_source']['sha256']:
        raise ValueError('The supplier activation control changed.')
    for side in [before, after]:
        check_bindings([side['supplier_source'],side['control_source']])
        commands=[[word for word,_ in command] for command in rocq_commands(Path(side['control_source']['path']).read_text())]
        if [record['activation_command'][:-1]] not in commands:
            raise ValueError('The control source does not execute its activation command.')
        control = read_bound(side['control_receipt'])
        if control['source_sha256'] != side['control_source']['sha256']:
            raise ValueError('The control receipt names another source.')
        if control['module'] != record['module']:
            raise ValueError('The activation receipt names another supplier.')
        if control['activation_command'] != record['activation_command']:
            raise ValueError('The activation command differs from its receipt.')
    old = read_bound(before['control_receipt'])
    new = read_bound(after['control_receipt'])
    if old['statement_sha256'] != new['statement_sha256']:
        raise ValueError('The activation statement changed.')
    old_groups = complete_groups(old['export'])
    if old.get('outcome') != 'open' or not any(old_groups.values()):
        raise ValueError('The old supplier lacks a complete open activation state.')
    new_groups = complete_groups(new['export'])
    if any(new_groups.values()):
        raise ValueError('The new supplier leaves an activation obligation.')
    if (new.get('compile_file_success') is not True
            or new.get('verification_success') is not True
            or new.get('verification_method') != 'module_m'
            or new.get('assumptions') != [] or new.get('Qed') is not True):
        raise ValueError('The new supplier lacks exact kernel acceptance.')
    if before['supplier_source']['sha256'] == after['supplier_source']['sha256']:
        raise ValueError('The supplier source did not change.')
    return {'module':record['module'], 'source':after['supplier_source'],
            'control_source':after['control_source'], 'accepted':True}


def releases(rows):
    result = [validate(row) for row in rows]
    names = [row['module'] for row in result]
    if len(names) != len(set(names)):
        raise ValueError('A supplier release repeats a module.')
    return result
