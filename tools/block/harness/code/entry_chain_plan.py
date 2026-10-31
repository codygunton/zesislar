"""Derive required block proofs. This module cannot launch a proof."""


def pc(value):
    if type(value) is not int or value < 0:
        raise ValueError('A PC must be a nonnegative integer.')
    return value


def derive(blocks, replacements, module_map):
    """Use direct CFG edges. Keep CFG block order and successor order."""
    if not isinstance(blocks, list) or not blocks:
        raise ValueError('The CFG must contain an ordered block list.')
    index = {}
    for row in blocks:
        start = pc(row['start'])
        if start in index:
            raise ValueError('The CFG repeats a block entry.')
        targets = row['successors']
        if not isinstance(targets, list):
            raise ValueError('The CFG successors must be an ordered list.')
        for target in targets:
            pc(target)
        index[start] = row
    if not isinstance(replacements, list) or not replacements:
        raise ValueError('The answer set must contain at least one replacement.')
    selected = set()
    for value in replacements:
        value = pc(value)
        if value in selected:
            raise ValueError('The answer set repeats an entry.')
        if value not in index:
            raise ValueError('A replacement is not a CFG block entry.')
        selected.add(value)
    result = []
    used_modules = set()
    for row in blocks:
        start = row['start']
        changed_targets = list(dict.fromkeys(x for x in row['successors'] if x in selected))
        if start not in selected and not changed_targets:
            continue
        module = module_map.get(start)
        if not isinstance(module, str) or not module:
            raise ValueError('An affected block lacks its bound native module.')
        if module in used_modules:
            raise ValueError('Two affected blocks share a native module.')
        used_modules.add(module)
        result.append({'pc': start, 'module': module,
                       'own_entry_changed': start in selected,
                       'changed_successor_entries': changed_targets,
                       'ordered_cfg_successors': list(row['successors'])})
    return result
