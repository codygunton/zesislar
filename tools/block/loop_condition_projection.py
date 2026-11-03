"""Project loop conditions without strengthening an emitted entry's evaluator."""
from copy import deepcopy


def project_loop_conditions(conditions, relations, dependencies, *, render, recheck=None):
    """Keep only checked relations and their renderable source conditions.

    dependencies lists original condition indices for each relation. A caller
    can supply one source checker after refusing conditions. That checker must
    return checked=True and exact original indices. No iteration adds facts.
    """
    if len(relations) != len(dependencies):
        raise ValueError('Every loop relation needs its condition dependencies')
    original = deepcopy(conditions)
    rendered, refused, records, refusals = {}, set(), [], []
    for index, condition in enumerate(original):
        try:
            text = render(deepcopy(condition))
            if not isinstance(text, str) or not text.strip():
                raise ValueError('The condition has no rendered proposition')
            rendered[index] = text
        except ValueError as error:
            refused.add(index)
            refusals.append({'kind': 'loop_condition_refusal', 'condition_index': index,
                'condition': deepcopy(condition), 'reason': str(error)})
    retained, relation_records, needed = [], [], set()
    allowed = sorted(rendered)
    for index, (relation, source_dependencies) in enumerate(zip(relations, dependencies)):
        if (not isinstance(source_dependencies, list)
                or any(type(item) is not int or not 0 <= item < len(original)
                       for item in source_dependencies)
                or len(set(source_dependencies)) != len(source_dependencies)):
            raise ValueError('A loop relation has invalid condition indices')
        required = list(source_dependencies)
        result = None
        if refused.intersection(required) and recheck is not None:
            result = recheck(deepcopy(relation),
                [(item, deepcopy(original[item])) for item in allowed])
            if isinstance(result, dict) and result.get('checked') is True:
                required = result.get('condition_dependencies')
                if (not isinstance(required, list)
                        or any(type(item) is not int or item not in rendered for item in required)
                        or len(set(required)) != len(required)
                        or not result.get('source_evidence')):
                    raise ValueError('The loop recheck lacks exact renderable dependencies and source evidence')
        failed = sorted(refused.intersection(source_dependencies))
        accepted = not refused.intersection(required)
        if failed and recheck is not None:
            accepted = isinstance(result, dict) and result.get('checked') is True
        if not accepted:
            refusal = {'kind': 'loop_relation_refusal', 'relation_index': index,
                'relation': deepcopy(relation), 'condition_dependencies': list(source_dependencies),
                'refused_condition_indices': failed,
                'reason': 'The source relation depends on a refused condition',
                'recheck': deepcopy(result)}
            refusals.append(refusal)
        else:
            retained.append(deepcopy(relation))
            needed.update(required)
        relation_records.append({'relation_index': index, 'retained': accepted,
            'original_dependencies': list(source_dependencies),
            'condition_dependencies': list(required) if accepted else [],
            'recheck': deepcopy(result)})
    for index, condition in enumerate(original):
        status = 'retained' if index in needed else 'refused' if index in refused else 'unused'
        records.append({'condition_index': index, 'condition': deepcopy(condition),
            'status': status, 'rendered': rendered.get(index)})
        if status == 'unused':
            refusals.append({'kind': 'loop_unused_condition', 'condition_index': index,
                'condition': deepcopy(condition),
                'reason': 'No retained checked relation requires this condition'})
    indices = sorted(needed)
    return {'original_conditions': original,
        'conditions': [deepcopy(original[index]) for index in indices],
        'condition_indices': indices, 'condition_records': records,
        'relations': retained, 'relation_records': relation_records,
        'refusals': refusals, 'kernel_entailments': 'OPEN'}
