"""Render join declarations and their exact reflexive introductions."""
from copy import deepcopy

try:
    from .render_support import binders, definition_introduction_source, identifier
    from .forward_resources import _render_tree
except ImportError:
    from render_support import binders, definition_introduction_source, identifier
    from forward_resources import _render_tree


def _loop_bodies(join, alternatives):
    """Factor the shared continuation without selecting a source region class."""
    records = join.get('loop_classes', [])
    fields = {'seed', 'binders', 'relations', 'folds', 'edge_records', 'refusals', 'witness_plan'}
    if not records or len(records) != len(alternatives):
        raise ValueError('A loop head needs one seed per source region class')
    indices = [row['source_index'] for row in records]
    if (any(type(index) is not int or index < 0 for index in indices)
            or len(set(indices)) != len(indices)):
        raise ValueError('The loop source classes repeat or have invalid identifiers')
    by_class = {row['source_index']: row for row in records}
    if [row.get('source_index') for row in alternatives] != indices:
        raise ValueError('The rendered loop class order differs from its source order')
    continuation = join['continuation']['terminal_id']
    bodies = []
    for alternative in alternatives:
        row = by_class[alternative['source_index']]
        if not fields <= row.keys():
            raise ValueError('A loop class lacks its seven-field widening result')
        seed = row['seed']
        state = seed.state.to_dict() if hasattr(seed, 'state') else seed.to_dict() if hasattr(seed, 'to_dict') else seed
        if alternative.get('state') != state:
            raise ValueError('The rendered loop state differs from its bound class seed')
        if (any(not isinstance(row[field], list) for field in
                ['binders', 'relations', 'folds', 'edge_records', 'refusals'])
                or not isinstance(row['witness_plan'], dict)):
            raise ValueError('The loop widening result has an unsupported field shape')
        if (alternative.get('predecessor_pc') is not None
                or alternative.get('seed_pc') != join['boundary']['pc']):
            raise ValueError('A loop declaration must render its seed, not an incoming edge')
        resource = alternative['resource_boundary']
        if resource.get('block_status') != 'completed':
            raise ValueError('A loop class has incomplete ownership')
        tree = resource['tree']
        if (tree.get('kind') != 'sep'
                or tree.get('right') != {'kind': 'component', 'id': continuation}):
            raise ValueError('The loop continuation has a different source scope')
        components = {item['id']: item['source'] for item in resource['components']}
        if len(components) != len(resource['components']):
            raise ValueError('A loop class repeats an ownership component')
        if components.get(continuation) != join['continuation']['name']:
            raise ValueError('The loop classes do not share the exact named continuation')
        bodies.append((row, _render_tree(tree['left'], components)))
    return bodies


def join_declarations(join, *, entry_name, entry_module, parameters, imports):
    """Return source proposals. Later compilation and entailments check them."""
    identifier(entry_name, 'join entry name')
    identifier(entry_module, 'join entry module', qualified=True)
    loop = join['boundary'].get('status') == 'generated_loop_head'
    if not loop and join.get('pullback', {}).get('status') != 'generated':
        raise ValueError('A return join declaration needs its explicit exit pullback')
    alternatives = join['boundary']['alternatives']
    if not loop and (len(alternatives) != 1 or alternatives[0].get('predecessor_pc') is not None):
        raise ValueError('A join declaration needs one generated seed')
    resource = alternatives[0]['resource_boundary'] if alternatives else {}
    if not loop and resource.get('block_status') != 'completed':
        raise ValueError('A join declaration has incomplete ownership')
    if not imports or imports[0] != 'ZesuSsz.Automation.All':
        raise ValueError('The join declaration must start with the standard automation import')
    if loop:
        imports = list(imports)
        for row in join.get('loop_classes', []):
            required = row.get('required_imports', [])
            if not isinstance(required, list):
                raise ValueError('Loop declaration imports must be an ordered module list')
            imports.extend(required)
    for module in imports:
        identifier(module, 'join import', qualified=True)
    # All imports automation, but its dependencies do not re-export the
    # machine and Iris notation used in a generated resource expression.
    imports = [imports[0], 'isla.riscv64.riscv64', 'Coq.Lists.List', *imports[1:]]
    header = ''.join('Require Import ' + module + '.\n' for module in dict.fromkeys(imports))
    header += 'Import ListNotations.\nOpen Scope Z_scope.\n'
    typed = ''.join(f' ({name} : {kind})' for name, kind in binders(parameters, ['Sigma']))
    continuation = join['continuation']
    if loop:
        classes = _loop_bodies(join, alternatives)
        declarations, applications, witnesses = [], [], []
        arguments = ''.join(' (' + name + ')' for name, _ in binders(parameters, ['Sigma']))
        for row, body in classes:
            name = entry_name + 'Class' + str(row['source_index'])
            declarations.append(f'Definition {name} `{{!islaG Sigma}} `{{!threadG}}{typed} : iProp Sigma :=\n'
                                f'  ({body})%I.\n')
            applications.append('(' + name + arguments + ')')
            witnesses.append({'source_index': row['source_index'], 'target': name,
                              'witness_plan': deepcopy(row['witness_plan'])})
        definition = (f'Definition {entry_name} `{{!islaG Sigma}} `{{!threadG}}{typed} : iProp Sigma :=\n'
                      f'  let {continuation["name"]} : iProp Sigma := ({continuation["coq"]})%I in\n'
                      '  ((' + ' ∨ '.join(applications) + ') ∗ ' + continuation['name'] + ')%I.\n')
        declarations.append(definition)
        names = [entry_name + 'Class' + str(row['source_index']) for row, _ in classes] + [entry_name]
        structural = header + f'Require Import {entry_module}.\n'
        structural += '\n'.join(definition_introduction_source(text, name)
                                for text, name in zip(declarations, names))
        evidence = deepcopy(join['loop_classes'])
        for row in evidence:
            seed = row['seed']
            row['seed'] = seed.state.to_dict() if hasattr(seed, 'state') else seed.to_dict() if hasattr(seed, 'to_dict') else seed
        return {'entry': header + '\n'.join(declarations) + '\n' +
                    '\n'.join('#[global] Typeclasses Opaque ' + name + '.' for name in names) + '\n',
                'structural': structural, 'definition': definition, 'definitions': declarations,
                'witness_plans': witnesses, 'loop_classes': evidence,
                'proof_established': False, 'kernel_entailments': 'OPEN'}
    definition = (f'Definition {entry_name} `{{!islaG Sigma}} `{{!threadG}}{typed} : iProp Sigma :=\n'
                  f'  let {continuation["name"]} : iProp Sigma := ({continuation["coq"]})%I in\n'
                  f'  ({resource["body"]})%I.\n')
    structural = header + f'Require Import {entry_module}.\n' + definition_introduction_source(definition, entry_name)
    return {'entry': header + definition + f'\n#[global] Typeclasses Opaque {entry_name}.\n',
            'structural': structural, 'definition': definition,
            'witness_plan': deepcopy(join['seed'].join_witness_plan), 'proof_established': False}
