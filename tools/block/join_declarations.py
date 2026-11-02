"""Render join declarations and their exact reflexive introductions."""
from copy import deepcopy

try:
    from .render_support import binders, definition_introduction_source, identifier
except ImportError:
    from render_support import binders, definition_introduction_source, identifier


def join_declarations(join, *, entry_name, entry_module, parameters, imports):
    """Return source proposals. Later compilation and entailments check them."""
    identifier(entry_name, 'join entry name')
    identifier(entry_module, 'join entry module', qualified=True)
    if join.get('pullback', {}).get('status') != 'generated':
        raise ValueError('A return join declaration needs its explicit exit pullback')
    alternatives = join['boundary']['alternatives']
    if len(alternatives) != 1 or alternatives[0].get('predecessor_pc') is not None:
        raise ValueError('A join declaration needs one generated seed')
    resource = alternatives[0]['resource_boundary']
    if resource.get('block_status') != 'completed':
        raise ValueError('A join declaration has incomplete ownership')
    if not imports or imports[0] != 'ZesuSsz.Automation.All':
        raise ValueError('The join declaration must start with the standard automation import')
    for module in imports:
        identifier(module, 'join import', qualified=True)
    # All imports automation, but its dependencies do not re-export the
    # machine and Iris notation used in a generated resource expression.
    imports = [imports[0], 'isla.riscv64.riscv64', 'Coq.Lists.List', *imports[1:]]
    header = ''.join('Require Import ' + module + '.\n' for module in dict.fromkeys(imports))
    header += 'Import ListNotations.\nOpen Scope Z_scope.\n'
    typed = ''.join(f' ({name} : {kind})' for name, kind in binders(parameters, ['Sigma']))
    continuation = join['continuation']
    definition = (f'Definition {entry_name} `{{!islaG Sigma}} `{{!threadG}}{typed} : iProp Sigma :=\n'
                  f'  let {continuation["name"]} : iProp Sigma := ({continuation["coq"]})%I in\n'
                  f'  ({resource["body"]})%I.\n')
    structural = header + f'Require Import {entry_module}.\n' + definition_introduction_source(definition, entry_name)
    return {'entry': header + definition + f'\nTypeclasses Opaque {entry_name}.\n',
            'structural': structural, 'definition': definition,
            'witness_plan': deepcopy(join['seed'].join_witness_plan), 'proof_established': False}
