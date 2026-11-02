"""Prepare literal entry-helper preservation while rule (d) stays disabled.

The planner does not expand helper equalities or construct after-state values.
Written helpers stay unsupported until an exact update recipe is reviewed.
"""
from copy import deepcopy
import hashlib
from pathlib import Path


def _sources(interface):
    bindings = interface.get('source_bindings')
    if not isinstance(bindings, dict) or not bindings:
        raise ValueError('An entry helper needs exact source bindings')
    for binding in bindings.values():
        if hashlib.sha256(Path(binding['path']).read_bytes()).hexdigest() != binding['sha256']:
            raise ValueError('An entry helper source differs from its bound hash')


def prepare_entry_helpers(interfaces, write_effects, *, enabled=False):
    """Return preparation records only. An enabled call always refuses.

    Every write needs its source event identity and owned-resource identity.
    Unrepresented or unknown writes remain explicit. An equal final value never
    establishes that a resource was unwritten.
    """
    if enabled:
        raise ValueError('Rule (d) has no reviewed execution release')
    effects = deepcopy(list(write_effects))
    ids = [(write.get('kind'), write.get('event_id'), tuple(write.get('provenance', {}).get('path', []))) for write in effects]
    if any(not isinstance(identity[1], str) or not identity[1] for identity in ids) or len(ids) != len(set(ids)):
        raise ValueError('Helper preparation needs unique source write identities')
    rows, owned = [], set()
    for interface in interfaces:
        _sources(interface)
        app = interface['literal_helper_application']
        footprint = interface['footprint']
        identity = app['seed_ownership_id']
        if identity in owned or identity != footprint.get('ownership_id'):
            raise ValueError('An entry helper footprint is duplicate or inconsistent')
        owned.add(identity)
        if (not isinstance(app.get('resource_owner'), str) or not isinstance(app.get('resource_name'), str)
                or not isinstance(app.get('ordered_arguments'), list) or not isinstance(app.get('exact_term'), str)):
            raise ValueError('An entry helper lacks its exact source application')
        if footprint.get('new_existential_values') != 0 or footprint.get('new_per_byte_facts') != 0:
            raise ValueError('Helper preparation cannot add witnesses or byte facts')
        recipe = interface['permitted_argument_update_recipe']
        if recipe.get('rule') != 'IDENTITY_ONLY':
            raise ValueError('The helper update recipe has no reviewed literal preservation form')
        if recipe.get('resource_arguments_before') != recipe.get('resource_arguments_after_literal_preservation'):
            raise ValueError('Literal preservation changes a helper argument')
        writes = [write for write in effects if write.get('ownership_id') == identity]
        unknown = [write for write in effects if write.get('ownership_id') is None and not write.get('outside_owned_footprint')]
        status = 'unknown_write_ownership' if unknown else 'unsupported_written_helper' if writes else 'literal_preservation_candidate'
        rows.append({'ownership_id': identity,
            'status': status,
            'literal_helper_application': deepcopy(app), 'footprint': deepcopy(footprint),
            'permitted_argument_update_recipe': deepcopy(recipe),
            'continuation': deepcopy(interface['continuation']),
            'source_bindings': deepcopy(interface['source_bindings']), 'ordered_write_effects': writes,
            'unknown_write_effects': unknown,
            'application_changed': False, 'scope_changed': False, 'fraction_changed': False,
            'new_witnesses': 0, 'new_per_byte_facts': 0,
            'reason': 'A source write has no established resource ownership.' if unknown else
                      'The source helper has no reviewed written-value update recipe.' if writes else None})
    uncovered = [write for write in effects if write.get('ownership_id') not in owned]
    return {'schema': 'entry-helper-preservation-preparation.v1', 'enabled': False,
        'helpers': rows, 'unrepresented_write_effects': uncovered,
        'all_write_effects_retained': True, 'emitted_helpers': [],
        'write_order_scope': 'Each source register or memory vector retains its order. No cross-kind total order is inferred.',
        'new_witnesses': 0, 'new_per_byte_facts': 0, 'whole_block_success': False,
        'written_helper_updates_supported': False, 'proof_ran': False}


def prepare_function_entry_helpers(report, interfaces, *, register_ownership, enabled=False):
    """Use path-specific optional register logs and existing owned memory writes.

    This function leaves its input report unchanged. Cuts and unreachable rows
    stay explicit. Missing register history prevents a preservation claim.
    """
    if enabled:
        raise ValueError('Rule (d) has no reviewed execution release')
    boundaries = []
    for boundary in report['boundaries']:
        row = {'pc': boundary['pc'], 'source_status': boundary['status'], 'alternatives': []}
        if boundary['status'] != 'generated':
            row['status'] = 'unchanged_cut_or_unreachable'
            boundaries.append(row)
            continue
        for index, alternative in enumerate(boundary['alternatives']):
            state = alternative['state']
            if 'register_writes' not in state:
                row['alternatives'].append({'index': index, 'status': 'missing_register_write_history',
                                            'emitted_helpers': []})
                continue
            merged = alternative.get('merged_source_paths', [])
            coverage = state.get('register_write_coverage')
            if ((coverage is not None and (not coverage.get('complete') or coverage.get('source_paths') != merged))
                    or (len(merged) > 1 and coverage is None)):
                row['alternatives'].append({'index': index, 'status': 'incomplete_merged_write_history',
                                            'emitted_helpers': []})
                continue
            effects = []
            for write in state['register_writes']:
                key = write['key']
                identities = {identity for name, identity in register_ownership.items()
                              if name == key or name.startswith(key + '.') or key.startswith(name + '.')}
                if len(identities) > 1:
                    raise ValueError('A register write has ambiguous resource ownership')
                effects.append({'kind': 'register', **deepcopy(write),
                                'ownership_id': next(iter(identities), None),
                                'outside_owned_footprint': not identities})
            for write in state['writes']:
                effects.append({'kind': 'memory', **deepcopy(write)})
            # Event identities carry a distinct instruction/path provenance.
            # Memory and register write vectors retain their original order.
            plan = prepare_entry_helpers(interfaces, effects)
            row['alternatives'].append({'index': index, 'status': 'preparation_only',
                                        'path': deepcopy(alternative.get('path')), 'plan': plan})
        row['status'] = 'preparation_only'
        boundaries.append(row)
    return {'schema': 'function-entry-helper-preparation.v1', 'enabled': False,
            'boundaries': boundaries, 'cuts': deepcopy(report['cuts']),
            'source_stops': deepcopy(report['stops']), 'input_report_changed': False,
            'emitted_assertions': [], 'proof_ran': False}
