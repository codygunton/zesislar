"""Run the pinned source engine (FP-20261115) from the entry seed, adding generated seeds.

A join is seeded only after every join that can reach it has its seed, so its
incoming edges are complete. A call's return site is seeded from the callee
summary (call_boundary.call_return_seed) once every path into the call block
is complete; the profile's `calls` rows name each callee spec. generalize_owned_join builds the seed from the
incoming edges; a join it refuses stays a cut, and the guards refuse what lies
beyond it. The run writes FORWARD.json, JOINS.json and the input receipt that
render_fp301_entries.py reads. No proof runs.

Usage: run_source_pass.py --inputs DIR --output DIR [--function NAME]
"""
from pathlib import Path
import argparse, hashlib, json, sys, time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/block'))
from boundary_guards import can_reach, cfg_successors
from call_boundary import CallRefused, call_return_seed
from function_profiles import add_return_alignment, load_profile
from loop_design import loop_head_seed
from forward_resource_design import evaluate_owned_function
from forward_resources import load_resource_vocabulary
from join_generalize import generalize_owned_join
from resource_seed import load_public_seed, seed_owned_resources
from system_shape_seed import seed_system_shapes


def bind(path):
    path = Path(path)
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def checked(row):
    if bind(row['path']) != row:
        raise ValueError('A source-pass input changed: ' + row['path'])
    return Path(row['path'])


def joins_of(function):
    loops = {int(loop['minimum_pc'], 0) for loop in function.get('loops', [])}
    predecessors = {}
    for block in function['blocks']:
        for target in block['successors']:
            predecessors.setdefault(target, set()).add(block['start'])
    return sorted(pc for pc, rows in predecessors.items() if len(rows) > 1 and pc not in loops)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inputs', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--function', default=None, help='function profile with call design rows')
    options = parser.parse_args()
    profile = load_profile(options.function) if options.function else None
    calls = profile.get('calls', []) if profile else []
    loop_designs = profile.get('loop_designs', []) if profile else []
    inputs, output = options.inputs.resolve(), options.output.resolve()
    output.mkdir(exist_ok=False)
    manifest = json.loads((inputs / 'SEED-MANIFEST.json').read_text())
    seed_path = checked(manifest['seed'])
    public = add_return_alignment(load_public_seed(seed_path, manifest['seed']['sha256']), profile)
    domain = json.loads(checked(manifest['domain']).read_text())
    shapes_path = inputs / 'SYSTEM-SHAPES.json'
    shapes = json.loads(shapes_path.read_text())
    vocabulary_path = inputs / 'VOCABULARY.json'
    vocabulary = load_resource_vocabulary(vocabulary_path, bind(vocabulary_path)['sha256'])
    index = json.loads(checked(manifest['trace_index']).read_text())
    function = json.loads(checked(index['function']).read_text())['functions'][0]
    traces = {int(pair['pc'], 0): checked(pair['raw']).read_text() for pair in index['instruction_pairs']}
    # Source register liveness at each block: a join drops an unheld binder only where no
    # successor reads a register that mentions it.
    from forward_design import source_liveness
    owned = seed_owned_resources(public, entry_pc=int(public['entry_pc'], 0), vocabulary=vocabulary,
                                 constants=domain['constants'], facts=domain['projection']['facts'])
    owned.state = seed_system_shapes(owned.state, shapes['rows'],
                                     collection_ownership_id=shapes['collection_ownership_id']).state
    terminal, = [row['id'] for row in owned.ownership['components'] if row['source'] == 'True']
    level1 = ROOT / 'ZesuSsz/Contracts/Level1.v'
    continuation = {'name': 'K', 'coq': 'K', 'source_binding': {'source': str(level1) + '#IslarisContractSpec'},
                    'terminal_id': terminal}
    joins = joins_of(function)
    successors = cfg_successors(function)
    seeds = {public['entry_pc']: owned}
    liveness = {hex(pc): registers for pc, registers in source_liveness(
        function, traces, {int(public['entry_pc'], 0): owned.state}).items()}
    # The seed whose ownership tree a seed's edges share: an entry or call-return seed is its own root.
    roots = {public['entry_pc']: public['entry_pc']}
    plans, refusals, rounds = {}, {}, []
    call_seeds, call_reports = {}, {}
    started = time.monotonic_ns()
    while True:
        report = evaluate_owned_function(function, traces, seeds, vocabulary=vocabulary)
        added = None
        for call in calls:
            site = call['return_site_pc']
            if site in seeds:
                continue
            block = next(row for row in report['calls'] if row['return_pc'] == site)['block_pc']
            boundary = next(row for row in report['boundaries'] if row['pc'] == block)
            edges = [stop for stop in report['stops'] if stop['reason'] == 'call_boundary'
                     and stop['target_pc'] == site]
            origins = {stop['seed_pc'] for stop in edges}
            if boundary['reaching_stops'] or not edges or len({roots.get(pc) for pc in origins}) != 1:
                refusals[site] = ('no path reaches the call' if not edges else
                                  'incomplete call block: ' + str(boundary['reaching_stops'][:1])
                                  if boundary['reaching_stops'] else 'call-site paths from different roots')
                continue
            try:
                seed, call_public, call_report = call_return_seed(
                    edges, call=call, function_root=ROOT, root_seed=seeds[roots[next(iter(origins))]],
                    shapes=shapes, vocabulary=vocabulary, constants=domain['constants'])
            except CallRefused as error:
                refusals[site] = 'call boundary refused: ' + str(error)
                continue
            seeds[site], roots[site] = seed, site
            call_seeds[site] = {'public': call_public, 'state': seed.state.to_dict(), 'facts': seed.facts}
            call_reports[site] = call_report
            refusals.pop(site, None)
            added = site
            break
        for design in loop_designs if added is None else []:
            head = profile.pc(design['head'])
            entry = next(row for row in report['boundaries'] if row['pc'] == profile.pc(design['entry_predecessor']))
            edges = [row for row in next(b for b in report['boundaries'] if b['pc'] == head)['alternatives']
                     if row['predecessor_pc'] == entry['pc']]
            origins = {roots.get(row['seed_pc']) for row in edges}
            if head in seeds or entry['reaching_stops'] or not edges or len(origins) != 1:
                continue
            root = origins.pop()
            try:
                seeds[head] = loop_head_seed(report, design, profile, root_seed=seeds[root],
                                             vocabulary=vocabulary, continuation=continuation,
                                             live_registers=liveness.get(head))
            except ValueError as error:
                refusals[head] = 'loop head seed refused: ' + str(error)
                continue
            roots[head] = root
            refusals.pop(head, None)
            added = head
            break
        for pc in joins if added is None else []:
            if hex(pc) in seeds:
                continue
            if any(other != pc and hex(other) not in seeds and can_reach(successors, other, pc)
                   for other in joins):
                continue
            boundary = next(row for row in report['boundaries'] if int(row['pc'], 0) == pc)
            incoming = [row for row in boundary['alternatives'] if row['predecessor_pc'] is not None]
            if not incoming or boundary['reaching_stops']:
                refusals[hex(pc)] = ('no incoming edge' if not incoming else
                                     'incomplete incoming edges: ' + str(boundary['reaching_stops'][0]))
                continue
            origins = {row['seed_pc'] for row in incoming}
            if len({roots.get(origin) for origin in origins}) != 1:
                refusals[hex(pc)] = 'join edges from different roots: ' + ', '.join(sorted(origins))
                continue
            root = roots[next(iter(origins))]
            try:
                # Edges through an earlier join seed are aligned on their root seed's tree.
                designs = profile.get('join_designs', {}) if profile else {}
                joined = generalize_owned_join(incoming, original_seed=seeds[root], entry_pc=pc, vocabulary=vocabulary,
                                               continuation=continuation, outer_names=['args', 'returnAddress'],
                                               design_facts=next((facts for suffix, facts in designs.items()
                                                                  if profile.pc(suffix) == hex(pc)), []),
                                               live_registers=liveness.get(hex(pc)))
            except ValueError as error:
                refusals[hex(pc)] = 'join generalization refused: ' + str(error) + ' (edge seeds: ' + \
                    ', '.join(sorted(origins)) + ')'
                continue
            seeds[hex(pc)] = joined['seed']
            roots[hex(pc)] = root
            refusals.pop(hex(pc), None)
            plans[hex(pc)] = {'edges': len(incoming), 'edge_seeds': sorted(origins),
                              'binders': [row['name'] for row in joined['plan']['owned_binders']],
                              'relations': [row.get('coq') for row in joined['plan']['relations']],
                              'common_guards': len(joined['plan']['common_guards']),
                              'join_refusals': joined['plan']['join_refusals'],
                              **({'dropped_binders': joined['plan']['dropped_binders']}
                                 if joined['plan'].get('dropped_binders') else {})}
            added = hex(pc)
            break
        rounds.append({'seeds': sorted(seeds), 'added': added})
        if added is None:
            break
    elapsed = time.monotonic_ns() - started
    report['liveness'] = liveness
    (output / 'FORWARD.json').write_text(json.dumps(report, indent=1) + '\n')
    rows = []
    for boundary in report['boundaries']:
        rows.append({'pc': boundary['pc'], 'status': boundary['status'],
                     'alternatives': len(boundary['alternatives']),
                     'completed': sum(row.get('resource_boundary', {}).get('block_status') == 'completed'
                                      for row in boundary['alternatives']),
                     'reaching_stops': boundary['reaching_stops']})
    (output / 'JOINS.json').write_text(json.dumps({'joins': [hex(pc) for pc in joins], 'plans': plans,
                                                   'refusals': refusals, 'rounds': rounds,
                                                   'roots': roots, 'calls': call_reports}, indent=2) + '\n')
    (output / 'CALL-SEEDS.json').write_text(json.dumps(
        {'schema': 'fp301.call-return-seeds.v1', 'seeds': call_seeds,
         'calls': calls}, indent=1, ensure_ascii=False) + '\n')
    receipt = {'source_pass': bind(output / 'FORWARD.json'), 'level1_K_source': bind(level1),
               'vocabulary': bind(vocabulary_path), 'system_shapes': bind(shapes_path),
               'engine': bind(ROOT / 'tools/block/FP-20261115.json'), 'joins': bind(output / 'JOINS.json'),
               'call_seeds': bind(output / 'CALL-SEEDS.json')}
    (output / 'INPUT-RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    stops = {}
    for stop in report['stops']:
        stops[stop['reason']] = stops.get(stop['reason'], 0) + 1
    result = {'status': 'SOURCE_PASS_ONLY', 'function': function['name'], 'input_receipt': bind(output / 'INPUT-RECEIPT.json'),
              'seed_manifest': bind(inputs / 'SEED-MANIFEST.json'), 'boundaries': rows,
              'reached': sum(row['alternatives'] > 0 for row in rows),
              'complete': sum(row['alternatives'] > 0 and not row['reaching_stops'] for row in rows),
              'stops': stops, 'elapsed_monotonic_ns': elapsed, 'proof_calls': 0}
    (output / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'reached': result['reached'], 'complete': result['complete'], 'blocks': len(rows),
                      'seeded_joins': sorted(plans), 'join_refusals': refusals, 'stops': stops}))


if __name__ == '__main__':
    main()
