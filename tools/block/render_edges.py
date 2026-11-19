"""Lane prototype (researcher/generator): the per-edge data of a function's rendered entries.

For each successor edge (block entry variant -> successor entry variant) the record holds
  - the binder map: every successor binder with the block-entry binder or term it stands for,
  - the successor facts that are unchanged block-entry facts (text identity over identity binders),
  - the new facts, each with the block-entry history facts that share a ghost binder with it,
  - for a call site, the call plan of JOINS.json `calls[]`.
`--rocq FILE` also writes one `ZesuHistEdge` instance per edge whose both ends have a history
(ZESU_ENTRY_HIST=wrap entries); each proof is the same data-only script.

Usage: render_edges.py --function NAME --entries RESULT.json --forward DIR --cfg FUNCTION.json
       --output EDGES.json [--rocq Edges.v]
"""
from pathlib import Path
import argparse, json, re, sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import entry_hist
from entry_hist import mentions, normal, telescope, unwrap
from function_profiles import load_profile, pilot_header
from symbolic_state import Expr


def coq(expression, reads=()):
    """The Coq term of an expression; a symbolic byte read renders as its owned-array lookup
    (`owned_read_renderings` of the path's resource boundary). None if a read has no rendering."""
    table = {json.dumps(row['expression'], sort_keys=True): row['term'] for row in reads}

    def owned(value):
        if value.get('op') == 'owned_array_byte':
            term = table.get(json.dumps(value, sort_keys=True))
            if term is None:
                raise ValueError('no owned rendering')
            return {'op': 'input', 'width': 8, 'value': term}
        return {**value, 'args': [owned(argument) for argument in value['args']]} if 'args' in value else value
    try:
        return Expr.from_dict(owned(expression)).coq()
    except ValueError:
        return None


def variants(cases):
    """{pc: [meta]} of the rendered entry variants that carry history data."""
    result = {}
    for case in cases:
        for meta in case.get('hist', {}).values():
            if 'hidden' in meta:   # A frame-slot-only loop record carries no history data.
                # An entry slot belongs to one incoming edge (its predecessor block and slot).
                result.setdefault(case['pc'], []).append({**meta, 'slot': case.get('slot')})
    return result


def binder_names(meta, key):
    return [binder['name'] for binder in meta[key]]


def edge_kind(profile, forward, calls, pre_pc, succ_pc):
    if succ_pc == 'function_return':
        return 'return'
    if any(row['return_site_pc'] == succ_pc and row['call_site_pc'] and
           int(pre_pc, 16) <= int(row['call_site_pc'], 16) < int(succ_pc, 16) for row in calls.values()):
        return 'call_return'
    boundary = next(row for row in forward['boundaries'] if row['pc'] == succ_pc)
    edges = [row for row in boundary['alternatives'] if row['predecessor_pc'] == pre_pc]
    if boundary['status'] == 'generated_loop_head':
        return 'loop_back' if edges and all(row['back_edge'] for row in edges) else 'loop_entry'
    if boundary['status'] == 'generated_join':
        return 'join'
    return 'forward'


def binder_map(kind, pre, succ, witnesses, loop_values, loop_binders=()):
    """[{succ, role, pre, identity, expression}] for every successor binder."""
    pre_live, pre_ghost = binder_names(pre, 'live'), binder_names(pre, 'ghost')
    rows = []
    for role in ('live', 'ghost'):
        for binder in succ[role]:
            name = binder['name']
            row = {'succ': name, 'type': binder['type'], 'role': role, 'pre': None, 'identity': False,
                   'expression': None}
            source = 'live' if name in pre_live else 'ghost' if name in pre_ghost else None
            if role == 'live' and source == 'ghost':
                source = None   # A resource value cannot be a binder that the block entry hides.
            if name in loop_values:
                row['expression'] = loop_values[name]
                row['identity'] = loop_values[name] == name and source is not None
            elif name in witnesses:
                row['expression'] = witnesses[name]
                row['identity'] = unwrap(witnesses[name]) == name and source is not None
            elif name in loop_binders:
                pass   # A loop register or the index without one term on this edge: no identity.
            elif source is not None:
                # The same seed tree (or a system or trace witness across a call): the name keeps its value.
                row['identity'] = True
            if row['identity']:
                row['pre'] = {'name': name, 'role': source}
                row['expression'] = name
            elif row['expression'] is not None and unwrap(row['expression']) in pre_live:
                # The successor binder is a block-entry live binder under another name.
                row['rename'] = unwrap(row['expression'])
            rows.append(row)
    return rows


MASK_FACT = re.compile(r'bool_decide|bv_and|bv_extract|bv_unsigned')


def free_witnesses(succ, rows):
    """A new ghost binder of type bv that only closed facts mention gets the witness 0.

    Such a binder (a system-register or trace witness) is tied to no resource and to no other
    binder, so any value that satisfies its own facts will do; with 0 the facts compute."""
    others = [binder['name'] for binder in succ['live'] + succ['ghost']]
    for row in rows:
        if row['role'] != 'ghost' or row['identity'] or row['expression'] is not None:
            continue
        match = re.fullmatch(r'bv (\d+)', row['type'])
        facts = [fact for fact in succ['hidden'] if mentions(row['succ'], fact)]
        if match and facts and all(MASK_FACT.search(fact) and not any(
                mentions(name, fact) for name in others if name != row['succ']) for fact in facts):
            row['expression'] = '(BV ' + match[1] + '%N 0%Z)'
            row['free'] = True


def classify_facts(pre, succ, rows):
    identity = {row['succ'] for row in rows if row['identity'] or row.get('rename')}
    renames = {row['succ']: row['rename'] for row in rows if row.get('rename')}
    succ_binders = binder_names(succ, 'live') + binder_names(succ, 'ghost')
    pre_ghost = binder_names(pre, 'ghost')
    pre_index = {}
    for where in ('hidden', 'visible'):
        for index, fact in enumerate(pre[where]):
            pre_index.setdefault(normal(fact), (where, index))
    free = {row['succ']: row['expression'] for row in rows if row.get('free')}
    unchanged, new, closed = [], [], []
    for where in ('visible', 'hidden'):
        for index, fact in enumerate(succ[where]):
            named = [name for name in succ_binders if mentions(name, fact)]
            origin = pre_index.get(normal(substitute(fact, renames)))
            if origin is not None and all(name in identity for name in named):
                unchanged.append({'succ': [where, index], 'pre': list(origin)})
                continue
            if where == 'hidden' and named and all(name in free for name in named):
                closed.append({'succ': [where, index], 'witness': {name: free[name] for name in named}})
                continue
            # loop-seal lane: a new history fact whose first conjunct is a block-entry history fact
            # (forward entries state a guard with its unsigned views; a loop class the guard only)
            # is proved inside the edge from that fact (`zesu_hist_view`).
            # The reverse (a loop class keeps the guard of a forward fact) is its first projection.
            renamed = substitute(fact, renames)
            head = key(conjuncts(renamed)[0])
            view = next((position for position, other in enumerate(pre['hidden']) if key(other) == head), None)
            if (where == 'hidden' and view is not None and len(conjuncts(renamed)) > 1
                    and all(name in identity for name in named)):
                unchanged.append({'succ': [where, index], 'pre': ['hidden', view], 'view': True})
                continue
            projection = next((position for position, other in enumerate(pre['hidden'])
                               if len(conjuncts(other)) > 1 and key(conjuncts(other)[0]) == key(renamed)), None)
            if where == 'hidden' and projection is not None and all(name in identity for name in named):
                unchanged.append({'succ': [where, index], 'pre': ['hidden', projection], 'projection': True})
                continue
            ghosts = [name for name in pre_ghost if name in identity and mentions(name, fact)]
            support = [position for position, other in enumerate(pre['hidden'])
                       if any(mentions(name, other) for name in ghosts)]
            new.append({'succ': [where, index], 'text': fact, 'binders': named, 'support': support})
    return unchanged, new, closed


def key(text):
    """Text identity up to whitespace and parentheses (the edge proof checks the match)."""
    return re.sub(r'[()\s]', '', text)


def conjuncts(text):
    """The top-level conjuncts of a fact."""
    text = unwrap(text)
    parts, depth, start = [], 0, 0
    for position, character in enumerate(text):
        depth += (character in '([') - (character in ')]')
        if depth == 0 and text.startswith('/\\', position):
            parts.append(text[start:position].strip())
            start = position + 2
    return parts + [text[start:].strip()]


def loop_back_values(profile, forward, succ_pc, pre_pc):
    """Loop registers and index after one iteration, as terms over the loop-head binders."""
    design = next((row for row in profile.get('loop_designs', []) if profile.pc(row['head']) == succ_pc), None)
    if design is None:
        return {}
    boundary = next(row for row in forward['boundaries'] if row['pc'] == succ_pc)
    edges = [row for row in boundary['alternatives'] if row['predecessor_pc'] == pre_pc and row['back_edge']]
    values = {}
    for register, binder in design.get('registers', {}).items():
        terms = {coq(row['state']['registers'][register], row['resource_boundary'].get('owned_read_renderings', []))
                 for row in edges if register in row['state']['registers']}
        if len(terms) == 1 and None not in terms:
            values[binder] = terms.pop()
    if design.get('index'):
        values[design['index']] = '(' + design['index'] + ' + 1)'
    return values


def loop_entry_values(profile, forward, succ_pc, pre_pc):
    """Loop registers at the first entry, as terms over the entry predecessor's binders; the index is 0."""
    design = next((row for row in profile.get('loop_designs', []) if profile.pc(row['head']) == succ_pc), None)
    if design is None:
        return {}
    boundary = next(row for row in forward['boundaries'] if row['pc'] == succ_pc)
    edges = [row for row in boundary['alternatives'] if row['predecessor_pc'] == pre_pc and not row['back_edge']]
    values = {}
    for register, binder in design.get('registers', {}).items():
        terms = {coq(row['state']['registers'][register], row['resource_boundary'].get('owned_read_renderings', []))
                 for row in edges if register in row['state']['registers']}
        if len(terms) == 1 and None not in terms:
            values[binder] = terms.pop()
    if design.get('index'):
        values[design['index']] = '0'
    return values


def substitute(text, renames):
    """Rename binders simultaneously (a new name may be another binder's old name)."""
    if not renames:
        return text
    pattern = r"(?<![\w'.])(" + '|'.join(re.escape(name) for name in sorted(renames, key=len, reverse=True)) + r")(?![\w'])"
    return re.sub(pattern, lambda match: renames[match[1]], text)


def rocq_edge(edge, pre, succ, index):
    """One ZesuHistEdge instance with its data-only proof."""
    rows = edge['binder_map']
    identity = {row['succ'] for row in rows if row['identity']}
    pre_live, pre_ghost = binder_names(pre, 'live'), binder_names(pre, 'ghost')
    succ_ghost = binder_names(succ, 'ghost')
    # A successor live binder that is no identity gets its own variable.
    renames = {binder['name']: binder['name'] + '_succ' for binder in succ['live']
               if binder['name'] not in identity and binder['name'] in pre_live + pre_ghost}
    renames.update({row['succ']: row['rename'] for row in rows if row.get('rename')})
    variables = [*pre['parameters'], *pre['live']]
    names = {binder['name'] for binder in variables}
    for binder in succ['live']:
        name = renames.get(binder['name'], binder['name'])
        if name not in names:
            variables.append({'name': name, 'type': binder['type']})
            names.add(name)
    new_hidden = [row for row in edge['new'] if row['succ'][0] == 'hidden']
    free = {row['succ']: row['expression'] for row in rows if row.get('free')}
    closed = {tuple(row['succ']) for row in edge.get('closed', [])}
    new_ghost = [name for name in succ_ghost if name not in identity and name not in free]
    ghost_renames = {name: name + '_new' for name in new_ghost if name in pre_live + pre_ghost}
    support = sorted({position for row in new_hidden for position in row['support']})
    new_texts = [substitute(row['text'], {**renames, **ghost_renames}) for row in new_hidden]
    used = [binder for binder in pre['ghost']
            if any(mentions(binder['name'], text) for text in new_texts + [pre['hidden'][p] for p in support])]
    # Second agent: a block-entry fact that is visible at the entry and hidden at the successor is carried
    # as a premise of the edge (the automation proves it from its own context).
    carried = [pre['visible'][row['pre'][1]] for row in sorted(edge['unchanged'], key=lambda row: row['succ'][1])
               if row['succ'][0] == 'hidden' and row['pre'][0] == 'visible'
               and not row.get('view') and not row.get('projection')]
    body = ' ∗ '.join(['⌜' + text + '⌝' for text in new_texts + carried] + ['True'])
    bound = [{'name': ghost_renames.get(binder['name'], binder['name']), 'type': binder['type']}
             for binder in succ['ghost'] if binder['name'] in new_ghost]
    if bound:
        body = '∃ ' + telescope(bound) + ', ' + body
    for position in reversed(support):
        body = '⌜' + pre['hidden'][position] + '⌝ -∗ ' + body
    if used:
        body = '∀ ' + telescope(used) + ', ' + body
    application = lambda meta, table: meta['hist'] + ''.join(
        ' (' + table.get(binder['name'], binder['name']) + ')'
        for binder in meta['parameters'] + meta.get('hist_live', meta['live']))
    # loop-seal lane: an instance quantifies only over the variables its statement mentions.
    statement = application(pre, {}) + ' ' + application(succ, renames) + ' ' + body
    variables = [binder for binder in variables if binder in pre['parameters'] or mentions(binder['name'], statement)]
    name = 'zesu_hist_edge_' + str(index)
    lines = ['(* ' + edge['pre_entry'] + ' -> ' + edge['succ_entry'] + ' (' + edge['kind'] + ') *)',
             'Global Instance ' + name + ' ' + telescope(variables) + ' :',
             '  ZesuHistEdge (PROP := iProp Sigma)',
             '    (' + application(pre, {}) + ')',
             '    (' + application(succ, renames) + ')',
             '    (' + body + ')%I.',
             'Proof.',
             '  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold ' + pre['hist'] + ' in Hh.']
    facts = ['HF' + str(position) for position in range(len(pre['hidden']))]
    pattern = binder_names(pre, 'ghost') + facts
    if not pre['hidden']:
        lines.append('  clear Hh.')
    elif len(pattern) == 1:
        lines.append('  pose proof Hh as HF0.')
    else:
        lines.append('  destruct Hh as (' + ' & '.join(pattern) + ').')
    lines.append('  iIntros "HN".')
    if new_texts or carried:
        arguments = [binder['name'] for binder in used] + ['HF' + str(position) for position in support]
        term = '("HN" $! ' + ' '.join(arguments) + ')' if arguments else '"HN"'
        intro = ' & '.join(['%HN' + str(position) for position in range(len(new_texts))]
                           + ['%HC' + str(position) for position in range(len(carried))]) + ' & _'
        lines.append('  iDestruct ' + term + ' as ' + ('(' + ' '.join(b['name'] for b in bound) + ') ' if bound else '')
                     + '"(' + intro + ')".')
    lines.append('  iPureIntro. apply zesu_hist_intro. unfold ' + succ['hist'] + '.')
    if succ['ghost']:
        lines.append('  exists ' + ', '.join(free.get(name, ghost_renames.get(name, name)) for name in succ_ghost) + '.')
    if not succ['hidden']:
        lines.append('  exact I.')
    else:
        proofs, fresh, kept = [], 0, 0
        origin = {tuple(row['succ']): row['pre'] for row in edge['unchanged']}
        views = {tuple(row['succ']) for row in edge['unchanged'] if row.get('view')}
        projections = {tuple(row['succ']) for row in edge['unchanged'] if row.get('projection')}
        for position in range(len(succ['hidden'])):
            source = origin.get(('hidden', position))
            if ('hidden', position) in closed:
                proofs.append('by vm_compute')
            elif source is None:
                proofs.append('exact HN' + str(fresh))
                fresh += 1
            elif source[0] == 'hidden' and ('hidden', position) in projections:
                proofs.append('exact (proj1 HF' + str(source[1]) + ')')
            elif source[0] == 'hidden' and ('hidden', position) in views:
                proofs.append('zesu_hist_view HF' + str(source[1]))
            elif source[0] == 'hidden':
                proofs.append('exact HF' + str(source[1]))
            else:
                proofs.append('exact HC' + str(kept))
                kept += 1
        for proof in proofs[:-1]:
            lines.append('  split; [' + proof + '|].')
        lines.append('  ' + proofs[-1] + '.')
    lines.append('Qed.')
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--function', required=True)
    parser.add_argument('--entries', type=Path, required=True)
    parser.add_argument('--forward', type=Path, required=True)
    parser.add_argument('--cfg', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rocq', type=Path)
    parser.add_argument('--rocq-blocks', default=None, help='comma list of block keys: instances of these blocks only')
    options = parser.parse_args()
    profile = load_profile(options.function)
    result = json.loads(options.entries.read_text())
    forward = json.loads((options.forward / 'FORWARD.json').read_text())
    joins = json.loads((options.forward / 'JOINS.json').read_text())
    seeds = json.loads((options.forward / 'JOIN-SEEDS.json').read_text())['seeds']
    function = json.loads(options.cfg.read_text())['functions'][0]
    entries = variants(result['cases'])
    calls = joins.get('calls', {})
    edges, rocq, used_entries = [], [], set()
    selected = ({profile.pc(key) for key in options.rocq_blocks.split(',')} if options.rocq_blocks else None)
    for block in function['blocks']:
        pre_pc = hex(block['start'])
        targets = [hex(target) for target in sorted(block['successors'])] or ['function_return']
        for succ_pc in targets:
            if pre_pc not in entries or succ_pc not in entries:
                continue
            kind = edge_kind(profile, forward, calls, pre_pc, succ_pc)
            witnesses = {}
            for row in seeds.get(succ_pc, {}).get('join_edges', []):
                if row['predecessor_pc'] == pre_pc:
                    for witness in row['ordered_witnesses']:
                        witnesses.setdefault(witness['binder'], set()).add(coq(witness['expression']))
            # Several paths of one edge may give one binder different terms: then no single term is
            # recorded, and the row lists the candidates.
            candidates = {name: sorted(terms) for name, terms in witnesses.items()
                          if len(terms) > 1 and None not in terms}
            witnesses = {name: next(iter(terms)) for name, terms in witnesses.items()
                         if len(terms) == 1 and None not in terms}
            loop_values = (loop_back_values(profile, forward, succ_pc, pre_pc) if kind == 'loop_back' else
                           loop_entry_values(profile, forward, succ_pc, pre_pc) if kind == 'loop_entry' else {})
            for pre in entries[pre_pc]:
                for succ in entries[succ_pc]:
                    if succ.get('slot') and (succ['slot']['predecessor_pc'] != pre_pc or
                                             succ['slot']['predecessor_slot'] != (pre.get('slot') or {}).get('index')):
                        continue
                    design = next((row for row in profile.get('loop_designs', [])
                                   if profile.pc(row['head']) == succ_pc), {}) if kind.startswith('loop') else {}
                    rows = binder_map(kind, pre, succ, witnesses, loop_values,
                                      list(design.get('registers', {}).values()) + [design.get('index')]
                                      + succ.get('varying', []) + pre.get('varying', []))
                    free_witnesses(succ, rows)
                    for row in rows:
                        if row['expression'] is None and row['succ'] in candidates:
                            row['candidates'] = candidates[row['succ']]
                    unchanged, new, closed = classify_facts(pre, succ, rows)
                    edge = {'pre_pc': pre_pc, 'succ_pc': succ_pc, 'kind': kind,
                            'pre_entry': pre['entry'], 'succ_entry': succ['entry'],
                            'binder_map': rows, 'unchanged': unchanged, 'new': new, 'closed': closed,
                            'counts': {'succ_binders': len(rows),
                                       'identity': sum(row['identity'] for row in rows),
                                       'with_term': sum(not row['identity'] and row['expression'] is not None
                                                        for row in rows),
                                       'without_term': sum(row['expression'] is None for row in rows),
                                       'several_terms': sum('candidates' in row for row in rows),
                                       'unchanged_facts': len(unchanged), 'new_facts': len(new),
                                       'closed_facts': len(closed),
                                       'new_hidden_facts': sum(row['succ'][0] == 'hidden' for row in new)}}
                    if kind == 'call_return':
                        edge['call'] = calls.get(succ_pc)
                    edges.append(edge)
                    if (options.rocq and pre.get('mode') == 'wrap' and succ.get('mode') == 'wrap'
                            and (selected is None or pre_pc in selected)):
                        rocq.append(rocq_edge(edge, pre, succ, len(edges) - 1))
                        used_entries.update([pre['entry'], succ['entry']])
    options.output.write_text(json.dumps({'schema': 'lane.generator.edges.v1', 'function': profile.name,
                                          'edges': edges}, indent=1, ensure_ascii=False) + '\n')
    if options.rocq:
        stems = sorted({('Function' if meta['entry'].startswith('fp_machineReturn') else 'Pilot')
                        + re.match(r'fp_machine(?:At)?([0-9a-zA-Z]+?)(?:_|$)', meta['entry'])[1]
                        for metas in entries.values() for meta in metas if meta['entry'] in used_entries})
        header = pilot_header(profile) + 'Require Import lithium.lvar.\n'
        header += ''.join('Require Import ' + profile.qualified(stem + kind) + '.\n'
                          for stem in stems for kind in ('Entries', 'Structural'))
        header += (entry_hist.HIST_LIBRARY + 'From iris.proofmode Require Import proofmode.\n\n'
                   'Section edges.\nContext `{!islaG Sigma} `{!threadG}.\n\n')
        options.rocq.write_text(header + '\n'.join(rocq) + '\nEnd edges.\n')
    print(json.dumps({'edges': len(edges), 'instances': len(rocq),
                      'kinds': {kind: sum(edge['kind'] == kind for edge in edges)
                                for kind in sorted({edge['kind'] for edge in edges})}}))


if __name__ == '__main__':
    main()
