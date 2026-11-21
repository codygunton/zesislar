"""The per-edge data of a function's rendered `entry_hist: wrap` entries and their history instances.

For each successor edge (block entry variant -> successor entry variant) the record holds
  - the binder map: every successor binder with the block-entry binder or term it stands for,
  - the successor facts that are unchanged block-entry facts (text identity over identity binders),
  - the new facts, each with the block-entry history facts that share a ghost binder with it,
  - for a call site, the call plan of JOINS.json `calls[]`.
`--rocq-dir DIR` also writes, per source block, `Edges<case>.v`: one `ZesuHistEdge` instance per edge
(none when the successor states the same history: `zesu_hist_edge_refl`), and one `ZesuHistReveal`
instance per block history fact that a successor states visibly (a loop exit). `Edges.v` exports them
all. Each proof uses only the sentence forms of `EDGE_SENTENCES` (AGENTS.md exception).

Usage: render_edges.py --function NAME --entries RESULT.json --forward DIR --cfg FUNCTION.json
       --output EDGES.json [--rocq-dir DIR]
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


def free_witnesses(succ, rows, pre=None):
    """A ghost binder of type bv that only closed facts mention gets the witness 0.

    Such a binder (a system-register or trace witness) is tied to no resource and to no other
    binder, so any value that satisfies its own facts will do; with 0 the facts compute. A new
    binder always qualifies; a binder the block entry holds (identity) only when the successor
    states a fact on it that the block entry does not (a guard of the block's own path, such as
    the mstatus bit test): with 0 that fact computes instead of being a premise of the edge."""
    others = [binder['name'] for binder in succ['live'] + succ['ghost']]
    pre_facts = {normal(fact) for fact in pre['hidden']} if pre else set()
    for row in rows:
        if row['role'] != 'ghost' or row.get('rename') or (row['expression'] is not None and not row['identity']):
            continue
        match = re.fullmatch(r'bv (\d+)', row['type'])
        facts = [fact for fact in succ['hidden'] if mentions(row['succ'], fact)]
        if row['identity'] and (pre is None or any(mentions(row['succ'], fact) for fact in succ['visible'])
                                or all(normal(fact) in pre_facts for fact in facts)):
            continue
        if match and facts and all(MASK_FACT.search(fact) and not any(
                mentions(name, fact) for name in others if name != row['succ']) for fact in facts):
            row.update({'expression': '(BV ' + match[1] + '%N 0%Z)', 'free': True, 'identity': False, 'pre': None})


def group_parts(text):
    """(bound names, members) of a group fact `[zesu_join_history] (∃ (b : T)…, (F1) /\\ … /\\ (Fk))`,
    or None."""
    from join_generalize import JOIN_HISTORY, history_members
    fact = unwrap(text)
    if fact.startswith(JOIN_HISTORY + ' (') and fact.endswith(')'):
        fact = fact[len(JOIN_HISTORY) + 2:-1].strip()
    if not fact.startswith('∃'):
        return None
    members = history_members('⌜' + fact + '⌝')
    if not members:
        return None
    depth = 0
    for position, char in enumerate(fact):
        depth += {'(': 1, ')': -1}.get(char, 0)
        if char == ',' and depth == 0:
            break
    names = [name for group in re.findall(r"\(([^():]+?) :", fact[1:position]) for name in group.split()]
    return (names, members) if names else None


class Source:
    """The facts a proof at a block entry can name: its history facts `HF<i>` (`destruct Hh`), the
    members `HF<i>_<j>` of a history group fact (`destruct HF<i>` binds the group's names as
    `<name>_HF<i>`), the members `HF<i>_<j>_<k>` of a group nested as a member (a join that bound an
    earlier history group as one of its own members) and, with `visible`, its visible facts `HV<k>`
    (premises of an edge, which the block proves from its context) and their group members."""

    def __init__(self, pre, visible=True):
        self.binders = set(binder_names(pre, 'parameters') + binder_names(pre, 'live')
                           + binder_names(pre, 'ghost')
                           + [binder['name'] for binder in pre.get('hist_live', [])])
        self.candidates, self.groups, self.parent = {}, {}, {}
        for where, prefix in (('hidden', 'HF'), ('visible', 'HV')) if visible else (('hidden', 'HF'),):
            for index, fact in enumerate(pre[where]):
                hypothesis = prefix + str(index)
                self.candidates.setdefault(key(fact), []).append((hypothesis, None))
                self._index_group(hypothesis, fact)

    def _index_group(self, hypothesis, fact):
        parts = group_parts(fact)
        if not parts:
            return
        self.groups[hypothesis] = parts
        for position, member in enumerate(parts[1]):
            name = hypothesis + '_' + str(position)
            self.candidates.setdefault(key(member), []).append((name, hypothesis))
            if group_parts(member):
                self.parent[name] = hypothesis
                self._index_group(name, member)

    def ancestors(self, group):
        """`group` and the groups it is nested in, innermost first."""
        chain = []
        while group is not None:
            chain.append(group)
            group = self.parent.get(group)
        return chain

    def binding(self, name, group):
        """The group whose telescope binds `name` in a member of `group` (the innermost one), None
        for a block binder, or False when neither binds it."""
        for scope in self.ancestors(group):
            if name in self.groups[scope][0]:
                return scope
        return None if name in self.binders else False

    def hidden_names(self):
        """Names a block cannot state: bound in a history group (and no block binder)."""
        return {name for hypothesis, (names, _) in self.groups.items() if hypothesis.startswith('HF')
                for name in names if name not in self.binders}

    def derive(self, text):
        """(proof term, opened groups, used top-level hypotheses) of `text`, or None: the fact itself,
        or a group `∃ b…, (F1) /\\ …` each of whose members is a source fact or a member of a (nested)
        source group, each b witnessed by the block binder b or by the b of the source group whose
        telescope binds it in that member. Opened groups include the groups they are nested in."""
        flat = [hypothesis for hypothesis, owner in self.candidates.get(key(text), []) if owner is None]
        if flat:
            return flat[0], set(), {flat[0]}
        parts = group_parts(text)
        if parts is None:
            return None
        names, members = parts
        choices = [self.candidates.get(key(member), []) for member in members]
        if not all(choices):
            return None
        from join_generalize import _free_in_fact
        free = lambda name, member: mentions(name, member) and _free_in_fact(unwrap(member), name)
        owner = {}
        for name in names:
            options = None
            for member, candidates in zip(members, choices):
                if free(name, member):
                    fits = {self.binding(name, group) for _, group in candidates} - {False}
                    options = fits if options is None else options & fits
            if not options:
                return None
            owner[name] = None if None in options else sorted(options)[0]
        terms, opened = [], set()
        for member, candidates in zip(members, choices):
            pick = None
            for term, group in candidates:
                # A name the candidate's (enclosing) groups bind that the fact does not bind would
                # stand for a different value than the fact's free name.
                captured = {name for scope in self.ancestors(group) for name in self.groups[scope][0]
                            if name not in names and free(name, member)}
                if not captured and all(self.binding(name, group) == owner[name]
                                        for name in names if free(name, member)):
                    pick = (term, group)
                    break
            if pick is None:
                return None
            terms.append(pick[0])
            opened.update(self.ancestors(pick[1]))
        proof = terms[-1]
        for term in reversed(terms[:-1]):
            proof = '(conj ' + term + ' ' + proof + ')'
        for name in reversed(names):
            proof = '(ex_intro _ ' + (name if owner[name] is None else name + '_' + owner[name]) + ' ' + proof + ')'
        used = {re.match(r'H[FV]\d+', term)[0] for term in terms}
        return (proof if proof.startswith('(') else '(' + proof + ')'), opened, used

    def open_sentence(self, hypothesis):
        names, members = self.groups[hypothesis]
        pattern = [name + '_' + hypothesis for name in names] + [hypothesis + '_' + str(position)
                                                                 for position in range(len(members))]
        return '  destruct ' + hypothesis + ' as (' + ' & '.join(pattern) + ').'


def succ_terms(rows):
    """Successor binder -> the block-entry term it stands for on this edge (binders with a term)."""
    return {row['succ']: row['expression'] for row in rows
            if row['expression'] is not None and not row['identity'] and row['expression'] != row['succ']}


def stated_at_source(text, rows, succ):
    """`text` (a successor fact) over block-entry terms, or None when it names a successor ghost
    binder that has no term on this edge. A successor live binder without a term is a value the block
    chooses from its resources (`<name>_succ`, no block-entry name)."""
    terms = succ_terms(rows)
    identity = {row['succ'] for row in rows if row['identity']}
    bound = set((group_parts(text) or ([], []))[0])
    table = {name: term if re.fullmatch(r"[\w']+", term) else '(' + unwrap(term) + ')' for name, term in terms.items()}
    for role in ('live', 'ghost'):
        for name in binder_names(succ, role):
            if name not in identity and name not in terms and name not in bound and mentions(name, text):
                if role == 'ghost':
                    return None
                table[name] = name + '_succ'
    return substitute(text, table)


def mentions_hidden(text, pre, source):
    """A fact names a block ghost binder or a name bound in a block history group outside every
    telescope that binds it (its own and those of its members)."""
    from join_generalize import _free_in_fact
    return any(mentions(name, text) and _free_in_fact(unwrap(text), name)
               for name in set(binder_names(pre, 'ghost')) | source.hidden_names())


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
            # A new history fact whose first conjunct is a block-entry fact (forward entries state a
            # guard with its unsigned views; a loop class the guard only) is proved inside the edge from
            # that fact (`zesu_hist_view`); the reverse (a loop class keeps the guard of a forward fact)
            # is its first projection. The block-entry fact may be hidden or visible (then a premise).
            renamed = substitute(fact, renames)
            head = key(conjuncts(renamed)[0])
            if where == 'hidden' and all(name in identity for name in named):
                found = None
                for origin_where in ('hidden', 'visible'):
                    view = next((position for position, other in enumerate(pre[origin_where])
                                 if key(other) == head), None)
                    if view is not None and len(conjuncts(renamed)) > 1:
                        found = {'succ': [where, index], 'pre': [origin_where, view], 'view': True}
                        break
                    projection = next((position for position, other in enumerate(pre[origin_where])
                                       if len(conjuncts(other)) > 1 and key(conjuncts(other)[0]) == key(renamed)),
                                      None)
                    if projection is not None:
                        found = {'succ': [where, index], 'pre': [origin_where, projection], 'projection': True}
                        break
                if found is not None:
                    unchanged.append(found)
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


def own_guards(forward, pre_pc, succ_pc):
    """The guards the block takes on its way to `succ_pc` (`<condition> = true`): the path conditions of
    the edge's paths after the longest prefix they share with every path from the same seed that leaves
    the block (the conditions of the block entry). Several paths of one edge give their disjunction; a
    guard that has no rendering is left out (the edge then states less, never more)."""
    leaving = [alternative for boundary in forward['boundaries'] for alternative in boundary['alternatives']
               if alternative.get('predecessor_pc') == pre_pc]
    succ_boundary = next((row for row in forward['boundaries'] if row['pc'] == succ_pc), None)
    paths = [alternative for alternative in (succ_boundary or {}).get('alternatives', [])
             if alternative.get('predecessor_pc') == pre_pc]
    disjuncts = []
    for path in paths:
        conditions = path['resource_boundary'].get('path_conditions', [])
        others = [row['resource_boundary'].get('path_conditions', []) for row in leaving
                  if row.get('seed_pc') == path.get('seed_pc')]
        shared = 0
        while shared < len(conditions) and all(shared < len(other) and other[shared] == conditions[shared]
                                               for other in others):
            shared += 1
        reads = path['resource_boundary'].get('owned_read_renderings', [])
        texts = [coq(condition, reads) for condition in conditions[shared:]]
        texts = [text + ' = true' for text in texts if text is not None]
        if texts:
            disjuncts.append(' /\\ '.join('(' + text + ')' for text in texts) if len(texts) > 1 else texts[0])
    if len(disjuncts) > 1:
        return [' \\/ '.join('(' + text + ')' for text in disjuncts)]
    return disjuncts


def rocq_edge(edge, pre, succ, index, obligation=None):
    """One ZesuHistEdge instance with its data-only proof.

    obligation: `{'rows', 'guards', 'name', 'declarations'}` when the successor is a join with design
    obligations (`entry_hist.design_obligations`): a successor history fact that is such a row and that
    the block history does not hold is proved by the registered lemma `<name>_<obligation>_holds` from
    the copied block history `HS`, the block-entry visible facts (`HV<k>`) of the classes the row's
    `premises` name and, when it names `guard` (the default), the edge's own guards (`HG<j>`); those
    become premises the block proves. Its data-only statement is appended to `declarations`
    (`EdgeObligations.v`)."""
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
    # A successor history fact that the opened block entry proves (a source fact, or a group of source
    # facts and members of source history groups, such as a join's `zesu_join_history`) is proved
    # inside the edge, not left to the block as a premise. A visible block-entry fact it needs is a
    # premise `HV<k>` (the automation proves it from its own context).
    source = Source(pre)
    succ_names = set(binder_names(succ, 'live') + binder_names(succ, 'ghost'))
    derived, opened, carried_index = {}, set(), set()
    for row in new_hidden:
        text = substitute(row['text'], renames)
        bound = set((group_parts(text) or ([], []))[0])
        if any(mentions(name, text) and name not in bound and name not in identity and name not in pre_live
               for name in succ_names):
            continue
        result = source.derive(text)
        if result is not None:
            derived[tuple(row['succ'])] = result[0]
            opened |= result[1]
            carried_index |= {name for name in result[2] if name.startswith('HV')}
    obligated = {}
    for row in new_hidden:
        design = (obligation or {}).get('rows', {}).get(normal(row['text']))
        if design is not None and tuple(row['succ']) not in derived:
            obligated[tuple(row['succ'])] = design
    new_hidden = [row for row in new_hidden if tuple(row['succ']) not in derived and tuple(row['succ']) not in obligated]
    edge['hidden_premises'] = sum(mentions_hidden(substitute(row['text'], renames), pre, source)
                                  for row in new_hidden)
    free = {row['succ']: row['expression'] for row in rows if row.get('free')}
    closed = {tuple(row['succ']) for row in edge.get('closed', [])}
    new_ghost = [name for name in succ_ghost if name not in identity and name not in free]
    ghost_renames = {name: name + '_new' for name in new_ghost if name in pre_live + pre_ghost}
    support = sorted({position for row in new_hidden for position in row['support']})
    new_texts = [substitute(row['text'], {**renames, **ghost_renames}) for row in new_hidden]
    used = [binder for binder in pre['ghost']
            if any(mentions(binder['name'], text) for text in new_texts + [pre['hidden'][p] for p in support])]
    carried_index |= {'HV' + str(row['pre'][1]) for row in edge['unchanged']
                      if row['succ'][0] == 'hidden' and row['pre'][0] == 'visible'}
    carried_index = sorted(carried_index, key=lambda name: int(name[2:]))
    carried = [pre['visible'][int(name[2:])] for name in carried_index]
    guards = []
    if obligated:
        # The obligation lemma reads the block entry's facts of the classes its rows declare.
        needs = set().union(*(set(design.get('premises', ['guard'])) for design in obligated.values()))
        selected = entry_hist.obligation_premise_positions(pre['live'] + pre['ghost'], pre['visible'], needs)
        premise_index = ['HV' + str(position) for position in selected]
        carried_index = sorted(set(carried_index) | set(premise_index), key=lambda name: int(name[2:]))
        carried = [pre['visible'][int(name[2:])] for name in carried_index]
        guards = obligation['guards'] if 'guard' in needs else []
        premise_facts = [pre['visible'][position] for position in selected]
        hypotheses = ['HS'] + premise_index + ['HG' + str(position) for position in range(len(guards))]
        statement_vars = [binder for binder in [*pre['parameters'], *pre['live']]
                          if binder in pre['parameters'] or any(mentions(binder['name'], text) for text in
                                                                [application(pre, {})] + premise_facts + guards)]
        for target, design in sorted(obligated.items()):
            declaration = obligation['name'] + '_' + design['obligation']
            premises = [application(pre, {})] + premise_facts + guards
            obligation['declarations'].append({
                'name': declaration, 'module': design['lemma_module'], 'entry': pre['entry'],
                'text': ('Definition ' + declaration + ' : Prop :=\n  forall ' + telescope(statement_vars) + ',\n'
                         + ''.join('  (' + premise + ') ->\n' for premise in premises)
                         + '  ' + design['coq'] + '.\n')})
            derived[target] = ('(' + declaration + '_holds ' + ' '.join(
                binder['name'] for binder in statement_vars) + ' ' + ' '.join(hypotheses) + ')')
    body = ' ∗ '.join(['⌜' + text + '⌝' for text in new_texts + carried + guards] + ['True'])
    bound = [{'name': ghost_renames.get(binder['name'], binder['name']), 'type': binder['type']}
             for binder in succ['ghost'] if binder['name'] in new_ghost]
    if bound:
        body = '∃ ' + telescope(bound) + ', ' + body
    for position in reversed(support):
        body = '⌜' + pre['hidden'][position] + '⌝ -∗ ' + body
    if used:
        body = '∀ ' + telescope(used) + ', ' + body
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
             '  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh.'
             + (' pose proof Hh as HS.' if obligated else '') + ' unfold ' + pre['hist'] + ' in Hh.']
    facts = ['HF' + str(position) for position in range(len(pre['hidden']))]
    pattern = binder_names(pre, 'ghost') + facts
    if not pre['hidden']:
        lines.append('  clear Hh.')
    elif len(pattern) == 1:
        lines.append('  pose proof Hh as HF0.')
    else:
        lines.append('  destruct Hh as (' + ' & '.join(pattern) + ').')
    lines.append('  iIntros "HN".')
    # The premise binds the successor's new ghosts even when it states no fact on them: destruct it
    # whenever it binds or states anything, so the `exists` below names variables in scope.
    if new_texts or carried or guards or bound:
        arguments = [binder['name'] for binder in used] + ['HF' + str(position) for position in support]
        term = '("HN" $! ' + ' '.join(arguments) + ')' if arguments else '"HN"'
        facts = (['%HN' + str(position) for position in range(len(new_texts))] + ['%' + name for name in carried_index]
                 + ['%HG' + str(position) for position in range(len(guards))])
        # A premise that only binds ghosts (`∃ b…, True`) has one conjunct: Iris refuses `"(_)"` for it.
        intro = '"(' + ' & '.join(facts + ['_']) + ')"' if facts else '"_"'
        lines.append('  iDestruct ' + term + ' as ' + ('(' + ' '.join(b['name'] for b in bound) + ') ' if bound else '')
                     + intro + '.')
    lines += [source.open_sentence(hypothesis) for hypothesis in sorted(opened)]
    lines.append('  iPureIntro. apply zesu_hist_intro. unfold ' + succ['hist'] + '.')
    if succ['ghost']:
        lines.append('  exists ' + ', '.join(free.get(name, ghost_renames.get(name, name)) for name in succ_ghost) + '.')
    if not succ['hidden']:
        lines.append('  exact I.')
    else:
        proofs, fresh = [], 0
        origin = {tuple(row['succ']): row['pre'] for row in edge['unchanged']}
        views = {tuple(row['succ']) for row in edge['unchanged'] if row.get('view')}
        projections = {tuple(row['succ']) for row in edge['unchanged'] if row.get('projection')}
        for position in range(len(succ['hidden'])):
            target = ('hidden', position)
            at = origin.get(target)
            if target in closed:
                proofs.append('by vm_compute')
                continue
            if target in derived:
                proofs.append('exact ' + derived[target])
                continue
            if at is None:
                proofs.append('exact HN' + str(fresh))
                fresh += 1
                continue
            name = 'HF' + str(at[1]) if at[0] == 'hidden' else 'HV' + str(at[1])
            proofs.append('exact (proj1 ' + name + ')' if target in projections else
                          'zesu_hist_view ' + name if target in views else 'exact ' + name)
        for proof in proofs[:-1]:
            lines.append('  split; [' + proof + '|].')
        lines.append('  ' + proofs[-1] + '.')
    lines.append('Qed.')
    return '\n'.join(lines) + '\n'


def application(meta, table):
    """The history term of an entry variant (binders renamed by `table`)."""
    return meta['hist'] + ''.join(' (' + table.get(binder['name'], binder['name']) + ')'
                                  for binder in meta['parameters'] + meta.get('hist_live', meta['live']))


def is_identity(pre, succ, new, unchanged, closed):
    """The successor states the block's own history term (a loop back edge on the class history) and
    every successor history fact is the block's fact at the same position: the identity instance
    `zesu_hist_edge_refl` of Hist applies and no instance is rendered. New successor-visible facts are
    the block's to prove; they never enter an instance."""
    return (application(pre, {}) == application(succ, {}) and not closed
            and not any(row['succ'][0] == 'hidden' for row in new)
            and all(tuple(row['succ']) == tuple(row['pre']) for row in unchanged if row['succ'][0] == 'hidden'))


def visible_accounting(edge, pre, succ):
    """How each fact the successor states visibly is proved on this edge.

    `visible`: the block-entry visible fact (modulo the binder map); `reveal`: derived from the
    opened block history alone (a `ZesuHistReveal` instance, `derivation` its proof); `path`: new
    on the block's own path over terms the block states (the block proves it); `violation`: the
    block would have to prove it from facts on names its history hides, or regroup block-entry
    facts under a new existential (the automation chooses no witnesses)."""
    rows = edge['binder_map']
    from_visible = {row['succ'][1] for row in edge['unchanged']
                    if row['succ'][0] == 'visible' and row['pre'][0] == 'visible'}
    history = Source(pre, visible=False)
    everything = Source(pre)
    result = []
    for position, fact in enumerate(succ['visible']):
        row = {'succ': ['visible', position]}
        if position in from_visible:
            result.append({**row, 'status': 'visible'})
            continue
        text = stated_at_source(fact, rows, succ)
        if text is not None and any(owner is None and hypothesis.startswith('HV')
                                    for hypothesis, owner in everything.candidates.get(key(text), [])):
            # The block-entry visible fact under the binder map: the block holds it in its context.
            result.append({**row, 'status': 'visible'})
            continue
        derivation = history.derive(text) if text is not None else None
        if derivation is not None and not mentions_hidden(text, pre, history):
            result.append({**row, 'status': 'reveal', 'fact': text, 'derivation': derivation})
            continue
        parts = group_parts(text or fact)
        regroup = parts is not None and any(key(member) in everything.candidates for member in parts[1])
        if text is None or mentions_hidden(text, pre, history) or regroup:
            result.append({**row, 'status': 'violation', 'fact': (text or fact)[:400],
                           'reason': 'no term for a successor binder' if text is None else
                           'regroups block-entry facts' if regroup else 'names a hidden block binder'})
            continue
        result.append({**row, 'status': 'path'})
    return result


def history_destruct(pre):
    """The sentences that open a block history hypothesis `Hh` into `HF<k>`."""
    pattern = binder_names(pre, 'ghost') + ['HF' + str(position) for position in range(len(pre['hidden']))]
    if not pre['hidden']:
        return '  clear Hh.'
    if len(pattern) == 1:
        return '  pose proof Hh as HF0.'
    return '  destruct Hh as (' + ' & '.join(pattern) + ').'


def rocq_reveal(pre, fact, derivation, index):
    """One ZesuHistReveal instance: a fact a successor states visibly, proved from the block history."""
    term, opened, _ = derivation
    statement = application(pre, {}) + ' ' + fact
    variables = [binder for binder in [*pre['parameters'], *pre['live']]
                 if binder in pre['parameters'] or mentions(binder['name'], statement)]
    source = Source(pre, visible=False)
    lines = ['Global Instance zesu_hist_reveal_' + str(index) + ' ' + telescope(variables) + ' :',
             '  ZesuHistReveal (' + application(pre, {}) + ') (' + fact + ').',
             'Proof.',
             '  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold ' + pre['hist'] + ' in Hh.',
             history_destruct(pre)]
    lines += [source.open_sentence(hypothesis) for hypothesis in sorted(opened)]
    lines += ['  exact ' + term + '.', 'Qed.']
    return '\n'.join(lines) + '\n'


def conjunct_reveals(fact, derivation):
    """(conjunct, derivation) for each top-level conjunct of a revealed conjunction. Lithium proves the
    pure conjuncts of an open existential (a loop class) as separate side goals, so the block tail asks
    for each conjunct (Hist.zesu_hist_reveal_pure), never for the conjunction. Empty when the fact is no
    plain conjunction (a binder, a disjunction or an implication at the top) or a projection of its
    term is not an EDGE_SENTENCES form."""
    term, opened, rest = derivation
    scoped = re.fullmatch(r'\s*(\(.*\))%(nat|Z|N)\s*', fact, re.S)
    body, scope = (scoped[1], '%' + scoped[2]) if scoped else (fact, '')
    parts = conjuncts(body)
    if len(parts) < 2 or re.match(r'\s*(?:∃|∀|exists\b|forall\b|fun\b)', unwrap(body)):
        return []
    if any(len(conjuncts_by(part, separator)) > 1 for part in parts for separator in ('\\/', '->', '↔', '→')):
        return []
    result = []
    for position, part in enumerate(parts):
        projection = term
        for _ in range(position):
            projection = '(proj2 ' + projection + ')'
        if position < len(parts) - 1:
            projection = '(proj1 ' + projection + ')'
        if not re.fullmatch(_SOLVE, 'exact ' + projection):
            return []
        result.append(('(' + part + ')' + scope if scope else part, (projection, opened, rest)))
    return result


def conjuncts_by(text, separator):
    """The parts of a fact split at a top-level separator."""
    parts, depth, start = [], 0, 0
    for position, character in enumerate(text):
        depth += (character in '([') - (character in ')]')
        if depth == 0 and text.startswith(separator, position):
            parts.append(text[start:position])
            start = position + len(separator)
    return parts + [text[start:]]


# Every sentence an edge proof may contain (AGENTS.md: generated proofs are limited to these forms;
# ZesuSsz/Evidence/check_proof_hygiene.py rule EDGE-PROOF enforces the list on the committed files).
_NAME = r"[A-Za-z_][\w']*"
_SOLVE = (r"(?:exact " + _NAME + r"|exact \(proj1 " + _NAME + r"\)|zesu_hist_view " + _NAME
          + r"|by vm_compute|exact I|exact \((?:" + _NAME + r"|[ ()])+\))")
EDGE_SENTENCES = [
    r"Proof", r"Qed",
    r"rewrite /ZesuHist(?:Edge|Reveal) => Hh",
    r"apply zesu_hist_elim in Hh",
    r"unfold " + _NAME + r" in Hh",
    r"clear Hh",
    r"pose proof Hh as (?:HF0|HS)",
    r"destruct (?:Hh|H[FV]\d+(?:_\d+)*) as \((?:" + _NAME + r")(?: & " + _NAME + r")*\)",
    r'iIntros "HN"',
    r'iDestruct (?:"HN"|\("HN" \$!(?: ' + _NAME + r')+\)) as (?:\((?:' + _NAME + r' ?)+\) )?(?:"\((?:%' + _NAME
    + r' & )+_\)"|"_")',
    r"iPureIntro",
    r"apply zesu_hist_intro",
    r"unfold " + _NAME,
    r"exists .+",
    r"split; \[" + _SOLVE + r"\|\]",
    _SOLVE,
]


EDGE_PROOF_FILE = 'ZesuSsz/Generated/*/FP301/Edges*.v'


def edge_sentences(text):
    """The sentences of the proofs of an edge module (each `Proof. … Qed.`)."""
    sentences = []
    for proof in re.findall(r"^Proof\.(.*?)^Qed\.", text, re.S | re.M):
        sentences += ['Proof', 'Qed'] + [part.strip() for part in re.split(r"\.(?:\s+|$)", proof) if part.strip()]
    return sentences


def edge_proof_problems(text):
    """Why an edge module breaks the AGENTS.md exception (empty: it conforms). Shared with
    ZesuSsz/Evidence/check_proof_hygiene.py rule EDGE-PROOF."""
    problems = []
    if re.search(r"\b(?:Admitted|Axiom|Ltac2?|Defined|Abort|admit)\b", text):
        problems.append('contains Admitted, Axiom, Ltac, Defined, Abort or admit')
    if len(re.findall(r"^Proof\.", text, re.M)) != len(re.findall(r"^Qed\.", text, re.M)):
        problems.append('a proof does not start with `Proof.` and end with `Qed.` on their own lines')
    problems += ['sentence outside EDGE_SENTENCES: ' + sentence[:200] for sentence in edge_sentences(text)
                 if not any(re.fullmatch(pattern, sentence, re.S) for pattern in EDGE_SENTENCES)]
    return problems


def check_edge_sentences(text):
    problems = edge_proof_problems(text)
    if problems:
        raise ValueError('An edge module breaks EDGE_SENTENCES: ' + '; '.join(problems))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--function', required=True)
    parser.add_argument('--entries', type=Path, required=True)
    parser.add_argument('--forward', type=Path, required=True)
    parser.add_argument('--cfg', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rocq-dir', type=Path, help='generated directory: Edges<case>.v per source block, Edges.v')
    options = parser.parse_args()
    profile = load_profile(options.function)
    result = json.loads(options.entries.read_text())
    forward = json.loads((options.forward / 'FORWARD.json').read_text())
    joins = json.loads((options.forward / 'JOINS.json').read_text())
    seeds = json.loads((options.forward / 'JOIN-SEEDS.json').read_text())['seeds']
    function = json.loads(options.cfg.read_text())['functions'][0]
    entries = variants(result['cases'])
    calls = joins.get('calls', {})
    edges, instances, reveals, used_entries = [], {}, {}, {}
    obligation_rows, declarations, lemma_modules = entry_hist.design_obligations(profile), [], {}
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
                    free_witnesses(succ, rows, pre)
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
                    if pre.get('mode') == 'wrap' and succ.get('mode') == 'wrap':
                        block_instances = instances.setdefault(pre_pc, [])
                        if is_identity(pre, succ, new, unchanged, closed):
                            edge['identity'] = True
                        else:
                            obligation = None
                            join_rows = entry_hist.design_obligations(profile, [
                                key for key in profile.get('join_designs') or {} if profile.pc(key) == succ_pc])
                            if obligation_rows and kind == 'join' and join_rows:
                                obligation = {'rows': join_rows, 'declarations': declarations,
                                              'guards': own_guards(forward, pre_pc, succ_pc),
                                              'name': 'fp_edge' + profile.key(pre_pc) + '_' + profile.key(succ_pc)}
                            before = len(declarations)
                            block_instances.append(rocq_edge(edge, pre, succ, len(edges) - 1, obligation))
                            for row in declarations[before:]:
                                lemma_modules.setdefault(pre_pc, set()).add(row['module'])
                                edge['obligation'] = row['name']
                        accounting = visible_accounting(edge, pre, succ)
                        edge['visible_accounting'] = [{k: v for k, v in row.items() if k != 'derivation'}
                                                      for row in accounting]
                        for row in accounting:
                            if row['status'] != 'reveal':
                                continue
                            facts = [(row['fact'], row['derivation']),
                                     *conjunct_reveals(row['fact'], row['derivation'])]
                            for fact, derivation in facts:
                                statement = (application(pre, {}), fact)
                                if statement not in reveals:
                                    reveals[statement] = len(reveals)
                                    block_instances.append(rocq_reveal(pre, fact, derivation, reveals[statement]))
                        used_entries.setdefault(pre_pc, set()).update([pre['entry'], succ['entry']])
    violations = [{'pre_entry': edge['pre_entry'], 'succ_entry': edge['succ_entry'], 'kind': edge['kind'], **row}
                  for edge in edges for row in edge.get('visible_accounting', []) if row['status'] == 'violation']
    options.output.write_text(json.dumps({'schema': 'zesu.fp301.edges.v1', 'function': profile.name,
                                          'edges': edges, 'visible_violations': violations},
                                         indent=1, ensure_ascii=False) + '\n')
    if options.rocq_dir:
        stem_of = lambda entry: (('Function' if entry.startswith('fp_machineReturn') else 'Pilot')
                                 + re.match(r'fp_machine(?:At)?([0-9a-zA-Z]+?)(?:_|$)', entry)[1])
        modules = []
        for block in function['blocks']:
            pre_pc = hex(block['start'])
            if pre_pc not in entries:
                continue
            case = profile.key(pre_pc)
            stems = sorted({stem_of(entry) for entry in used_entries.get(pre_pc, ())})
            header = pilot_header(profile).replace(
                'No proof script.', 'Proofs use only EDGE_SENTENCES (tools/block/render_edges.py).', 1
            ) + 'Require Import lithium.lvar.\n'
            header += ''.join('Require Import ' + profile.qualified(stem + kind) + '.\n'
                              for stem in stems for kind in ('Entries', 'Structural'))
            header += ''.join('Require Import ' + module + '.\n' for module in sorted(lemma_modules.get(pre_pc, ())))
            header += (entry_hist.HIST_LIBRARY + 'From iris.proofmode Require Import proofmode.\n\n'
                       'Section edges.\nContext `{!islaG Sigma} `{!threadG}.\n\n')
            text = header + '\n'.join(instances.get(pre_pc, [])) + '\nEnd edges.\n'
            check_edge_sentences(text)
            (options.rocq_dir / ('Edges' + case + '.v')).write_text(text)
            modules.append('Edges' + case)
        if modules:   # A function whose entries carry no history (all facts visible) has no edges.
            (options.rocq_dir / 'Edges.v').write_text(''.join('Require Export ' + profile.qualified(module)
                                                              + '.\n' for module in modules))
        if declarations:
            # The edge obligations: data-only statements, proved in the profile's lemma modules.
            stems = sorted({stem_of(row['entry']) for row in declarations})
            text = (pilot_header(profile) + ''.join('Require Import ' + profile.qualified(stem + 'Entries') + '.\n'
                                                    for stem in stems)
                    + '\n' + '\n'.join(row['text'] for row in declarations))
            if re.search(r'\b(?:Proof|Qed|Admitted|Axiom|Ltac)\b', text):
                raise ValueError('An edge obligation module holds no proof')
            (options.rocq_dir / 'EdgeObligations.v').write_text(text)
    kinds = sorted({edge['kind'] for edge in edges})
    print(json.dumps({'edges': len(edges), 'instances': sum(map(len, instances.values())),
                      'reveals': len(reveals), 'identity': sum(bool(edge.get('identity')) for edge in edges),
                      'hidden_premises': sum(edge.get('hidden_premises', 0) for edge in edges),
                      'hidden_premises_by_kind': {kind: sum(edge.get('hidden_premises', 0) for edge in edges
                                                            if edge['kind'] == kind) for kind in kinds},
                      'visible_violations': len(violations),
                      'kinds': {kind: sum(edge['kind'] == kind for edge in edges) for kind in kinds}}))
    if violations:
        sys.exit('render_edges: %d successor-visible facts the block cannot prove (EDGES.json '
                 '`visible_violations`)' % len(violations))


if __name__ == '__main__':
    main()
