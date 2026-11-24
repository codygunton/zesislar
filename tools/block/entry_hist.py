"""Hidden history and per-slot frame cells for FP301 entries.

The function profile selects the shape (`configure`):
  `"entry_hist": "wrap"`  (required; the only shape) the pure facts of one entry variant become
                          visible facts and one hidden
                          `⌜zesu_hist (<entry>_Hist args returnAddress <live binders>)⌝`.
  `"frame_slots": true`   each saved-register slot of the frame is one 8-byte cell at the address the
                          store computes.

Visible facts: facts that mention no entry binder (function domain, return alignment), `List.length`
facts of live binders, facts that match a profile `hist_pinned` regular expression (their binders stay
live), and facts on live binders that match a profile `hist_visible` regular expression (weak: see
`classify`). Every other fact is hidden; a join history (`zesu_join_history`) is always hidden. A live
binder is one that an owned resource, a pinning pattern or a backward pin mentions; the others are
ghost binders and are bound inside the history. decodeItem pins `.*`: nothing is hidden, so its
entries keep the plain shape (`seal_alternative` returns None).
"""
import re

FRAME_SLOTS = False
HIST_VISIBLE = ()
STORE_SPLICE = 'linear'
JOIN_GUARD_FORM = 'factored'
ARRAY_SPELLING = 'definition'
HELD_BINDERS = frozenset()
# `value` of a join's edge-guard disjunction under `join_guard_form: prop` or `factored`; `entry_formatter` renders
# such a condition as its normal-form proposition only. Kept through substitution, so successors inherit the form.
PROP_ONLY_GUARD = 'join_guard_prop'
HIST_LIBRARY = 'Require Import ZesuSsz.Automation2.Hist.\n'


def configure(profile):
    """Read the shape keys of a function profile: `entry_hist` (required, `wrap`), `frame_slots`,
    `hist_visible`, `store_splice` (`linear`, default, or `per_store`: constant-offset stores into a byte
    array are spliced one by one, the spelling the function's proofs consume), `join_guard_form` (how a
    join states which edge reached it, `join_generalize.join_guard_fact`: `factored`, default, the disjunction
    with shared guard prefixes stated once, proposition only (linear in a chain of tests); `both`, the flat
    disjunction as boolean fact and normal-form proposition; `prop`, the flat proposition only; `none`, no fact),
    `array_spelling` (how an owned stored array `a ↦ₘ{DfracOwn 1}∗ l` of the forward state is written:
    `definition`, default, through `isla.ghost_state.mem_mapsto_array_def`; `sealed`, isla's `a ↦ₘ∗ l`),
    `held_binders` (names of seed binders that a join or loop head keeps as owned ghosts, like a loop's
    owned binder, so the stored bytes that name them stay exact; join_generalize.drop_unheld_binders)."""
    global FRAME_SLOTS, HIST_VISIBLE, STORE_SPLICE, JOIN_GUARD_FORM, ARRAY_SPELLING, HELD_BINDERS
    mode = profile.get('entry_hist')
    if mode is None:
        raise ValueError('entry_hist: the function profile lacks the required key (only "wrap" exists)')
    if mode != 'wrap':
        raise ValueError('entry_hist: unknown mode ' + str(mode))
    slots = profile.get('frame_slots', False)
    if not isinstance(slots, bool):
        raise ValueError('frame_slots: a boolean is required')
    FRAME_SLOTS = slots
    HIST_VISIBLE = tuple(profile.get('hist_visible', []))
    splice = profile.get('store_splice', 'linear')
    if splice not in ('linear', 'per_store'):
        raise ValueError('store_splice: unknown value ' + str(splice))
    STORE_SPLICE = splice
    guard_form = profile.get('join_guard_form', 'factored')
    if guard_form not in ('factored', 'both', 'prop', 'none'):
        raise ValueError('join_guard_form: unknown value ' + str(guard_form))
    JOIN_GUARD_FORM = guard_form
    spelling = profile.get('array_spelling', 'definition')
    if spelling not in ('definition', 'sealed'):
        raise ValueError('array_spelling: unknown value ' + str(spelling))
    ARRAY_SPELLING = spelling
    held = profile.get('held_binders', [])
    if not isinstance(held, list) or not all(isinstance(name, str) and re.fullmatch(r"[A-Za-z_][\w']*", name)
                                             for name in held):
        raise ValueError('held_binders: a list of binder names is required')
    HELD_BINDERS = frozenset(held)


def mentions(name, text):
    text = re.sub(r'"[^"]*"', '', text)
    return re.search(r"(?<![\w'.])" + re.escape(name) + r"(?![\w'])", text) is not None


def unwrap(text, scopes=False):
    """Strip redundant outer parentheses (with scopes: also an outer scope suffix, for shape tests only)."""
    text = text.strip()
    while text.startswith('('):
        scoped = re.fullmatch(r'(\(.*\))%(?:nat|Z|N)', text, re.S) if scopes else None
        if scoped:
            text = scoped[1]
        depth = 0
        for position, character in enumerate(text):
            if character == '(':
                depth += 1
            elif character == ')':
                depth -= 1
                if depth == 0:
                    break
        if position != len(text) - 1:
            break
        text = text[1:-1].strip()
    return text


def normal(text):
    """Text identity of two facts: whitespace and redundant outer parentheses do not count."""
    return re.sub(r'\s+', ' ', unwrap(text))


def is_length_fact(inner):
    return re.match(r'(?:List\.)?length\b', unwrap(inner, scopes=True)) is not None


def is_join_history(inner):
    """A join's history (`join_generalize.ghost_group`): hidden whatever the profile shows."""
    return re.match(r'zesu_join_history\b', unwrap(inner)) is not None


def design_fact_text(row):
    """The Coq text of a join-design row (profile `join_designs`): a string is the fact itself; an
    object `{"coq", "history", "obligation", "lemma_module"}` with `history` is a fact of the join's
    history (`zesu_join_history`, hidden), which each edge into the join proves (`design_obligations`)."""
    if isinstance(row, str):
        return row
    return 'zesu_join_history (' + row['coq'] + ')' if row.get('history') else row['coq']


# The classes of block-entry visible facts an edge obligation may take as premises (profile
# `join_designs` row `premises`; default: the edge's own guards only): `guard` (the conditions the
# block takes on its way to the join), `domain` (facts on no entry binder), `length` (`List.length`
# facts), `named_eq` (`zesu_named_eq` equations), and the newest call's `newest_call_record`,
# `newest_call_guard`, `newest_call_window` (`newest_call_groups`), `newest_call_named_eq` (the
# named equations of that call layer's binders only: a step over the newest call needs no older
# layer's names, and `named_eq` grows with the call number) and `newest_call_outcome` (every fact on
# that call's outcome binders: its record, guards and the values the code computed from it).
OBLIGATION_PREMISES = ('guard', 'domain', 'length', 'named_eq', 'newest_call_record', 'newest_call_guard',
                       'newest_call_window', 'newest_call_named_eq', 'newest_call_outcome')


def _obligation_rows(designs, key, rows):
    """Add to `rows` the rows of `designs` (profile list `key`) that name an `obligation`."""
    for row in designs:
        if isinstance(row, dict) and row.get('obligation'):
            if not re.fullmatch(r'[A-Za-z]\w*', row['obligation']) or not row.get('lemma_module'):
                raise ValueError(key + ': an obligation needs an identifier and a lemma_module')
            unknown = set(row.get('premises', [])) - set(OBLIGATION_PREMISES)
            if unknown:
                raise ValueError(key + ': unknown obligation premise classes ' + ', '.join(sorted(unknown)))
            rows[normal(design_fact_text(row))] = row
    return rows


def design_obligations(profile, keys=None):
    """{normal text of the stated fact: row} of the join-design rows that name an `obligation` (of the
    joins `keys` of `join_designs`, every join when None): an edge into such a join whose block history
    does not already hold the fact proves it by the lemma `fp_edge<source>_<join>_<obligation>_holds` of
    the row's `lemma_module`, from the classes of block facts the row's `premises` name."""
    rows = {}
    for key, designs in (profile.get('join_designs') or {}).items():
        if keys is None or key in keys:
            _obligation_rows(designs, 'join_designs', rows)
    return rows


def return_obligations(profile, sites=None):
    """{normal text of the stated fact: row} of the `return_facts` rows (profile `calls`) that name an
    `obligation` (of the calls whose `return_site_pc` is in `sites`, every call when None). Such a row
    is a fact of the return site's entry (`zesu_join_history` when `history`): the call block's edge into
    the return site proves it as an edge into a join proves a join design (`design_obligations`)."""
    rows = {}
    for call in profile.get('calls') or []:
        if sites is None or call.get('return_site_pc') in sites:
            _obligation_rows(call.get('return_facts', []), 'return_facts', rows)
    return rows


def obligation_premise_positions(binders, facts, classes):
    """The positions of the facts (an entry's visible facts, over its `binders`) in the premise
    `classes` (`OBLIGATION_PREMISES`; `guard` names no entry fact)."""
    groups = newest_call_groups(binders, facts)
    prefixes = call_prefixes(binders)
    newest_named = (r"zesu_named_eq \(?" + re.escape(prefixes[-1]) + r"\w+\)?\s") if prefixes else None
    outcome = (r"(?<![\w'.])" + re.escape(prefixes[-1]) + CALL_OUTCOME + r"(?![\w'])") if prefixes else None
    tests = {'domain': lambda fact: not any(mentions(binder['name'], fact) for binder in binders),
             'length': is_length_fact,
             'named_eq': lambda fact: re.match(r'zesu_named_eq\b', unwrap(fact)) is not None,
             'newest_call_named_eq': lambda fact: newest_named is not None
             and re.match(newest_named, unwrap(fact)) is not None,
             'newest_call_outcome': lambda fact: outcome is not None and re.search(outcome, fact) is not None}
    for name, patterns in groups.items():
        tests['newest_call_' + name] = lambda fact, patterns=patterns: any(re.search(pattern, fact)
                                                                          for pattern in patterns)
    return [position for position, fact in enumerate(facts)
            if any(tests[name](fact) for name in classes if name in tests)]


def call_prefixes(binders):
    """The call layers whose binders an entry has, oldest first: `call_`, `call2_`, `call3_`, ..."""
    numbers = {int(match[1] or 1) for binder in binders
               for match in [re.match(r'call(\d*)_', binder['name'])] if match}
    return ['call' + ('' if number == 1 else str(number)) + '_' for number in sorted(numbers)]


def call_visible_patterns(pc, calls, block_starts, binders, facts=()):
    """Visible facts of a block that ends in a call or is the return site of one (JOINS.json `calls`).

    The record of the last call (`newest_call_patterns`), the windows of the slice passed to it and
    the named equations of the registers the calls pass on (`named_registers`). Function-domain facts
    and the lengths of live outcome arrays are visible in every block. Records, guards and windows of
    older calls stay hidden."""
    start = int(pc, 0)
    later = [other for other in block_starts if other > start]
    end = min(later) if later else None
    # A tail call (`return_site_pc` null) has no return site.
    involved = any(plan['return_site_pc'] is not None and int(plan['return_site_pc'], 0) == start
                   or start <= int(plan['call_site_pc'], 0) and (end is None or int(plan['call_site_pc'], 0) < end)
                   for plan in calls.values())
    prefixes = call_prefixes(binders)
    if not involved or not prefixes:
        return []
    patterns = newest_call_patterns(binders, facts)
    named = sorted({name for plan in calls.values()
                    for name in [*plan.get('named_registers', {}).values(), *plan.get('named_arguments', {})]})
    if named:
        patterns.append(r"\bzesu_named_eq \(?(?:" + '|'.join(map(re.escape, named)) + r")(?![\w'])")
    return patterns


def loop_entry_patterns(pc, entry_pcs, binders, facts=()):
    """Visible facts of a loop's entry predecessor (a loop design's `entry_predecessor`): the loop
    head's invariant bounds the cursor by the newest call's payload, so that call's record, its
    nonzero guards and its slice window stay visible there as they do in the loop class."""
    return newest_call_patterns(binders, facts) if pc in entry_pcs else []


# A call layer's outcome binders (`call_boundary`): a by-value callee's outcome bytes `<prefix>after`
# and kept cursors `<prefix>kept_*`; a by-reference callee's outcome record `<prefix>result` and the
# words it stored back `<prefix>word_*`.
CALL_OUTCOME = r"(?:after|result|word_\w+)"
# A call record: the callee interface's predicates on the call (`…CallDomain`, `…CallMeaning`,
# `…CallResult`).
CALL_RECORD = r"\w+Call(?:Domain|Meaning|Result)\b"
# A window fact `base <= bv_unsigned p /\ bv_unsigned p + bv_unsigned l <= …` (`call_boundary`).
WINDOW_FACT = re.compile(r"[\s\S]*?<= bv_unsigned (?P<p>[\s\S]+?) /\\ bv_unsigned (?P=p) \+ bv_unsigned "
                         r"(?P<l>[\s\S]+?) <= ")


def _terms(text):
    """The parenthesised subterms of a fact, each without parentheses and whitespace."""
    terms, stack = set(), []
    for position, character in enumerate(text):
        if character == '(':
            stack.append(position)
        elif character == ')' and stack:
            terms.add(re.sub(r'[\s()]', '', text[stack.pop() + 1:position]))
    return terms


def newest_call_groups(binders, facts=()):
    """The patterns of `newest_call_patterns` by group: `record`, `guard`, `window`."""
    prefixes = call_prefixes(binders)
    if not prefixes:
        return {'record': [], 'guard': [], 'window': []}
    newest = re.escape(prefixes[-1])
    outcome = r"(?<![\w'.])" + newest + CALL_OUTCOME + r"(?![\w'])"
    kept = r"\(?" + newest + r"kept_\w+\)?"
    record = [CALL_RECORD + r"(?=[\s\S]*" + outcome + ")", outcome + r"[\s\S]*" + CALL_RECORD]
    window = [r"<= bv_unsigned " + kept + r" /\\ bv_unsigned " + kept + r" \+ bv_unsigned "]
    arguments = set().union(*[_terms(fact) for fact in facts
                              if any(re.search(pattern, fact) for pattern in record)])
    for fact in facts:
        match = WINDOW_FACT.match(unwrap(fact))
        if match and all(re.sub(r'[\s()]', '', match[part]) in arguments for part in ('p', 'l')):
            window.append('^' + re.escape(fact) + '$')
    return {'record': record, 'guard': [r"^(?=[\s\S]*" + outcome + r")(?=[\s\S]*<> \(0%Z\))"], 'window': window}


def newest_call_patterns(binders, facts=()):
    """The record of the newest call layer an entry has (`…CallDomain`/`…CallMeaning`/`…CallResult`
    on its outcome binders), its nonzero guards on those binders and the windows of the slice it was
    passed: over its kept cursors, and every window fact (`facts`) whose pointer and length are
    argument terms of the record. Visible at call and return sites and in loop classes; older records
    stay hidden."""
    groups = newest_call_groups(binders, facts)
    return groups['record'] + groups['guard'] + groups['window']


def classify(binders, resources, facts, visible_patterns=(), pinned=(), definitional=False, weak_patterns=(),
             visible_texts=()):
    """Split binders into live and ghost and facts into visible and hidden.

    binders: [{'name', 'type'}]; resources, facts: texts (facts without the pure brackets).
    weak_patterns: facts that stay visible when every binder they mention is live for another
    reason, but pin no binder: a binder that only such a fact mentions has no resource and no
    record to take its value from at the successor, so it stays in the history (its facts too).
    visible_texts: facts (`normal` texts) that stay visible as the weak patterns do (`backward_pins`)."""
    visible_texts = set(visible_texts)
    # A fact that matches a visible pattern (access or call facts) pins its binders live.
    pinned = set(pinned) | {binder['name'] for binder in binders for fact in facts
                            if not is_join_history(fact)
                            and any(re.search(pattern, fact, re.S) for pattern in visible_patterns)
                            and mentions(binder['name'], fact)}
    visible_patterns = tuple(visible_patterns) + tuple(weak_patterns)
    live = [binder for binder in binders
            if binder['name'] in pinned or any(mentions(binder['name'], text) for text in resources)]
    live_names = {binder['name'] for binder in live}
    ghost = [binder for binder in binders if binder['name'] not in live_names]
    visible, hidden = [], []
    for fact in facts:
        if unwrap(fact) == 'True':
            continue
        named = [binder['name'] for binder in binders if mentions(binder['name'], fact)]
        on_ghost = any(name not in live_names for name in named)
        keep = not on_ghost and not is_join_history(fact) and (
            not named or is_length_fact(fact) or any(re.search(pattern, fact, re.S) for pattern in visible_patterns)
            or normal(fact) in visible_texts)
        # Loop classes: `b = <closed term>` fixes the value of a live binder; it is
        # state, not history, and stays visible (decodeItem's loop end register).
        if (definitional and not keep and len(named) == 1 and named[0] in live_names
                and re.fullmatch(re.escape(named[0]) + r'\s*=\s*.*', unwrap(fact), re.S)):
            keep = True
        (visible if keep else hidden).append(fact)
    ghost = [binder for binder in ghost if any(mentions(binder['name'], fact) for fact in hidden)]
    return live, ghost, visible, hidden


def telescope(binders):
    return ' '.join('(' + binder['name'] + ' : ' + binder['type'] + ')' for binder in binders)


def conjunction(facts):
    return ' /\\ '.join('(' + unwrap(fact) + ')' for fact in facts) if facts else 'True'


def seal_alternative(name, plain_telescope, plain_binders, binders, resources, facts, visible_patterns=(), pinned=(),
                     grouped=False, varying=(), weak_patterns=(), visible_texts=()):
    """Return (declarations, body, meta) of one sealed entry variant; None when its history is empty.

    declarations: [(symbol, text, kind)] with kind 'hist' (needs opacity in Structural) or 'aux';
    body: the iProp body of the entry variant; meta: the data that the edge record reads.
    weak_patterns: the profile's `hist_visible` (and a loop design's `visible`): see `classify`.
    pinned, visible_texts: also the binders and facts that `backward_pins` carries to this entry.
    A variant with no hidden fact and no ghost binder (every fact visible) has nothing to seal: the
    caller renders the plain shape, all binders kept, and no edge instance enters or leaves it."""
    live, ghost, visible, hidden = classify(binders, resources, facts, visible_patterns, pinned,
                                            definitional=grouped, weak_patterns=weak_patterns,
                                            visible_texts=visible_texts)
    if not hidden and not ghost:
        return None
    hist = name + '_Hist'
    # The history takes only the live binders its facts mention. A loop class keeps
    # every fact on a loop-varying binder visible, so its history is the same on both sides of the
    # back edge and on the exit edge (identity, no binder renames).
    hist_live = [binder for binder in live if any(mentions(binder['name'], fact) for fact in hidden)]
    clash = [binder['name'] for binder in hist_live if binder['name'] in varying]
    if clash:
        raise ValueError(name + ': a hidden fact mentions a loop-varying binder: ' + ', '.join(clash))
    parameters = plain_telescope + (' ' + telescope(hist_live) if hist_live else '')
    proposition = conjunction(hidden)
    if ghost:
        proposition = '∃ ' + telescope(ghost) + ', ' + proposition
    arguments = ''.join(' (' + binder['name'] + ')' for binder in plain_binders + hist_live)
    declarations = [(hist, 'Definition ' + hist + parameters + ' : Prop := (' + proposition + ').\n', 'hist')]
    application = 'zesu_hist (' + hist + arguments + ')'
    if grouped:
        # A loop class keeps its shape: the resources in one group, then one conjunction of visible facts.
        body = ('(' + ' ∗ '.join(resources) + ') ∗ ⌜' + conjunction(visible) + '⌝ ∗ ⌜' + application + '⌝')
    else:
        parts = list(resources) + ['⌜' + fact + '⌝' for fact in visible] + ['⌜' + application + '⌝']
        body = '(' + ' ∗ '.join(parts) + ')'
    if live:
        body = '(∃ ' + telescope(live) + ', ' + body + ')'
    elif grouped:
        body = '(' + body + ')'
    meta = {'entry': name, 'hist': hist, 'mode': 'wrap', 'parameters': plain_binders,
            'live': live, 'hist_live': hist_live, 'varying': list(varying), 'ghost': ghost, 'resources': list(resources), 'visible': visible, 'hidden': hidden,
            'dropped_binders': [binder['name'] for binder in binders
                                if binder not in live and binder not in ghost]}
    return declarations, body, meta


def backward_pins(variants, edges, witnessed=()):
    """The binders and facts that each entry must show so that its successors' live binders have a value.

    A successor binder that is live without a resource takes its value from the block before the
    successor: nothing at the successor fixes it. The block entry before it must hold that value
    live, with the successor's visible facts on it visible, or the block cannot choose the witness.
    So each predecessor entry variant that has the binder (live, or a ghost of its history) gets it
    pinned live and those facts visible; a predecessor that holds no resource for it passes the need
    on to its own predecessors, back to the block that binds the value from a resource.

    variants: {pc: [meta]} (meta keys 'live', 'ghost', 'resources', 'visible' of `seal_alternative`);
    edges: [(pre_pc, succ_pc)]; witnessed: (pre_pc, succ_pc, name) of a successor binder that the edge
    gives a term (a join witness): its value comes from that term, not from the same name.
    Returns {pc: {'pinned': [names], 'facts': [normal texts]}}, sorted."""
    witnessed = set(witnessed)
    predecessors = {}
    for pre, succ in edges:
        predecessors.setdefault(succ, set()).add(pre)

    def names(meta, key):
        return {binder['name'] for binder in meta.get(key, [])}

    def unbound(meta, name):
        return not any(mentions(name, text) for text in meta.get('resources', []))

    work = [(pc, name, frozenset(normal(fact) for fact in meta.get('visible', []) if mentions(name, fact)))
            for pc, metas in variants.items() for meta in metas
            for name in sorted(names(meta, 'live')) if unbound(meta, name)]
    pins = {}
    while work:
        succ, name, facts = work.pop()
        for pre in sorted(predecessors.get(succ, ())):
            if (pre, succ, name) in witnessed:
                continue
            for meta in variants.get(pre, []):
                if name not in names(meta, 'live') | names(meta, 'ghost'):
                    continue
                row = pins.setdefault(pre, {'pinned': set(), 'facts': set()})
                grows = name not in row['pinned'] or not facts <= row['facts']
                row['pinned'].add(name)
                row['facts'] |= facts
                if grows and unbound(meta, name):
                    work.append((pre, name, facts | {normal(fact) for fact in meta.get('visible', [])
                                                     if mentions(name, fact)}))
    return {pc: {'pinned': sorted(row['pinned']), 'facts': sorted(row['facts'])} for pc, row in sorted(pins.items())}


def _result_offset(address, base):
    """Offset of a Z address text from `bv_unsigned (<pointer>)` (compact text `base`), or None
    when the address is not on that pointer."""
    compact = re.sub(r'[\s()]', '', address.replace('%Z', ''))
    if base not in compact:
        return None
    if compact == base:
        return 0
    match = (re.fullmatch(r'Z\.add' + re.escape(base) + r'(\d+)', compact)
             or re.fullmatch(re.escape(base) + r'\+(\d+)', compact))
    if match is None:
        raise ValueError('exit_result: an address on the result pointer is not pointer plus a numeral: '
                         + address)
    return int(match[1])


def _top_groups(text):
    """The top-level parenthesized groups of text, without their outer parentheses."""
    groups, depth, start = [], 0, None
    for position, character in enumerate(text):
        if character == '(':
            if depth == 0:
                start = position + 1
            depth += 1
        elif character == ')':
            depth -= 1
            if depth == 0:
                groups.append(text[start:position])
    return groups


def array_definition_piece(text):
    """(address, list) of an owned array rendered through its declaration
    `isla.ghost_state.mem_mapsto_array_def (a) (q) (l)`, or None."""
    text = normal(text)
    prefix = 'isla.ghost_state.mem_mapsto_array_def'
    if not text.startswith(prefix):
        return None
    groups = _top_groups(text[len(prefix):])
    return (groups[0], groups[2]) if len(groups) == 3 else None


def _cons_spine_length(value):
    """Number of elements of a `Coq.Init.Datatypes.cons` spine ending in `nil` whose elements hold no list."""
    if 'Datatypes.nil' not in value or value.count('Datatypes.nil') != 1:
        return None
    return value.count('Datatypes.cons')


def result_declarations(name, plain_telescope, plain_binders, meta, pieces, region):
    """Data-only declarations of the result a return package leaves (profile `compliance.exit_result`).

    `<name>_ResultBytes`: the bytes of the result region in address order; a piece the package stores
    is its byte list, a piece it does not write is a list parameter `unwritten_<offset>`.
    `<name>_ExitMeaning M`: for all binders, the package's history, its visible facts and the lengths of
    the unwritten pieces imply `M args (<name>_ResultBytes ...)`.
    pieces: [(kind, address text, value text)] of the package's memory components, kind 'byte_array'
    (value: the stored list) or 'unknown_byte_array' (value: the length). region: {'pointer': term,
    'size': bytes}. Returns [(symbol, text, 'aux')]."""
    base = 'bv_unsigned' + re.sub(r'[\s()]', '', region['pointer'])
    rows = []
    for kind, address, value in pieces:
        offset = _result_offset(address, base)
        if offset is None:
            continue
        if kind == 'unknown_byte_array':
            length = str(CONSTANTS.get(unwrap(value), {}).get('value', unwrap(value).replace('%Z', '')))
            if not re.fullmatch(r'\d+', length):
                raise ValueError('exit_result: an unwritten piece has no numeral length: ' + value)
            rows.append((offset, int(length), None))
        elif kind == 'byte_array':
            items = _list_items(value)
            count = len(items) if items is not None else _cons_spine_length(value)
            if count is None:
                raise ValueError('exit_result: a stored piece is not an explicit byte list: ' + value)
            rows.append((offset, count, unwrap(value)))
        else:
            raise ValueError('exit_result: a result piece of kind ' + kind)
    rows.sort()
    cursor = 0
    for offset, length, _ in rows:
        if offset != cursor:
            raise ValueError(name + ': the result region is not covered without gap or overlap at ' + str(offset)
                             + ' (pieces at offset, length: '
                             + ', '.join(str(row[0]) + ', ' + str(row[1]) for row in rows) + ')')
        cursor += length
    if cursor != region['size']:
        raise ValueError(name + ': the result pieces cover ' + str(cursor) + ' of ' + str(region['size']) + ' bytes')
    stored = ' '.join(text for _, _, text in rows if text is not None)
    unwritten = [{'name': 'unwritten_' + str(offset), 'type': 'list byte', 'length': length}
                 for offset, length, text in rows if text is None]
    used = [binder for binder in meta['live'] if mentions(binder['name'], stored)]
    result = name + '_ResultBytes'
    parameters = plain_telescope + ''.join(' ' + telescope([binder]) for binder in used + unwritten)
    body = ' ++ '.join('(' + text + ')' if text is not None else 'unwritten_' + str(offset)
                       for offset, _, text in rows)
    declarations = [(result, 'Definition ' + result + parameters + ' : list byte := (' + body + ').\n', 'aux')]
    facts = ['zesu_hist (' + meta['hist'] + ''.join(' (' + binder['name'] + ')'
                                                     for binder in plain_binders + meta['hist_live']) + ')']
    facts += [unwrap(fact) for fact in meta['visible']]
    facts += ['length ' + binder['name'] + ' = ' + str(binder['length']) + '%nat' for binder in unwritten]
    quantified = [binder for binder in meta['live'] if binder in used or binder in meta['hist_live']
                  or any(mentions(binder['name'], fact) for fact in meta['visible'])]
    application = ('M ' + plain_binders[0]['name'] + ' (' + result
                   + ''.join(' (' + binder['name'] + ')' for binder in plain_binders + used + unwritten) + ')')
    meaning = name + '_ExitMeaning'
    declarations.append((meaning, 'Definition ' + meaning + ' (M : ' + plain_binders[0]['type']
                         + ' -> list byte -> Prop) : Prop := forall' + plain_telescope
                         + ''.join(' ' + telescope([binder]) for binder in quantified + unwritten) + ', '
                         + ' -> '.join('(' + fact + ')' for fact in facts) + ' -> ' + application + '.\n', 'aux'))
    return declarations


def structural_opacity(symbol, kind):
    """The Structural lines of a history declaration: opacity only, no unfold instance, no introduction."""
    return '#[export] Typeclasses Opaque ' + symbol + '.\n' if kind == 'hist' else ''


# ---- per-slot frame cells ----

MASK = (1 << 64) - 1


def affine(expression):
    """(symbol text, constant) of a bvadd/bvsub chain over one input; None otherwise."""
    op = expression.get('op')
    if op == 'input':
        return expression['value'], 0
    if op == 'bits':
        return None, expression['value']
    if op in ('bvadd', 'bvsub'):
        left, right = (affine(argument) for argument in expression['args'])
        if left is None or right is None or (left[0] is not None and right[0] is not None):
            return None
        if op == 'bvsub' and right[0] is not None:
            return None
        constant = (left[1] + right[1]) if op == 'bvadd' else (left[1] - right[1])
        return left[0] if left[0] is not None else right[0], constant & MASK
    return None


def signed(value):
    return value - (1 << 64) if value >> 63 else value


def frame_slot_table(forward, coq):
    """The saved-register slots of the function's frame, from the entry seed's first stores.

    A slot is an 8-byte store of the prologue whose address is the entry stack pointer plus a constant
    and whose value is an entry register. Returns {'pointer': symbol, 'slots': {offset from the entry
    stack pointer: address term as the store computes it}}. coq renders an expression."""
    entry = forward['boundaries'][0]['pc']
    states = [row['state'] for row in forward.get('stops', []) + forward.get('exits', [])
              if row.get('seed_pc') == entry]
    for boundary in forward['boundaries']:
        states += [row['state'] for row in boundary['alternatives'] if row.get('seed_pc') == entry]
    pointer = affine(forward['boundaries'][0]['alternatives'][0]['state']['registers']['x2'])
    table = {'pointer': pointer[0] if pointer else None, 'slots': {}}
    if pointer is None or pointer[0] is None or pointer[1] != 0:
        return table
    for state in states:
        for write in state.get('writes', []):
            address = affine(write['address'])
            if (write.get('size') == 8 and address and address[0] == pointer[0]
                    and write['value'].get('op') == 'input'):
                table['slots'][signed(address[1])] = coq(write['address'])
    return table


def frame_writes(rows, forward):
    """The stores of a `frame` annotation at one join (profile `join_frames[pc]`: [{offset, coq}]):
    an 8-byte store of the value `coq` at the slot's address as the prologue computes it
    (`frame_slot_table`). An offset the prologue does not store is refused."""
    import json
    from symbolic_state import Expr, MemoryWrite, input_expr
    table = frame_slot_table(forward, lambda value: json.dumps(value, sort_keys=True))
    writes = []
    for row in rows:
        address = table['slots'].get(row['offset'])
        if address is None:
            raise ValueError('join_frames: the prologue stores no saved register at offset %d' % row['offset'])
        writes.append(MemoryWrite(address=Expr.from_dict(json.loads(address)), value=input_expr(row['coq'], 64),
                                  size=8, provenance={'join_frame': row}))
    return writes


def region_offsets(forward):
    """{normal Z address text: (pointer symbol, signed offset)} of every recorded owned region."""
    result = {}
    rows = [row for boundary in forward['boundaries'] for row in boundary['alternatives']]
    rows += forward.get('exits', []) + forward.get('tail_returns', [])
    for row in rows:
        for alternative in row.get('alternatives', [row]):
            accounting = alternative.get('resource_boundary', {}).get('write_accounting', {})
            for resource in accounting.get('resources', []):
                base = affine(resource['base']) if isinstance(resource.get('base'), dict) else None
                if base and base[0] is not None and resource.get('address_z'):
                    result[normal(resource['address_z'].replace('%Z', ''))] = (base[0], signed(base[1]))
    return result


_BYTE_ASCRIPTION = re.compile(r'^\((.*) : bv 8%N\)$', re.S)


def _cons_items(value):
    """The items of a byte list spelled as the forward pass writes a stored span
    (`Coq.Init.Datatypes.cons (b : bv 8%N) (… (@Coq.Init.Datatypes.nil (bv 8%N)))`); None otherwise."""
    items = []
    while True:
        value = unwrap(value)
        if re.fullmatch(r'@?Coq\.Init\.Datatypes\.nil(?: \(bv 8%N\))?', value):
            return items
        if not value.startswith('Coq.Init.Datatypes.cons ('):
            return None
        start = len('Coq.Init.Datatypes.cons ')
        end = _group_end(value, start)
        item = value[start:end]
        ascribed = _BYTE_ASCRIPTION.fullmatch(item)
        items.append('(' + ascribed[1].strip() + ')' if ascribed else item)
        value = value[end:].strip()


def _list_items(value):
    value = unwrap(value)
    if value.startswith('Coq.Init.Datatypes.cons '):
        return _cons_items(value)
    if not (value.startswith('[') and value.endswith(']')):
        return None
    items, depth, start = [], 0, 1
    for position in range(1, len(value) - 1):
        character = value[position]
        if character in '([':
            depth += 1
        elif character in ')]':
            depth -= 1
        elif character == ';' and depth == 0:
            items.append(value[start:position].strip())
            start = position + 1
    items.append(value[start:len(value) - 1].strip())
    return items


def _word_of_bytes(items):
    """The 64-bit term whose little-endian bytes the eight items are; None otherwise."""
    words = set()
    for index, item in enumerate(items):
        match = re.fullmatch(r'bv_extract (\d+)%N 8%N (.*)', unwrap(item), re.S)
        if match is None or int(match[1]) != 8 * index:
            return None
        words.add(unwrap(match[2]))
    return words.pop() if len(words) == 1 else None


def _group_end(text, start):
    """The end (exclusive) of the balanced group that opens at text[start]."""
    depth = 0
    for position in range(start, len(text)):
        if text[position] in '([':
            depth += 1
        elif text[position] in ')]':
            depth -= 1
            if depth == 0:
                return position + 1
    raise ValueError('An entry term has unbalanced delimiters: ' + text[start:start + 80])


def _application(text):
    """The head and top-level arguments of an application text without outer parentheses."""
    parts, position = [], 0
    while position < len(text):
        if text[position].isspace():
            position += 1
            continue
        end = _group_end(text, position) if text[position] in '([' else position
        while end < len(text) and not text[end].isspace() and text[end] not in '([':
            end += 1
        parts.append(text[position:end])
        position = end
    return parts


def _literal_nth(text):
    """The element text of `List.nth K%nat [literal list] d` with K inside the list; None otherwise."""
    parts = _application(unwrap(text))
    if len(parts) != 4 or parts[0] != 'List.nth':
        return None
    index = re.fullmatch(r'(\d+)%nat', parts[1])
    items = _list_items(parts[2])
    if index is None or items is None or items == [''] or int(index[1]) >= len(items):
        return None
    return unwrap(items[int(index[1])])


def _concat_leaves(text):
    """The operands of a `bv_concat` tree, most significant first."""
    parts = _application(unwrap(text))
    if len(parts) == 4 and parts[0] == 'bv_concat':
        return _concat_leaves(parts[2]) + _concat_leaves(parts[3])
    return [unwrap(text)]


def fold_literal_words(text):
    """Read a word loaded from a literal byte list as the term the frame cell holds.

    The forward pass reads a saved-register slot of the packed frame array as
    `bv_concat 64 … (List.nth K [b0; …; bn] d) …`; the entry states that slot as the cell
    `a ↦ₘ W` (`slot_components`). Two rewrites make a register or fact state the same `W`:
    `List.nth K [literal list] d` with K inside the list is its K-th element (by computation),
    and a 64-bit `bv_concat` tree whose eight bytes are `bv_extract 56 8 W`, …, `bv_extract 0 8 W`
    is `W`."""
    position = 0
    while (position := text.find('(List.nth ', position)) >= 0:
        end = _group_end(text, position)
        element = _literal_nth(text[position:end])
        if element is None:
            position += 1
            continue
        text = text[:position] + '(' + element + ')' + text[end:]
    position = 0
    while (position := text.find('(bv_concat 64%N ', position)) >= 0:
        end = _group_end(text, position)
        leaves = _concat_leaves(text[position:end])
        word = (_word_of_bytes(list(reversed(leaves))) if len(leaves) == 8
                and all(re.fullmatch(r'bv_extract \d+%N 8%N .*', leaf, re.S) for leaf in leaves) else None)
        if word is None:
            position += 1
            continue
        text = text[:position] + '(' + word + ')' + text[end:]
    return text


def slot_binder_name(offset):
    """The binder of an unknown saved-register slot at `offset` from the entry stack pointer
    (`slot_components`): `frame_old_m8` for -8. A join design (annotation `frame` row) names it."""
    return 'frame_old_' + (str(offset) if offset >= 0 else 'm' + str(-offset))


def slot_components(kind, address, value, table, regions, taken):
    """Split one memory component at the frame's saved-register slots.

    Returns ([component text], [new binder]) or None when the component holds no slot.
    kind: 'byte_array' (value: byte-list term) or 'unknown_byte_array' (value: length)."""
    region = regions.get(normal(address.replace('%Z', '')))
    if region is None or region[0] != table['pointer'] or not table['slots']:
        return None
    start = region[1]
    if kind == 'unknown_byte_array':
        # A length may be a named constant of the function domain (DOMAIN.json `constants`).
        value = str(CONSTANTS.get(unwrap(value), {}).get('value', unwrap(value)))
        if not re.fullmatch(r'\d+', value):
            return None
        length, items = int(value), None
    else:
        items = _list_items(value)
        if items is None:
            return None
        length = len(items)
    inside = sorted(offset for offset in table['slots'] if start <= offset and offset + 8 <= start + length)
    if not inside:
        return None
    base = unwrap(address.replace('%Z', ''))
    texts, binders, cursor = [], [], start

    def piece(begin, end):
        if begin == end:
            return
        location = '(' + base + ')' if begin == start else '((' + base + ') + ' + str(begin - start) + ')'
        if items is None:
            texts.append(location + ' ↦ₘ? (' + str(end - begin) + ')')
        else:
            texts.append(location + ' ↦ₘ∗ ([' + '; '.join(items[begin - start:end - start]) + '])')

    for offset in inside:
        piece(cursor, offset)
        cell = '(bv_unsigned ' + table['slots'][offset] + ')'
        if items is None:
            name = slot_binder_name(offset)
            while name in taken:
                name += "'"
            taken.add(name)
            binders.append({'name': name, 'type': 'bv 64'})
            texts.append(cell + ' ↦ₘ (' + name + ')')
        else:
            word = _word_of_bytes(items[offset - start:offset - start + 8])
            if word is None:
                texts.append(cell + ' ↦ₘ∗ ([' + '; '.join(items[offset - start:offset - start + 8]) + '])')
            else:
                texts.append(cell + ' ↦ₘ (' + word + ')')
        cursor = offset + 8
    piece(cursor, start + length)
    return texts, binders


# ---- loop classes (render_fp301_statements.render_loop_head) ----

SLOT_TABLE = SLOT_REGIONS = None
CONSTANTS = {}


# A design placeholder stands for one term: it never spans a conjunction or disjunction, so a design
# fact never matches a conjunct of a larger fact (a call's slice window `base <= start /\ …` against
# the payload-start fact `base <= {x11}`).
TERM = r"(?:(?!/\\|\\/).)+?"


def design_patterns(design):
    """Regular expressions of the loop design facts: `{name}` stands for any term (no connective)."""
    patterns = []
    for fact in design.get('facts', []):
        text = re.sub(r'\s+', ' ', fact['coq'].strip())
        pieces = re.split(r'(\{[^}]*\})', text)
        patterns.append(''.join(TERM if piece.startswith('{') else re.escape(piece).replace('\\ ', r'\s*')
                                for piece in pieces))
    return patterns


def parse_binders(text):
    from boundary_guards import binder_groups
    result = []
    for names, group in binder_groups(text):
        kind = group[1:-1].split(':', 1)[1].strip()
        result.extend({'name': name, 'type': kind} for name in names)
    return result


def seal_class(name, prefix, binders_text, resources, facts, plain_binders, design, visible=()):
    """Return (declarations, class text, meta) of one loop class; None if nothing changes."""
    binders = parse_binders(binders_text)
    slot_reports = []
    if FRAME_SLOTS and SLOT_TABLE:
        taken, pieces = {binder['name'] for binder in binders}, []
        for resource in resources:
            match = re.fullmatch(r'(.*?) (↦ₘ∗|↦ₘ\?) (.*)', resource, re.S)
            split = match and slot_components('byte_array' if match[2] == '↦ₘ∗' else 'unknown_byte_array',
                                              match[1], match[3], SLOT_TABLE, SLOT_REGIONS, taken)
            if split:
                pieces.extend(split[0])
                binders.extend(split[1])
                slot_reports.append({'address': match[1], 'pieces': len(split[0])})
            else:
                pieces.append(resource)
        resources = pieces
    def plain():
        if not slot_reports:
            return None
        text = (prefix + ':= (∃ ' + telescope(binders) + ', (' + ' ∗ '.join(resources) + ') ∗ ⌜'
                + conjunction(facts) + '⌝)%I.\n')
        return [], text, {'entry': name, 'frame_slots': slot_reports}
    # The loop-varying binders are the design's registers (by binder name, or by the
    # class's register resource when the design names its seed binders) and the index.
    names = {binder['name'] for binder in binders}
    register_binders = {}
    for resource in resources:
        match = re.fullmatch(r'"(x\d+)" ↦ᵣ RVal_Bits \((\w+) : bv 64%N\)', resource.strip())
        if match and match[2] in names:
            register_binders[match[1]] = match[2]
    registers = [register_binders.get(register, binder) for register, binder in design.get('registers', {}).items()]
    registers = [binder for binder in registers + [design.get('index')] if binder in names]
    # Call facts: the newest call layer's record, guards and window (its payload is what the loop reads);
    # older records and the named equations of older cursors stay in the class history.
    patterns = (newest_call_patterns(binders, facts) + design_patterns(design)
                + [r"(?<![\w'.])" + re.escape(binder) + r"(?![\w'])" for binder in registers])
    sealed = seal_alternative(
        name, ' ' + telescope(plain_binders), plain_binders, binders, resources, facts,
        visible_patterns=patterns, pinned=registers, grouped=True, varying=registers, weak_patterns=list(visible))
    if sealed is None:
        return plain()
    declarations, body, meta = sealed
    meta['frame_slots'] = slot_reports
    meta['loop_class'] = True
    return declarations, prefix + ':= ' + body + '%I.\n', meta
