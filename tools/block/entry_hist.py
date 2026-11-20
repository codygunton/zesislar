"""Hidden history and per-slot frame cells for FP301 entries.

The function profile selects the shape (`configure`):
  `"entry_hist": "wrap"`  (required; the only shape) the pure facts of one entry variant become
                          visible facts and one hidden
                          `⌜zesu_hist (<entry>_Hist args returnAddress <live binders>)⌝`.
  `"frame_slots": true`   each saved-register slot of the frame is one 8-byte cell at the address the
                          store computes.

Visible facts: facts that mention no entry binder (function domain, return alignment), `List.length`
facts of live binders, and facts that match a profile `hist_visible` regular expression. Every other
fact is hidden; a join history (`zesu_join_history`) is always hidden. A live binder is one that an
owned resource mentions; the others are ghost binders and are bound inside the history.
"""
import re

FRAME_SLOTS = False
HIST_VISIBLE = ()
STORE_SPLICE = 'linear'
HIST_LIBRARY = 'Require Import ZesuSsz.Automation2.Hist.\n'


def configure(profile):
    """Read the shape keys of a function profile: `entry_hist` (required, `wrap`), `frame_slots`,
    `hist_visible`, `store_splice` (`linear`, default, or `per_store`: constant-offset stores into a byte
    array are spliced one by one, the spelling the function's proofs consume)."""
    global FRAME_SLOTS, HIST_VISIBLE, STORE_SPLICE
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


def call_prefixes(binders):
    """The call layers whose binders an entry has, oldest first: `call_`, `call2_`, `call3_`, ..."""
    numbers = {int(match[1] or 1) for binder in binders
               for match in [re.match(r'call(\d*)_', binder['name'])] if match}
    return ['call' + ('' if number == 1 else str(number)) + '_' for number in sorted(numbers)]


def call_visible_patterns(pc, calls, block_starts, binders):
    """Visible facts of a block that ends in a call or is the return site of one (JOINS.json `calls`).

    The record of the last call (`…CallDomain`/`…CallMeaning` facts on the newest call layer's
    binders), its nonzero guards on that outcome (`… <> (0%Z)`), its slice window over the newest
    kept cursors (`call_boundary` `<call>window_<binder>`) and the named equations of the registers
    the calls pass on (`named_registers`). Function-domain facts and the lengths of live outcome
    arrays are visible in every block. Records, guards and windows of older calls stay hidden."""
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
    patterns = newest_call_patterns(binders)
    named = sorted({name for plan in calls.values() for name in plan.get('named_registers', {}).values()})
    if named:
        patterns.append(r"\bzesu_named_eq \(?(?:" + '|'.join(map(re.escape, named)) + r")(?![\w'])")
    return patterns


def newest_call_patterns(binders):
    """The record of the newest call layer an entry has (`…CallDomain`/`…CallMeaning` on its outcome
    `<prefix>after`), its nonzero guards on that outcome and its slice window over its kept cursors.
    Visible at call and return sites and in loop classes; older records stay hidden."""
    prefixes = call_prefixes(binders)
    if not prefixes:
        return []
    newest = re.escape(prefixes[-1])
    # A call record names the call's outcome bytes `<prefix>after`.
    outcome = r"(?<![\w'.])" + newest + r"after(?![\w'])"
    kept = r"\(?" + newest + r"kept_\w+\)?"
    return [r"\w+Call(?:Domain|Meaning)\b(?=[\s\S]*" + outcome + ")", outcome + r"[\s\S]*\w+Call(?:Domain|Meaning)\b",
            r"^(?=[\s\S]*" + outcome + r")(?=[\s\S]*<> \(0%Z\))",
            r"<= bv_unsigned " + kept + r" /\\ bv_unsigned " + kept + r" \+ bv_unsigned "]


def classify(binders, resources, facts, visible_patterns=(), pinned=(), definitional=False):
    """Split binders into live and ghost and facts into visible and hidden.

    binders: [{'name', 'type'}]; resources, facts: texts (facts without the pure brackets)."""
    # A fact that matches a visible pattern (access or call facts) pins its binders live.
    pinned = set(pinned) | {binder['name'] for binder in binders for fact in facts
                            if not is_join_history(fact)
                            and any(re.search(pattern, fact, re.S) for pattern in visible_patterns)
                            and mentions(binder['name'], fact)}
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
            not named or is_length_fact(fact) or any(re.search(pattern, fact, re.S) for pattern in visible_patterns))
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
                     grouped=False, varying=()):
    """Return (declarations, body, meta) of one sealed entry variant; None when its history is empty.

    declarations: [(symbol, text, kind)] with kind 'hist' (needs opacity in Structural) or 'aux';
    body: the iProp body of the entry variant; meta: the data that the edge record reads.
    A variant with no hidden fact and no ghost binder (every fact visible) has nothing to seal: the
    caller renders the plain shape, all binders kept, and no edge instance enters or leaves it."""
    live, ghost, visible, hidden = classify(binders, resources, facts, visible_patterns, pinned,
                                            definitional=grouped)
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


def _list_items(value):
    value = unwrap(value)
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
            name = 'frame_old_' + (str(offset) if offset >= 0 else 'm' + str(-offset))
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
    patterns = (list(visible) + newest_call_patterns(binders) + design_patterns(design)
                + [r"(?<![\w'.])" + re.escape(binder) + r"(?![\w'])" for binder in registers])
    sealed = seal_alternative(
        name, ' ' + telescope(plain_binders), plain_binders, binders, resources, facts,
        visible_patterns=patterns, pinned=registers, grouped=True, varying=registers)
    if sealed is None:
        return plain()
    declarations, body, meta = sealed
    meta['frame_slots'] = slot_reports
    meta['loop_class'] = True
    return declarations, prefix + ':= ' + body + '%I.\n', meta
