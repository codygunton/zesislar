"""Inherited join binders without a holder, and per-site function-return packages."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from join_generalize import (_list_items, _mentions_free, _register_definition, _span_bytes, align_history_groups,
                             check_fact_accounting, common_root_ancestor, drop_unheld_binders, history_members)
from forward_resources import OwnedBytes
from symbolic_state import Expr, MemoryRegion, SymbolicState, bits, input_expr, operation
from function_profiles import return_site
from loop_design import reseat_orphaned
import entry_hist


def state_with(registers, conditions):
    state = SymbolicState(registers=dict(registers))
    state.conditions = list(conditions)
    return state


class UnheldBinders(unittest.TestCase):
    b = input_expr('machine_x10', 64)

    def run_rules(self, state, live, components=()):
        plan = {'binders': []}
        drop_unheld_binders(state, list(components), {}, [{'name': 'machine_x10', 'type': 'bv 64'}], plan, live,
                            lambda key, writes: '')
        return plan

    def test_a_defining_equation_is_substituted(self):
        entry = input_expr('(Z_to_bv 64%N (n args))', 64)
        state = state_with({'x13': operation('bvadd', self.b, bits(1, 64))},
                           [operation('=', self.b, entry)])
        plan = self.run_rules(state, live=['x13'])
        self.assertEqual(state.registers['x13'], operation('bvadd', entry, bits(1, 64)))
        self.assertEqual(state.conditions, [])
        self.assertEqual(plan['dropped_binders'][0]['rule'], 'definition')

    def test_a_dead_register_gets_a_fresh_binder_and_its_conditions_go(self):
        guard = operation('bvult', self.b, bits(8, 64))
        state = state_with({'x13': operation('bvadd', self.b, bits(1, 64)), 'x1': input_expr('ra', 64)}, [guard])
        plan = self.run_rules(state, live=['x1', 'x2'])
        self.assertEqual(state.registers['x13'], input_expr('machine_x13_1', 64))
        self.assertEqual(state.conditions, [])
        self.assertEqual(plan['binders'], [{'name': 'machine_x13_1', 'type': 'bv 64', 'value_key': 'x13'}])
        self.assertEqual(plan['dropped_binders'][0]['registers'], ['x13'])

    def test_a_live_register_forgets_the_binder(self):
        guard = operation('bvult', self.b, bits(8, 64))
        for live in (['x13'], None):  # Without liveness every register counts as live.
            state = state_with({'x13': operation('bvadd', self.b, bits(1, 64))}, [guard])
            components = [{'id': 'fact', 'kind': 'opaque', 'source': '⌜bv_unsigned machine_x10 < 8⌝'},
                          {'id': 'other', 'kind': 'opaque', 'source': '⌜True⌝'}]
            plan = self.run_rules(state, live=live, components=components)
            self.assertEqual(state.registers['x13'], input_expr('machine_x13_1', 64))
            self.assertEqual(state.conditions, [])
            # The dropped fact moves into the join's history group (entry_hist wrap).
            self.assertEqual(components[0]['source'],
                             '⌜zesu_join_history (∃ (machine_x10 : bv 64), (bv_unsigned machine_x10 < 8))⌝')
            self.assertEqual(plan['dropped_binders'][0]['rule'], 'forgotten')
            self.assertEqual(plan['dropped_binders'][0]['facts'], ['fact'])

    def test_a_fact_on_the_whole_forgotten_value_keeps_it_through_the_fresh_binder(self):
        value = operation('bvadd', self.b, bits(1, 64))
        state = state_with({'x13': value}, [operation('bvult', value, bits(8, 64)),
                                            operation('bvult', self.b, bits(8, 64))])
        components = [{'id': 'slice', 'kind': 'opaque', 'source': '⌜P (%s) (%s)⌝' % (value.coq(), value.coq())},
                      {'id': 'inner', 'kind': 'opaque', 'source': '⌜bv_unsigned machine_x10 < 8⌝'}]
        plan = self.run_rules(state, live=['x13'], components=components)
        fresh = input_expr('machine_x13_1', 64)
        self.assertEqual(state.registers['x13'], fresh)
        self.assertEqual(state.conditions, [operation('bvult', fresh, bits(8, 64))])
        self.assertEqual(components[0]['source'], '⌜P (machine_x13_1) (machine_x13_1)⌝')
        self.assertEqual(components[1]['source'],
                         '⌜zesu_join_history (∃ (machine_x10 : bv 64), (bv_unsigned machine_x10 < 8))⌝')
        self.assertEqual(plan['dropped_binders'][0]['kept_facts'], ['slice'])
        self.assertEqual(plan['dropped_binders'][0]['facts'], ['inner'])

    def test_a_fact_that_binds_the_name_itself_does_not_use_the_binder(self):
        state = state_with({'x13': operation('bvadd', self.b, bits(1, 64))}, [])
        closed = '⌜∃ (x14 : bv 64) (machine_x10 : bv 64), Q x14 machine_x10⌝'
        components = [{'id': 'closed', 'kind': 'opaque', 'source': closed}]
        plan = self.run_rules(state, live=['x13'], components=components)
        self.assertEqual(components[0]['source'], closed)
        self.assertNotIn('facts', plan['dropped_binders'][0])

    def test_a_held_binder_stays(self):
        state = state_with({'x10': self.b, 'x13': operation('bvadd', self.b, bits(1, 64))}, [])
        plan = self.run_rules(state, live=['x1'])
        self.assertEqual(state.registers['x13'], operation('bvadd', self.b, bits(1, 64)))
        self.assertNotIn('dropped_binders', plan)


class RegisterDefinition(unittest.TestCase):
    b = input_expr('machine_x15', 64)
    out = input_expr('(Z_to_bv 64%N (outPointer args))', 64)

    def state(self, ranged=True):
        cursor = operation('bvadd', operation('bvadd', self.b, self.out), bits(1, 64))
        flag = operation('bvor', self.b, input_expr('(Z_to_bv 64%N (n args))', 64))
        state = state_with({'x13': cursor, 'x15': flag},
                           [operation('bvuge', self.b, bits(0, 64)), operation('bvule', self.b, bits(1, 64))]
                           if ranged else [])
        state.source_intervals = [{'expression': self.out.to_dict(), 'minimum': 0xa0000000,
                                   'maximum': 0xa0400000, 'origin': {'source': 'test'}}]
        return state

    def test_a_live_register_determines_the_binder(self):
        register, width, rest = _register_definition(self.state(), 'machine_x15')
        self.assertEqual((register, width), ('x13', 64))
        self.assertEqual(rest, operation('bvadd', self.out, bits(1, 64)))

    def test_no_range_no_definition(self):
        self.assertIsNone(_register_definition(self.state(ranged=False), 'machine_x15'))

    def test_the_definition_replaces_the_binder_everywhere(self):
        state = self.state()
        plan = {'binders': []}
        drop_unheld_binders(state, [], {}, [{'name': 'machine_x15'}], plan, ['x13', 'x15'], lambda key, writes: '')
        fresh = input_expr('machine_x13_1', 64)
        self.assertEqual(state.registers['x13'], fresh)
        definition = operation('bvsub', fresh, operation('bvadd', self.out, bits(1, 64)))
        self.assertEqual(state.registers['x15'], operation('bvor', definition, input_expr('(Z_to_bv 64%N (n args))', 64)))
        self.assertEqual(state.conditions[1], operation('bvule', definition, bits(1, 64)))
        self.assertEqual(plan['dropped_binders'][0]['rule'], 'register_definition')


class StoredRegisterValue(unittest.TestCase):
    """An inherited array binder that an owned span holds only through a stored register value."""
    array = input_expr('call_after', None)
    word = operation('concat', Expr('array_byte', (array,), 8, 1), Expr('array_byte', (array,), 8, 0))

    def test_the_stored_value_gets_a_fresh_binder(self):
        stored = operation('bvadd', input_expr('t', 16), self.word)
        state = state_with({'x19': stored, 'x13': operation('bvsub', input_expr('u', 16), self.word)},
                           [operation('=', Expr('array_byte', (self.array,), 8, 5), bits(0, 8))])
        stored_bytes = tuple(operation('extract', stored, width=8, value=8 * i) for i in range(2))
        text = '[' + '; '.join(byte.coq() for byte in stored_bytes) + ']'
        state.memory = [MemoryRegion(input_expr('base', 64), stored_bytes, input_expr(text, None), 2,
                                     ownership_id='span')]
        components = [{'id': 'span', 'kind': 'byte_array', 'source': 'base ↦ₘ∗ ' + text, 'value': text}]
        plan = {'binders': []}
        drop_unheld_binders(state, components, {}, [{'name': 'call_after'}], plan, ['x19'], lambda key, writes: '')
        fresh = input_expr('machine_x19_1', 16)
        self.assertEqual(state.registers['x19'], fresh)
        self.assertEqual(state.memory[0].bytes, tuple(operation('extract', fresh, width=8, value=8 * i)
                                                      for i in range(2)))
        self.assertNotIn('call_after', components[0]['source'] + components[0]['value']
                         + state.memory[0].byte_array.value)
        # The dead register x13 forgets the binder; the path condition on another byte goes.
        self.assertEqual(state.registers['x13'], input_expr('machine_x13_1', 16))
        self.assertEqual(state.conditions, [])
        self.assertEqual(plan['dropped_binders'][0]['rule'], 'stored_register_value')
        self.assertEqual([row['name'] for row in plan['binders']], ['machine_x19_1', 'machine_x13_1'])

    def test_a_pure_fact_on_the_stored_value_keeps_it_through_the_fresh_binder(self):
        stored = operation('bvadd', input_expr('t', 16), self.word)
        state = state_with({'x19': stored}, [])
        stored_bytes = tuple(operation('extract', stored, width=8, value=8 * i) for i in range(2))
        text = '[' + '; '.join(byte.coq() for byte in stored_bytes) + ']'
        state.memory = [MemoryRegion(input_expr('base', 64), stored_bytes, input_expr(text, None), 2,
                                     ownership_id='span')]
        components = [{'id': 'span', 'kind': 'byte_array', 'source': 'base ↦ₘ∗ ' + text, 'value': text},
                      {'id': 'fact', 'kind': 'opaque', 'source': '⌜P (%s)⌝' % stored.coq()}]
        plan = {'binders': []}
        drop_unheld_binders(state, components, {}, [{'name': 'call_after'}], plan, ['x19'], lambda key, writes: '')
        self.assertEqual(components[1]['source'], '⌜P (machine_x19_1)⌝')
        self.assertEqual(plan['dropped_binders'][0]['kept_facts'], ['fact'])

    def test_an_array_with_another_use_of_the_binder_becomes_uninitialized(self):
        stored = operation('bvadd', input_expr('t', 16), self.word)
        state = state_with({'x19': stored}, [])
        other = Expr('array_byte', (self.array,), 8, 7)
        state.memory = [MemoryRegion(input_expr('base', 64), (other,), input_expr('[x]', None), 1,
                                     ownership_id='span')]
        components = [{'id': 'span', 'kind': 'byte_array', 'source': 'base ↦ₘ∗ [' + other.coq() + ']',
                       'address_z': 'base', 'value': '[' + other.coq() + ']', 'fraction': None}]
        plan = {'binders': []}
        drop_unheld_binders(state, components, {}, [{'name': 'call_after'}], plan, ['x19'], lambda key, writes: '')
        self.assertEqual((components[0]['kind'], components[0]['source']), ('unknown_byte_array', 'base ↦ₘ? 1'))
        self.assertNotIn('value', components[0])
        self.assertEqual((state.memory[0].bytes, state.memory[0].byte_array, state.memory[0].uninitialized),
                         ((), None, True))
        self.assertEqual(plan['dropped_binders'][0]['arrays'], ['span'])

    def test_a_shared_array_is_not_forgotten(self):
        from join_generalize import forget_array_bytes
        state = state_with({}, [])
        state.memory = [MemoryRegion(input_expr('base', 64), (), input_expr('[x]', None), 1, ownership_id='span')]
        component = {'id': 'span', 'kind': 'byte_array', 'source': 'base ↦ₘ{#1/2}∗ [x]', 'address_z': 'base',
                     'value': '[x]', 'fraction': '{#1/2}'}
        with self.assertRaisesRegex(ValueError, 'not a wholly owned array'):
            forget_array_bytes(state, component)



class OrphanedLoopBinders(unittest.TestCase):
    def test_a_register_naming_an_overwritten_holders_binder_gets_a_fresh_binder(self):
        entry = input_expr('machine_x13_1', 64)
        flag = operation('bvor', operation('bvsub', entry, input_expr('(Z_to_bv 64%N (out args))', 64)), bits(2, 64))
        before = {'x13': entry, 'x15': flag, 'x1': input_expr('ra', 64)}
        registers = dict(before, x13=input_expr('machine_x13', 64))
        added = reseat_orphaned(registers, before, {'x13': 'machine_x13'}, {'machine_x15_1'})
        self.assertEqual(registers['x15'], input_expr('machine_x15_2', 64))
        self.assertEqual(registers['x1'], input_expr('ra', 64))
        self.assertEqual([row['name'] for row in added], ['machine_x15_2'])

    def test_a_binder_another_register_still_holds_is_not_orphaned(self):
        entry = input_expr('machine_x13_1', 64)
        before = {'x13': entry, 'x14': entry, 'x15': operation('bvadd', entry, bits(1, 64))}
        registers = dict(before, x13=input_expr('machine_x13', 64))
        self.assertEqual(reseat_orphaned(registers, before, {'x13': 'machine_x13'}, set()), [])
        self.assertEqual(registers['x15'], operation('bvadd', entry, bits(1, 64)))


class CallReturnLift(unittest.TestCase):
    def test_the_deepest_common_ancestor_of_call_return_roots(self):
        parents = {'c1': 'entry', 'c2': 'c1', 'c3': 'c2', 'side': 'c1'}
        self.assertEqual(common_root_ancestor(['c3', 'c2'], parents), 'c2')
        self.assertEqual(common_root_ancestor(['c3', 'side'], parents), 'c1')
        self.assertEqual(common_root_ancestor(['c3', 'entry'], parents), 'entry')
        self.assertIsNone(common_root_ancestor(['c3', 'other'], parents))

    def test_literal_lists_split_at_top_level_only(self):
        self.assertEqual(_list_items(input_expr('[(f a; b) ; c]', None)), ['(f a; b)', 'c'])
        self.assertEqual(_list_items(input_expr('[]', None)), [])
        self.assertIsNone(_list_items(input_expr('call_after', None)))

    def test_span_bytes_name_each_known_byte_and_leave_gaps_unknown(self):
        def span(array, length):
            return OwnedBytes('r', input_expr('sp', 64), 'sp', array, length, True, None, {}, {}, 8)
        listed = _span_bytes(span(input_expr('[(BV 8 1); x]', None), 2), None)
        self.assertEqual([text for text, _ in listed], ['BV 8 1', 'x'])
        array = _span_bytes(span(input_expr('call_after', None), 2), None)
        self.assertEqual(array[1][0], 'List.nth 1%nat call_after (BV 8%N 0%Z)')
        region = MemoryRegion(input_expr('sp', 64), (bits(7, 8),), None, 3, True, 'r')
        self.assertEqual([None if byte is None else byte[0] for byte in _span_bytes(span(None, 3), region)],
                         ['BV 8%N 7%Z', None, None])
        with self.assertRaisesRegex(ValueError, 'disagrees with its owned length'):
            _span_bytes(span(input_expr('[a]', None), 2), None)


class HistoryJoin(unittest.TestCase):
    """`entry_hist: wrap` joins: dropped facts become one hidden history fact, also those a
    visible pattern (`zesu_named_eq` here) selects."""
    b = input_expr('machine_x10', 64)

    def setUp(self):
        entry_hist.configure({'entry_hist': 'wrap', 'hist_visible': ['zesu_named_eq']})
        self.addCleanup(entry_hist.configure, {'entry_hist': 'wrap'})

    def run_rules(self):
        state = state_with({'x13': operation('bvadd', self.b, bits(1, 64))}, [])
        components = [{'id': 'eq', 'kind': 'opaque', 'source': '⌜zesu_named_eq machine_x10 (word8 call_after)⌝'},
                      {'id': 'range', 'kind': 'opaque', 'source': '⌜bv_unsigned machine_x10 < 8⌝'}]
        plan = {'binders': []}
        drop_unheld_binders(state, components, {}, [{'name': 'machine_x10', 'type': 'bv 64'}], plan, ['x13'],
                            lambda key, writes: '')
        return state, components, plan

    def test_dropped_facts_form_one_hidden_join_history(self):
        state, components, plan = self.run_rules()
        self.assertEqual(state.registers['x13'], input_expr('machine_x13_1', 64))
        self.assertEqual(components[0]['source'],
                         '⌜zesu_join_history (∃ (machine_x10 : bv 64), (zesu_named_eq machine_x10 (word8 call_after))'
                         ' /\\ (bv_unsigned machine_x10 < 8))⌝')
        self.assertEqual(components[1]['source'], '⌜True⌝')
        self.assertEqual(plan['ghost_history'], {'component': 'eq', 'facts': ['eq', 'range']})
        self.assertTrue(entry_hist.is_join_history(components[0]['source'][1:-1]))


class WeakVisiblePatterns(unittest.TestCase):
    """A profile `hist_visible` fact keeps a live binder's fact visible but pins no binder: an
    outcome that no resource holds (a dead call result) stays in the history with its guards."""
    BINDERS = [{'name': 'held', 'type': 'list byte'}, {'name': 'dead', 'type': 'list byte'}]
    RESOURCES = ['p ↦ₘ∗ held']
    FACTS = ['guard8 held', 'guard8 dead', '(List.length dead = 40)%nat']

    def test_a_weak_pattern_pins_no_binder(self):
        live, ghost, visible, hidden = entry_hist.classify(self.BINDERS, self.RESOURCES, self.FACTS,
                                                           weak_patterns=['guard8'])
        self.assertEqual([binder['name'] for binder in live], ['held'])
        self.assertEqual([binder['name'] for binder in ghost], ['dead'])
        self.assertEqual(visible, ['guard8 held'])
        self.assertEqual(hidden, ['guard8 dead', '(List.length dead = 40)%nat'])

    def test_a_visible_pattern_still_pins(self):
        live, ghost, visible, _ = entry_hist.classify(self.BINDERS, self.RESOURCES, self.FACTS,
                                                      visible_patterns=['guard8'])
        self.assertEqual([binder['name'] for binder in live], ['held', 'dead'])
        self.assertEqual(ghost, [])
        self.assertEqual(visible, self.FACTS)

    def test_a_loop_design_visible_list_is_weak(self):
        entry_hist.configure({'entry_hist': 'wrap'})
        self.addCleanup(entry_hist.configure, {'entry_hist': 'wrap'})
        _, _, meta = entry_hist.seal_class(
            'C', 'Definition C ', '(machine_x11 : bv 64) (held : list byte) (dead : list byte)',
            ['"x11" ↦ᵣ RVal_Bits (machine_x11 : bv 64%N)', 'p ↦ₘ∗ held'], self.FACTS,
            [{'name': 'args', 'type': 'A'}], {'registers': {'x11': 'machine_x11'}, 'facts': []},
            visible=['guard8'])
        self.assertEqual([binder['name'] for binder in meta['live']], ['machine_x11', 'held'])
        self.assertEqual(meta['visible'], ['guard8 held'])
        self.assertEqual([binder['name'] for binder in meta['ghost']], ['dead'])

    def test_a_loop_entry_predecessor_shows_the_newest_call_record(self):
        binders = [{'name': 'call2_after', 'type': 'list byte'}, {'name': 'call_after', 'type': 'list byte'}]
        facts = ['decodeItemCallMeaning a call2_after', 'decodeItemCallMeaning a call_after']
        self.assertEqual(entry_hist.loop_entry_patterns('0x10', {'0x20'}, binders), [])
        patterns = entry_hist.loop_entry_patterns('0x20', {'0x20'}, binders)
        live, ghost, visible, hidden = entry_hist.classify(binders, [], facts, patterns)
        self.assertEqual([binder['name'] for binder in live], ['call2_after'])
        self.assertEqual(visible, facts[:1])
        self.assertEqual(hidden, facts[1:])


class BackwardPins(unittest.TestCase):
    """A successor binder that is live without a resource takes its value from the entry before it:
    the pin goes back along edges, with the successor's visible facts on it, to the entry that holds
    the value in a resource; the predecessor's classification then shows binder and fact."""
    FACT = '(zesu_named_eq new (bv_sub old w))'

    def meta(self, live=(), ghost=(), resources=(), visible=()):
        return {'live': [{'name': name, 'type': 'bv 64'} for name in live],
                'ghost': [{'name': name, 'type': 'bv 64'} for name in ghost],
                'resources': list(resources), 'visible': list(visible)}

    def variants(self, middle_resources=()):
        return {
            'succ': [self.meta(live=['new', 'old'], resources=['"x18" ↦ᵣ new'], visible=['(' + self.FACT + ')'])],
            'pre': [self.meta(live=['new'], ghost=['old'], resources=['"x18" ↦ᵣ new', *middle_resources])],
            'root': [self.meta(live=['old'], resources=['"x9" ↦ᵣ old'])],
        }

    def test_the_pin_reaches_the_entry_with_the_resource(self):
        pins = entry_hist.backward_pins(self.variants(), [('root', 'pre'), ('pre', 'succ')])
        self.assertEqual(pins['pre'], {'pinned': ['old'], 'facts': [entry_hist.normal(self.FACT)]})
        self.assertEqual(pins['root'], {'pinned': ['old'], 'facts': [entry_hist.normal(self.FACT)]})
        binders = [{'name': 'new', 'type': 'bv 64'}, {'name': 'old', 'type': 'bv 64'}]
        live, ghost, visible, hidden = entry_hist.classify(
            binders, ['"x18" ↦ᵣ new'], [self.FACT, 'other old'], pinned=pins['pre']['pinned'],
            visible_texts=pins['pre']['facts'])
        self.assertEqual([binder['name'] for binder in live], ['new', 'old'])
        self.assertEqual((ghost, visible, hidden), ([], [self.FACT], ['other old']))
        # Without the pins the binder and its fact stay in the history.
        live, ghost, visible, _ = entry_hist.classify(binders, ['"x18" ↦ᵣ new'], [self.FACT])
        self.assertEqual(([binder['name'] for binder in ghost], visible), (['old'], []))

    def test_a_resource_stops_the_pin(self):
        pins = entry_hist.backward_pins(self.variants(['p ↦ₘ∗ old']), [('root', 'pre'), ('pre', 'succ')])
        self.assertEqual(list(pins), ['pre'])

    def test_a_witnessed_binder_needs_no_pin(self):
        pins = entry_hist.backward_pins(self.variants(), [('root', 'pre'), ('pre', 'succ')],
                                        witnessed={('pre', 'succ', 'old')})
        self.assertEqual(pins, {})

    def test_a_binder_live_only_through_a_visible_call_record(self):
        # The successor (a call block) shows the newest call's record group, which names the
        # predecessor's ghost `cursor`; no resource holds it there. The record is no fact of the
        # predecessor: the pin makes `cursor` live, the predecessor's own facts stay hidden.
        record = '(∃ (arg : bv 64), calleeDomain (mk cursor arg) /\\ calleeResult (mk cursor arg) out)'
        variants = {'call': [self.meta(live=['cursor'], resources=['"x10" ↦ᵣ arg0'], visible=[record])],
                    'mid': [self.meta(ghost=['cursor'], resources=['"x10" ↦ᵣ arg0'])],
                    'root': [self.meta(live=['cursor'], resources=['"x19" ↦ᵣ cursor'])]}
        pins = entry_hist.backward_pins(variants, [('root', 'mid'), ('mid', 'call')])
        self.assertEqual(pins['mid'], {'pinned': ['cursor'], 'facts': [entry_hist.normal(record)]})
        self.assertEqual(pins['root']['pinned'], ['cursor'])
        binders = [{'name': 'cursor', 'type': 'bv 64'}]
        live, ghost, visible, hidden = entry_hist.classify(
            binders, ['"x10" ↦ᵣ arg0'], ['guard cursor'], pinned=pins['mid']['pinned'],
            visible_texts=pins['mid']['facts'])
        self.assertEqual(([binder['name'] for binder in live], ghost, visible, hidden),
                         (['cursor'], [], [], ['guard cursor']))


class NewestCallVisible(unittest.TestCase):
    """The newest call's record, guards and slice window are visible at the call block and at the
    call's return site, also for a callee that takes its slice by reference (record `…CallResult`,
    outcome `<prefix>result`, stored words `<prefix>word_*`); an older call's stay hidden."""
    binders = [{'name': name, 'type': 'bv 64'} for name in
               ('call_kept_x19', 'call_kept_x18', 'call2_kept_x19', 'call2_kept_x18', 'call2_after',
                'call3_result', 'call3_word_1_0', 'call3_word_1_8')]
    pointer = '(bv_add call2_kept_x19 (word24 call2_after))'
    record = ('∃ (call3_arg_x12 : bv 64), (nextUint64CallDomain (nextUint64CallDataArgs ([o; r; (call3_arg_x12)]) sp '
              '(' + pointer + ') ie (take (Z.to_nat (bv_unsigned ((call2_kept_x18)))) bytes)) /\\ '
              'nextUint64CallResult (nextUint64Base (nextUint64CallDataArgs ([o; r; (call3_arg_x12)]) sp '
              '(' + pointer + ') ie bytes)) (call3_result) /\\ '
              'call3_word_1_0 = Z_to_bv 64 (nextRestPointer (call3_result)))')
    window = ('(bv_unsigned (base args) <= bv_unsigned ((' + pointer + ')) /\\ bv_unsigned ((' + pointer + '))'
              ' + bv_unsigned ((call2_kept_x18)) <= bv_unsigned (base args) + Z.of_nat (List.length bytes))%Z')
    guard = '(((bv_unsigned call3_word_1_8) <> (0%Z))%Z)'
    older_record = ('decodeItemCallMeaning (decodeItemCallDataArgs ([o; (call_kept_x19); (call_kept_x18)]) sp ie '
                    'bytes before) (call2_after)')
    older_window = ('(bv_unsigned (base args) <= bv_unsigned (call_kept_x19) /\\ bv_unsigned (call_kept_x19)'
                    ' + bv_unsigned (call_kept_x18) <= bv_unsigned (base args) + Z.of_nat (List.length bytes))%Z')
    facts = [record, window, guard, older_record, older_window]
    calls = {'0x80000020': {'call_site_pc': '0x8000001c', 'return_site_pc': '0x80000020'}}
    starts = [0x80000000, 0x80000010, 0x80000020, 0x80000030]

    def visible(self, pc):
        patterns = entry_hist.call_visible_patterns(pc, self.calls, self.starts, self.binders, self.facts)
        return entry_hist.classify(self.binders, [], self.facts, patterns)[2]

    def test_call_block_and_return_site_show_the_by_reference_record_guard_and_window(self):
        for pc in ('0x80000010', '0x80000020'):
            self.assertEqual(self.visible(pc), [self.record, self.window, self.guard])

    def test_a_block_with_no_call_shows_none(self):
        self.assertEqual(self.visible('0x80000030'), [])

    def test_without_the_record_the_window_stays_hidden(self):
        patterns = entry_hist.newest_call_patterns(self.binders, [self.window, self.older_window])
        self.assertEqual(entry_hist.classify(self.binders, [], [self.window, self.older_window], patterns)[2], [])


class HistoryAlignment(unittest.TestCase):
    """A join whose edges hold the same facts once in a history group, once one per component."""
    GROUP = ('⌜∃ (call10_kept_x19 : bv 64), (zesu_named_eq call11_kept_x18 (bv_add call10_kept_x19 c))'
             ' /\\ (zesu_named_eq call10_kept_x19 d)⌝')
    KINDS = {'eq18': 'opaque', 'eq19': 'opaque', 'other': 'opaque', 'x1': 'register'}

    def edges(self, raw_other='⌜P⌝'):
        through_loop_head = {'eq18': {'id': 'eq18', 'source': self.GROUP}, 'eq19': {'id': 'eq19', 'source': '⌜True⌝'},
                             'other': {'id': 'other', 'source': '⌜P⌝'}, 'x1': {'id': 'x1', 'source': 'x1'}}
        bypass = {'eq18': {'id': 'eq18', 'source': '⌜zesu_named_eq call11_kept_x18 (bv_add call10_kept_x19 c)⌝'},
                  'eq19': {'id': 'eq19', 'source': '⌜zesu_named_eq call10_kept_x19 d⌝'},
                  'other': {'id': 'other', 'source': raw_other}, 'x1': {'id': 'x1', 'source': 'x1'}}
        return [through_loop_head, bypass]

    def test_members_of_both_group_shapes(self):
        self.assertEqual(history_members(self.GROUP),
                         ['zesu_named_eq call11_kept_x18 (bv_add call10_kept_x19 c)', 'zesu_named_eq call10_kept_x19 d'])
        hidden = '⌜zesu_join_history (∃ (b : bv 64), (b = c))⌝'
        self.assertEqual(history_members(hidden), ['b = c'])
        self.assertIsNone(history_members('⌜∃ (b : bv 64), b = c /\\ c = d⌝'))
        self.assertIsNone(history_members('⌜zesu_named_eq b c⌝'))

    def test_the_bypassing_edge_binds_the_same_group(self):
        records = self.edges()
        aligned = align_history_groups(records, self.KINDS)
        self.assertEqual(aligned, [{'component': 'eq18', 'edge': 1, 'members': ['eq18', 'eq19']}])
        self.assertEqual([{key: row['source'] for key, row in record.items()} for record in records][0],
                         {key: row['source'] for key, row in records[1].items()})

    def test_an_edge_missing_a_member_is_not_aligned(self):
        records = self.edges()
        records[1]['eq19']['source'] = '⌜zesu_named_eq call10_kept_x19 e⌝'
        self.assertEqual(align_history_groups(records, self.KINDS), [])
        self.assertEqual(records[1]['eq18']['source'],
                         '⌜zesu_named_eq call11_kept_x18 (bv_add call10_kept_x19 c)⌝')

    def test_a_name_bound_by_a_nested_group_member_is_not_free(self):
        nested = {'source': '⌜∃ (b : bv 64), (∃ (c : bv 64), (c = b)) /\\ (P d)⌝'}
        self.assertFalse(_mentions_free(nested, 'c'))
        self.assertFalse(_mentions_free(nested, 'b'))
        self.assertTrue(_mentions_free(nested, 'd'))
        self.assertTrue(_mentions_free({'source': '⌜∃ (b : bv 64), c = b /\\ (∃ (c : bv 64), c = b)⌝'}, 'c'))

    def test_a_silent_drop_is_refused_and_a_logged_drop_reported(self):
        kept = [{'id': 'eq18', 'source': self.GROUP}, {'id': 'eq19', 'source': '⌜True⌝'},
                {'id': 'other', 'source': '⌜True⌝'}]
        with self.assertRaisesRegex(ValueError, 'without a named rule: other'):
            check_fact_accounting(['eq18', 'other'], kept, {})
        plan = {'dropped_facts': [{'component': 'other', 'rule': 'edges_disagree', 'edges': [0]}]}
        report = check_fact_accounting(['eq18', 'eq19', 'other'], kept,
                                       {**plan, 'ghost_history': {'facts': ['eq19']}})
        self.assertEqual(report, {'kept': 2, 'dropped': [{'component': 'other', 'rule': 'edges_disagree'}]})
        report = check_fact_accounting(['other'], kept, {'dropped_binders': [{'binder': 'b', 'facts': ['other']}]})
        self.assertEqual(report['dropped'], [{'component': 'other', 'rule': 'unheld_binder:b'}])


class ReturnSites(unittest.TestCase):
    def test_each_return_block_names_its_site(self):
        sites = [('3ed8', {'return_instruction_pc': '0x800d3ed8'}),
                 ('3f10', {'return_instruction_pc': '0x800d3f10'})]
        self.assertEqual(return_site(sites, 0x800d3ec8, 0x800d3edc), '3ed8')
        self.assertEqual(return_site(sites, 0x800d3f04, 0x800d3f14), '3f10')
        self.assertIsNone(return_site(sites, 0x800d3f00, 0x800d3f04))
        self.assertEqual(return_site([('', {'return_instruction_pc': '0x10'})], 0x40, 0x44), '')
        self.assertEqual(return_site([], 0x40, None), '')


if __name__ == '__main__':
    unittest.main()
