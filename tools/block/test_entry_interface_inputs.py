"""The general entry-interface input builder, return designs, and their profile defaults."""
from pathlib import Path
import json
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent / 'functions'))
from function_profiles import FunctionProfile, function_returns, load_profile
from return_exit import allows_exit_resources_only, match_return_exits

CONTRACT = '''From Coq Require Import List ZArith.
Notation tStackBytes := ((16) : Z) (only parsing).
Notation tResultBytes := ((24) : Z) (only parsing).
Notation tLow := ((0xa0000000) : Z) (only parsing).
Notation tHigh := ((0xa0400000) : Z) (only parsing).

Definition tSeparate (p n q m : Z) : Prop :=
  p + n <= q \\/ q + m <= p.

Definition tArgsWellFormed (args : TArgs) : Prop :=
  0 <= tInputLength args < 2 ^ 64 /\\
  Z.of_nat (length (tInputBytes args)) = tInputLength args /\\
  length (tBeforeResult args) = 24%nat /\\
  tLow <= tInputPointer args /\\
  tInputPointer args + tInputLength args <= tHigh /\\
  tLow <= tResultPointer args /\\
  tResultPointer args + tResultBytes <= tHigh /\\
  tLow + tStackBytes <= tStackPointer args <= tHigh /\\
  tStackPointer args mod 16 = 0 /\\
  0 <= tReturnAddress args < 2 ^ 64 /\\ tReturnAddress args mod 4 = 0 /\\
  2 * tInputLength args <= tHigh /\\
  tSeparate (tInputPointer args) (tInputLength args) (tResultPointer args) tResultBytes /\\
  tSeparate (tResultPointer args) tResultBytes (tStackPointer args - tStackBytes) tStackBytes /\\
  0 <= tOutputLength args < 2 ^ 64 /\\
  Z.of_nat (length (tBeforeOutput args)) = tOutputLength args /\\
  2 * tInputLength args <= tOutputLength args.

Definition tEntryResources `{!islaG Sigma} `{!threadG} (args : TArgs) : iProp Sigma :=
  (∃ (x15 x16 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (tReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (tStackPointer args)) ∗
   "x8" ↦ᵣ RVal_Bits (tSavedFramePointer args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (tResultPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (tInputPointer args)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (tInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (tOutputPointer args)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (tOutputLength args)) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗ "x16" ↦ᵣ RVal_Bits x16 ∗
   tInputPointer args ↦ₘ∗ tInputBytes args ∗
   tResultPointer args ↦ₘ∗ tBeforeResult args ∗
   tOutputPointer args ↦ₘ∗ tBeforeOutput args ∗
   (tStackPointer args - tStackBytes) ↦ₘ? tStackBytes ∗
   ⌜tArgsWellFormed args⌝ ∗ True)%I.
'''

PROFILE = {'function': 'tFunction', 'args_type': 'TArgs', 'cfg_function': 'module.tFunction',
           'domain_component': '⌜tDomainAt returnAddress args⌝',
           'entry_interface': {'entry_resources': 'tEntryResources', 'well_formed': 'tArgsWellFormed',
                               'exit_resources': 'tExitResources', 'source': 'T.v'},
           'blocks': [], 'loop_heads': [], 'pc_prefix': '0x8000', 'generated_directory': 'G',
           'callers_directory': 'C', 'contract_requires': [], 'loop_contract_requires': [],
           'selected_code': {'module': 'M', 'premise': 'p'}}


class EntryInterface(unittest.TestCase):
    def setUp(self):
        from entry_interface_inputs import domain, notations, public_seed
        directory = Path(tempfile.mkdtemp())
        self.contract = directory / 'T.v'
        self.contract.write_text(CONTRACT)
        profile = FunctionProfile(dict(PROFILE), directory / 'tFunction.json')
        self.constants = notations(self.contract, CONTRACT)
        self.seed = public_seed(profile, self.contract, CONTRACT)
        self.domain = domain(profile, self.contract, CONTRACT, self.seed, self.constants,
                             (0xa0000000, 0xc0000000))

    def facts(self):
        return {fact['fact_id']: fact for fact in self.domain['projection']['facts']}

    def test_seed_keeps_witnesses_registers_ownership_and_the_domain(self):
        tree = self.seed['assertion_tree']
        self.assertEqual([binder['name'] for binder in tree['binders']], ['x15', 'x16'])
        kinds = [node['kind'] for node in tree['components']]
        self.assertEqual(kinds.count('byte_array'), 3)
        self.assertEqual(kinds.count('uninitialized_memory'), 1)
        self.assertIn('⌜domain args⌝', [node.get('coq') for node in tree['components']])
        self.assertEqual(self.seed['domain_binding']['actual_domain'], 'tDomainAt returnAddress args')

    def test_conjunct_shapes(self):
        facts = self.facts()
        ids = {node['original_component'].split(' ↦ₘ')[0]: node['id']
               for node in self.seed['assertion_tree']['components'] if '↦ₘ' in node['original_component']}
        self.assertEqual(facts['wellformed:length-2']['terms']['count'], 24)
        self.assertEqual(facts['wellformed:length-view-1']['terms']['length_view']['value'],
                         '(Z_to_bv 64%N (tInputLength args))')
        self.assertEqual(facts['wellformed:alignment-8']['terms']['alignment']['modulus'], 16)
        self.assertEqual(facts['wellformed:alignment-10']['terms']['alignment']['modulus'], 4)
        stack = facts['wellformed:interval-x2']['terms']['unsigned_interval']
        self.assertEqual((stack['minimum'], stack['maximum'], stack['ram_base']), (0xa0000010, 0xa0400000, 0xa0000000))
        result = facts['wellformed:interval-x10']['terms']['unsigned_interval']
        self.assertEqual(result['maximum'], 0xa0400000 - 24)
        self.assertEqual(facts['wellformed:separate-12']['terms'], {
            'left': ids['tInputPointer args'], 'right': ids['tResultPointer args'],
            'coq_statement': facts['wellformed:separate-12']['terms']['coq_statement']})
        self.assertEqual(facts['wellformed:separate-13']['terms']['right'], ids['(tStackPointer args - tStackBytes)'])
        # A scaled register quantity bounds the output array's length from below.
        relation = facts['wellformed:length-relation-16']['terms']
        self.assertEqual(relation['resource_id'], ids['tOutputPointer args'])
        self.assertEqual(relation['length_relation'], {
            'view': {'op': 'input', 'width': 64, 'value': '(Z_to_bv 64%N (tInputLength args))'},
            'scale': 2, 'offset': 0})
        # A full-range bound and a scaled relation to a constant are recorded, not used.
        self.assertIn(9, self.domain['projection']['unused_clauses'])
        self.assertIn(11, self.domain['projection']['unused_clauses'])

    def test_the_length_of_a_constant_array_names_the_constant_bare(self):
        from entry_interface_inputs import domain, notations, public_seed
        text = (CONTRACT
                .replace('Notation tHigh', 'Notation tNoneConstant := ((0x80001000) : Z) (only parsing).\n'
                                           'Notation tHigh')
                .replace('  2 * tInputLength args <= tOutputLength args.',
                         '  2 * tInputLength args <= tOutputLength args /\\\n  length tNoneBytes = 16%nat.')
                .replace('   ⌜tArgsWellFormed args⌝', '   tNoneConstant ↦ₘ∗ tNoneBytes ∗\n   ⌜tArgsWellFormed args⌝'))
        self.contract.write_text(text)
        profile = FunctionProfile(dict(PROFILE), self.contract.parent / 'tFunction.json')
        constants = notations(self.contract, text)
        seed = public_seed(profile, self.contract, text)
        facts = domain(profile, self.contract, text, seed, constants, (0xa0000000, 0xc0000000))['projection']['facts']
        none, = [node['id'] for node in seed['assertion_tree']['components']
                 if node.get('original_component', '').startswith('tNoneConstant ↦ₘ∗')]
        length, = [fact['terms'] for fact in facts if fact['terms'].get('resource_id') == none]
        self.assertEqual((length['count'], length['coq_statement']), (16, 'length tNoneBytes = 16%nat'))

    def variant(self, text):
        from entry_interface_inputs import domain, notations, public_seed
        self.contract.write_text(text)
        profile = FunctionProfile(dict(PROFILE), self.contract.parent / 'tFunction.json')
        seed = public_seed(profile, self.contract, text)
        notes = {}
        result = domain(profile, self.contract, text, seed, notations(self.contract, text),
                        (0xa0000000, 0xc0000000), notes)
        ids = {node['original_component'].split(' ↦ₘ')[0]: node['id']
               for node in seed['assertion_tree']['components'] if '↦ₘ' in node['original_component']}
        return {fact['fact_id']: fact for fact in result['projection']['facts']}, result, notes, ids

    def test_closed_arithmetic_bounds_are_evaluated(self):
        from entry_interface_inputs import Linear, closed_value
        self.assertEqual(closed_value('2 ^ 31 + 2 ^ 29', {}), 0xa0000000)
        self.assertEqual(closed_value('(2 ^ 3) * (tResultBytes - 8) - 1', self.constants), 127)
        self.assertEqual(closed_value('2 ^ 2 ^ 3', {}), 256)
        self.assertIsNone(closed_value('2 ^ n', {}))
        self.assertEqual(Linear.parse('64 * n args', {}), ({'n args': 64}, 0))
        self.assertEqual(Linear.parse('n args * 2 ^ 6', {}), ({'n args': 64}, 0))
        self.assertIsNone(Linear.parse('n args * m args', {}))
        facts, _, _, _ = self.variant(CONTRACT.replace('  tLow <= tResultPointer args /\\',
                                                       '  2 ^ 31 + 2 ^ 29 <= tResultPointer args /\\'))
        self.assertEqual(facts['wellformed:interval-x10']['terms']['unsigned_interval']['minimum'], 0xa0000000)
        # A scaled quantity is bounded by integer division: 64 * n < 2 ^ 64 gives n <= 2 ^ 58 - 1.
        facts, _, _, _ = self.variant(CONTRACT.replace('  0 <= tOutputLength args < 2 ^ 64 /\\',
                                                       '  0 <= tOutputLength args /\\ 64 * tOutputLength args < 2 ^ 64 /\\'))
        interval = facts['wellformed:interval-x14']['terms']['unsigned_interval']
        self.assertEqual((interval['minimum'], interval['maximum']), (0, 2 ** 58 - 1))

    def test_a_separation_over_a_wider_range_covers_the_owned_ranges_inside_it(self):
        text = CONTRACT.replace(
            '  2 * tInputLength args <= tOutputLength args.',
            '  2 * tInputLength args <= tOutputLength args /\\\n'
            '  tSeparate (tInputPointer args) (tInputLength args) (tResultPointer args - 8) (2 ^ 5 + 8) /\\\n'
            '  tSeparate (tInputPointer args) (tInputLength args) (tResultPointer args) 16.')
        facts, result, notes, ids = self.variant(text)
        wide = 'wellformed:separate-17-%s-%s' % (ids['tInputPointer args'], ids['tResultPointer args'])
        self.assertEqual((facts[wide]['kind'], facts[wide]['terms']['left'], facts[wide]['terms']['right']),
                         ('disjoint_ranges', ids['tInputPointer args'], ids['tResultPointer args']))
        # A range shorter than the owned array covers nothing: reported, with the clause, not dropped silently.
        self.assertIn(18, result['projection']['unused_clauses'])
        self.assertTrue(notes[18].startswith('separation: no owned range'))
        self.assertIn('[tResultPointer args, +16)', notes[18])

    def test_every_unused_conjunct_has_a_reason(self):
        _, result, notes, _ = self.variant(CONTRACT)
        self.assertEqual(sorted(notes), result['projection']['unused_clauses'])
        self.assertTrue(notes[11].startswith('bound: linear'))

    LINKS = CONTRACT.replace(
        'Definition tArgsWellFormed',
        'Definition tWordAt (bytes : list byte) (offset : Z) : Z :=\n'
        '  little_endian_to_bv 8 (take 8 (drop (Z.to_nat offset) bytes)).\n\n'
        'Definition tArgsWellFormed').replace(
        '  2 * tInputLength args <= tOutputLength args.',
        '  2 * tInputLength args <= tOutputLength args /\\\n'
        '  tWordAt (tBeforeResult args) (tResultBytes - 16) = tInputPointer args /\\\n'
        '  tOutputLength args =\n'
        '    little_endian_to_bv 8 (take 8 (drop (Z.to_nat 16) (tBeforeResult args))) /\\\n'
        '  tWordAt (tBeforeResult args) (tInputLength args) = tOutputPointer args /\\\n'
        '  (tOutputLength args <> 0 -> tOutputLength args = tResultPointer args) /\\\n'
        '  tWordAt (tMissing args) 0 = tInputPointer args.')

    def test_word_links_are_recognised_and_unusable_ones_reported(self):
        facts, result, notes, ids = self.variant(self.LINKS)
        pointer = facts['wellformed:word-link-17']
        self.assertEqual(pointer['kind'], 'word_link')
        self.assertEqual({key: value for key, value in pointer['terms'].items() if key != 'coq_statement'},
                         {'resource_id': ids['tResultPointer args'], 'offset': 8, 'size': 8,
                          'quantity': 'tInputPointer args', 'target_resource_id': ids['tInputPointer args']})
        scalar = facts['wellformed:word-link-18']['terms']
        self.assertEqual((scalar['offset'], scalar['quantity'], 'target_resource_id' in scalar),
                         (16, 'tOutputLength args', False))
        self.assertEqual(sorted(notes), result['projection']['unused_clauses'])
        self.assertTrue(notes[19].startswith('word link: the offset `tInputLength args`'))
        self.assertTrue(notes[20].startswith('word link: a conditional equation'))
        self.assertTrue(notes[21].startswith('word link: `tMissing args` is not an owned array'))
        # Without links nothing changes: no word_link fact, the same unused conjuncts.
        plain, plain_result, _, _ = self.variant(CONTRACT)
        self.assertFalse([fact for fact in plain.values() if fact['kind'] == 'word_link'])
        self.assertEqual(plain_result['projection']['unused_clauses'], self.domain['projection']['unused_clauses'])

    def test_a_seeded_pointer_link_reads_as_the_target_array_base(self):
        from entry_interface_inputs import notations
        from resource_seed import seed_owned_resources
        facts, result, _, ids = self.variant(self.LINKS)
        profile = FunctionProfile(dict(PROFILE), self.contract.parent / 'tFunction.json')
        from entry_interface_inputs import public_seed
        seed = public_seed(profile, self.contract, self.LINKS)
        seed['_input_sha256'] = '0' * 64
        owned = seed_owned_resources(seed, entry_pc=0x80000000, vocabulary={'rows': []},
                                     constants=notations(self.contract, self.LINKS),
                                     facts=result['projection']['facts'])
        bases = {region.ownership_id: region.base for region in owned.state.memory}
        link, scalar = owned.state.word_links
        self.assertEqual((link['offset'], link['value']), (8, bases[ids['tInputPointer args']]))
        self.assertEqual(scalar['value'].value, '(Z_to_bv 64%N (tOutputLength args))')
        self.assertNotIn('word_link', [fact['kind'] for fact in owned.facts])

    def test_a_word_cell_is_seeded_and_a_load_of_it_reads_its_value(self):
        from entry_interface_inputs import notations, public_seed
        from resource_seed import seed_owned_resources
        from symbolic_state import _Evaluator, bits, input_expr, operation
        text = ('Record TArgs : Type := {\n  tCellPointer : bv 64;\n  tCellValue tOther : bv 64;\n  tSmall : Z\n}.\n'
                + CONTRACT.replace('   ⌜tArgsWellFormed args⌝',
                                   '   bv_unsigned (tCellPointer args) ↦ₘ tCellValue args ∗\n'
                                   '   (bv_unsigned (tCellValue args) + 8) ↦ₘ\n     tOther args ∗\n'
                                   '   tResultPointer args ↦ₘ tSmall args ∗\n   ⌜tArgsWellFormed args⌝'))
        self.contract.write_text(text)
        profile = FunctionProfile(dict(PROFILE), self.contract.parent / 'tFunction.json')
        seed = public_seed(profile, self.contract, text)
        cells = [node['word_cell'] for node in seed['assertion_tree']['components'] if 'word_cell' in node]
        # A `Z` value has no width: that cell stays opaque.
        self.assertEqual(cells, [
            {'address_z': 'bv_unsigned (tCellPointer args)', 'value_coq': 'tCellValue args', 'width': 64},
            {'address_z': 'bv_unsigned (tCellValue args) + 8', 'value_coq': 'tOther args', 'width': 64}])
        seed['_input_sha256'] = '0' * 64
        owned = seed_owned_resources(seed, entry_pc=0x80000000, vocabulary={'rows': []},
                                     constants=notations(self.contract, text), facts=[])
        # The forward pass reads separations from the seed's facts (forward_resource_design._prepare_state).
        owned.state.memory_disjoint = [(fact['terms']['left'], fact['terms']['right'])
                                       for fact in owned.facts if fact['kind'] == 'disjoint_ranges']
        evaluator = _Evaluator(owned.state)
        pointer = evaluator.memory_read(input_expr('tCellPointer args', 64), 8)
        self.assertEqual(pointer, input_expr('tCellValue args', 64))
        self.assertEqual(evaluator.memory_read(operation('bvadd', pointer, bits(8, 64)), 8),
                         input_expr('tOther args', 64))
        self.assertEqual(evaluator.memory_read(input_expr('tCellPointer args', 64), 4).op, 'concat')
        # The loaded value's interval and alignment conjuncts become facts on it.
        bounded = text.replace('  2 * tInputLength args <= tOutputLength args.',
                               '  2 * tInputLength args <= tOutputLength args /\\\n'
                               '  tLow <= bv_unsigned (tCellValue args) /\\\n'
                               '  bv_unsigned (tCellValue args) + 16 <= tHigh /\\\n'
                               '  bv_unsigned (tCellValue args) mod 8 = 0.')
        facts, result, _, _ = self.variant(bounded)
        interval, = [fact['terms']['unsigned_interval'] for key, fact in facts.items()
                     if key.startswith('wellformed:interval-cell-')]
        self.assertEqual((interval['expression']['value'], interval['minimum'], interval['maximum']),
                         ('tCellValue args', 0xa0000000, 0xa0400000 - 16))
        self.assertEqual(facts['wellformed:alignment-19']['terms']['alignment']['modulus'], 8)
        self.assertFalse({17, 18, 19} & set(result['projection']['unused_clauses']))


class LengthRelation(unittest.TestCase):
    def test_a_path_condition_on_the_related_value_bounds_the_array(self):
        from forward_resources import OwnedBytes, _Facts
        from symbolic_state import bits, input_expr, operation
        count = input_expr('(Z_to_bv 64%N (n args))', 64)
        out = OwnedBytes('out', input_expr('(Z_to_bv 64%N (p args))', 64), 'p args', input_expr('o', None),
                         input_expr('List.length o', None), True, 'DfracOwn 1', {}, {}, 8)
        fact = {'fact_id': 'relation', 'kind': 'bounds', 'status': 'supplied', 'origin': {'source': 'test'},
                'terms': {'resource_id': 'out', 'length_relation': {'view': count.to_dict(), 'scale': 2, 'offset': 1}}}
        nonzero = operation('not', operation('=', count, bits(0, 64)))
        self.assertEqual(_Facts([], [fact]).lower_bound(out)[0], 1)
        self.assertEqual(_Facts([nonzero], [fact]).lower_bound(out)[0], 3)
        self.assertEqual(_Facts([nonzero], []).lower_bound(out)[0], 0)


class ReturnDesigns(unittest.TestCase):
    EXITS = [{'instruction_pc': '0x10', 'block_pc': '0x8'}, {'instruction_pc': '0x10', 'block_pc': '0xc'},
             {'instruction_pc': '0x20', 'block_pc': '0x18'}]

    def test_each_exit_pairs_with_the_design_of_its_return(self):
        designs = [{'return_instruction_pc': '0x10', 'return_fact': 'True'},
                   {'return_instruction_pc': '0x20', 'return_fact': 'P'},
                   {'return_instruction_pc': '0x30', 'return_fact': True}]
        pairs, unreached = match_return_exits(designs, self.EXITS)
        self.assertEqual([(d['return_instruction_pc'], e['block_pc']) for d, e in pairs],
                         [('0x10', '0x8'), ('0x10', '0xc'), ('0x20', '0x18')])
        self.assertEqual(unreached, ['0x30'])
        self.assertEqual([allows_exit_resources_only(d) for d in designs], [True, False, True])

    def test_an_exit_without_a_design_is_refused(self):
        with self.assertRaisesRegex(ValueError, 'no return design'):
            match_return_exits([{'return_instruction_pc': '0x10', 'return_fact': 'True'}], self.EXITS)

    def test_single_and_list_designs(self):
        single = {'return_instruction_pc': '0x10', 'return_fact': 'P'}
        self.assertEqual(function_returns({'function_return': single}), [single])
        self.assertEqual(function_returns({'function_returns': [single]}), [single])
        self.assertEqual(function_returns({}), [])

    def test_loop_head_fixture_default(self):
        directory = Path(tempfile.mkdtemp())
        path = directory / 'someFunction.json'
        path.write_text(json.dumps({**PROFILE, 'function': 'someFunction', 'loop_heads': ['1234']}))
        self.assertEqual(load_profile(str(path))['loop_head_fixture'],
                         'tools/block/fixtures/somefunction-loop-heads.json')
        self.assertEqual(load_profile('nextUint64')['loop_head_fixture'],
                         'tools/block/fixtures/nextuint64-loop-heads.json')


if __name__ == '__main__':
    unittest.main()
