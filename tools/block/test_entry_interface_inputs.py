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
  tSeparate (tResultPointer args) tResultBytes (tStackPointer args - tStackBytes) tStackBytes.

Definition tEntryResources `{!islaG Sigma} `{!threadG} (args : TArgs) : iProp Sigma :=
  (∃ (x15 x16 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (tReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (tStackPointer args)) ∗
   "x8" ↦ᵣ RVal_Bits (tSavedFramePointer args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (tResultPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (tInputPointer args)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (tInputLength args)) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗ "x16" ↦ᵣ RVal_Bits x16 ∗
   tInputPointer args ↦ₘ∗ tInputBytes args ∗
   tResultPointer args ↦ₘ∗ tBeforeResult args ∗
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
        self.assertEqual(kinds.count('byte_array'), 2)
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
        # A full-range bound and a scaled relation are recorded, not used.
        self.assertIn(9, self.domain['projection']['unused_clauses'])
        self.assertIn(11, self.domain['projection']['unused_clauses'])


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
