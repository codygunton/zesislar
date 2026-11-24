"""Step budgets (budgets.py) and their rendering under the profile key `charged`."""
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import budgets
import render_function_callers
from budgets import Budget, BudgetError, Walk, maximum
from function_profiles import FunctionProfile, call_premise, load_profile, pilot_header
from render_fp301_statements import render_block_caller, render_loop_head

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/oblig'))
import annotations  # noqa: E402

ENTRY = 0x1000
CALLEE = 0x9000


def function(blocks, calls=()):
    """A CFG function from rows (offset, instructions, successor offsets, last kind[, writes]).

    A `call` block calls CALLEE and returns to its successor; `tail` jumps to CALLEE."""
    rows, cfg_blocks, cfg_calls = [], [], []
    for spec in blocks:
        offset, count, successors, last = spec[:4]
        writes = spec[4] if len(spec) > 4 else {}
        start = ENTRY + offset
        for number in range(count):
            pc = start + 4 * number
            kind = last if number == count - 1 else 'plain'
            row = {'pc': pc, 'size': 4, 'kind': {'tail': 'jump'}.get(kind, kind), 'rd': writes.get(number, 0)}
            if kind == 'call':
                row['rd'] = 1
            rows.append(row)
            if kind in ('call', 'tail'):
                cfg_calls.append({'pc': pc, 'target': CALLEE, 'kind': kind})
        targets = [CALLEE] if last == 'tail' else [ENTRY + item for item in successors]
        cfg_blocks.append({'start': start, 'end': start + 4 * count, 'successors': targets})
    end = max(row['pc'] for row in rows) + 4
    return {'name': 'demo.fn', 'entry': ENTRY, 'end': end, 'rows': rows, 'blocks': cfg_blocks,
            'calls': list(cfg_calls) + list(calls), 'returns': [], 'loops': []}


CALLEE_FUNCTION = {'name': 'demo.callee', 'entry': CALLEE, 'end': CALLEE + 4,
                   'rows': [{'pc': CALLEE, 'size': 4, 'kind': 'return', 'rd': 0}],
                   'blocks': [{'start': CALLEE, 'end': CALLEE + 4, 'successors': []}], 'calls': [], 'returns': [],
                   'loops': []}


def profile(**keys):
    data = {'function': 'demo', 'args_type': 'DemoArgs', 'generated_directory': 'ZesuSsz/Generated/Demo',
            'callers_directory': 'x', 'contract_requires': [], 'loop_contract_requires': [],
            'selected_code': {'module': 'Demo.Selected', 'premise': 'demoCode'}, 'domain_component': '⌜True⌝',
            'blocks': [], 'loop_heads': [], 'pc_base': hex(ENTRY)}
    data.update(keys)
    return FunctionProfile(data)


def walk(blocks, profile_keys=None, registry=None, calls=()):
    return Walk(function(blocks, calls), profile(**(profile_keys or {})), functions=[CALLEE_FUNCTION],
                registry=registry or {})


class Algebra(unittest.TestCase):
    def test_literals_stay_integers(self):
        self.assertEqual((Budget.of(3) + 4).json(), 7)
        self.assertEqual(maximum([3, 9, 4]).json(), 9)

    def test_a_literal_arm_folds_into_the_constant(self):
        self.assertEqual(maximum([3, Budget.of('e') + 1]).text(), '(e) + 3')
        self.assertEqual(maximum([Budget.of('e') + 2, Budget.of('e') + 5]).text(), '(e) + 5')

    def test_z_max_only_between_two_expression_arms(self):
        self.assertEqual(maximum([Budget.of('e1') + 2, Budget.of('e2') + 5, 1]).text(),
                         '(Z.max (e1) ((e2) + 3)) + 2')


class Walks(unittest.TestCase):
    def test_straight_line(self):
        record = walk([(0, 3, [12], 'plain'), (12, 2, [], 'return')]).run()
        self.assertEqual(record['entry_budget'], 5)
        self.assertEqual(record['entries']['000c']['budget'], 2)
        self.assertEqual(record['entries']['0000']['instructions'], 3)

    def test_diamond_takes_the_longer_arm(self):
        blocks = [(0, 1, [4, 20], 'branch'), (4, 4, [28], 'plain'), (20, 2, [28], 'plain'), (28, 1, [], 'return')]
        record = walk(blocks).run()
        self.assertEqual(record['entry_budget'], 1 + 4 + 1)
        self.assertEqual([term['term'] for term in record['entries']['0000']['successors']], [5, 3])

    def test_call_with_an_integer_budget(self):
        record = walk([(0, 2, [8], 'call'), (8, 1, [], 'return')], registry={'demo.callee': 10}).run()
        self.assertEqual(record['entry_budget'], 2 + 10 + 1)
        self.assertEqual(record['callees'], {'demo.callee': {'budget': 10, 'source': 'registry'}})

    def test_call_with_an_expression_budget(self):
        registry = {'demo.callee': '3 * bv_unsigned {argv:1} + 4'}
        record = walk([(0, 2, [8], 'call'), (8, 1, [], 'return')], registry=registry).run()
        self.assertEqual(record['entry_budget'], '(3 * bv_unsigned {reg:x11} + 4) + 3')
        with self.assertRaisesRegex(BudgetError, 'reads argument 1'):
            walk([(0, 2, [8], 'call', {0: 11}), (8, 1, [], 'return')], registry=registry).run()

    def test_a_callee_without_budget_is_refused(self):
        with self.assertRaisesRegex(BudgetError, 'demo.callee has no budget'):
            walk([(0, 2, [8], 'call'), (8, 1, [], 'return')]).run()

    def test_tail_call(self):
        record = walk([(0, 2, [], 'tail')], registry={'demo.callee': 7}).run()
        self.assertEqual(record['entry_budget'], 9)

    def test_unreachable_arm_is_no_successor(self):
        blocks = [(0, 1, [4, 20], 'branch'), (4, 4, [28], 'plain'), (20, 2, [28], 'plain'), (28, 1, [], 'return')]
        record = walk(blocks, {'unreachable_entries': ['0004']}).run()
        self.assertEqual(record['entry_budget'], 1 + 2 + 1)
        self.assertEqual(record['entries']['0004'], {'pc': '0x1004', 'offset': '+0x4', 'kind': 'unreachable',
                                                     'budget': 0, 'instructions': 4, 'successors': []})

    LOOP = [(0, 1, [4], 'plain'), (4, 2, [4, 12], 'branch'), (12, 1, [], 'return')]

    def test_loop_without_potential_is_refused_with_its_offset(self):
        with self.assertRaisesRegex(BudgetError, r'the loop at \+0x4 has no potential row'):
            walk(self.LOOP).run()

    def test_loop_with_potential_over_register_binders(self):
        keys = {'loop_heads': ['0004'], 'potentials': {'0004': {'potential': '2 * (bv_unsigned e - bv_unsigned c) + 1',
                                                                'binders': ['c', 'e']}},
                'loop_designs': [{'head': '0004', 'registers': {'x11': 'c', 'x12': 'e'}}]}
        record = walk(self.LOOP, keys).run()
        cut = record['entries']['0004']
        self.assertEqual(cut['kind'], 'loop_cut')
        self.assertEqual(cut['budget'], '(2 * (bv_unsigned e - bv_unsigned c) + 1)')
        self.assertEqual([(term['kind'], term['term']) for term in cut['successors']],
                         [('back_edge', '(2 * (bv_unsigned e - bv_unsigned c) + 1)'), ('edge', 1)])
        self.assertEqual(record['entry_budget'], '(2 * (bv_unsigned {reg:x12} - bv_unsigned {reg:x11}) + 1) + 1')

    def test_loop_entry_needs_an_entry_bound_for_a_binder_without_register(self):
        keys = {'loop_heads': ['0004'], 'potentials': {'0004': {'potential': '2 * (n - i)', 'binders': ['n', 'i']}},
                'loop_designs': [{'head': '0004', 'registers': {}, 'index': 'i'}]}
        with self.assertRaisesRegex(BudgetError, r'loop at \+0x4 cannot be stated at its entry from \+0x0'):
            walk(self.LOOP, keys).run()
        keys['potentials']['0004']['entry_bound'] = '2 * demoLength args'
        self.assertEqual(walk(self.LOOP, keys).run()['entry_budget'], '(2 * demoLength args) + 1')


class Annotations(unittest.TestCase):
    def data(self, *rows, **profile_keys):
        cut = {'id': 'cut', 'at': {'pc': '+0x4', 'boundary': 'loop_cut'},
               'binders': [{'name': 'c', 'register': 'x11'}, {'name': 'i', 'role': 'index'}], 'facts': []}
        return {'schema': annotations.SCHEMA, 'function': 'demo', 'symbol': 'demo.fn', 'profile': dict(profile_keys),
                'rows': [cut, *rows]}

    def test_a_potential_row_compiles(self):
        row = {'id': 'p', 'at': {'pc': '+0x4', 'boundary': 'loop_cut'}, 'potential': '3 * (10 - i)'}
        compiled = annotations.compile_profile(self.data(row))
        self.assertEqual(compiled['potentials'], {'+0x4': {'potential': '3 * (10 - i)', 'binders': ['c', 'i']}})
        self.assertEqual(len(compiled['loop_designs']), 1)

    def test_a_potential_row_is_validated(self):
        for row, message in [
                ({'potential': 'i', 'at': {'pc': '+0x8', 'boundary': 'loop_cut'}}, 'no loop cut exists'),
                ({'potential': 'machine_x12 + i', 'at': {'pc': '+0x4', 'boundary': 'loop_cut'}}, 'does not bind'),
                ({'potential': 'demoLength args', 'at': {'pc': '+0x4', 'boundary': 'loop_cut'}}, 'names none')]:
            with self.assertRaisesRegex(annotations.AnnotationError, message):
                annotations.compile_profile(self.data({'id': 'p', **row}))

    def test_charged_needs_its_code(self):
        with self.assertRaisesRegex(annotations.AnnotationError, 'charged_code'):
            annotations.compile_profile(self.data(charged=True))
        code = {'module': 'Demo.Charged', 'premise': 'demoChargedCode'}
        compiled = annotations.compile_profile(self.data(charged=True, charged_code=code))
        self.assertEqual((compiled['charged'], compiled['charged_code']), (True, code))


class ChargedRendering(unittest.TestCase):
    CODE = {'module': 'ZesuSsz.Contracts.KeysToOwnedSliceCharged', 'premise': 'keysToOwnedSliceChargedCode'}

    def charged(self, scratch):
        data = json.loads((ROOT / 'tools/block/functions/keysToOwnedSlice.json').read_text())
        data.update(charged=True, charged_code=self.CODE)
        path = Path(scratch) / 'keysToOwnedSliceCharged.json'
        path.write_text(json.dumps(data))
        return path

    def registry(self, scratch):
        path = Path(scratch) / 'proved_functions.json'
        path.write_text(json.dumps({'functions': [
            {'symbol': 'alt_fl_alloc.alloc', 'budget': 53}, {'symbol': 'alt_fl_alloc.remap', 'budget': 9},
            {'symbol': 'alt_fl_alloc.free', 'budget': 42}, {'symbol': 'memcpy', 'budget': 3}]}))
        return path

    def test_headers_and_code_premise(self):
        with tempfile.TemporaryDirectory() as scratch:
            charged = load_profile(str(self.charged(scratch)))
        plain = load_profile('keysToOwnedSlice')
        self.assertIn('Require Import ZesuSsz.Automation2.StepBudget.\n', pilot_header(charged))
        self.assertNotIn('StepBudget', pilot_header(plain))
        source = render_block_caller(charged, '0000', [], [])
        self.assertIn('Require Import ZesuSsz.Contracts.KeysToOwnedSliceCharged.\n', source)
        self.assertIn('  keysToOwnedSliceChargedCode -∗\n', source)
        self.assertNotIn('keysToOwnedSliceSelectedCode', source)

    def test_call_premise_hands_the_callee_its_budget(self):
        with tempfile.TemporaryDirectory() as scratch:
            charged = load_profile(str(self.charged(scratch)))
            call = charged['calls'][0]
            self.assertEqual(call_premise(load_profile('keysToOwnedSlice'), call)[0],
                             'instr_pre 0x80041f38 (ZesuSsz.Contracts.AltFlAllocPremises.altFlFreeCallSpec)%I')
            with mock.patch.object(budgets, 'REGISTRY', self.registry(scratch)):
                premise, modules = call_premise(charged, call)
            self.assertEqual(premise, 'instr_pre 0x80041f38 (step_budget (42) ∗ '
                                      'ZesuSsz.Contracts.AltFlAllocPremises.altFlFreeCallSpec)%I')
            self.assertEqual(modules, ['ZesuSsz.Contracts.AltFlAllocPremises', 'ZesuSsz.Automation2.StepBudget'])

    def test_charged_callers_fixture(self):
        with tempfile.TemporaryDirectory() as scratch:
            scratch = Path(scratch)
            path = self.charged(scratch)
            charged = load_profile(str(path))
            cfg = json.loads((ROOT / 'build/stock-zisk/cfg.json').read_text())
            fn = next(item for item in cfg['functions'] if item['name'] == charged['cfg_function'])
            (scratch / 'FUNCTION.json').write_text(json.dumps({'functions': [fn]}))
            cases = [{'pc': charged.pc(block), 'status': 'source_declarations_rendered'} for block in charged['blocks']]
            cases.append({'pc': 'function_return', 'status': 'source_declarations_rendered'})
            (scratch / 'RESULT.json').write_text(json.dumps({'cases': cases}))
            argv = ['render_function_callers.py', '--function', str(path), '--entries', str(scratch / 'RESULT.json'),
                    '--cfg', str(scratch / 'FUNCTION.json'), '--output', str(scratch / 'callers')]
            with mock.patch.object(sys, 'argv', argv), mock.patch.object(budgets, 'REGISTRY', self.registry(scratch)):
                render_function_callers.main()
            source = (scratch / 'callers/Caller007c.v').read_text()
            self.assertIn('  instr_pre 0x80041f38 (step_budget (42) ∗ '
                          'ZesuSsz.Contracts.AltFlAllocPremises.altFlFreeCallSpec)%I -∗\n', source)
            self.assertIn('  keysToOwnedSliceChargedCode -∗\n', source)
            self.assertIn('Require Import ZesuSsz.Automation2.StepBudget.\n', source)

    def test_loop_head_classes_own_the_potential(self):
        decode = load_profile('decodeItem')
        header = pilot_header(decode)
        plain = render_loop_head('00c4', header, False, decode)
        text = render_loop_head('00c4', header, False, decode, budget='3 * (bv_unsigned loop_seed_x16 - i)')
        self.assertNotIn('step_budget', plain)
        classes = [line for line in text.splitlines() if line.startswith('Definition fp_machineAt00c4_LoopClass')]
        self.assertTrue(classes)
        for line in classes:
            conjunct = ' ∗ step_budget (3 * (bv_unsigned loop_seed_x16 - i))'
            self.assertEqual(line.count(conjunct), 1)
            self.assertLess(line.index(conjunct), line.index('⌜'))   # owned, before the pure facts

    def test_entry_budget_reads_registers_and_goes_before_pure_facts(self):
        components = ['"x2" ↦ᵣ (RVal_Bits (call_x2 : bv 64%N))',
                      '"x11" ↦ᵣ (RVal_Bits ((bv_add machine_x11 (BV 64%N 1%Z)) : bv 64%N))']
        text = budgets.resolve_registers('(3 * bv_unsigned {reg:x11}) + 2', components)
        self.assertEqual(budgets.budget_conjunct(text),
                         'step_budget ((3 * bv_unsigned ((bv_add machine_x11 (BV 64%N 1%Z)))) + 2)')
        self.assertEqual(budgets.place_budget(['register', 'byte_array', 'pure', 'continuation']), 2)
        self.assertEqual(budgets.place_budget(['register', 'continuation']), 1)
        with self.assertRaisesRegex(BudgetError, 'does not own'):
            budgets.resolve_registers('{reg:x12}', components)


if __name__ == '__main__':
    unittest.main()
