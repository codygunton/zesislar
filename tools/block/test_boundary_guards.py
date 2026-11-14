"""Refuse incomplete and contradictory generated boundaries."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from boundary_guards import (BoundaryRefused, RocqContradictionCheck, alternative_facts, annotate_reaching_stops,
                             check_groups, contradiction_source, contradictory_alternatives,
                             contradictory_sources, fact_conjuncts,
                             refused_alternative_indices, require_complete_boundary,
                             require_consistent_alternatives, without_alternatives)
from forward_design import evaluate_function
from symbolic_state import SymbolicState, bits

# A loop head at 16 with a back edge from 24 and an exit to 32.
FUNCTION = {'name': 'loop', 'entry': 16, 'end': 36,
            'rows': [{'pc': pc} for pc in range(16, 36, 4)],
            'blocks': [{'start': 16, 'end': 24, 'successors': [24, 32]},
                       {'start': 24, 'end': 32, 'successors': [16]},
                       {'start': 32, 'end': 36, 'successors': []}],
            'loops': [{'minimum_pc': 16}]}


def stop(reason, block_pc):
    return {'reason': reason, 'block_pc': hex(block_pc), 'instruction_pc': hex(block_pc),
            'seed_pc': hex(16), 'path': [0], 'detail': {'large': 'state'}}


def report(*stops):
    return {'boundaries': [{'pc': hex(pc), 'status': 'generated', 'alternatives': [{}]}
                           for pc in (16, 24, 32)],
            'stops': list(stops)}


def boundary(result, pc):
    return next(row for row in result['boundaries'] if row['pc'] == hex(pc))


EXIT = ('Definition fp_machineAt32_LoopExit `{!islaG Sigma} (args : DecodeItemArgs) : iProp Sigma := '
        '(∃ (machine_x15 : bv 64) (machine_x11 : bv 64), ("x15" ↦ᵣ RVal_Bits (machine_x15 : bv 64%N) ∗ '
        '⌜(bv_unsigned machine_x15 = bv_unsigned machine_x11) /\\ (bv_unsigned machine_x15 < 4)⌝))%I.\n')
FORWARD = ('Definition fp_machineAt32_ForwardA1N0 `{!islaG Sigma} (args : DecodeItemArgs) : iProp Sigma := '
           '(∃ (machine_x15 : bv 64), (⌜(bv_unsigned machine_x15 > 3)⌝ ∗ ⌜(bv_unsigned machine_x15 < 2)⌝))%I.\n')
MAIN = ('Definition fp_machineAt32 `{!islaG Sigma} (args : DecodeItemArgs) (K : iProp Sigma) : iProp Sigma := '
        '(fp_machineAt32_ForwardA1N0 (args) ∗ K)%I.\n')


class StopReachability(unittest.TestCase):
    def test_stop_that_reaches_a_boundary_refuses_the_render(self):
        result = annotate_reaching_stops(report(stop('state_check', 16)), FUNCTION)
        with self.assertRaisesRegex(BoundaryRefused, r'1 retained stops can reach the boundary 0x20'):
            require_complete_boundary(boundary(result, 32))
        self.assertEqual(boundary(result, 32)['reaching_stops'][0]['reason'], 'state_check')
        self.assertNotIn('detail', boundary(result, 32)['reaching_stops'][0])

    def test_stop_after_the_exit_does_not_reach_the_loop(self):
        result = annotate_reaching_stops(report(stop('unsupported', 32)), FUNCTION)
        for pc in (16, 24):
            require_complete_boundary(boundary(result, pc))
        with self.assertRaises(BoundaryRefused):
            require_complete_boundary(boundary(result, 32))

    def test_cut_and_infeasible_stops_drop_no_path(self):
        result = annotate_reaching_stops(report(stop('handwritten_cut', 24), stop('infeasible', 16)), FUNCTION)
        for pc in (16, 24, 32):
            require_complete_boundary(boundary(result, pc))

    def test_unseeded_cut_drops_the_paths_beyond_it(self):
        # The pass stops at the loop head 16 from block 24. Without a seed at 16,
        # every boundary after 16 misses the path, the head too through its back edge.
        cut = {**stop('handwritten_cut', 24), 'target_pc': hex(16)}
        unseeded = report(cut)
        for row in unseeded['boundaries']:
            row['alternatives'] = [{'predecessor_pc': hex(24)}]
        result = annotate_reaching_stops(unseeded, FUNCTION)
        for pc in (16, 24, 32):
            with self.assertRaisesRegex(BoundaryRefused, 'handwritten_cut'):
                require_complete_boundary(boundary(result, pc))
        seeded = report(cut)
        boundary(seeded, 16)['alternatives'] = [{'predecessor_pc': None}]
        result = annotate_reaching_stops(seeded, FUNCTION)
        for pc in (16, 24, 32):
            require_complete_boundary(boundary(result, pc))

    def test_fault_arm_that_leaves_the_function_drops_no_path(self):
        # The trap vector 0 and the address 64 are outside the function [16, 36).
        leaving = [dict(stop('intermediate_pc_mismatch', 16), actual_pc=hex(0)),
                   dict(stop('outside_pc', 24), actual_pc=hex(64))]
        result = annotate_reaching_stops(report(*leaving), FUNCTION)
        for pc in (16, 24, 32):
            require_complete_boundary(boundary(result, pc))
        inside = dict(stop('intermediate_pc_mismatch', 16), actual_pc=hex(32))
        result = annotate_reaching_stops(report(inside), FUNCTION)
        with self.assertRaisesRegex(BoundaryRefused, '1 retained stops can reach the boundary 0x20'):
            require_complete_boundary(boundary(result, 32))

    def test_call_stop_is_a_call_boundary_not_a_fault_exit(self):
        # Block 16 ends in a call at 20 to the callee 64, outside the function [16, 32).
        function = {'name': 'caller', 'entry': 16, 'end': 32,
                    'rows': [{'pc': pc} for pc in range(16, 32, 4)],
                    'blocks': [{'start': 16, 'end': 24, 'successors': [24]},
                               {'start': 24, 'end': 32, 'successors': []}],
                    'calls': [{'pc': 20, 'target': 64, 'kind': 'call'}]}
        call = dict(stop('outside_pc', 16), instruction_pc=hex(20), actual_pc=hex(64))
        result = annotate_reaching_stops(report(call), function)
        with self.assertRaisesRegex(BoundaryRefused, '1 retained stops can reach the boundary 0x18; '
                                                     'the first is outside_pc in block 0x10 at 0x14'):
            require_complete_boundary(boundary(result, 24))
        # A fault arm of the call instruction (the trap vector 0) still leaves the function.
        result = annotate_reaching_stops(report(dict(call, actual_pc=hex(0))), function)
        require_complete_boundary(boundary(result, 24))

    def test_boundary_without_a_reachability_record_is_refused(self):
        with self.assertRaisesRegex(BoundaryRefused, 'no stop-reachability record'):
            require_complete_boundary({'pc': hex(32), 'status': 'generated', 'alternatives': [{}]})

    def test_forward_pass_records_reaching_stops(self):
        # Block 16 has no trace, so the pass stops there and drops every path to 24 and 32.
        state = SymbolicState(registers={'PC': bits(16, 64)})
        result = evaluate_function(FUNCTION, {}, {16: state})
        self.assertEqual([row['reason'] for row in result['stops']], ['missing_trace'])
        for pc in (16, 24, 32):
            with self.assertRaises(BoundaryRefused):
                require_complete_boundary(boundary(result, pc))


class CallBoundary(unittest.TestCase):
    # Block 16 ends in a call at 20 to the callee 64; the return site 24 is a cut.
    CALLER = {'name': 'caller', 'entry': 16, 'end': 32, 'rows': [{'pc': pc} for pc in range(16, 32, 4)],
              'blocks': [{'start': 16, 'end': 24, 'successors': [24]},
                         {'start': 24, 'end': 32, 'successors': []}],
              'calls': [{'pc': 20, 'target': 64, 'kind': 'call'}]}
    CALL = '(trace (write-reg |PC| nil #x0000000000000040))'
    PLAIN = '(trace (write-reg |PC| nil #x0000000000000014))'

    def test_call_stops_at_the_call_and_drops_the_return_site_until_it_has_a_seed(self):
        state = SymbolicState(registers={'PC': bits(16, 64)})
        result = evaluate_function(self.CALLER, {16: self.PLAIN, 20: self.CALL}, {16: state})
        self.assertEqual([(row['reason'], row['target_pc']) for row in result['stops']],
                         [('call_boundary', hex(24))])
        self.assertIn({'pc': hex(24), 'reason': 'call_return'}, result['cuts'])
        require_complete_boundary(boundary(result, 16))
        with self.assertRaisesRegex(BoundaryRefused, 'call_boundary in block 0x10'):
            require_complete_boundary(boundary(result, 24))
        seeded = evaluate_function(self.CALLER, {16: self.PLAIN, 20: self.CALL},
                                   {16: state, 24: SymbolicState(registers={'PC': bits(24, 64)})},
                                   generated_seeds={24: 'call_return'})
        # With a return-site seed the call stop drops no path; block 24 itself has no trace here.
        self.assertEqual([row['reason'] for row in boundary(seeded, 24)['reaching_stops']], ['missing_trace'])

    def test_a_tail_jump_is_an_exit_not_a_call(self):
        tail = {**self.CALLER, 'end': 24, 'rows': [{'pc': pc} for pc in range(16, 24, 4)],
                'blocks': [{'start': 16, 'end': 24, 'successors': []}],
                'calls': [{'pc': 20, 'target': 64, 'kind': 'tail'}]}
        result = evaluate_function(tail, {16: self.PLAIN, 20: self.CALL}, {16: SymbolicState(registers={'PC': bits(16, 64)})})
        self.assertEqual(result['cuts'], [])
        self.assertNotIn('call_boundary', [row['reason'] for row in result['stops']])

    def test_machine_call_spec_summary(self):
        from call_boundary import parse_machine_call_spec
        source = (Path(__file__).resolve().parents[2] / 'ZesuSsz/Contracts/DecodeItemCallSpec.v').read_text()
        spec = parse_machine_call_spec(source, 'decodeItemCallSpec')
        self.assertEqual((spec['map'], spec['stack']), ('decodeItemCallMap', 'decodeItemStackBytes'))
        self.assertEqual(spec['pre']['arrays'], [{'argument': 1, 'binder': 'input'}, {'argument': 0, 'binder': 'before'}])
        self.assertEqual(spec['post']['arrays'], [{'argument': 1, 'binder': 'input'}, {'argument': 0, 'binder': 'after'}])
        self.assertEqual(spec['post']['registers'], [{'register': 'zisk_input_end', 'binder': 'inputEndBits'}])
        self.assertTrue(spec['post']['facts'][0].startswith('DecodeMeaningModuloKnownBugs'))

    def test_return_fact_names_the_callers_load_of_the_output(self):
        from call_boundary import _return_fact
        from symbolic_state import Expr, input_expr, operation
        array = input_expr('call_after', None)
        # The forward pass's 8-byte little-endian load at offset 8 of the output array.
        chunks = [Expr('array_byte', (array,), 8, 8 + index) for index in range(8)][::-1]
        load = chunks[0]
        for chunk in chunks[1:]:
            load = operation('concat', load, chunk)
        self.assertEqual(_return_fact('0 < bv_unsigned {word:after:8}', {'after': 'call_after'}),
                         '0 < bv_unsigned ' + load.coq())

    def test_a_new_piece_never_reuses_a_coalesced_pieces_name(self):
        from call_boundary import PieceNames
        names = PieceNames([{'id': 'frame'}, {'id': 'frame_call_output_length'}])
        self.assertEqual(names('frame_call_output'), 'frame_call_output_2')
        self.assertEqual(names('frame_call_output'), 'frame_call_output_3')
        self.assertEqual(names('frame_call_after'), 'frame_call_after')

    def test_a_caller_array_with_stores_keeps_its_bytes_only_when_they_are_known(self):
        from call_boundary import stored_caller_span
        from forward_resources import OwnedBytes
        from symbolic_state import input_expr
        def array(value):
            return OwnedBytes('span', input_expr('base'), 'base', value, 8, True, 'DfracOwn 1',
                              {'source': 'base ↦ₘ∗ before'}, {'source': 'fixture'}, 8)
        stored = {offset: {'value': None} for offset in range(8)}
        self.assertTrue(stored_caller_span(array(None), {0: {'value': None}}))
        self.assertTrue(stored_caller_span(array(input_expr('before', None)), stored))
        # An initialized array that keeps some old bytes, or a store at a symbolic offset, refuses.
        self.assertFalse(stored_caller_span(array(input_expr('before', None)), {0: {'value': None}}))
        self.assertFalse(stored_caller_span(array(None), {'i': {'value': None}}))

    def test_a_spec_reaches_its_input_through_stored_words(self):
        from call_boundary import parse_machine_call_spec
        source = (Path(__file__).resolve().parents[2] / 'ZesuSsz/Contracts/NextUint64CallSpec2.v').read_text()
        spec = parse_machine_call_spec(source, 'nextUint64CallSpec2')
        self.assertEqual(spec['pre']['words'], [{'argument': 1, 'offset': 0, 'value': 'inputPointer'},
                                                {'argument': 1, 'offset': 8, 'value': 'inputLength'}])
        self.assertEqual(spec['post']['words'][1],
                         {'argument': 1, 'offset': 8, 'value': 'Z_to_bv 64 (nextRestLength result)'})
        self.assertEqual(spec['pre']['arrays'], [{'pointer': 'inputPointer', 'binder': 'input'}])
        self.assertEqual(spec['pre']['uninitialized'], [{'argument': 0, 'length': '16'}])
        self.assertEqual(spec['post']['arrays'], [{'pointer': 'inputPointer', 'binder': 'input'},
                                                 {'argument': 0, 'value': 'nextResultBytes result'}])
        self.assertEqual(spec['post_binders'], [('result', 'NextUint64Return')])

    def test_a_word_at_a_call_argument_is_the_value_the_caller_holds(self):
        from call_boundary import CallRefused, stored_word
        from forward_resources import OwnedBytes
        from symbolic_state import MemoryRegion, input_expr, operation
        frame = OwnedBytes('frame', input_expr('sp', 64), 'sp', None, 32, True, 'DfracOwn 1',
                           {'source': 'sp ↦ₘ? 32'}, {'source': 'fixture'})
        pointer = input_expr('pointer', 64)
        chunks = [operation('extract', pointer, width=8, value=8 * index) for index in range(8)]
        stored = {8 + index: {'value': chunk.to_dict()} for index, chunk in enumerate(chunks)}
        address = operation('bvadd', input_expr('sp', 64), bits(8, 64))
        self.assertEqual(stored_word({'frame': frame}, {'frame': stored}, address), ('frame', 8, pointer))
        # A byte the paths did not store is read from the caller's known bytes, if any.
        del stored[15]
        with self.assertRaises(CallRefused):
            stored_word({'frame': frame}, {'frame': stored}, address)
        known = MemoryRegion(input_expr('sp', 64), bytes=(bits(0, 8),) * 8 + tuple(chunks), ownership_id='frame')
        self.assertEqual(stored_word({'frame': frame}, {'frame': stored}, address, [known]), ('frame', 8, pointer))


class PureExistentials(unittest.TestCase):
    def test_existential_inside_a_pure_fact_is_not_hoisted(self):
        definition = ('Definition d `{!islaG Sigma} (args : A) : iProp Sigma := (∃ (w : bv 64), '
                      '("x1" ↦ᵣ RVal_Bits (w : bv 64%N) ∗ ⌜(∃ r : R, P r w)⌝ ∗ (∃ (v : bv 64), ⌜Q v⌝)))%I.\n')
        binders, facts = alternative_facts(definition)
        self.assertEqual(binders, '(w : bv 64) (v : bv 64)')
        self.assertEqual(facts, ['(∃ r : R, P r w)', 'Q v'])


class FunctionReturn(unittest.TestCase):
    RETURN = {'name': 'ret', 'entry': 16, 'end': 20, 'rows': [{'pc': 16}],
              'blocks': [{'start': 16, 'end': 20, 'successors': []}], 'returns': [16]}
    TRACE = '(trace (declare-const v1 (_ BitVec 64)) (read-reg |x1| nil v1) (write-reg |PC| nil v1))'

    def state(self):
        from symbolic_state import input_expr
        return SymbolicState(registers={'PC': bits(16, 64), 'x1': input_expr('returnAddress', 64)})

    def test_return_site_is_an_exit_not_a_stop(self):
        result = evaluate_function(self.RETURN, {16: self.TRACE}, {16: self.state()})
        self.assertEqual(result['stops'], [])
        self.assertEqual([row['kind'] for row in result['exits']], ['function_return'])
        self.assertEqual(result['exits'][0]['instruction_pc'], hex(16))
        require_complete_boundary(boundary(result, 16))

    def test_jump_to_an_unknown_address_elsewhere_still_stops(self):
        function = {**self.RETURN, 'returns': []}
        result = evaluate_function(function, {16: self.TRACE}, {16: self.state()})
        self.assertEqual([row['reason'] for row in result['stops']], ['unknown_pc'])
        self.assertEqual(result['exits'], [])
        with self.assertRaises(BoundaryRefused):
            require_complete_boundary(boundary(result, 16))


class Contradictions(unittest.TestCase):
    def test_contradictory_alternative_is_refused(self):
        calls = []

        def check(name, binders, facts):
            calls.append((name, binders, facts))
            return name.endswith('ForwardA1N0')

        definitions = [('fp_machineAt32_ForwardA1N0', FORWARD), ('fp_machineAt32', MAIN)]
        self.assertEqual(contradictory_alternatives(definitions, check), ['fp_machineAt32_ForwardA1N0'])
        self.assertEqual([call[0] for call in calls], ['fp_machineAt32_ForwardA1N0'])
        self.assertEqual(calls[0][1:], ('(machine_x15 : bv 64)',
                                        ['(bv_unsigned machine_x15 > 3)', '(bv_unsigned machine_x15 < 2)']))
        with self.assertRaisesRegex(BoundaryRefused, 'fp_machineAt32_ForwardA1N0'):
            require_consistent_alternatives(definitions, check)

    def test_consistent_alternative_is_kept(self):
        definitions = [('fp_machineAt32_LoopExit', EXIT)]
        self.assertEqual(contradictory_alternatives(definitions, lambda *args: False), [])
        binders, facts = alternative_facts(EXIT)
        self.assertEqual(binders, '(machine_x15 : bv 64) (machine_x11 : bv 64)')
        self.assertEqual(facts, ['(bv_unsigned machine_x15 = bv_unsigned machine_x11) /\\ (bv_unsigned machine_x15 < 4)'])

    def test_refused_alternative_leaves_the_boundary(self):
        source = {'pc': hex(32), 'status': 'generated', 'alternatives': [{'path': [0]}, {'path': [1]}]}
        indices = refused_alternative_indices(['fp_machineAt32_ForwardA1N0'])
        self.assertEqual(without_alternatives(source, indices)['alternatives'], [{'path': [0]}])
        with self.assertRaisesRegex(BoundaryRefused, 'Every alternative'):
            without_alternatives(source, [0, 1])
        with self.assertRaisesRegex(BoundaryRefused, 'plain generated'):
            without_alternatives({**source, 'status': 'generated_join'}, indices)

    def test_contradictory_source_leaves_the_cut_before_generalization(self):
        source = {'pc': hex(32), 'status': 'generated',
                  'alternatives': [{'path': [0]}, {'path': [1]}, {'path': [2]}]}
        rendered, checked = [], []

        def render_alone(alone):
            alternative, = alone['alternatives']
            rendered.append(alternative['path'])
            if alternative['path'] == [2]:
                return None
            return [('fp_machineAt32_ForwardA0N0', FORWARD), ('fp_machineAt32', MAIN)]

        def check(name, binders, facts):
            checked.append(name)
            return name.endswith('ForwardA1N0')

        self.assertEqual(contradictory_sources(source, render_alone, check), [1])
        self.assertEqual(rendered, [[0], [1], [2]])
        self.assertEqual(checked, ['fp_machineAt32_ForwardA0N0', 'fp_machineAt32_ForwardA1N0'])
        self.assertEqual(without_alternatives(source, [1])['alternatives'],
                         [{'path': [0]}, {'path': [2]}])

    def test_check_compiles_only_when_the_solver_fails(self):
        binders, facts = alternative_facts(FORWARD)
        source = contradiction_source('Require Import Header.\n', check_groups(binders, facts))
        self.assertIn('Goal forall (args : DecodeItemArgs) (returnAddress : Z) (machine_x15 : bv 64),', source)
        self.assertIn('Fail solve [zesu_contradiction_check]', source)
        self.assertLess(source.index('Ltac zesu_contradiction_check'), source.index('Fail solve'))
        self.assertNotRegex(source, r'\b(?:Timeout|timeout|Qed|Admitted)\b')
        other = contradiction_source('Require Import Header.\n', check_groups(binders, facts), 'FreeArgs')
        self.assertIn('Goal forall (args : FreeArgs) (returnAddress : Z) (machine_x15 : bv 64),', other)


class DuplicatedJoins(unittest.TestCase):
    # 16 branches to 20 or 24; both reach the join 28, and 24 splits into two paths
    # inside its block. 32 (two instructions) follows the join; 40 is the exit.
    FUNCTION = {'name': 'diamond', 'entry': 16, 'end': 44, 'rows': [{'pc': pc} for pc in range(16, 44, 4)],
                'blocks': [{'start': 16, 'end': 20, 'successors': [20, 24]},
                           {'start': 20, 'end': 24, 'successors': [28]},
                           {'start': 24, 'end': 28, 'successors': [28]},
                           {'start': 28, 'end': 32, 'successors': [32]},
                           {'start': 32, 'end': 40, 'successors': [40]},
                           {'start': 40, 'end': 44, 'successors': []}]}

    @staticmethod
    def jump(*targets):
        arms = ['(trace (write-reg |PC| nil #x%016x))' % target for target in targets]
        return arms[0] if len(arms) == 1 else '(trace (cases "branch" ' + ' '.join(arms) + '))'

    def run_pass(self, duplicated):
        traces = {16: self.jump(20, 24), 20: self.jump(28), 24: self.jump(28, 28), 28: self.jump(32),
                  32: self.jump(36), 36: self.jump(40)}
        return evaluate_function(self.FUNCTION, traces, {16: SymbolicState(registers={'PC': bits(16, 64)})},
                                 duplicated_joins=duplicated)

    def test_a_duplicated_join_is_no_cut_and_keeps_one_slot_per_incoming_edge(self):
        result = self.run_pass([28])
        self.assertNotIn('handwritten_cut', [row['reason'] for row in result['stops']])
        self.assertEqual(result['cuts'], [])
        self.assertEqual(result['duplicated_joins'], [hex(28)])
        join = boundary(result, 28)
        self.assertEqual(join['status'], 'generated')
        self.assertEqual(join['slots'], [{'predecessor_pc': hex(20), 'predecessor_slot': None, 'alternatives': [0]},
                                         {'predecessor_pc': hex(24), 'predecessor_slot': None,
                                          'alternatives': [1, 2]}])
        # The blocks after the join keep the slots: each continues its own join slot.
        for pc, predecessor in ((32, 28), (40, 32)):
            self.assertEqual([(row['predecessor_pc'], row['predecessor_slot'], len(row['alternatives']))
                              for row in boundary(result, pc)['slots']],
                             [(hex(predecessor), 0, 1), (hex(predecessor), 1, 2)])
        self.assertNotIn('slots', boundary(result, 20))

    def test_without_duplication_the_join_stays_a_cut(self):
        result = self.run_pass(())
        self.assertEqual(result['cuts'], [{'pc': hex(28), 'reason': 'join'}])
        self.assertNotIn('slots', boundary(result, 28))
        self.assertNotIn('predecessor_alternative', boundary(result, 28)['alternatives'][0])

    def test_only_a_plain_join_can_be_duplicated(self):
        with self.assertRaisesRegex(ValueError, 'must be a join and nothing else'):
            self.run_pass([32])



class GroupedChecks(unittest.TestCase):
    BINDERS = '(a : bv 64) (b : bv 64) (c : list (bv 8)) (d : bv 64)'
    FACTS = ['((bool_decide (a = b) = true) /\\ ((bv_unsigned a = bv_unsigned b)%Z))',
             '(∃ (x : bv 64), P x a c)',
             '((List.length c = 4)%nat)',
             'bv_unsigned b < 8',
             '(bv_unsigned d < 2) /\\ (∃ y, Q y d)']

    def test_conjunctions_split_and_an_existential_is_not_read(self):
        self.assertEqual(fact_conjuncts(self.FACTS[0]),
                         ['(bool_decide (a = b) = true)', '((bv_unsigned a = bv_unsigned b)%Z)'])
        self.assertEqual(fact_conjuncts('(A -> B) /\\ C'), ['(A -> B) /\\ C'])
        self.assertEqual(fact_conjuncts('~ (A /\\ B)'), ['~ (A /\\ B)'])

    def test_facts_that_share_no_name_are_checked_apart(self):
        groups = check_groups(self.BINDERS, self.FACTS)
        self.assertEqual(groups, [
            (['(a : bv 64)', '(b : bv 64)'],
             ['(bool_decide (a = b) = true)', '((bv_unsigned a = bv_unsigned b)%Z)', 'bv_unsigned b < 8']),
            (['(c : list (bv 8))'], ['((List.length c = 4)%nat)']),
            (['(d : bv 64)'], ['(bv_unsigned d < 2)'])])
        source = contradiction_source('Require Import Header.\n', groups)
        self.assertEqual(source.count('Fail solve [zesu_contradiction_check]'), 3)
        self.assertNotIn('P x a c', source)

    def test_a_group_inside_an_unrefuted_group_is_not_checked_again(self):
        with tempfile.TemporaryDirectory() as directory:
            check = RocqContradictionCheck(['true'], 'Require Import Header.\n', directory)
            self.assertFalse(check('first', self.BINDERS, self.FACTS))
            # The same facts, fewer facts in a group: every group was checked before.
            self.assertFalse(check('second', self.BINDERS, self.FACTS[:2] + self.FACTS[3:]))
            # A new fact joins the group of d; only that group is checked.
            self.assertFalse(check('third', self.BINDERS, self.FACTS + ['bv_unsigned d > 0']))
            first, second, third = check.runs
            self.assertEqual((first['groups'], first['checked_groups']), (3, 3))
            self.assertEqual((second['check'], second['reused']), (None, [first['check']]))
            self.assertEqual((third['groups'], third['checked_groups']), (3, 1))
            source = Path(third['check']).read_text()
            self.assertEqual(source.count('Goal forall'), 1)
            self.assertIn('(bv_unsigned d > 0)', source)
            self.assertNotIn('bv_unsigned b < 8', source)

    def test_a_refuted_group_is_not_reused(self):
        with tempfile.TemporaryDirectory() as directory:
            check = RocqContradictionCheck(['sh', '-c', 'echo "The command has not failed"; exit 1', 'check'],
                                           'Require Import Header.\n', directory)
            self.assertTrue(check('first', self.BINDERS, self.FACTS))
            self.assertTrue(check('second', self.BINDERS, self.FACTS))
            self.assertEqual(check.checked, [])


if __name__ == '__main__':
    unittest.main()
