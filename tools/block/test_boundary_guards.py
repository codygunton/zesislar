"""Refuse incomplete and contradictory generated boundaries."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from boundary_guards import (BoundaryRefused, alternative_facts, annotate_reaching_stops,
                             contradiction_source, contradictory_alternatives,
                             contradictory_sources,
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
        source = contradiction_source('Require Import Header.\n', binders, facts)
        self.assertIn('Goal forall (args : DecodeItemArgs) (returnAddress : Z) (machine_x15 : bv 64),', source)
        self.assertIn('Fail solve [zesu_contradiction_check]', source)
        self.assertLess(source.index('Ltac zesu_contradiction_check'), source.index('Fail solve'))
        self.assertNotRegex(source, r'\b(?:Timeout|timeout|Qed|Admitted)\b')
        other = contradiction_source('Require Import Header.\n', binders, facts, 'FreeArgs')
        self.assertIn('Goal forall (args : FreeArgs) (returnAddress : Z) (machine_x15 : bv 64),', other)


if __name__ == '__main__':
    unittest.main()
