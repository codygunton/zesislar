"""Alternatives that differ only in their path conditions continue as one (forward_design)."""
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from forward_design import evaluate_function
from symbolic_state import SymbolicState, bits, input_expr


BOUND = '(bvult v1 #x00000000c0000000)'


def guard(target, width):
    """The address test of a block: a memory-map guard (128-bit, as the platform widens the
    address) or, at width 64, an ordinary comparison."""
    if width == 128:
        return '(bvult ((_ zero_extend 64) v1) #x%032x)' % (0xa0000000 + target)
    return '(bvult v1 #x%016x)' % (0xa0000000 + target)


def region_load(target, width=128):
    """A load-like instruction: two region arms give the same value, a third arm gives zero.

    Every arm keeps the shared bound; the region arms add their own guard on the address
    (one guard per block, so no later block refutes an earlier arm)."""
    jump = '(write-reg |PC| nil #x%016x)' % target
    low = guard(target, width)
    return ('(trace (declare-const v1 (_ BitVec 64)) (read-reg |x10| nil v1) (declare-const v2 (_ BitVec 64)) '
            '(read-reg |x11| nil v2) (assert %s) (cases "region" '
            '(trace (assert %s) (write-reg |x11| nil #x0000000000000001) %s) '
            '(trace (assert (not %s)) (write-reg |x11| nil #x0000000000000001) %s) '
            '(trace (assert (not %s)) (write-reg |x11| nil #x0000000000000000) %s)))'
            % (BOUND, low, jump, low, jump, low, jump))


RETURN = ('(trace (declare-const v1 (_ BitVec 64)) (read-reg |x1| nil v1) (declare-const v2 (_ BitVec 64)) '
          '(read-reg |x11| nil v2) (write-reg |PC| nil v1))')


def state():
    return SymbolicState(registers={'PC': bits(16, 64), 'x1': input_expr('returnAddress', 64),
                                    'x10': input_expr('pointer', 64), 'x11': input_expr('limb', 64)})


def boundary(result, pc):
    return next(row for row in result['boundaries'] if row['pc'] == hex(pc))


def conditions(alternative):
    return [json.dumps(row) for row in alternative['state']['conditions']]


class ChainMerge(unittest.TestCase):
    # Five load blocks in a chain (16 to 32), then the return block 36.
    CHAIN = {'name': 'chain', 'entry': 16, 'end': 40, 'rows': [{'pc': pc} for pc in range(16, 40, 4)],
             'blocks': [{'start': pc, 'end': pc + 4, 'successors': [pc + 4]} for pc in range(16, 36, 4)]
                       + [{'start': 36, 'end': 40, 'successors': []}], 'returns': [36]}
    TRACES = {**{pc: region_load(pc + 4) for pc in range(16, 36, 4)}, 36: RETURN}

    def run_pass(self, merge, max_paths=4096):
        return evaluate_function(self.CHAIN, self.TRACES, {16: state()}, max_paths=max_paths,
                                 merge_condition_alternatives=merge)

    def test_without_merging_the_region_arms_multiply_to_the_path_limit(self):
        # Six blocks: the whole pass may create 6 * 20 paths; unmerged, block k runs 3^k times.
        result = self.run_pass(False, max_paths=20)
        self.assertIn('path_limit', [row['reason'] for row in result['stops']])
        self.assertTrue(boundary(result, 36)['reaching_stops'])
        self.assertEqual(len(boundary(result, 24)['alternatives']), 9)
        self.assertNotIn('merged_alternatives', result)

    def test_the_budget_counts_per_block_so_a_long_chain_completes(self):
        # Each block run creates two extra paths; the pass creates 19 in all, more than 6.
        result = self.run_pass(True, max_paths=6)
        self.assertEqual([row['reason'] for row in result['stops']], [])
        self.assertEqual(len(result['exits']), 2)

    def test_each_block_run_has_its_own_budget(self):
        # Two leaves per block run: every load block drops its third arm, none runs out of
        # a budget an earlier block used.
        result = self.run_pass(True, max_paths=2)
        limits = [row for row in result['stops'] if row['reason'] == 'path_limit']
        self.assertEqual(sorted({row['block_pc'] for row in limits}), [hex(pc) for pc in range(16, 36, 4)])

    def test_merged_region_arms_stay_two_alternatives_per_block(self):
        result = self.run_pass(True, max_paths=100)
        self.assertEqual([row['reason'] for row in result['stops']], [])
        for pc in range(20, 40, 4):
            self.assertEqual(len(boundary(result, pc)['alternatives']), 2, hex(pc))
            self.assertEqual(boundary(result, pc)['reaching_stops'], [])
        # One region arm merges into the other at 20; at later blocks each arm of the
        # second alternative merges too.
        self.assertEqual(result['merged_alternatives'][hex(20)], 1)
        self.assertEqual(result['merged_alternatives'][hex(24)], 4)
        self.assertEqual(len(result['exits']), 2)

    def test_the_merged_alternative_keeps_only_the_conditions_both_arms_share(self):
        result = self.run_pass(True)
        first, second = boundary(result, 20)['alternatives']
        self.assertEqual(first['state']['registers']['x11'], bits(1, 64).to_dict())
        self.assertEqual(second['state']['registers']['x11'], bits(0, 64).to_dict())
        # The value-one alternative stands for both region arms: the bound stays, the
        # region guard (true on one arm, false on the other) is gone.
        self.assertEqual(len(first['state']['conditions']), 1)
        self.assertIn(str(0xc0000000), conditions(first)[0])
        self.assertNotIn(str(0xa0000000 + 20), conditions(first)[0])
        # The zero arm is a path of its own: it keeps its own guard.
        self.assertEqual(len(second['state']['conditions']), 2)

    def test_states_that_differ_in_a_live_value_are_not_merged(self):
        result = self.run_pass(True)
        values = {str(row['state']['registers']['x11']) for row in boundary(result, 36)['alternatives']}
        self.assertEqual(len(values), 2)

    def test_arms_that_differ_in_an_ordinary_guard_merge_into_a_disjunction(self):
        # One alternative per edge and state: the two arms with the same value hold an ordinary
        # guard and its negation alone; they become one alternative with their disjunction
        # (`_disjoined_conditions`). The zero arm has another state and stays apart.
        traces = {**{pc: region_load(pc + 4, width=64) for pc in range(16, 36, 4)}, 36: RETURN}
        result = evaluate_function(self.CHAIN, traces, {16: state()}, merge_condition_alternatives=True)
        alternatives = boundary(result, 20)['alternatives']
        self.assertEqual(len(alternatives), 2)
        self.assertIn(hex(20), result.get('merged_alternatives', {}))
        self.assertEqual(sum('or' in [c['op'] for c in alternative['state']['conditions']]
                             for alternative in alternatives), 1)


class ExitMerge(unittest.TestCase):
    # One return block whose two region arms return the same state.
    FUNCTION = {'name': 'ret', 'entry': 16, 'end': 20, 'rows': [{'pc': 16}],
                'blocks': [{'start': 16, 'end': 20, 'successors': []}], 'returns': [16]}
    TRACE = ('(trace (declare-const v1 (_ BitVec 64)) (read-reg |x10| nil v1) (declare-const v3 (_ BitVec 64)) '
             '(read-reg |x1| nil v3) (cases "region" (trace (assert %s) (write-reg |PC| nil v3)) '
             '(trace (assert (not %s)) (write-reg |PC| nil v3))))' % (guard(0, 128), guard(0, 128)))

    def test_exits_that_differ_only_in_a_memory_map_guard_merge(self):
        apart = evaluate_function(self.FUNCTION, {16: self.TRACE}, {16: state()})
        self.assertEqual(len(apart['exits']), 2)
        result = evaluate_function(self.FUNCTION, {16: self.TRACE}, {16: state()}, merge_condition_alternatives=True)
        self.assertEqual(len(result['exits']), 1)
        self.assertEqual(result['exits'][0]['state']['conditions'], [])
        self.assertEqual(result['merged_alternatives'], {'function_return': 1})


class JoinMerge(unittest.TestCase):
    # 16 branches to 20 (a region load) or 24; both reach the join 28, which returns.
    FUNCTION = {'name': 'join', 'entry': 16, 'end': 32, 'rows': [{'pc': pc} for pc in range(16, 32, 4)],
                'blocks': [{'start': 16, 'end': 20, 'successors': [20, 24]},
                           {'start': 20, 'end': 24, 'successors': [28]},
                           {'start': 24, 'end': 28, 'successors': [28]},
                           {'start': 28, 'end': 32, 'successors': []}], 'returns': [28]}
    TRACES = {16: '(trace (cases "branch" (trace (write-reg |PC| nil #x0000000000000014)) '
                  '(trace (write-reg |PC| nil #x0000000000000018))))',
              20: region_load(28), 24: '(trace (write-reg |PC| nil #x000000000000001c))', 28: RETURN}

    def test_edges_into_a_cut_merge_and_their_stop_carries_the_merged_state(self):
        result = evaluate_function(self.FUNCTION, self.TRACES, {16: state()}, merge_condition_alternatives=True)
        join = boundary(result, 28)
        self.assertEqual([row['predecessor_pc'] for row in join['alternatives']], [hex(20), hex(20), hex(24)])
        cuts = [row for row in result['stops'] if row['reason'] == 'handwritten_cut']
        self.assertEqual(len(cuts), 3)
        self.assertEqual(cuts[0]['state']['conditions'], join['alternatives'][0]['state']['conditions'])
        self.assertEqual(len(cuts[0]['state']['conditions']), 1)
        self.assertEqual(result['merged_alternatives'], {hex(28): 1})


class UnreachableTarget(unittest.TestCase):
    # The JoinMerge function: an `unreachable` row (reached: contradictory_guards) at 24.
    def test_a_path_into_an_unreachable_target_stops_as_infeasible(self):
        result = evaluate_function(JoinMerge.FUNCTION, JoinMerge.TRACES, {16: state()}, unreachable_targets=[24])
        self.assertEqual(boundary(result, 24)['alternatives'], [])
        stops = [row for row in result['stops'] if row['reason'] == 'infeasible']
        self.assertEqual([(row['block_pc'], row['target_pc'], row['rule']) for row in stops],
                         [(hex(16), hex(24), 'annotation_unreachable_row')])
        self.assertEqual(boundary(result, 28)['reaching_stops'], [])
        self.assertEqual({row['predecessor_pc'] for row in boundary(result, 28)['alternatives']}, {hex(20)})

    def test_without_the_row_the_pass_is_unchanged(self):
        self.assertEqual(evaluate_function(JoinMerge.FUNCTION, JoinMerge.TRACES, {16: state()}),
                         evaluate_function(JoinMerge.FUNCTION, JoinMerge.TRACES, {16: state()}, unreachable_targets=()))
        result = evaluate_function(JoinMerge.FUNCTION, JoinMerge.TRACES, {16: state()})
        self.assertEqual(len(boundary(result, 24)['alternatives']), 1)


if __name__ == '__main__':
    unittest.main()
