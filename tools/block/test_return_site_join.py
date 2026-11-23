"""A return site that is also a join: the blocks after it continue from the join of all its edges
(functions/run_source_pass.return_site_seed), never from the call path's own seed."""
from dataclasses import replace
from pathlib import Path
import json
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent / 'functions'))
from forward_resource_design import evaluate_owned_function  # noqa: E402
from forward_resources import ownership_from_assertion_tree  # noqa: E402
from resource_seed import OwnedSeed  # noqa: E402
from run_source_pass import return_site_seed  # noqa: E402
from join_generalize import drop_root_resources  # noqa: E402
from symbolic_state import SymbolicState, bits, input_expr, operation  # noqa: E402

VOCABULARY = {'input_sha256': 'fixture', 'source_vocabulary': {'imports': []}}
CONTINUATION = {'name': 'K', 'coq': 'instr_pre exit_pc exit_resources',
                'source_binding': {'source': 'Level1.IslarisContractSpec'}, 'terminal_id': 'terminal'}
# 16 tests x13: zero skips to 24, nonzero falls into the call block 20, whose call (to 0x100) returns
# to 24. 24 is a join and the call's return site; it falls into 28.
FUNCTION = {'name': 'release', 'entry': 16, 'end': 32, 'rows': [{'pc': pc} for pc in range(16, 32, 4)],
            'blocks': [{'start': 16, 'end': 20, 'successors': [20, 24]},
                       {'start': 20, 'end': 24, 'successors': [24]},
                       {'start': 24, 'end': 28, 'successors': [28]},
                       {'start': 28, 'end': 32, 'successors': []}],
            'calls': [{'pc': 20, 'target': 0x100, 'kind': 'call'}]}
TRACES = {16: '(trace (declare-const v (_ BitVec 64)) (read-reg |x13| nil v) (cases "branch" '
              '(trace (assert (= v #x0000000000000000)) (write-reg |PC| nil #x0000000000000018)) '
              '(trace (assert (not (= v #x0000000000000000))) (write-reg |PC| nil #x0000000000000014))))',
          20: '(trace (write-reg |PC| nil #x0000000000000100))',
          24: '(trace (write-reg |PC| nil #x000000000000001c))',
          28: '(trace (write-reg |PC| nil #x0000000000000000))'}
# The guard only the path through the call holds.
CALL_GUARD = operation('not', operation('=', input_expr('old'), bits(0, 64)))
BLOCK = 'altFlBlock p n a'


def root_seed():
    tree = {'kind': 'exists', 'binders': [{'name': 'old', 'type': 'bv 64', 'expression': input_expr('old').to_dict()}],
            'components': [{'kind': 'register', 'id': 'r', 'register': 'x13', 'value_coq': 'old'},
                           {'kind': 'opaque', 'id': 'terminal', 'coq': 'True'}]}
    ownership = ownership_from_assertion_tree(tree, provenance={'source': 'fixture'})
    return OwnedSeed(SymbolicState(registers={'PC': bits(16, 64), 'x13': input_expr('old')}), ownership, [], [], [])


def boundary(report, pc):
    return next(row for row in report['boundaries'] if row['pc'] == hex(pc))


def guards(alternative):
    return [json.dumps(row, sort_keys=True) for row in alternative['state']['conditions']]


class ReturnSiteJoin(unittest.TestCase):
    def setUp(self):
        root = root_seed()
        report = evaluate_owned_function(FUNCTION, TRACES, {16: root}, vocabulary=VOCABULARY)
        edge, = [row for row in report['stops'] if row['reason'] == 'call_boundary']
        self.assertIn(json.dumps(CALL_GUARD.to_dict(), sort_keys=True), guards(edge))
        # The call-return seed of the site, in the shape call_boundary.call_return_seed gives: the
        # call edge's state at the return site, with the call path's guard.
        state = root.state.copy()
        state.registers['PC'] = bits(24, 64)
        state.conditions = [CALL_GUARD]
        self.root = root
        self.call_seed = replace(root, state=state, join_kind='call_return')
        self.seeds, self.roots, self.parents = {'0x10': root}, {'0x10': '0x10'}, {'0x18': '0x10'}

    def pass_with(self, site_seed):
        return evaluate_owned_function(FUNCTION, TRACES, {16: self.root, 24: site_seed}, vocabulary=VOCABULARY)

    def test_the_call_seed_alone_carries_the_call_guard_past_the_join(self):
        # What the pass did before: the block after the site assumes the call path's guard, which
        # the edge that skips the call (x13 = 0) cannot establish.
        after, = boundary(self.pass_with(self.call_seed), 28)['alternatives']
        self.assertIn(json.dumps(CALL_GUARD.to_dict(), sort_keys=True), guards(after))

    def test_the_successor_continues_from_the_join_of_both_edges(self):
        site = boundary(self.pass_with(self.call_seed), 24)
        self.assertEqual(sorted(str(row['predecessor_pc']) for row in site['alternatives']), ['0x10', 'None'])
        seed, root, plan = return_site_seed(site, self.call_seed, seeds=self.seeds, roots=self.roots,
                                            parents=self.parents, profile=None, vocabulary=VOCABULARY,
                                            continuation=CONTINUATION, live_registers=None, report=None,
                                            seed_drops={})
        self.assertEqual((root, plan['edges'], plan['edge_seeds'], seed.join_kind),
                         ('0x10', 2, ['0x10', '0x18'], 'call_return'))
        self.assertNotIn(json.dumps(CALL_GUARD.to_dict(), sort_keys=True),
                         [json.dumps(row.to_dict(), sort_keys=True) for row in seed.state.conditions])
        # The engine takes the joined seed as the site's call-return seed; the block after the site
        # no longer assumes the call path's guard.
        after, = boundary(self.pass_with(seed), 28)['alternatives']
        self.assertNotIn(json.dumps(CALL_GUARD.to_dict(), sort_keys=True), guards(after))

    def test_a_site_only_the_call_reaches_keeps_its_call_seed(self):
        site = boundary(self.pass_with(self.call_seed), 24)
        site = dict(site, alternatives=[row for row in site['alternatives'] if row['predecessor_pc'] is None])
        seed, root, plan = return_site_seed(site, self.call_seed, seeds=self.seeds, roots=self.roots,
                                            parents=self.parents, profile=None, vocabulary=VOCABULARY,
                                            continuation=CONTINUATION, live_registers=None, report=None,
                                            seed_drops={})
        self.assertEqual((seed, root, plan), (self.call_seed, '0x18', None))

    def test_an_incomplete_edge_makes_the_call_wait(self):
        site = dict(boundary(self.pass_with(self.call_seed), 24), reaching_stops=[{'reason': 'unsupported'}])
        with self.assertRaisesRegex(ValueError, 'return-site join waits'):
            return_site_seed(site, self.call_seed, seeds=self.seeds, roots=self.roots, parents=self.parents,
                             profile=None, vocabulary=VOCABULARY, continuation=CONTINUATION, live_registers=None,
                             report=None, seed_drops={})

    def test_a_resource_the_call_path_dropped_is_not_owned_after_the_return_site(self):
        # The root owns `altFlBlock p n a`; a drop row on the way to the call left it behind, so the
        # call-return seed is built without it (seed_drops of the site: run_source_pass.main).
        tree = {'kind': 'exists', 'binders': [{'name': 'old', 'type': 'bv 64',
                                              'expression': input_expr('old').to_dict()}],
                'components': [{'kind': 'register', 'id': 'r', 'register': 'x13', 'value_coq': 'old'},
                               {'kind': 'opaque', 'id': 'block', 'coq': BLOCK},
                               {'kind': 'opaque', 'id': 'terminal', 'coq': 'True'}]}
        root = replace(self.root, ownership=ownership_from_assertion_tree(tree, provenance={'source': 'fixture'}))
        call_seed = replace(drop_root_resources(root, [BLOCK])[0], state=self.call_seed.state, join_kind='call_return')
        site = boundary(evaluate_owned_function(FUNCTION, TRACES, {16: root, 24: call_seed}, vocabulary=VOCABULARY),
                        24)

        def joined(seed_drops):
            return return_site_seed(site, call_seed, seeds={'0x10': root}, roots=self.roots, parents=self.parents,
                                    profile=None, vocabulary=VOCABULARY, continuation=CONTINUATION,
                                    live_registers=None, report=None, seed_drops=seed_drops)

        def owned(seed):
            return [row['id'] for row in seed.ownership['components']]

        seed, _, plan = joined({'0x18': [BLOCK]})
        self.assertEqual((plan['drops'], 'block' in owned(seed)), ([BLOCK], False))
        # Nothing happens without a row: the edge lifted onto the root tree owns the block again.
        seed, _, plan = joined({})
        self.assertEqual(('drops' in plan, 'block' in owned(seed)), (False, True))


if __name__ == '__main__':
    unittest.main()
