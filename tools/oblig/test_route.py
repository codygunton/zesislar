"""Check the router (tools/oblig/route.py): every row of the plan's A7 table and the spin rule."""
import contextlib
import hashlib
import io
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import route  # noqa: E402
import store  # noqa: E402

F = 'fn'
GOAL = store.goal_id(F, '0040', 'a < b')
BLOCK = 'fn/block/0040'


def ev(identifier, state, **fields):
    return store.event(id=identifier, function=F, kind=store.parse_id(identifier)[0], state=state, **fields)


def tried(identifier, tier, number, failure=None, prompt=None, closed=False):
    prompt = hashlib.sha256((prompt or '%s-%d' % (tier, number)).encode()).hexdigest()
    state = 'closed' if closed else 'failed'
    return [ev(identifier, 'running', tier=tier, attempt=number, prompt_sha256=prompt),
            ev(identifier, state, tier=tier, attempt=number, prompt_sha256=prompt,
               **({'class': failure or 'give_up'} if not closed else {}))]


def falsified(identifier=GOAL):
    return ev(identifier, 'derived', tier='falsify', **{'class': 'PURE-linear'})


class Router(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.run = Path(self.tmp.name)
        self.routing = {}

    def tearDown(self):
        self.tmp.cleanup()

    def add(self, *rows):
        flat = []
        for row in rows:
            flat.extend(row if isinstance(row, list) else [row])
        store.append(self.run, flat)

    def next(self, identifier=None):
        items = route.next_items(self.run, F, tiers=list(route.DEFAULT_TIERS), routing=self.routing)
        if identifier is None:
            return items
        found = [(action, tier) for i, action, tier, _ in items if i == identifier]
        return found[0] if found else None

    def pure_goal(self):
        self.add(ev(GOAL, 'derived', parent=BLOCK, **{'class': 'PURE-linear'}))

    # Blocks
    def test_block_derived_reruns(self):
        self.add(ev(BLOCK, 'derived'))
        self.assertEqual(self.next(BLOCK), ('rerun', None))

    def test_block_input_changed_reruns(self):
        self.add(ev(BLOCK, 'closed'), ev(BLOCK, 'derived'))
        self.assertEqual(self.next(BLOCK), ('rerun', None))

    def test_block_closed_or_running_has_no_step(self):
        self.add(ev(BLOCK, 'closed'), ev('fn/block/0048', 'running'))
        self.assertEqual(self.next(), [])

    def test_failed_block_packages_then_waits_then_reruns(self):
        self.add(ev(BLOCK, 'failed', **{'class': 'not_closed'}))
        self.assertEqual(self.next(BLOCK), ('package', None))
        self.pure_goal()
        self.assertIsNone(self.next(BLOCK))
        self.add(ev(GOAL, 'closed', tier='haiku-low'))
        self.assertEqual(self.next(BLOCK), ('rerun', None))

    def test_refused_block_goes_to_derive(self):
        self.add(ev(BLOCK, 'failed', **{'class': 'REFUSED'}))
        self.assertEqual(self.next(BLOCK), ('derive', None))

    # Decisions
    def test_proposed_assertion_is_tested_then_checked(self):
        decision = 'fn/decision/loop_assertion-00c4'
        self.add(ev(decision, 'derived', artifact={'path': 'p.json', 'sha256': '0' * 64}))
        self.assertEqual(self.next(decision), ('test', None))
        self.add(ev(decision, 'derived', tier='machine-run', **{'class': 'tested'}))
        self.assertEqual(self.next(decision), ('check', None))

    def test_proposal_rejected_by_machine_run_returns_to_decision(self):
        decision = 'fn/decision/contract-0000'
        self.add(ev(decision, 'derived', artifact={'path': 'p.json', 'sha256': '0' * 64}),
                 ev(decision, 'failed', tier='machine-run', **{'class': 'rejected_by_run'}))
        self.assertEqual(self.next(decision), ('decide', 'opus-medium'))

    def test_decision_with_derived_proposal_is_checked(self):
        decision = 'fn/decision/access_placement-01f0'
        self.add(ev(decision, 'derived', artifact={'path': 'p.json', 'sha256': '0' * 64}))
        self.assertEqual(self.next(decision), ('check', None))

    def test_decision_without_proposal_goes_to_opus(self):
        decision = 'fn/decision/callee_premise-033c'
        self.add(ev(decision, 'derived'))
        self.assertEqual(self.next(decision), ('decide', 'opus-medium'))

    # Pure goals
    def test_pure_goal_falsity_check_first(self):
        self.pure_goal()
        self.assertEqual(self.next(GOAL), ('falsify', None))

    def test_false_goal_and_rule_gap_go_to_owner(self):
        self.pure_goal()
        self.add(falsified(), ev(GOAL, 'false', tier='falsify', artifact={'path': 'cex', 'sha256': '0' * 64}))
        self.assertEqual(self.next(GOAL), ('owner', None))
        other = store.goal_id(F, '0040', 'c < d')
        self.add(ev(other, 'failed', **{'class': 'rule_gap'}))
        self.assertEqual(self.next(other), ('owner', None))

    def test_goal_naming_a_code_address_goes_to_owner(self):
        statement = self.run / 'goal.v'
        statement.write_text('Lemma g : pc = 0x%x.\n' % ((8 << 28) + 0xd6960))
        self.add(ev(GOAL, 'derived', artifact={'path': str(statement), 'sha256': '0' * 64}))
        self.assertEqual(self.next(GOAL), ('owner', None))
        other = store.goal_id(F, '0040', 'q')
        self.add(ev(other, 'derived', **{'class': 'ADDRESS'}))
        self.assertEqual(self.next(other), ('owner', None))

    def test_ladder_mechanical_then_first_model_tier(self):
        self.pure_goal()
        self.add(falsified())
        self.assertEqual(self.next(GOAL), ('prove', 'mechanical'))
        self.add(tried(GOAL, 'mechanical', 1))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-low'))

    def test_routing_table_moves_the_first_tier(self):
        self.routing = {'PURE-linear': {'first_tier': 'haiku-high'}}
        self.pure_goal()
        self.add(falsified(), tried(GOAL, 'mechanical', 1))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-high'))

    def test_compiler_error_retries_same_tier_once_then_escalates(self):
        self.pure_goal()
        self.add(falsified(), tried(GOAL, 'mechanical', 1), tried(GOAL, 'haiku-low', 1, 'compile_error'))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-low'))
        self.add(tried(GOAL, 'haiku-low', 2, 'compile_error'))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-medium'))

    def test_give_up_escalates(self):
        self.pure_goal()
        self.add(falsified(), tried(GOAL, 'mechanical', 1), tried(GOAL, 'haiku-low', 1, 'give_up'))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-medium'))

    def test_need_context_retries_same_tier(self):
        self.pure_goal()
        self.add(falsified(), tried(GOAL, 'mechanical', 1), tried(GOAL, 'haiku-low', 1, 'need_context'))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-low'))

    def test_top_tier_failed_reconsiders_parent(self):
        self.routing = {'PURE-linear': {'first_tier': 'opus-medium'}}
        self.pure_goal()
        self.add(falsified(), tried(GOAL, 'mechanical', 1), tried(GOAL, 'opus-medium', 1),
                 tried(GOAL, 'opus-medium', 2))
        self.assertEqual(self.next(GOAL), ('reconsider', 'opus-medium'))
        other = store.goal_id(F, '0040', 'w')
        self.add(ev(other, 'waiting-decision'))
        self.assertEqual(self.next(other), ('reconsider', 'opus-medium'))

    def test_spatial_leftover_gets_a_diagnosis(self):
        self.add(ev(GOAL, 'derived', parent=BLOCK, **{'class': 'LOOKUP'}))
        self.assertEqual(self.next(GOAL), ('diagnose', 'opus-medium'))

    # Ladder and spin
    LADDER = {'PURE-linear': {'attempts': {'mechanical': 1, 'haiku-low': 2, 'haiku-medium': 0, 'haiku-high': 1,
                                           'opus-medium': 2}}}

    def test_never_spins_before_the_top_tier(self):
        self.pure_goal()
        rows = [falsified()]
        for tier in ('mechanical', 'haiku-low', 'haiku-medium'):
            rows += tried(GOAL, tier, 1, 'compile_error') + tried(GOAL, tier, 2, 'compile_error')
        self.add(*rows)
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-high'))

    def test_ladder_skips_tiers_with_no_attempts(self):
        self.routing = self.LADDER
        self.pure_goal()
        self.add(falsified(), tried(GOAL, 'mechanical', 1), tried(GOAL, 'haiku-low', 1), tried(GOAL, 'haiku-low', 2))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-high'))
        self.add(tried(GOAL, 'haiku-high', 1, 'compile_error'))
        self.assertEqual(self.next(GOAL), ('prove', 'opus-medium'))

    def test_default_row_applies_to_a_goal_without_a_class_row(self):
        self.routing = {route.DEFAULT_CLASS: self.LADDER['PURE-linear']}
        self.pure_goal()
        self.add(falsified(), tried(GOAL, 'mechanical', 1), tried(GOAL, 'haiku-low', 1), tried(GOAL, 'haiku-low', 2))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-high'))

    def test_attempts_off_the_ladder_do_not_count(self):
        self.routing = self.LADDER
        self.pure_goal()
        self.add(falsified(), tried(GOAL, 'mechanical', 1), tried(GOAL, 'haiku-low', 1), tried(GOAL, 'haiku-low', 2),
                 tried(GOAL, 'haiku-medium', 1), tried(GOAL, 'haiku-medium', 2),
                 tried(GOAL, 'haiku-high', 1, 'need_context'))
        self.assertEqual(self.next(GOAL), ('prove', 'opus-medium'))

    def test_six_attempts_spin_once_the_ladder_is_exhausted(self):
        self.routing = self.LADDER
        self.pure_goal()
        rows = [falsified(), tried(GOAL, 'mechanical', 1), tried(GOAL, 'haiku-low', 1), tried(GOAL, 'haiku-low', 2),
                tried(GOAL, 'haiku-high', 1), tried(GOAL, 'opus-medium', 1, 'compile_error')]
        self.add(*rows)
        self.assertEqual(self.next(GOAL), ('prove', 'opus-medium'))
        self.add(tried(GOAL, 'opus-medium', 2))
        self.assertEqual(self.next(GOAL), ('spin', None))

    def test_exhausted_ladder_below_six_reconsiders(self):
        self.routing = {'PURE-linear': {'attempts': {'mechanical': 1, 'haiku-low': 1, 'haiku-medium': 0,
                                                     'haiku-high': 0, 'opus-medium': 1}}}
        self.pure_goal()
        self.add(falsified(), tried(GOAL, 'mechanical', 1), tried(GOAL, 'haiku-low', 1), tried(GOAL, 'opus-medium', 1))
        self.assertEqual(self.next(GOAL), ('reconsider', 'opus-medium'))

    def test_missing_context_escalates_without_the_second_attempt(self):
        self.pure_goal()
        self.add(falsified(), tried(GOAL, 'mechanical', 1), tried(GOAL, 'haiku-low', 1, 'need_context'),
                 ev(GOAL, 'failed', tier='haiku-low', **{'class': 'missing_context'}))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-medium'))

    def test_too_large_tier_is_skipped_until_a_reset(self):
        self.routing = self.LADDER
        self.pure_goal()
        self.add(falsified(), tried(GOAL, 'mechanical', 1), ev(GOAL, 'failed', tier='haiku-low', **{'class': 'too_large'}))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-high'))
        self.add(ev(GOAL, 'derived', **{'class': 'PURE-linear'}), falsified())
        self.assertEqual(self.next(GOAL), ('prove', 'mechanical'))

    def test_reset_runs_the_ladder_again(self):
        self.routing = self.LADDER
        self.pure_goal()
        self.add(falsified(), tried(GOAL, 'mechanical', 1), tried(GOAL, 'haiku-low', 1), tried(GOAL, 'haiku-low', 2),
                 tried(GOAL, 'haiku-high', 1), tried(GOAL, 'opus-medium', 1), tried(GOAL, 'opus-medium', 2))
        self.assertEqual(self.next(GOAL), ('spin', None))
        # A reset with a hinted task: the ladder runs again; the unchanged mechanical prompt is marked.
        self.add(ev(GOAL, 'derived', **{'class': 'PURE-linear'}), falsified(),
                 ev(GOAL, 'failed', tier='mechanical', **{'class': 'repeated_prompt'}))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-low'))
        self.add(tried(GOAL, 'haiku-low', 3, prompt='hinted'))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-high'))

    def test_waiting_decision_after_every_tier_too_large_is_reconsidered(self):
        self.pure_goal()
        self.add(falsified(), ev(GOAL, 'waiting-decision', **{'class': 'PURE-linear'}))
        self.assertEqual(self.next(GOAL), ('reconsider', 'opus-medium'))

    def test_malformed_reply_retries_once_without_counting(self):
        self.routing = self.LADDER
        self.pure_goal()
        self.add(falsified(), tried(GOAL, 'mechanical', 1), tried(GOAL, 'haiku-low', 1, 'malformed'))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-low'))
        self.add(tried(GOAL, 'haiku-low', 2, 'compile_error'))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-low'))  # the malformed reply did not count
        self.add(tried(GOAL, 'haiku-low', 3, 'malformed'))
        self.assertEqual(self.next(GOAL), ('prove', 'haiku-high'))  # a second one does

    def test_three_resets_spin(self):
        decision = 'fn/decision/join_assertion-0100'
        for _ in range(3):
            self.add(ev(decision, 'failed', **{'class': 'rejected_by_run'}), ev(decision, 'derived'))
        self.assertEqual(self.next(decision), ('spin', None))

    def test_order_no_model_first_then_cheapest_tier(self):
        cheap, dear = store.goal_id(F, '0040', 'cheap'), store.goal_id(F, '0040', 'dear')
        self.add(ev('fn/decision/contract-0000', 'derived'),
                 ev(dear, 'derived'), falsified(dear), tried(dear, 'mechanical', 1), tried(dear, 'haiku-low', 1),
                 ev(cheap, 'derived'), falsified(cheap), ev(BLOCK, 'derived'))
        self.assertEqual([(i, a) for i, a, _, _ in self.next()],
                         [(BLOCK, 'rerun'), (cheap, 'prove'), (dear, 'prove'), ('fn/decision/contract-0000', 'decide')])

    def test_cli_prints_lines_and_records_coordinator_bytes(self):
        self.add(ev(BLOCK, 'derived'))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            route.main(['next', '--function', F, '--run', str(self.run), '--limit', '5'])
        self.assertEqual(out.getvalue(), 'fn/block/0040 rerun new or input changed\n')
        self.assertTrue((self.run / store.COORDINATOR).is_file())


if __name__ == '__main__':
    unittest.main()
