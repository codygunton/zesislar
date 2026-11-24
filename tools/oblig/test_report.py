"""Check the obligation report (tools/oblig/report.py): every measure printed, n/a without input."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import report  # noqa: E402
import store  # noqa: E402

F = 'fn'
NAMES = ['blocks closed with no model', 'rounds', 'requests per round', 'decisions made / floor',
         'requests derivable', 'unhandled refusals', 'proposals rejected by machine runs',
         'missing-context failures per attempt', 'supplied context absent from accepted proof',
         'premises dropped by the minimiser', 'premises omitted for size', 'goals found false after a model attempt',
         'prompt bytes per attempt', 'answer bytes per attempt', 'tokens per attempt',
         'coordinator bytes read per round', 'pure goals closed by Haiku tiers',
         'goals that reached opus-medium as prover', 'escalations', 'spin', 'tokens per block',
         'checked-lemma lines per block']


def ev(identifier, state, **fields):
    return store.event(id=identifier, function=F, kind=store.parse_id(identifier)[0], state=state, **fields)


def attempt(identifier, state, tier, number, **fields):
    prompt = hashlib.sha256(('%s %s %d' % (identifier, tier, number)).encode()).hexdigest()
    return ev(identifier, state, tier=tier, attempt=number, prompt_sha256=prompt, **fields)


class Report(unittest.TestCase):
    def test_empty_run_prints_n_a(self):
        with tempfile.TemporaryDirectory() as run:
            got = dict(report.measures(run, F))
            for name in NAMES:
                self.assertEqual(got[name], 'n/a', name)

    def test_measures(self):
        with tempfile.TemporaryDirectory() as tmp:
            run = Path(tmp)
            (run / 'round-1' / 'derived').mkdir(parents=True)
            (run / 'round-1' / 'derived' / 'REQUESTS.json').write_text(json.dumps({
                'schema': 'oblig-requests/1', 'function': F, 'round': 1,
                'answered': ['fn/decision/callee_premise-033c'],
                'requests': [{'kind': 'contract', 'derivable': False}, {'kind': 'loop_assertion', 'derivable': False},
                             {'kind': 'call_row', 'derivable': True}, {'kind': 'call_row', 'derivable': False}],
                'refusals_without_request': [{'source': 'render/RESULT.json', 'reason': 'r'}]}))
            proof = run / 'proof.v'
            proof.write_text('Lemma a : True.\nProof.\nexact I.\nQed.\n')
            g1, g2 = store.goal_id(F, '0040', 'a'), store.goal_id(F, '0040', 'b')
            store.append(run, [
                ev('fn/block/0000', 'closed', tier='evidence'),
                ev('fn/block/0040', 'failed', **{'class': 'not_closed'}),
                ev(g1, 'derived', parent='fn/block/0040'),
                attempt(g1, 'failed', 'haiku-low', 1, prompt_bytes=100, tokens_in=10, tokens_out=5,
                        **{'class': 'need_context'}),
                attempt(g1, 'closed', 'haiku-medium', 1, prompt_bytes=300, tokens_in=30, tokens_out=5,
                        context_items=4, context_used=1, artifact={'path': str(proof), 'sha256': '0' * 64}),
                ev(g2, 'derived', parent='fn/block/0040'),
                attempt(g2, 'failed', 'haiku-low', 1, **{'class': 'give_up'}),
                ev(g2, 'false', tier='falsify'),
                ev('fn/decision/contract-0000', 'closed'),
                ev('fn/decision/loop_assertion-00c4', 'failed', tier='machine-run', **{'class': 'rejected_by_run'}),
            ])
            store.record_coordinator_read(run, 'route.next', 'x' * 40)
            got = dict(report.measures(run, F))
            for name in NAMES:
                self.assertIn(name, got)
            self.assertEqual(got['blocks closed with no model'], '1 of 1 closed (2 blocks)')
            self.assertEqual(got['rounds'], '1')
            self.assertEqual(got['requests per round'], '1:4')
            self.assertEqual(got['decisions made / floor'], '1 / 3 (0.3 x floor)')
            self.assertEqual(got['requests derivable'], '25.0%')
            self.assertEqual(got['unhandled refusals'], '1:1')
            self.assertEqual(got['proposals rejected by machine runs'], '1 of 1 tested')
            self.assertEqual(got['missing-context failures per attempt'], '1 / 3 (33.3%)')
            self.assertEqual(got['supplied context absent from accepted proof'], '75.0%')
            self.assertEqual(got['goals found false after a model attempt'], '1')
            self.assertEqual(got['prompt bytes per attempt'], '200.0')
            self.assertEqual(got['tokens per attempt'], '25.0')
            self.assertEqual(got['coordinator bytes read per round'], '1:40')
            self.assertEqual(got['pure goals closed by Haiku tiers'], '100.0%')
            self.assertEqual(got['escalations'], '1')
            self.assertEqual(got['spin'], '0')
            self.assertEqual(got['tokens per block'], '25.0')
            self.assertEqual(got['checked-lemma lines per block'], '2.0')
            self.assertEqual(got['tier haiku-medium'], 'reached 1, closed at first attempt 100.0%, '
                                                       'within its attempts 100.0%, tokens per closed 35.0')
            self.assertEqual(got['tier mechanical'], 'n/a')

    def test_superseded_obligations_are_counted_and_left_out(self):
        with tempfile.TemporaryDirectory() as run:
            goal = store.goal_id(F, '0040', 'a')
            store.append(run, [ev(goal, 'derived'),
                               attempt(goal, 'failed', 'haiku-low', 1, prompt_bytes=100, tokens_in=10, tokens_out=5,
                                       **{'class': 'give_up'}),
                               ev(goal, 'superseded', **{'class': 'artifact-gone'})])
            got = dict(report.measures(run, F))
            self.assertEqual(got['superseded obligations (left out of every measure below)'], '1')
            self.assertEqual(got['tokens per attempt'], 'n/a')
            self.assertEqual(got['tier haiku-low'], 'n/a')

    def test_premises_omitted_for_size_are_counted_once_per_goal(self):
        with tempfile.TemporaryDirectory() as tmp:
            run = Path(tmp)
            resid = run / 'resid' / '0164'
            for gid in ('0164-1', '0164-2', '0164-3'):
                (resid / 'goals' / gid).mkdir(parents=True)
            dropped = [dict(name='H7', nodes=3021, head='and'), dict(name='H9', nodes=2600, head='and')]
            (resid / 'MANIFEST.json').write_text(json.dumps(dict(block='0164', goals=[
                dict(id='0164-1', statement='G', dropped_facts=dropped),
                dict(id='0164-2', statement='P', part_of='0164-1', dropped_facts=dropped),
                dict(id='0164-3', statement='Q')])))
            self.assertEqual(dict(report.measures(run, F))['premises omitted for size'], '2 facts in 1 goals')


if __name__ == '__main__':
    unittest.main()
