"""Check the obligation store (tools/oblig/store.py): ids, the attempt rule, the fold, sync."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import store  # noqa: E402

F = 'fn'


def ev(identifier, state, **fields):
    kind = store.parse_id(identifier)[0]
    return store.event(id=identifier, function=F, kind=kind, state=state, **fields)


def attempt(identifier, state, tier, number, prompt='p', **fields):
    return ev(identifier, state, tier=tier, attempt=number,
              prompt_sha256=hashlib.sha256(prompt.encode()).hexdigest(), **fields)


class Ids(unittest.TestCase):
    def test_forms(self):
        self.assertEqual(store.parse_id('fn/block/00c4')[0], 'block')
        self.assertEqual(store.goal_id(F, '00c4', 'True')[:13], 'fn/goal/00c4-')
        self.assertEqual(store.parse_id(store.goal_id(F, '00c4', 'True'))[0], 'goal')
        self.assertEqual(store.parse_id('fn/decision/loop_assertion-00c4')[1]['decision'], 'loop_assertion')
        self.assertEqual(store.parse_id("fn/meaning/keys_ok'")[0], 'meaning')
        for bad in ('fn/block/xyz', 'fn/goal/00c4-abc', 'fn/decision/guess-00c4', 'fn/other/1'):
            self.assertIsNone(store.parse_id(bad), bad)

    def test_event_refusals(self):
        with tempfile.TemporaryDirectory() as run:
            bad = [ev('fn/block/0000', 'sleeping'), ev('fn/block/0000', 'failed'),
                   ev('fn/block/0000', 'blocked-on', **{'class': 'nothing'}),
                   dict(ev('fn/block/0000', 'derived'), kind='goal'),
                   dict(ev('fn/block/0000', 'derived'), function='other'),
                   ev('fn/block/0000', 'running', attempt=1)]
            for row in bad:
                with self.assertRaises(store.Rejected):
                    store.append(run, row)
            with self.assertRaises(store.Rejected):
                store.event(id='fn/block/0000', colour='red')
            self.assertEqual(store.read_events(run), [])


class Attempts(unittest.TestCase):
    def test_repeated_prompt_and_tier_rejected(self):
        goal = store.goal_id(F, '0010', 'x = x')
        with tempfile.TemporaryDirectory() as run:
            store.append(run, ev(goal, 'derived'))
            store.append(run, attempt(goal, 'running', 'haiku-low', 1))
            store.append(run, attempt(goal, 'failed', 'haiku-low', 1, **{'class': 'give_up'}))
            with self.assertRaises(store.Rejected):
                store.append(run, attempt(goal, 'running', 'haiku-low', 2))
            with self.assertRaises(store.Rejected):
                store.append(run, attempt(goal, 'running', 'haiku-low', 1))
            store.append(run, attempt(goal, 'running', 'haiku-medium', 1))
            store.append(run, attempt(goal, 'closed', 'haiku-medium', 1))
            store.append(run, attempt(store.goal_id(F, '0010', 'y = y'), 'running', 'haiku-low', 1))
            state = store.fold(store.read_events(run))
            self.assertEqual(state[goal]['state'], 'closed')
            self.assertEqual(state[goal]['closed_by'], 'haiku-medium')
            self.assertEqual(state[goal]['tier_attempts'], {'haiku-low': 1, 'haiku-medium': 1})

    def test_one_append_with_running_and_result(self):
        goal = store.goal_id(F, '0010', 'x = x')
        with tempfile.TemporaryDirectory() as run:
            store.append(run, [attempt(goal, 'running', 'mechanical', 1),
                               attempt(goal, 'failed', 'mechanical', 1, **{'class': 'give_up'})])
            self.assertEqual(len(store.read_events(run)), 2)

    def test_events_of_an_open_attempt_of_a_best_of_n_round(self):
        goal = store.goal_id(F, '0010', 'x = x')
        with tempfile.TemporaryDirectory() as run:
            store.append(run, [attempt(goal, 'running', 'haiku-low', n, prompt='s%d' % n) for n in (1, 2, 3)])
            # The siblings' results, then the submitted sample announced again: all one open attempt each.
            store.append(run, [attempt(goal, 'failed', 'haiku-low', 1, prompt='s1', **{'class': 'compile_error'}),
                               attempt(goal, 'failed', 'haiku-low', 3, prompt='s3', **{'class': 'superseded'}),
                               attempt(goal, 'running', 'haiku-low', 2, prompt='s2')])
            state = store.fold(store.read_events(run))
            self.assertEqual((state[goal]['state'], state[goal]['last_attempt']['attempt']), ('running', 2))
            self.assertEqual(state[goal]['tier_attempts'], {'haiku-low': 3})
            store.append(run, attempt(goal, 'closed', 'haiku-low', 2, prompt='s2'))
            # A settled attempt takes no further event, and its prompt is never sent again.
            for row in (attempt(goal, 'failed', 'haiku-low', 1, prompt='s1', **{'class': 'give_up'}),
                        attempt(goal, 'running', 'haiku-low', 4, prompt='s3')):
                with self.assertRaises(store.Rejected):
                    store.append(run, row)


class Fold(unittest.TestCase):
    def test_states_resets_and_classes(self):
        block, goal = 'fn/block/0040', store.goal_id(F, '0040', 'a < b')
        with tempfile.TemporaryDirectory() as run:
            store.append(run, [ev(block, 'derived'), ev(block, 'failed', **{'class': 'not_closed'}),
                               ev(block, 'blocked-on', **{'class': goal}),
                               ev(goal, 'derived', parent=block, **{'class': 'PURE-linear'}),
                               ev(goal, 'failed', **{'class': 'compile_error'}),
                               ev(block, 'derived'), ev(block, 'derived')])
            state = store.fold(store.read_events(run))
            self.assertEqual(state[block]['state'], 'derived')
            self.assertEqual(state[block]['resets'], 1)
            self.assertEqual(state[block]['blocked_by'], goal)
            self.assertEqual(state[goal]['goal_class'], 'PURE-linear')
            self.assertEqual(state[goal]['failure'], 'compile_error')
            self.assertEqual(state[goal]['parent'], block)
            self.assertEqual(store.count_lines(state), ['block derived 1', 'goal failed 1', 'total 2 open 2'])


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data) if not isinstance(data, str) else data)


class Sync(unittest.TestCase):
    def test_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            run = Path(tmp)
            rows = [{'case': c, 'status': 'rendered', 'caller': {'path': 'x', 'sha256': c * 16}}
                    for c in ('0000', '0040', '0048', '0054')]
            rows += [{'case': '0060', 'status': 'refused', 'reason': 'r'}, {'case': '0068', 'status': 'inlined'}]
            write(run / 'callers' / 'CALLERS.json', {'function': F, 'rows': rows})
            write(run / 'runs' / '0000' / 'CLOSURE.json', {'verdict': 'CLOSED', 'caller_sha256': '0000' * 16})
            write(run / 'runs' / '0040' / 'CLOSURE.json', {'verdict': 'CLOSED', 'caller_sha256': 'stale'})
            write(run / 'b' / '0048' / 'NOT-CLOSED.json', {'verdict': 'NOT-CLOSED', 'caller_sha256': '0048' * 16})
            write(run / 'results.jsonl', json.dumps({'function': F, 'case': '0048', 'verdict': 'NOT-CLOSED',
                                                     'dir': str(run / 'b' / '0048')}) + '\n')
            res = run / 'residual' / '0048'
            write(res / 'MANIFEST.json', {'block': '0048', 'goals': [{'id': '0048-1', 'statement': 'P'},
                                                                     {'id': '0048-2', 'statement': 'Q'}]})
            write(res / 'goals' / '0048-1' / 'STATUS.json', {'result': 'PASS', 'attempts': [{}]})
            write(res / 'goals' / '0048-1' / 'proof.v', 'Lemma l : True.\nProof. exact I. Qed.\n')
            write(res / 'goals' / '0048-2' / 'STATUS.json', {'result': 'FAIL', 'attempts': [{}]})
            self.assertEqual(store.sync(F, run), 7)
            self.assertEqual(store.sync(F, run), 0)
            state = store.fold(store.read_events(run))
            got = {k: (v['state'], v['failure']) for k, v in state.items()}
            self.assertEqual(got['fn/block/0000'], ('closed', None))
            self.assertEqual(got['fn/block/0040'], ('derived', None))
            self.assertEqual(got['fn/block/0048'], ('failed', 'not_closed'))
            self.assertEqual(got['fn/block/0054'], ('derived', None))
            self.assertEqual(got['fn/block/0060'], ('failed', 'REFUSED'))
            self.assertNotIn('fn/block/0068', got)
            self.assertEqual(got[store.goal_id(F, '0048', 'P')], ('closed', None))
            self.assertEqual(got[store.goal_id(F, '0048', 'Q')], ('failed', 'compile_error'))
            self.assertEqual(state[store.goal_id(F, '0048', 'P')]['parent'], 'fn/block/0048')
            # The caller changes: the old certificate no longer counts and the block resets.
            write(run / 'callers' / 'CALLERS.json', {'function': F, 'rows': [
                {'case': '0000', 'status': 'rendered', 'caller': {'path': 'x', 'sha256': 'new'}}]})
            self.assertEqual(store.sync(F, run), 1)
            state = store.fold(store.read_events(run))
            self.assertEqual((state['fn/block/0000']['state'], state['fn/block/0000']['resets']), ('derived', 1))

    def test_requests_become_decisions(self):
        with tempfile.TemporaryDirectory() as tmp:
            run = Path(tmp)
            requests = [{'id': 'fn/decision/contract-0000', 'kind': 'contract', 'pc': '+0x0', 'proposal': None},
                        {'id': 'fn/decision/call_row-0094', 'kind': 'call_row', 'pc': '+0x94', 'proposal': None},
                        {'kind': 'access_placement', 'pc': '+0x1f0', 'derivable': True,
                         'proposal': {'array': 'keys', 'index': 'i', 'scale': 32, 'offset': 0}}]
            write(run / 'round-1' / 'derived' / 'REQUESTS.json',
                  {'schema': 'oblig-requests/1', 'round': 1, 'answered': [], 'requests': requests})
            # A decision filed by hand earlier with the same id is not filed again.
            store.append(run, ev('fn/decision/contract-0000', 'derived'))
            self.assertEqual(store.sync(F, run), 2)
            self.assertEqual(store.sync(F, run), 0)
            state = store.fold(store.read_events(run))
            self.assertEqual({k: v['state'] for k, v in state.items()},
                             {'fn/decision/contract-0000': 'derived', 'fn/decision/call_row-0094': 'derived',
                              'fn/decision/access_placement-01f0': 'derived'})
            self.assertIsNone(state['fn/decision/call_row-0094']['artifact'])
            artifact = state['fn/decision/access_placement-01f0']['artifact']
            self.assertEqual(artifact['path'], str(run / 'round-1' / 'derived' / 'REQUESTS.json'))
            # A later round with a new proposal re-derives; an answered request is left out.
            requests[1]['proposal'] = {'spec': 'freeCallSpec'}
            write(run / 'round-2' / 'derived' / 'REQUESTS.json',
                  {'schema': 'oblig-requests/1', 'round': 2, 'answered': ['fn/decision/access_placement-01f0'],
                   'requests': requests[:2] + [{'id': 'fn/decision/predicate-0200', 'kind': 'predicate',
                                                'pc': '+0x200', 'proposal': None}]})
            self.assertEqual(store.sync(F, run), 2)
            self.assertEqual(store.sync(F, run), 0)
            state = store.fold(store.read_events(run))
            self.assertIsNotNone(state['fn/decision/call_row-0094']['artifact'])
            self.assertIn('fn/decision/predicate-0200', state)
            # A proposal an agent files later is not replaced by the derived one.
            store.append(run, ev('fn/decision/call_row-0094', 'derived', artifact={'path': 'p', 'sha256': '1' * 64}))
            self.assertEqual(store.sync(F, run), 0)
            write(run / 'round-3' / 'derived' / 'REQUESTS.json',
                  {'requests': [{'id': 'fn/decision/loop_assertion-0010', 'kind': 'contract'}]})
            with self.assertRaises(store.Rejected):
                store.sync(F, run)

    def test_decode_parent_header_old_ground(self):
        """The committed decodeParentHeader callers and certificates: 98 blocks closed, nothing open."""
        with tempfile.TemporaryDirectory() as run:
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(store.main(['sync', '--function', 'decodeParentHeader', '--run', run]), 0)
            self.assertIn('blocks closed 98 of 98; open obligations 0', out.getvalue())


if __name__ == '__main__':
    unittest.main()
