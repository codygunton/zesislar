"""Check complete schema2 points without proof execution."""

import copy
import hashlib
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block import _point
from trace_block_filtered_events import EventFiles
from trace_block_filtered_points import FilteredPoints, stable_capture_lazy
from trace_block_stream import SnapshotMap, json_document
from trace_block_text import StreamText
import test_trace_block_chunks as fixtures


def capture(closed=False):
    hyps = [{'names': ['H'], 'type': 'True', 'body': 'I'}]
    evar = {'evar': 7, 'name': None, 'hyps': hyps, 'filter': [True],
            'defined': closed, 'body': 'I' if closed else None, 'type': 'True'}
    evar.update({'type_source': 'Retyping of defined body.'} if closed else {'candidates': None})
    mode = {'goals': [] if closed else [{'evar': 7, 'conclusion': 'True', 'hyps': hyps}],
            'shelf': [], 'given_up': [], 'evars': [evar], 'show_existentials': 'No existentials.' if closed else '?Goal : True',
            'hidden_stack': {'availability': 'unavailable', 'reason': 'Nested frames stay in tactic continuations.'}}
    return {'notation': mode, 'no_notation': copy.deepcopy(mode)}


class FilteredPointTests(unittest.TestCase):
    setUp = fixtures.ChunkTests.setUp
    write = fixtures.ChunkTests.write
    leaf = fixtures.ChunkTests.leaf
    index = fixtures.ChunkTests.index
    envelope = fixtures.ChunkTests.envelope

    def event_row(self, sequence, **row):
        for field in ('capture', 'message', 'refusal'):
            if field in row:
                self.event = 'event-%08d/%s' % (sequence, field)
                row[field] = self.envelope([json.dumps(row[field])])
        row.update(schema=2, sequence=sequence)
        path = self.root / ('events/process-17/event-%08d.json' % sequence)
        path.parent.mkdir(parents=True, exist_ok=True)
        raw = json.dumps(row).encode()
        path.write_bytes(raw)
        return {'path': str(path.relative_to(self.root)), 'sha256': hashlib.sha256(raw).hexdigest()}

    def rows(self, refused=False, changes=None):
        entry = dict(rule='Control', invocation=1)
        rows = [dict(entry, kind='native-entry', trial=False, capture=capture())]
        if not refused:
            rows.append(dict(entry, kind='hand-accepted', trial=True, clause='whole-rule', capture=capture(True)))
        rows.append(dict(entry, kind='hand-rollback', trial=False, clause='whole-rule', exact=True, capture=capture()))
        if refused:
            rows.append(dict(entry, kind='hand-refused', trial=False, clause='whole-rule', refusal='Exact refusal.'))
        rows.append(dict(entry, kind='branch-counter', client='Control', trial=False, outcome='native-local-success'))
        if changes:
            changes(rows)
        return [self.event_row(i + 1, **row) for i, row in enumerate(rows)]

    def points(self, references):
        events = EventFiles(self.root, references, {'pid': 17, 'start_ticks': 99})
        return FilteredPoints(events, {'Control': {'rule': 'Control', 'log_filter': ['Control'],
                          'commands': {'whole-rule': 'exact I'}}}, 'fixture-session', self.root / 'indexes')

    def test_accepted_point_snapshot_and_renderer_preserve_content(self):
        with self.points(self.rows()) as view:
            point = next(view.iter_points())
            snapshots = SnapshotMap(view, 'fixture-session')
            errors = []
            _point(point, 'point', errors, snapshots=snapshots, session_id='fixture-session')
            self.assertEqual(errors, [])
            self.assertEqual(point['hyps'][0]['body'], 'I')
            after = snapshots[point['hand_call'][0]['after_trial']]
            self.assertEqual(after['evars']['entries'][0]['body'], 'I')
            self.assertEqual(after['current_goals'], [])
            document = json.loads(''.join(json_document({'points': [point], 'snapshots': snapshots})))
            self.assertEqual(document['points'][0]['hyps'][0]['names'], ['H'])
            self.assertEqual(document['snapshots'][point['hand_call'][0]['after_trial']]['evars']['entries'][0]['status'], 'defined')

    def test_refusal_uses_rollback_without_invented_partial_state(self):
        with self.points(self.rows(refused=True)) as view:
            point = next(view.iter_points())
            self.assertEqual(point['hand_call'][0]['message'], 'Exact refusal.')
            self.assertEqual(point['refusal'][0]['hand_call_index'], 0)
            self.assertEqual(point['refusal'][0]['exposure'], 'not-exposed')
            self.assertEqual(point['completeness']['missing_observations'], [])
            errors = []
            _point(point, 'point', errors, snapshots=SnapshotMap(view, 'fixture-session'), session_id='fixture-session')
            self.assertEqual(errors, [])

    def test_native_invocation_duplicate_rejects(self):
        with self.assertRaisesRegex(ValueError, 'repeats its entry'):
            self.points(self.rows(changes=lambda rows: rows.append(rows[0])))

    def test_trial_client_and_duplicate_snapshots_reject(self):
        for change in (lambda rows: rows[1].update(rule='Other'), lambda rows: rows.insert(2, rows[1])):
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.points(self.rows(changes=change))

    def test_refusal_must_exist_and_match_trial(self):
        changes = (lambda rows: rows.pop(2), lambda rows: rows[2].update(rule='Other'),
                   lambda rows: rows.append(rows[2]))
        for change in changes:
            with self.subTest(change=change), self.assertRaises(ValueError):
                with self.points(self.rows(refused=True, changes=change)) as view:
                    list(view.iter_points())

    def test_unattributed_feedback_rejects(self):
        def change(rows):
            rows.append(dict(kind='feedback', trial=False, invocation=None, level='debug', message='Control'))
        with self.assertRaisesRegex(ValueError, 'exact invocation'):
            self.points(self.rows(changes=change))

    def test_cross_printer_identity_rejects(self):
        value = capture()
        value['no_notation']['goals'][0]['evar'] = 9
        with self.assertRaisesRegex(ValueError, 'goal identities'):
            stable_capture_lazy(value)

    def test_missing_declared_clause_rejects(self):
        with self.points(self.rows()) as view:
            view.descriptors['Control']['commands']['required-clause'] = 'idtac'
            with self.assertRaisesRegex(ValueError, 'exact declared trial set'):
                list(view.iter_points())

    def test_stream_search_crosses_fragments(self):
        value = StreamText(lambda: iter(['ab', 'c', 'def']))
        self.assertIn('bcd', value)
        self.assertIn('', value)
        self.assertNotIn('bd', value)
        with self.assertRaises(TypeError):
            1 in value


if __name__ == '__main__':
    unittest.main()
