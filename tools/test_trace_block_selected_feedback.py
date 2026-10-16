"""Reject unsupported or incomplete selected-feedback evidence."""
from pathlib import Path
import copy
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_selected_feedback import selected_feedback, apply_selected_feedback, bind_selected_feedback
from trace_block_text import StreamText


class SelectedFeedbackTests(unittest.TestCase):
    def valid(self):
        return {'selected_feedback': {'emitted': 2, 'omitted': 0,
                'complete': True, 'first_error': None}}

    def test_complete(self):
        self.assertEqual(selected_feedback(self.valid())['availability'], 'complete')

    def test_missing_status(self):
        self.assertEqual(selected_feedback(None)['availability'], 'unavailable')

    def test_missing_field(self):
        self.assertEqual(selected_feedback({})['availability'], 'unavailable')

    def test_omission(self):
        status = self.valid()
        status['selected_feedback'].update(omitted=1, complete=False, first_error='write denied')
        checked = selected_feedback(status)
        self.assertEqual(checked['availability'], 'partial')
        self.assertEqual(checked['status']['first_error'], 'write denied')

    def test_wrong_status(self):
        with self.assertRaises(ValueError):
            selected_feedback([])

    def test_bad_fields(self):
        for key in ('emitted', 'omitted', 'complete', 'first_error'):
            with self.subTest(missing=key):
                status = self.valid()
                del status['selected_feedback'][key]
                with self.assertRaises(ValueError):
                    selected_feedback(status)
        status = self.valid()
        status['selected_feedback']['extra'] = 0
        with self.assertRaises(ValueError):
            selected_feedback(status)

    def test_bad_counts(self):
        for key in ('emitted', 'omitted'):
            for value in (-1, True, 1.0, '0'):
                with self.subTest(key=key, value=value):
                    status = self.valid()
                    status['selected_feedback'][key] = value
                    with self.assertRaises(ValueError):
                        selected_feedback(status)

    def test_contradictory_completeness(self):
        for omitted, complete in ((0, False), (1, True), (0, 1)):
            status = self.valid()
            status['selected_feedback'].update(omitted=omitted, complete=complete)
            with self.assertRaises(ValueError):
                selected_feedback(status)

    def test_contradictory_error(self):
        status = self.valid()
        status['selected_feedback']['first_error'] = 'unexpected'
        with self.assertRaises(ValueError):
            selected_feedback(status)
        for error in (None, '', 1):
            status['selected_feedback'].update(omitted=1, complete=False, first_error=error)
            with self.assertRaises(ValueError):
                selected_feedback(status)

    def test_point_keeps_exact_messages(self):
        points = [{'hint_log': {'availability': 'complete', 'events': [{'message': 'retained'}]}}]
        before = copy.deepcopy(points[0]['hint_log']['events'])
        checked = apply_selected_feedback(points, None)
        self.assertEqual(checked['availability'], 'unavailable')
        self.assertEqual(points[0]['hint_log']['availability'], 'unavailable')
        self.assertEqual(points[0]['hint_log']['events'], before)
        self.assertEqual(points[0]['hint_log']['selected_feedback']['evidence'],
                         'evidence/SESSION.json#/observer_status/status/selected_feedback')


class FeedbackJoinTests(unittest.TestCase):
    def events(self, rows):
        class Events:
            references = list(range(len(rows)))
            def read(self, reference):
                return rows[reference]
            def text_field(self, reference, field):
                value = rows[reference]['message']
                if isinstance(value, Exception):
                    def fail():
                        raise value
                        yield ''
                    return StreamText(fail)
                return StreamText(lambda: iter((value,)))
        return Events()

    def status(self, count):
        return {'selected_feedback': {'emitted': count, 'omitted': 0,
                'complete': True, 'first_error': None}}

    def test_missing_event_rejects(self):
        with self.assertRaisesRegex(ValueError, 'emitted count'):
            bind_selected_feedback(self.events([]), self.status(1))

    def test_extra_event_rejects(self):
        events = self.events([{'sequence': 3, 'kind': 'feedback', 'message': 'retained'}])
        with self.assertRaisesRegex(ValueError, 'emitted count'):
            bind_selected_feedback(events, self.status(0))

    def test_discarded_event_counts_before_partition(self):
        events = self.events([{'sequence': 3, 'kind': 'feedback', 'trial': True, 'message': 'discarded'},
                              {'sequence': 8, 'kind': 'feedback', 'trial': False, 'message': 'retained'}])
        result = bind_selected_feedback(events, self.status(2))
        self.assertEqual(result['verified_event_count'], 2)
        self.assertEqual(result['availability'], 'complete')

    def test_corrupt_discarded_payload_rejects(self):
        events = self.events([{'sequence': 3, 'kind': 'feedback', 'trial': True,
                               'message': ValueError('corrupt chunk')}])
        with self.assertRaisesRegex(ValueError, 'corrupt chunk'):
            bind_selected_feedback(events, self.status(1))

    def test_missing_status_stays_unavailable(self):
        result = bind_selected_feedback(self.events([]), None)
        self.assertEqual(result['availability'], 'unavailable')

    def test_duplicate_event_rejects(self):
        row = {'sequence': 3, 'kind': 'feedback', 'message': 'retained'}
        with self.assertRaisesRegex(ValueError, 'sequence repeats'):
            bind_selected_feedback(self.events([row, row]), self.status(2))

    def test_denied_log_stays_partial(self):
        status = self.status(0)
        status['selected_feedback'].update(omitted=1, complete=False, first_error='denied')
        self.assertEqual(bind_selected_feedback(self.events([]), status)['availability'], 'partial')


if __name__ == '__main__':
    unittest.main()
