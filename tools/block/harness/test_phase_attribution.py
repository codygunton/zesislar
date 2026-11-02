"""Keep optional phase measurements separate from compilation authority."""

import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from phase_attribution import Recorder, aggregate_sample, enabled


def sample(index, aggregate=None):
    return {'time_ns': 100 - index, 'monotonic_ns': index * 1_000_000_000,
            'self_user': index * 0.2, 'self_system': index * 0.1,
            'child_user': index * 0.4, 'child_system': index * 0.3,
            'aggregate': aggregate or {'known': False, 'reason': 'unavailable_before_entry'}}


class PhaseAttributionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.output = Path(temporary.name)

    def recorder(self):
        return Recorder({'phase_attribution': {'enabled': True}}, self.output,
                        runtime_reference={'path': '/owned/RUNTIME.json', 'sha256': 'a' * 64})

    def events(self):
        return sorted((json.loads(p.read_text())
                       for p in (self.output / 'phase-attribution').glob('*.json')),
                      key=lambda value: value['sequence'])

    def test_old_runtime_performs_no_measurement_or_write(self):
        with patch.object(Recorder, 'snapshot') as snapshot, \
                patch('phase_attribution.resource.getrusage') as usage, \
                patch.dict('phase_attribution.os.environ', {'ZESU_PHASE_ATTRIBUTION': '1'}), \
                patch.object(Path, 'read_text') as read:
            recorder = Recorder({}, self.output)
            with recorder.span('outer_runtime_validation'):
                pass
            snapshot.assert_not_called()
            usage.assert_not_called()
            read.assert_not_called()
        self.assertEqual(list(self.output.iterdir()), [])

    def test_wall_uses_monotonic_time_and_cpu_roles_stay_separate(self):
        recorder = self.recorder()
        with patch.object(recorder, 'snapshot', side_effect=[sample(0), sample(1)]):
            with recorder.span('snapshot_publication'):
                pass
        event, = self.events()
        self.assertEqual(event['wall_seconds'], 1)
        self.assertLess(event['ended_time_ns'], event['started_time_ns'])
        self.assertEqual(event['self_user_CPU_seconds'], 0.2)
        self.assertEqual(event['waited_child_user_CPU_seconds'], 0.4)
        self.assertEqual(event['outcome'], 'completed')
        self.assertFalse(event['aggregate_CPU']['known'])

    def test_exception_is_preserved_without_retaining_its_text(self):
        recorder = self.recorder()
        error = ValueError('private exception payload')
        with self.assertRaises(ValueError) as caught, \
                patch.object(recorder, 'snapshot', side_effect=[sample(0), sample(1)]):
            with recorder.span('physical_input_validation'):
                raise error
        self.assertIs(caught.exception, error)
        event, = self.events()
        self.assertEqual(event['outcome'], 'exception')
        self.assertNotIn('private exception payload', json.dumps(event))

    def test_recording_failure_does_not_replace_the_original_exception(self):
        recorder = self.recorder()
        error = ValueError('original')
        with self.assertRaises(ValueError) as caught, \
                patch.object(recorder, 'retain', side_effect=OSError('disk unavailable')), \
                patch('phase_attribution.sys.stderr'):
            with recorder.span('physical_input_validation'):
                raise error
        self.assertIs(caught.exception, error)

    def test_nested_spans_are_inclusive_and_do_not_overwrite(self):
        recorder = self.recorder()
        with patch.object(recorder, 'snapshot', side_effect=[sample(i) for i in range(4)]):
            with recorder.span('snapshot_publication'):
                with recorder.span('snapshot_forced_validation'):
                    pass
        outer, inner = self.events()
        self.assertEqual(outer['wall_seconds'], 3)
        self.assertEqual(inner['wall_seconds'], 1)
        self.assertIn('not additive', outer['interval_scope'])
        self.assertEqual(len(list((self.output / 'phase-attribution').iterdir())), 2)

    def test_changed_or_missing_aggregate_reports_unknown(self):
        group = self.output / 'aggregate'
        group.mkdir()
        (group / 'cpu.stat').write_text('usage_usec 125\n')
        info = group.stat()
        identity = {'aggregate_path': str(group), 'aggregate_device': info.st_dev,
                    'aggregate_inode': info.st_ino}
        self.assertEqual(aggregate_sample(identity)['usage_usec'], 125)
        changed = dict(identity, aggregate_inode=info.st_ino + 1)
        self.assertEqual(aggregate_sample(changed)['reason'], 'identity_changed')
        (group / 'cpu.stat').unlink()
        self.assertFalse(aggregate_sample(identity)['known'])

    def test_aggregate_delta_requires_identical_identity_and_monotonic_counter(self):
        recorder = self.recorder()
        for right, reason in [({'known': True, 'device': 2, 'inode': 3, 'usage_usec': 20}, 'identity_changed'),
                              ({'known': True, 'device': 1, 'inode': 3, 'usage_usec': 5}, 'counter_regressed')]:
            left = {'known': True, 'device': 1, 'inode': 3, 'usage_usec': 10}
            with patch.object(recorder, 'snapshot', side_effect=[sample(0, left), sample(1, right)]):
                with recorder.span('physical_compilation'):
                    pass
            self.assertEqual(self.events()[-1]['aggregate_CPU']['reason'], reason)

    def test_unknown_configuration_refuses_without_enabling_from_environment(self):
        self.assertFalse(enabled({}))
        self.assertFalse(enabled({'phase_attribution': {'enabled': False}}))
        for value in [True, {'enabled': 1}, {'enabled': True, 'output': '/unowned'}]:
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, 'setting'):
                enabled({'phase_attribution': value})

    def test_metadata_consumer_requires_its_exact_owned_import_and_file(self):
        import transport_mapping
        path = self.output / 'entry_chain_provider.py'
        path.write_text('from phase_attribution import for_runtime\nfor_runtime(runtime,"owned")\n')
        report = transport_mapping.audit(path)
        self.assertEqual(report['reviewed_sinks'][0]['module'], 'phase_attribution')
        for source in ['from another_module import for_runtime\nfor_runtime(runtime,"owned")',
                       'from phase_attribution import for_runtime\nfor_runtime_nearby(runtime,"owned")']:
            path.write_text(source)
            with self.assertRaises(ValueError):
                transport_mapping.audit(path)
        path = self.output / 'another_consumer.py'
        path.write_text('from phase_attribution import for_runtime\nfor_runtime(runtime,"owned")')
        with self.assertRaisesRegex(ValueError, 'escapes'):
            transport_mapping.audit(path)


class AsyncEntryTests(unittest.IsolatedAsyncioTestCase):
    async def test_timing_preserves_async_entry_and_exception_suppression(self):
        events = []

        class Manager:
            async def __aenter__(self):
                events.append('enter')
                return 'session'

            async def __aexit__(self, kind, error, traceback):
                events.append(error)
                return True

        with tempfile.TemporaryDirectory() as output:
            recorder = Recorder({'phase_attribution': {'enabled': True}}, output)
            manager = Manager()
            error = ValueError('session exception')
            with patch.object(recorder, 'snapshot', side_effect=[sample(0), sample(1)]):
                async with recorder.enter('MCP_transport_startup', manager) as session:
                    self.assertEqual(session, 'session')
                    raise error
            self.assertEqual(events, ['enter', error])
            paths = list((Path(output) / 'phase-attribution').glob('*.json'))
            self.assertEqual(len(paths), 1)
            self.assertEqual(json.loads(paths[0].read_text())['outcome'], 'completed')

    async def test_disabled_entry_returns_the_original_manager(self):
        manager = object()
        self.assertIs(Recorder({}, '/unused').enter('MCP_transport_startup', manager), manager)


if __name__ == '__main__':
    unittest.main()
