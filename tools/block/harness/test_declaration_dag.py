"""Check DAG resource leases with private nonproof worker artifacts."""
import threading
import unittest

from declaration_dag import CLAIM_BYTES, GIB, execute


class DeclarationDagTests(unittest.TestCase):
    def run_plan(self, ordered, edges=(), weights=None, **changes):
        weights = weights or {name: GIB for name in ordered}
        values = dict(claim_bytes=CLAIM_BYTES, fence_bytes=CLAIM_BYTES,
                      available_bytes=lambda: 256 * GIB,
                      compile_private=lambda name: {'private': name},
                      publish=lambda name, artifact: {'path': '/' + name, 'sha256': 'a' * 64},
                      compile_protected=lambda name: {'protected': name})
        values.update(changes)
        return execute(ordered, list(edges), weights, **values)

    def test_independent_modules_use_up_to_48_workers(self):
        ready = threading.Event()
        lock = threading.Lock()
        started = []
        controller = threading.get_ident()
        def compile_private(name):
            with lock:
                started.append(name)
                if len(started) == 48:
                    ready.set()
            if not ready.wait(5):
                raise AssertionError('The scheduler did not dispatch 48 ready workers.')
            return name
        def publish(name, artifact):
            self.assertEqual(threading.get_ident(), controller)
            self.assertEqual(name, artifact)
            return {'path': '/' + name, 'sha256': 'a' * 64}
        result = self.run_plan(['M' + str(index) for index in range(49)],
                               maximum_workers=96, compile_private=compile_private, publish=publish)
        self.assertEqual(result['peak_workers'], 48)
        self.assertEqual(len(result['receipts']), 49)
        self.assertLess(result['peak_weight_bytes'], CLAIM_BYTES)

    def test_weight_leases_keep_sum_below_64_gib(self):
        ready = threading.Event()
        lock = threading.Lock()
        started = []
        def compile_private(name):
            with lock:
                started.append(name)
                if len(started) == 3:
                    ready.set()
            self.assertTrue(ready.wait(5))
            return name
        ordered = ['M' + str(index) for index in range(8)]
        result = self.run_plan(ordered, weights={name: 16 * GIB for name in ordered},
                               compile_private=compile_private)
        self.assertEqual(result['peak_workers'], 3)
        self.assertEqual(result['peak_weight_bytes'], 48 * GIB)

    def test_dependent_waits_for_accepted_publication(self):
        accepted = set()
        def compile_private(name):
            if name == 'B':
                self.assertIn('A', accepted)
            return name
        def publish(name, artifact):
            accepted.add(name)
            return {'path': '/' + name, 'sha256': 'a' * 64}
        result = self.run_plan(['A', 'B'], [{'from': 'B', 'to': 'A'}],
                               compile_private=compile_private, publish=publish)
        self.assertEqual(list(result['receipts']), ['A', 'B'])

    def test_protected_barrier_runs_on_controller_between_segments(self):
        accepted = set()
        controller = threading.get_ident()
        def compile_private(name):
            if name == 'After':
                self.assertIn('Barrier', accepted)
            return name
        def barrier(name):
            self.assertEqual(threading.get_ident(), controller)
            self.assertEqual(accepted, {'Before'})
            return name
        def publish(name, artifact):
            accepted.add(name)
            return {'path': '/' + name, 'sha256': 'a' * 64}
        result = self.run_plan(['Before', 'Barrier', 'After'], protected={'Barrier'},
                               compile_private=compile_private, compile_protected=barrier,
                               publish=publish)
        self.assertEqual(list(result['receipts']), ['Before', 'Barrier', 'After'])

    def test_compile_failure_stops_later_dispatch(self):
        starts = []
        def fail(name):
            starts.append(name)
            raise RuntimeError('Synthetic compiler refusal.')
        with self.assertRaises(RuntimeError) as caught:
            self.run_plan(['A', 'B'], maximum_workers=1, compile_private=fail)
        self.assertEqual(starts, ['A'])
        self.assertEqual(caught.exception.result['pending'], ['B'])

    def test_protected_compiler_has_an_active_lease_and_peak(self):
        observations = []
        def barrier(name):
            self.assertEqual(observations[-1]['active'], ['Barrier'])
            self.assertEqual(observations[-1]['running_weight_bytes'], 2 * GIB)
            return name
        result = self.run_plan(['Barrier'], weights={'Barrier': 2 * GIB},
                               protected={'Barrier'}, compile_protected=barrier,
                               checkpoint=observations.append)
        self.assertEqual(result['peak_workers'], 1)
        self.assertEqual(result['peak_weight_bytes'], 2 * GIB)

    def test_protected_compiler_obeys_available_memory(self):
        with self.assertRaises(RuntimeError) as caught:
            self.run_plan(['Barrier'], weights={'Barrier': 8 * GIB}, protected={'Barrier'},
                          available_bytes=lambda: 10 * GIB,
                          compile_protected=lambda name: self.fail('Unexpected compiler.'))
        self.assertEqual(caught.exception.result['peak_workers'], 0)

    def test_failed_publication_keeps_dependent_unstarted(self):
        starts = []
        def compile_private(name):
            starts.append(name)
            return name
        with self.assertRaises(RuntimeError):
            self.run_plan(['A', 'B'], [{'from': 'B', 'to': 'A'}],
                          compile_private=compile_private, publish=lambda name, artifact: None)
        self.assertEqual(starts, ['A'])

    def test_failure_drains_and_publishes_an_existing_healthy_worker(self):
        healthy_started = threading.Event()
        failed = threading.Event()
        published = []
        def compile_private(name):
            if name == 'A':
                self.assertTrue(healthy_started.wait(5))
                failed.set()
                raise RuntimeError('Synthetic compiler refusal.')
            healthy_started.set()
            self.assertTrue(failed.wait(5))
            return name
        def publish(name, artifact):
            published.append(name)
            return {'path': '/' + name, 'sha256': 'a' * 64}
        with self.assertRaises(RuntimeError) as caught:
            self.run_plan(['A', 'B', 'C'], maximum_workers=2,
                          compile_private=compile_private, publish=publish)
        self.assertEqual(published, ['B'])
        self.assertEqual(caught.exception.result['pending'], ['C'])

    def test_running_weight_survives_until_publication(self):
        observations = []
        def publish(name, artifact):
            self.assertIn(name, observations[-1]['active'])
            self.assertGreaterEqual(observations[-1]['running_weight_bytes'], GIB)
            return {'path': '/' + name, 'sha256': 'a' * 64}
        self.run_plan(['A', 'B'], checkpoint=observations.append, publish=publish)

    def test_unknown_dependency_refuses_before_dispatch(self):
        with self.assertRaisesRegex(ValueError, 'lacks an accepted object'):
            self.run_plan(['A'], [{'from': 'A', 'to': 'Unknown'}],
                          compile_private=lambda name: self.fail('Unexpected compiler.'))

    def test_completed_external_import_is_allowed(self):
        result = self.run_plan(['A'], [{'from': 'A', 'to': 'Installed'}], completed={'Installed'})
        self.assertEqual(list(result['receipts']), ['A'])

    def test_cycle_refuses_before_dispatch(self):
        with self.assertRaisesRegex(ValueError, 'not topological'):
            self.run_plan(['A', 'B'], [{'from': 'A', 'to': 'B'}, {'from': 'B', 'to': 'A'}])

    def test_non_fixed_booking_refuses(self):
        for key in ['claim_bytes', 'fence_bytes']:
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, '64/64'):
                self.run_plan(['A'], **{key: 24 * GIB})

    def test_available_memory_preserves_30_percent(self):
        with self.assertRaises(RuntimeError) as caught:
            self.run_plan(['A'], weights={'A': 8 * GIB}, available_bytes=lambda: 10 * GIB)
        self.assertEqual(caught.exception.result['receipts'], {})

    def test_invalid_weights_refuse(self):
        for value in [0, True, CLAIM_BYTES]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.run_plan(['A'], weights={'A': value})


if __name__ == '__main__':
    unittest.main()
