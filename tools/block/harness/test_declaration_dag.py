"""Check DAG resource leases with private nonproof worker artifacts."""
import threading
import unittest

from declaration_dag import CLAIM_BYTES, GIB, ModuleCompileFailure, execute, frontier_claim


class DeclarationDagTests(unittest.TestCase):
    def run_plan(self, ordered, edges=(), weights=None, **changes):
        weights = weights or {name: GIB for name in ordered}
        claim = frontier_claim(ordered, list(edges), weights, changes.get('completed', ()),
                               changes.get('protected', ()), changes.get('maximum_workers', 48))
        values = dict(claim_bytes=claim, fence_bytes=CLAIM_BYTES,
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

    def test_keep_going_skips_only_failed_transitive_dependents(self):
        started = []
        edges = [{'from': 'B', 'to': 'A'}, {'from': 'C', 'to': 'B'},
                 {'from': 'GoodEnd', 'to': 'Good'}]
        def compile_private(name):
            started.append(name)
            if name == 'A':
                raise ModuleCompileFailure('Synthetic module error.', {'physical_result': '/A'})
            return name
        with self.assertRaises(RuntimeError) as caught:
            self.run_plan(['A', 'B', 'C', 'Good', 'GoodEnd'], edges,
                          maximum_workers=1, compile_private=compile_private, keep_going=True)
        result = caught.exception.result
        self.assertEqual(started, ['A', 'Good', 'GoodEnd'])
        self.assertEqual(result['skipped'], {'B': ['A'], 'C': ['B']})
        self.assertEqual(result['pending'], [])
        self.assertEqual(list(result['receipts']), ['Good', 'GoodEnd'])

    def test_keep_going_reports_every_independent_module_error(self):
        def fail(name):
            raise ModuleCompileFailure('Module ' + name, {'physical_result': '/' + name})
        with self.assertRaises(RuntimeError) as caught:
            self.run_plan(['A', 'B', 'C'], compile_private=fail, keep_going=True, maximum_workers=1)
        self.assertEqual([x['module'] for x in caught.exception.result['failures']], ['A', 'B', 'C'])
        self.assertEqual(caught.exception.result['pending'], [])

    def test_keep_going_does_not_bypass_global_identity_refusal(self):
        started = []
        def fail(name):
            started.append(name)
            raise ValueError('The runtime identity changed.')
        with self.assertRaises(RuntimeError) as caught:
            self.run_plan(['A', 'B'], compile_private=fail, keep_going=True, maximum_workers=1)
        self.assertEqual(started, ['A'])
        self.assertEqual(caught.exception.result['failures'][0]['kind'], 'unsafe_runtime')
        self.assertEqual(caught.exception.result['pending'], ['B'])

    def test_keep_going_does_not_bypass_publication_refusal(self):
        def refuse(name, artifact):
            raise ModuleCompileFailure('Publication is unsafe.', {})
        with self.assertRaises(RuntimeError) as caught:
            self.run_plan(['A', 'B'], publish=refuse, keep_going=True, maximum_workers=1)
        self.assertEqual(caught.exception.result['failures'][0]['kind'], 'unsafe_runtime')
        self.assertEqual(caught.exception.result['pending'], ['B'])

    def test_keep_going_crosses_failed_protected_barrier_only_for_independent_work(self):
        def fail(name):
            raise ModuleCompileFailure('Protected compiler error.', {})
        with self.assertRaises(RuntimeError) as caught:
            self.run_plan(['Barrier', 'Dependent', 'Independent'],
                          [{'from': 'Dependent', 'to': 'Barrier'}],
                          protected={'Barrier'}, compile_protected=fail, keep_going=True)
        result = caught.exception.result
        self.assertEqual(result['skipped'], {'Dependent': ['Barrier']})
        self.assertEqual(list(result['receipts']), ['Independent'])

    def test_default_still_stops_after_authenticated_module_error(self):
        def fail(name):
            raise ModuleCompileFailure('Module error.', {})
        with self.assertRaises(RuntimeError) as caught:
            self.run_plan(['A', 'B'], compile_private=fail, maximum_workers=1)
        self.assertFalse(caught.exception.result['keep_going'])
        self.assertEqual(caught.exception.result['pending'], ['B'])

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
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'frontier booking'):
                self.run_plan(['A'], **{key: 24 * GIB})

    def test_pair_and_dependent_book_one_concurrent_frontier(self):
        edges = [{'from': 'C', 'to': 'A'}, {'from': 'C', 'to': 'B'}]
        self.assertEqual(frontier_claim(['A', 'B', 'C'], edges,
            {name: 16 * GIB for name in ['A', 'B', 'C']}), 32 * GIB)

    def test_uneven_chains_overlap_across_graph_depths(self):
        # LongA can overlap ShortB even though they occur at different depths.
        edges = [{'from': 'LongA', 'to': 'A'}, {'from': 'ShortB', 'to': 'B'},
                 {'from': 'DeepB', 'to': 'ShortB'}]
        weights = {'A': GIB, 'B': GIB, 'LongA': 20 * GIB,
                   'ShortB': GIB, 'DeepB': 25 * GIB}
        self.assertEqual(frontier_claim(list(weights), edges, weights), 45 * GIB)

    def test_protected_barriers_prevent_cross_segment_booking(self):
        ordered = ['A', 'Barrier', 'B']
        weights = {'A': 10 * GIB, 'Barrier': 16 * GIB, 'B': 12 * GIB}
        self.assertEqual(frontier_claim(ordered, [], weights, protected=['Barrier']), 16 * GIB)

    def test_frontier_respects_worker_cap_and_aggregate_cap(self):
        names = ['M' + str(i) for i in range(60)]
        self.assertEqual(frontier_claim(names, [], dict.fromkeys(names, GIB)), 48 * GIB)
        self.assertEqual(frontier_claim(names, [], dict.fromkeys(names, 16 * GIB)), CLAIM_BYTES)

    def test_frontier_matches_exhaustive_small_graphs(self):
        import itertools
        import random
        rng = random.Random(171)
        for unused in range(40):
            names = list('ABCDEFG')
            edges = [{'from': names[i], 'to': names[j]} for i in range(7)
                     for j in range(i) if rng.random() < .3]
            weights = {name: rng.randrange(1, 15) * GIB for name in names}
            parents = {name: set() for name in names}
            for name in names:
                for edge in edges:
                    if edge['from'] == name:
                        parents[name] |= parents[edge['to']] | {edge['to']}
            for cap in [1, 3, 48]:
                expected = max(sum(weights[x] for x in group) for size in range(min(cap, 7) + 1)
                    for group in itertools.combinations(names, size)
                    if all(a not in parents[b] and b not in parents[a]
                           for a, b in itertools.combinations(group, 2)))
                self.assertEqual(frontier_claim(names, edges, weights, maximum_workers=cap),
                                 min(CLAIM_BYTES, expected))

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
