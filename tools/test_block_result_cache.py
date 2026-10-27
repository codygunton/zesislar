"""Check semantic invalidation and retained native result evidence."""
from concurrent.futures import ThreadPoolExecutor
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
import result_cache as cache


class ResultCacheTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.store = self.root / 'cache'
        self.source = self.root / 'block.v'
        self.source.write_text('Proof. zesu_block. Qed.\n')
        self.state = self.root / 'state.json'
        self.state.write_text(json.dumps({
            'goals': [], 'stack': [], 'shelf': [], 'given_up': [],
            'kernel_groups': {'goals': [], 'stack': [], 'shelf': [], 'given_up': []}}))
        self.obj = self.root / 'block.vo'
        self.obj.write_bytes(b'checked object')
        binding = {'sha256': cache.digest(self.source)}
        self.spec = {'schema': cache.KEY_SCHEMA, 'block': '800d0000',
                     'proof': self.bind(self.source),
                     'entries': [{'name': 'Entries.own', 'source': binding}],
                     'entry_context': [{'name': 'Entries.context', 'source': binding}],
                     'hints': [{'name': 'Hints', 'source': binding}],
                     'imports': [{'name': 'Automation.All', 'source': binding}],
                     'toolchain': {'rocq': 'pinned-binary-digest'},
                     'search': {'provider_sha256': 'pinned-provider', 'tactic': 'zesu_block', 'memo': False}}
        self.result = {'block': '800d0000', 'phase': 'native', 'success': True,
                       'status': 'passed', 'complete_state': self.bind(self.state),
                       'group_counts': {'active': 0, 'focus_frames': 0, 'frame_goals': 0,
                                        'shelves': 0, 'given_up': 0},
                       'CPU': {'cpu_seconds': 91.0},
                       'native_receipts': {'block': {
                           'compile_file_success': True, 'verification_method': 'module_m',
                           'assumptions': [], 'source': str(self.source),
                           'source_sha256': cache.digest(self.source), 'object': str(self.obj),
                           'object_sha256': cache.digest(self.obj)}}}
        self.result['complete_state']['state_source'] = 'successful_command_returned_state'
        self.result_file = self.root / 'RESULT.json'

    def bind(self, path):
        return {'path': str(path), 'sha256': cache.digest(path)}

    def save(self):
        self.result_file.write_text(json.dumps(self.result))
        return cache.store(self.store, cache.build_key(self.spec), self.result_file)

    def test_each_semantic_input_invalidates(self):
        original = cache.build_key(self.spec)['sha256']
        for name in ['proof', 'entries', 'entry_context', 'hints', 'imports', 'toolchain', 'search']:
            with self.subTest(name=name):
                changed = deepcopy(self.spec)
                if name == 'proof':
                    changed[name] = {'sha256': '1' * 64}
                elif isinstance(changed[name], list):
                    changed[name][0]['source'] = {'sha256': '1' * 64}
                else:
                    changed[name]['new'] = 'different'
                self.assertNotEqual(original, cache.build_key(changed)['sha256'])

    def test_relocated_inputs_keep_identity(self):
        key = cache.build_key(self.spec)
        copy = self.root / 'relocated.v'
        copy.write_bytes(self.source.read_bytes())
        self.spec['proof'] = self.bind(copy)
        self.assertEqual(cache.build_key(self.spec), key)

    def test_source_change_refuses_key(self):
        self.source.write_text('changed')
        with self.assertRaisesRegex(ValueError, 'changed'):
            cache.build_key(self.spec)

    def test_duplicate_or_incomplete_identity_refuses(self):
        self.spec['entries'] *= 2
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            cache.build_key(self.spec)
        self.spec['entries'] = []
        with self.assertRaisesRegex(ValueError, 'empty'):
            cache.build_key(self.spec)

    def test_miss_does_not_create_store(self):
        self.assertIsNone(cache.lookup(self.store, cache.build_key(self.spec)))
        self.assertFalse(self.store.exists())

    def test_closed_hit_retains_object_after_original_removal(self):
        key = cache.build_key(self.spec)
        hit = self.save()
        self.source.unlink()
        self.obj.unlink()
        self.state.unlink()
        hit = cache.lookup(self.store, key)
        self.assertTrue(hit['result']['success'])
        self.assertEqual(hit['fresh_search_cpu_seconds'], 0)
        self.assertEqual(hit['historical_cpu']['cpu_seconds'], 91)
        obj = Path(hit['result']['native_receipts']['block']['object'])
        self.assertEqual(obj.read_bytes(), b'checked object')

    def test_open_hit_preserves_all_residual_groups(self):
        state = json.loads(self.state.read_text())
        for name in ['goals', 'shelf', 'given_up']:
            state[name] = [{'ty': name}]
            state['kernel_groups'][name] = [{'term': name}]
        state['shared_state'] = {'complete': True, 'evar_assignments': {},
                                 'universe_constraints': [], 'shared_context': {}}
        self.state.write_text(json.dumps(state))
        self.result.update(success=False, status='native_open', native_receipts={},
                           complete_state=self.bind(self.state), normal_tactic_return=True,
                           proof_finished=False)
        self.result['complete_state']['state_source'] = 'successful_command_returned_state'
        self.result['group_counts'].update(active=1, shelves=1, given_up=1)
        hit = self.save()
        actual = json.loads(Path(hit['result']['complete_state']['path']).read_text())
        self.assertEqual(actual, state)
        self.assertFalse(hit['result']['success'])

    def test_incomplete_residual_refuses(self):
        state = json.loads(self.state.read_text())
        del state['kernel_groups']
        self.state.write_text(json.dumps(state))
        self.result['complete_state'] = self.bind(self.state)
        self.result['complete_state']['state_source'] = 'successful_command_returned_state'
        with self.assertRaisesRegex(ValueError, 'kernel group'):
            self.save()

    def test_false_closed_and_infrastructure_failures_refuse(self):
        self.result['group_counts']['active'] = 1
        with self.assertRaises(ValueError):
            self.save()
        self.result['group_counts']['active'] = 0
        self.result['shared_infrastructure_failure'] = True
        with self.assertRaisesRegex(ValueError, 'infrastructure'):
            self.save()

    def test_missing_kernel_verification_refuses(self):
        self.result['native_receipts']['block']['assumptions'] = ['axiom']
        with self.assertRaisesRegex(ValueError, 'kernel verification'):
            self.save()

    def test_pre_call_fallback_refuses(self):
        self.result['complete_state']['state_source'] = 'retained_pre_call_state'
        with self.assertRaisesRegex(ValueError, 'pre-call fallback'):
            self.save()

    def test_focus_frame_count_and_source_identity_refuse(self):
        self.result['group_counts']['frame_goals'] = 1
        with self.assertRaises(ValueError):
            self.save()
        self.result['group_counts']['frame_goals'] = 0
        self.spec['proof'] = {'sha256': '1' * 64}
        with self.assertRaisesRegex(ValueError, 'proof source'):
            self.save()

    def test_corrupt_result_or_artifact_refuses_without_rerun(self):
        hit = self.save()
        path = Path(hit['result']['complete_state']['path'])
        path.write_text('corrupt')
        with self.assertRaisesRegex(ValueError, 'artifact changed'):
            cache.lookup(self.store, cache.build_key(self.spec))

    def test_concurrent_writers_keep_one_complete_entry(self):
        self.result_file.write_text(json.dumps(self.result))
        key = cache.build_key(self.spec)
        with ThreadPoolExecutor(max_workers=4) as pool:
            hits = list(pool.map(lambda _: cache.store(self.store, key, self.result_file), range(4)))
        self.assertEqual(len({hit['manifest'] for hit in hits}), 1)
        self.assertEqual(len(list(self.store.iterdir())), 1)

    def test_pluggable_normalizer_ignores_execution_metadata(self):
        def normalize(spec):
            return {'key_function': 'example-normalizer-v1', 'block': spec['block'],
                    'proof_text': spec['proof_text'].replace('\r\n', '\n'),
                    'toolchain_binary': spec['binary_sha256']}
        a = {'block': '800d0000', 'proof_text': 'Proof.\r\nexact I.\r\n',
             'binary_sha256': '1' * 64, 'path': '/first', 'pid': 123,
             'timestamp': 1000, 'environment': {'HOME': '/first'}}
        b = dict(reversed(list(a.items())))
        b.update(proof_text='Proof.\nexact I.\n', path='/second', pid=456,
                 timestamp=2000, environment={'HOME': '/second'})
        key = cache.build_key(a, key_function=normalize)
        self.assertEqual(key, cache.build_key(b, key_function=normalize))
        self.result_file.write_text(json.dumps(self.result))
        hit = cache.store(self.store, key, self.result_file)
        self.assertEqual(hit['key'], key['sha256'])
        b['proof_text'] += 'changed'
        self.assertNotEqual(key, cache.build_key(b, key_function=normalize))

    def test_key_function_must_supply_its_version(self):
        with self.assertRaisesRegex(ValueError, 'key_function'):
            cache.build_key({}, key_function=lambda _: {'block': '800d0000'})

    def test_dictionary_order_does_not_change_key(self):
        a = cache.build_key(self.spec)
        self.spec['search'] = dict(reversed(list(self.spec['search'].items())))
        self.assertEqual(a, cache.build_key(dict(reversed(list(self.spec.items())))))

    def test_open_pretty_groups_without_shared_state_refuse(self):
        self.result.update(success=False, status='native_open', native_receipts={},
                           normal_tactic_return=True, proof_finished=False)
        with self.assertRaisesRegex(ValueError, 'shared evar state'):
            self.save()

    def test_vos_object_refuses_closed_acceptance(self):
        self.result['native_receipts']['block']['object'] = str(self.obj.with_suffix('.vos'))
        with self.assertRaisesRegex(ValueError, 'full proof object'):
            self.save()


if __name__ == '__main__':
    unittest.main()
