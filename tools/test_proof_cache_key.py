"""Check normalized semantic identities and conservative cache validity."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
import proof_cache_key as keys
import result_cache as cache


class ProofCacheKeyTests(unittest.TestCase):
    def setUp(self):
        environment = patch.dict('os.environ', {'ZESU_PROOF_CACHE': 'on', 'ZESU_IO': 'unit-control'})
        environment.start()
        self.addCleanup(environment.stop)
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.work = self.root / 'first'
        self.work.mkdir()
        self.files = []
        for name, kind, text in [('Proof.v', 'source', 'Lemma goal : True. Proof. exact I. Qed.\n'),
                                  ('Entries.v', 'source', 'Definition entry := True.\n'),
                                  ('Hints.v', 'source', 'Hint Resolve goal | 1 : core.\n'),
                                  ('coqc', 'binary', 'pinned compiler'),
                                  ('runtime.so', 'dynamic_library', 'pinned runtime'),
                                  ('provider.py', 'source', 'pinned provider')]:
            path = self.work / name
            path.write_text(text)
            self.files.append({'id': name, 'kind': kind, 'path': str(path),
                               'sha256': keys.file_digest(path), 'root_role': 'workspace'})
        def literal(text):
            return {'kind': 'literal', 'value': text}
        path = {'kind': 'path', 'value': str(self.work), 'root_role': 'workspace'}
        config = {'argv': [literal('-q'), literal('-Q'), path, literal('Test')],
                  'execution_vectors': [{'role': 'python-provider', 'argv': [literal('python'), literal('provider.py')],
                                         'cwd': path}],
                  'load_paths': [{'flag': '-Q', 'physical_root_role': 'workspace',
                                  'relative_path': '.', 'logical_prefix': 'Test', 'ordinal': 0}],
                  'cwd': path, 'environment': {name: {'kind': 'paths', 'values': []}
                                              for name in ['COQPATH', 'OCAMLPATH', 'CAML_LD_LIBRARY_PATH', 'PATH']},
                  'init_file_policy': 'disabled', 'warnings_as_errors': [],
                  'native_compilation': 'ondemand', 'proof_skipping': False,
                  'locale': 'C.UTF-8', 'python_version': '3.12.11',
                  'python_hash_seed': '0', 'solver_seeds': {}}
        self.spec = {'schema': keys.INPUT_SCHEMA, 'block': '800d0000',
                     'roots': [{'role': 'workspace', 'path': str(self.work)}], 'files': self.files,
                     'recipe': {'schema': keys.RECIPE_SCHEMA, 'module': 'Test.Proof', 'proof': 'Proof.v',
                                'dependencies': [{'id': r['id'], 'requires': []} for r in self.files],
                                'producers': [], 'imports': ['Require Import Test.Entries.', 'Require Import Test.Hints.'],
                                'toolchain': {'compiler': ['coqc'], 'ocaml_runtime': ['runtime.so'],
                                              'standard_library': ['Entries.v'], 'pet': ['coqc'],
                                              'coq_lsp': ['provider.py'], 'mcp': ['provider.py'],
                                              'python': ['coqc'], 'python_dependencies': ['provider.py'],
                                              'plugins': [], 'solvers': [], 'dynamic_libraries': ['runtime.so']},
                                'configuration': config,
                                'backend': {'files': ['provider.py'], 'tactics': ['zesu_block.'],
                                            'features': {'context_collection': False}},
                                'acceptance': {'method': 'module_m', 'compilation': 'vo', 'allowed_assumptions': []}},
                     'attempt': {'schema': keys.ATTEMPT_SCHEMA,
                                 'limits': {'cpu_seconds': None, 'wall_seconds': None,
                                            'memory_bytes': 64 * 1024**3, 'swap_bytes': 0, 'steps': None},
                                 'scope_limits': [{'role': 'aggregate', 'parent': None,
                                                   'memory_bytes': 150 * 1024**3, 'swap_bytes': 0,
                                                   'cpu_seconds': None, 'wall_seconds': None},
                                                  {'role': 'client', 'parent': 'aggregate',
                                                   'memory_bytes': 64 * 1024**3, 'swap_bytes': 0,
                                                   'cpu_seconds': None, 'wall_seconds': None}],
                                 'tool_timeouts': {'rocq_call_seconds': 604800,
                                                   'pet_seconds': 604800, 'query_seconds': 604800},
                                 'arithmetic_caches': [{'name': name, 'policy': 'empty-private',
                                                        'initial_files': [], 'compiler_format': 'coqc'}
                                                       for name in ['.lia.cache', '.nia.cache', '.nra.cache', '.csdp.cache']]}}

    def build(self, spec=None):
        return keys.build_keys(self.spec if spec is None else spec)

    def test_domain_separated_hashes_and_adapter_match(self):
        value = self.build()
        expected = hashlib.sha256(b'zesu-proof-recipe-v1\0' + keys.canonical(value['recipe'])).hexdigest()
        self.assertEqual(value['recipe_key'], expected)
        self.assertEqual(value['attempt_key'], cache.build_key(self.spec, key_function=keys.normalize)['sha256'])
        self.assertNotEqual(value['recipe_key'], value['attempt_key'])

    def test_mapped_relocation_preserves_keys(self):
        before = self.build()
        second = self.root / 'other location'
        shutil.copytree(self.work, second)
        relocated = deepcopy(self.spec)
        relocated['roots'][0]['path'] = str(second)
        for row in relocated['files']:
            row['path'] = str(second / Path(row['path']).name)
        config = relocated['recipe']['configuration']
        config['argv'][2]['value'] = str(second)
        config['cwd']['value'] = str(second)
        config['execution_vectors'][0]['cwd']['value'] = str(second)
        self.assertEqual(before, self.build(relocated))

    def test_object_and_file_set_order_do_not_change_keys(self):
        before = self.build()
        changed = dict(reversed(list(deepcopy(self.spec).items())))
        changed['files'].reverse()
        changed['recipe']['dependencies'].reverse()
        self.assertEqual(before, self.build(changed))

    def test_source_bytes_and_dependency_content_invalidate(self):
        for name in ['Proof.v', 'Entries.v', 'Hints.v', 'coqc', 'runtime.so', 'provider.py']:
            with self.subTest(name=name):
                before = self.build()['recipe_key']
                path = self.work / name
                path.write_bytes(path.read_bytes() + b' ')
                next(row for row in self.files if row['id'] == name)['sha256'] = keys.file_digest(path)
                self.assertNotEqual(before, self.build()['recipe_key'])

    def test_tactic_and_hint_order_invalidate(self):
        before = self.build()['recipe_key']
        self.spec['recipe']['backend']['features']['context_collection'] = True
        self.assertNotEqual(before, self.build()['recipe_key'])
        self.spec['recipe']['backend']['features']['context_collection'] = False
        self.spec['recipe']['imports'].reverse()
        self.assertNotEqual(before, self.build()['recipe_key'])

    def test_load_path_order_is_semantic(self):
        conf = self.spec['recipe']['configuration']
        conf['argv'].extend([{'kind': 'literal', 'value': '-R'}, deepcopy(conf['cwd']),
                             {'kind': 'literal', 'value': 'Other'}])
        conf['load_paths'].append({'flag': '-R', 'physical_root_role': 'workspace',
                                   'relative_path': '.', 'logical_prefix': 'Other', 'ordinal': 1})
        before = self.build()['recipe_key']
        conf['argv'] = [conf['argv'][0], *conf['argv'][4:7], *conf['argv'][1:4]]
        conf['load_paths'].reverse()
        for i, row in enumerate(conf['load_paths']):
            row['ordinal'] = i
        self.assertNotEqual(before, self.build()['recipe_key'])

    def test_limits_and_cache_policy_change_only_attempt(self):
        before = self.build()
        self.spec['attempt']['limits']['cpu_seconds'] = 1200
        after = self.build()
        self.assertEqual(before['recipe_key'], after['recipe_key'])
        self.assertNotEqual(before['attempt_key'], after['attempt_key'])
        self.spec['attempt']['limits']['cpu_seconds'] = None
        self.spec['attempt']['arithmetic_caches'][0].update(policy='warm-private', initial_files=['coqc'])
        after = self.build()
        self.assertEqual(before['recipe_key'], after['recipe_key'])
        self.assertNotEqual(before['attempt_key'], after['attempt_key'])

    def test_run_diagnostics_remain_separate(self):
        before = self.build()
        run_record = {'diagnostics': {'clock': {'started_UTC': 'first'}, 'processes': [{'pid': 1}]}}
        run_record['diagnostics'].update(clock={'started_UTC': 'second'}, processes=[{'pid': 2}])
        self.assertEqual(before, self.build())
        self.spec['diagnostics'] = run_record['diagnostics']
        with self.assertRaisesRegex(ValueError, 'unknown fields'):
            self.build()

    def test_unknown_duplicate_nonfinite_and_invalid_types_refuse(self):
        with self.assertRaises(ValueError):
            keys.strict_loads('{"x":1,"x":2}')
        with self.assertRaises(ValueError):
            keys.strict_loads('{"x":NaN}')
        with self.assertRaises(ValueError):
            keys.strict_loads('{"x":1e9999}')
        self.spec['attempt']['limits']['memory_bytes'] = True
        with self.assertRaises(ValueError):
            self.build()

    def test_python_object_keys_cannot_collide_after_json_encoding(self):
        with self.assertRaisesRegex(ValueError, 'non-string key'):
            keys.canonical({1: 'value'})
        self.spec['recipe']['backend']['features'] = {1: True}
        with self.assertRaisesRegex(ValueError, 'non-string key'):
            self.build()

    def test_unresolved_dependency_and_unrecorded_environment_refuse(self):
        self.spec['recipe']['dependencies'][0]['requires'] = ['missing']
        with self.assertRaisesRegex(ValueError, 'unresolved'):
            self.build()
        self.spec['recipe']['dependencies'][0]['requires'] = []
        del self.spec['recipe']['configuration']['environment']['CAML_LD_LIBRARY_PATH']
        with self.assertRaisesRegex(ValueError, 'omits'):
            self.build()

    def test_symlink_escape_and_ambiguous_roots_refuse(self):
        outside = self.root / 'outside'
        outside.write_text('outside')
        link = self.work / 'link'
        link.symlink_to(outside)
        self.files.append({'id': 'escaped', 'kind': 'source', 'path': str(link),
                           'sha256': keys.file_digest(outside), 'root_role': 'workspace',
                           'symlink_target': str(outside)})
        with self.assertRaisesRegex(ValueError, 'escapes'):
            self.build()
        self.files.pop()
        self.spec['roots'].append({'role': 'duplicate', 'path': str(self.work)})
        with self.assertRaisesRegex(ValueError, 'ambiguous'):
            self.build()

    def test_source_whitespace_and_literals_are_not_scrubbed(self):
        before = self.build()['recipe_key']
        self.spec['recipe']['configuration']['argv'].append({'kind': 'literal', 'value': '/unmapped/one'})
        first = self.build()['recipe_key']
        self.spec['recipe']['configuration']['argv'][-1]['value'] = '/unmapped/two'
        self.assertNotEqual(first, self.build()['recipe_key'])
        self.assertNotEqual(before, first)

    def test_vos_and_skipping_refuse(self):
        self.spec['recipe']['acceptance']['compilation'] = 'vos'
        with self.assertRaises(ValueError):
            self.build()
        self.spec['recipe']['acceptance']['compilation'] = 'vo'
        self.spec['recipe']['configuration']['argv'].append({'kind': 'literal', 'value': '-vos'})
        with self.assertRaisesRegex(ValueError, 'Skipped'):
            self.build()

    def test_artifact_identity_binds_raw_shared_state(self):
        manifest = {'schema': keys.ARTIFACT_SCHEMA, 'attempt_key': self.build()['attempt_key'],
                    'status': 'open', 'acceptance': self.spec['recipe']['acceptance'],
                    'files': [{'id': 'shared_state', 'sha256': hashlib.sha256(b'evar unresolved').hexdigest()}]}
        before = keys.artifact_key(manifest)
        manifest['files'][0]['sha256'] = hashlib.sha256(b'evar assigned in another goal').hexdigest()
        self.assertNotEqual(before, keys.artifact_key(manifest))

    def test_scope_hierarchy_and_tool_timeouts_are_independent(self):
        before = self.build()
        self.spec['attempt']['scope_limits'][0]['memory_bytes'] += 1
        self.assertNotEqual(before['attempt_key'], self.build()['attempt_key'])
        self.spec['attempt']['scope_limits'][0]['memory_bytes'] -= 1
        self.spec['attempt']['tool_timeouts']['rocq_call_seconds'] += 1
        after = self.build()
        self.assertEqual(before['recipe_key'], after['recipe_key'])
        self.assertNotEqual(before['attempt_key'], after['attempt_key'])
        self.assertIsNone(after['attempt']['limits']['wall_seconds'])

    def test_runtime_closure_and_scope_cycles_refuse(self):
        self.spec['recipe']['toolchain']['python_dependencies'] = []
        with self.assertRaisesRegex(ValueError, 'closure is incomplete'):
            self.build()
        self.spec['recipe']['toolchain']['python_dependencies'] = ['provider.py']
        self.spec['attempt']['scope_limits'][0]['parent'] = 'client'
        with self.assertRaisesRegex(ValueError, 'cycle'):
            self.build()

    def test_named_execution_vectors_are_semantic(self):
        before = self.build()['recipe_key']
        self.spec['recipe']['configuration']['execution_vectors'][0]['argv'].append(
            {'kind': 'literal', 'value': '--different'})
        self.assertNotEqual(before, self.build()['recipe_key'])

    def test_transport_envelope_is_separately_checked_not_a_semantic_hash(self):
        envelope = self.work / 'runtime.json'
        envelope.write_text('{"claim":"first","output":"first"}')
        def transport():
            return {'kind': 'transport', 'role': 'entry-chain-runtime', 'encoding': 'sha256',
                    'binding': {'path': str(envelope), 'sha256': keys.file_digest(envelope),
                                'root_role': 'workspace'},
                    'semantic_projection': 'provider.py',
                    'semantic_dependencies': ['Proof.v', 'Entries.v', 'Hints.v', 'provider.py']}
        env = self.spec['recipe']['configuration']['environment']
        env['ENTRY_CHAIN_RUNTIME_SHA256'] = transport()
        before = self.build()
        envelope.write_text('{"claim":"second","output":"second"}')
        with self.assertRaisesRegex(ValueError, 'transport envelope changed'):
            self.build()
        env['ENTRY_CHAIN_RUNTIME_SHA256'] = transport()
        self.assertEqual(before, self.build())
        env['ENTRY_CHAIN_RUNTIME_SHA256']['semantic_dependencies'].append('missing')
        with self.assertRaisesRegex(ValueError, 'unresolved'):
            self.build()

    def test_scope_field_transport_preserves_the_key_across_admission(self):
        envelope = self.work / 'scope.json'
        envelope.write_text('{"aggregate":{"slice":"planned"}}')
        value = {'kind': 'transport', 'role': 'aggregate', 'encoding': 'json-field',
                 'selector': ['aggregate', 'slice'],
                 'binding': {'path': str(envelope), 'sha256': keys.file_digest(envelope),
                             'root_role': 'workspace'},
                 'semantic_projection': 'provider.py', 'semantic_dependencies': ['provider.py']}
        self.spec['recipe']['configuration']['environment']['ZESU_AGGREGATE_SLICE'] = value
        before = self.build()
        envelope.write_text('{"aggregate":{"slice":"actual-owned-slice"}}')
        value['binding']['sha256'] = keys.file_digest(envelope)
        self.assertEqual(before, self.build())
        envelope.write_text('{"aggregate":{"slice":"actual-owned-slice","other":"value"}}')
        value['binding']['sha256'] = keys.file_digest(envelope)
        value['selector'] = ['aggregate', 'other']
        self.assertNotEqual(before, self.build())
        for selector in [[], ['absent'], ['aggregate']]:
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                value['selector'] = selector
                self.build()

    def test_derived_bytecode_does_not_change_keys(self):
        before = self.build()
        for relative in ['__pycache__/provider.cpython-312.pyc', 'provider.pyc',
                         '__pycache__/unrelated.data']:
            path = self.work / relative
            path.parent.mkdir(exist_ok=True)
            path.write_bytes(b'derived bytecode')
            name = 'derived:' + relative
            self.spec['files'].append({'id': name, 'kind': 'binary', 'path': str(path),
                                       'sha256': keys.file_digest(path), 'root_role': 'workspace'})
            self.spec['recipe']['dependencies'].append({'id': name, 'requires': ['provider.py']})
            self.spec['recipe']['dependencies'][0]['requires'].append(name)
            self.spec['recipe']['toolchain']['python_dependencies'].append(name)
            self.spec['recipe']['backend']['files'].append(name)
            self.assertEqual(before, self.build())
            path.write_bytes(b'changed derived bytecode')
            self.assertEqual(before, self.build())
            path.unlink()
            self.assertEqual(before, self.build())
        self.assertTrue(any(row['id'] == 'provider.py' for row in self.spec['files']))
        self.assertEqual(len(self.spec['files']), 3 + len(keys.without_python_bytecode(self.spec)['files']))

    def test_unchanged_closed_observation_hits_without_search(self):
        key = cache.build_key(self.spec, key_function=keys.normalize)
        state = self.work / 'state.json'
        state.write_text(json.dumps({'goals': [], 'stack': [], 'shelf': [], 'given_up': [],
                                    'kernel_groups': {'goals': [], 'stack': [], 'shelf': [], 'given_up': []}}))
        obj = self.work / 'Proof.vo'
        obj.write_bytes(b'controlled checked-object fixture')
        result = {'block': '800d0000', 'phase': 'native', 'success': True, 'status': 'passed',
                  'complete_state': {'path': str(state), 'sha256': keys.file_digest(state),
                                     'state_source': 'successful_command_returned_state'},
                  'group_counts': {'active': 0, 'focus_frames': 0, 'frame_goals': 0, 'shelves': 0, 'given_up': 0},
                  'native_receipts': {'block': {'compile_file_success': True, 'verification_method': 'module_m',
                                                'assumptions': [], 'object': str(obj), 'object_sha256': keys.file_digest(obj),
                                                'source': str(self.work / 'Proof.v'),
                                                'source_sha256': keys.file_digest(self.work / 'Proof.v')}}}
        result_file = self.work / 'RESULT.json'
        result_file.write_text(json.dumps(result))
        cache_dir = self.root / 'cache'
        cache.store(cache_dir, key, result_file)
        def kernel_check(hit):
            return {'success': True, 'method': 'coqchk', 'checked_key': hit['key'],
                    'recursive': True, 'admitted_modules': []}
        hit = cache.lookup(cache_dir, cache.build_key(self.spec, key_function=keys.normalize),
                           verify_closed=kernel_check)
        self.assertEqual(hit['key'], self.build()['attempt_key'])
        self.assertEqual(hit['fresh_search_cpu_seconds'], 0)
        self.assertEqual(hit['cache_status'], 'cached')
        other_cache = self.root / 'wrong-source-cache'
        result['native_receipts']['block']['source_sha256'] = '1' * 64
        result_file.write_text(json.dumps(result))
        with self.assertRaisesRegex(ValueError, 'verified source'):
            cache.store(other_cache, key, result_file)


if __name__ == '__main__':
    unittest.main()
