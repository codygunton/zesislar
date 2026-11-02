from pathlib import Path
import json
import tempfile
import unittest

import scratch
from entry_chain import binding
from entry_chain_stage import invalidation
from object_imports import compatibility, normalized_flags, require_reuse


class ObjectImportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.old = self.root / 'old'
        self.current = self.root / 'current'
        self.old.mkdir()
        self.current.mkdir()
        self.compiler = self.root / 'coqc'
        self.compiler.write_bytes(b'pinned compiler fixture')
        self.compiler = binding(self.compiler)
        self.modules, self.edges, self.receipts = {}, [], {}
        self.flags = ['-Q', str(self.current), 'ZesuSsz']

    def save(self, name, data):
        path = self.root / name
        path.write_text(json.dumps(data))
        return binding(path)

    def module(self, name):
        relative = Path(*name.removeprefix('ZesuSsz.').split('.')).with_suffix('.v')
        self.modules[name] = str(relative)
        for workspace in [self.old, self.current]:
            source = workspace / relative
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text('(* Exact unchanged source fixture. *)\n')
            source.with_suffix('.vo').write_bytes(('object:' + name).encode())

    def record(self, name, dependencies):
        source = self.old / self.modules[name]
        flags = ['-Q', str(self.old), 'ZesuSsz']
        snapshot = self.save(name + '-snapshot.json', {'immutable': True})
        imports = [{'module': dependency,
                    'object': binding((self.old / self.modules[dependency]).with_suffix('.vo'))}
                   for dependency in dependencies]
        validation = self.save(name + '-validation.json', {
            'snapshot': snapshot, 'directly_hashed_inputs': [row['object'] for row in imports]})
        inputs = self.save(name + '-input.json', {
            'source': binding(source), 'compiler': self.compiler, 'owned_workspace': str(self.old),
            'physical_argv': [self.compiler['path'], *flags, str(source)],
            'validation': {'snapshot': snapshot}})
        physical = self.save(name + '-physical.json', {
            'input': inputs, 'input_validation': validation, 'returncode': 0,
            'output_capture': {'complete': True}, 'output_validation': {'success': True},
            'compiler_outputs': {'object': {'binding': binding(source.with_suffix('.vo'))}},
            'physical_argv': [self.compiler['path'], *flags, str(source)]})
        self.receipts[name] = self.save(name + '-receipt.json', {
            'source': binding(source), 'object': binding(source.with_suffix('.vo')),
            'compiler': self.compiler, 'normalized_flags': flags, 'snapshot': snapshot,
            'successful_compilation': True, 'tool_result': {'success': True},
            'physical_result': physical, 'import_provenance': {
                'schema': 'entry-chain.object-imports.v1', 'module': name,
                'owned_workspace': str(self.old), 'compiler': self.compiler,
                'normalized_flags': normalized_flags(flags, self.old),
                'validation': validation, 'imported_objects': imports}})

    def check(self, target):
        return compatibility([target], self.edges, self.modules, self.current,
                             self.receipts, self.compiler, self.flags)

    def pair(self, consumer, dependency):
        for name in [consumer, dependency]:
            self.module(name)
        self.edges.append({'from': consumer, 'to': dependency})
        self.record(dependency, [])
        self.record(consumer, [dependency])

    def test_matching_import_hashes_allow_owned_relocation(self):
        owner, dependency = 'ZesuSsz.Automation.Switches.ReturnBundle', 'ZesuSsz.Automation.PureFacts'
        self.pair(owner, dependency)
        result = self.check(owner)
        self.assertEqual(result['rebuild_modules'], [])
        self.assertEqual(set(result['compatible_owned_modules']), {owner, dependency})

    def test_exact_reported_import_regressions_rebuild_unchanged_sources(self):
        pairs = [('ZesuSsz.Automation.Switches.ReturnBundle', 'ZesuSsz.Automation.PureFacts'),
                 ('ZesuSsz.Automation.Switches.InstructionLookup', 'ZesuSsz.Automation.PureFacts'),
                 ('ZesuSsz.Contracts.DecodeItemReturnExitResources', 'ZesuSsz.Automation.Calls')]
        for owner, dependency in pairs:
            with self.subTest(owner=owner):
                self.modules, self.edges, self.receipts = {}, [], {}
                self.pair(owner, dependency)
                before = binding(self.current / self.modules[owner])['sha256']
                (self.current / self.modules[dependency]).with_suffix('.vo').write_bytes(b'changed dependency')
                result = self.check(owner)
                self.assertIn(owner, result['rebuild_modules'])
                self.assertIn(dependency, next(row['reason'] for row in result['rebuild'] if row['module'] == owner))
                plan = invalidation(self.edges, result['rebuild_modules'], ['Native'])
                self.assertIn(owner, plan['invalidated_modules'])
                self.assertEqual(binding(self.current / self.modules[owner])['sha256'], before)

    def test_unknown_inherited_object_requires_source_compilation(self):
        owner = 'ZesuSsz.Automation.Switches.ReturnBundle'
        self.module(owner)
        result = self.check(owner)
        self.assertEqual(result['rebuild_modules'], [owner])
        self.assertEqual(invalidation([], result['rebuild_modules'], [owner])['ordered_required'], [owner])

    def test_legacy_receipt_without_import_hashes_is_unknown(self):
        owner = 'ZesuSsz.Automation.Switches.ReturnBundle'
        self.module(owner)
        self.record(owner, [])
        path = Path(self.receipts[owner]['path'])
        data = json.loads(path.read_text())
        del data['import_provenance']
        self.receipts[owner] = self.save(path.name, data)
        self.assertEqual(self.check(owner)['rebuild_modules'], [owner])

    def test_source_and_object_hashes_alone_do_not_authenticate_imports(self):
        owner, dependency = 'ZesuSsz.Automation.Switches.ReturnBundle', 'ZesuSsz.Automation.PureFacts'
        self.pair(owner, dependency)
        data = json.loads(Path(self.receipts[owner]['path']).read_text())
        data['import_provenance']['imported_objects'] = []
        self.receipts[owner] = self.save(owner + '-receipt.json', data)
        self.assertIn(owner, self.check(owner)['rebuild_modules'])

    def test_changed_validation_report_refuses_reuse(self):
        owner = 'ZesuSsz.Automation.Switches.ReturnBundle'
        self.module(owner)
        self.record(owner, [])
        (self.root / (owner + '-validation.json')).write_text('{}')
        self.assertEqual(self.check(owner)['rebuild_modules'], [owner])

    def test_other_flags_or_compiler_refuse_reuse(self):
        owner = 'ZesuSsz.Automation.Switches.ReturnBundle'
        self.module(owner)
        self.record(owner, [])
        self.flags.append('-w')
        self.assertEqual(self.check(owner)['rebuild_modules'], [owner])
        self.flags.pop()
        self.compiler = dict(self.compiler, sha256='0' * 64)
        self.assertEqual(self.check(owner)['rebuild_modules'], [owner])

    def test_missing_objects_stay_with_the_existing_missing_object_planner(self):
        owner = 'ZesuSsz.Automation.Switches.ReturnBundle'
        self.module(owner)
        (self.current / self.modules[owner]).with_suffix('.vo').unlink()
        self.assertEqual(self.check(owner)['rebuild_modules'], [])
        self.assertEqual(scratch.missing_prerequisite_objects([owner], {}, self.modules, self.current), [owner])

    def test_stage_refuses_unplanned_consumer_of_scheduled_dependency(self):
        owner, dependency = 'ZesuSsz.Automation.Switches.ReturnBundle', 'ZesuSsz.Automation.PureFacts'
        self.pair(owner, dependency)
        result = compatibility([owner], self.edges, self.modules, self.current,
                               self.receipts, self.compiler, self.flags, planned=[dependency])
        self.assertEqual(result['rebuild_modules'], [owner])
        result = compatibility([owner], self.edges, self.modules, self.current,
                               self.receipts, self.compiler, self.flags, planned=[dependency, owner])
        self.assertEqual(result['rebuild_modules'], [])

    def test_transitive_import_change_invalidates_unchanged_intermediate(self):
        top, middle, leaf = ['ZesuSsz.' + name for name in ['Top', 'Middle', 'Leaf']]
        for name in [top, middle, leaf]:
            self.module(name)
        self.edges = [{'from': top, 'to': middle}, {'from': middle, 'to': leaf}]
        self.record(leaf, [])
        self.record(middle, [leaf])
        self.record(top, [middle, leaf])
        (self.current / self.modules[leaf]).with_suffix('.vo').write_bytes(b'changed leaf')
        self.assertEqual(set(self.check(top)['rebuild_modules']), {top, middle, leaf})

    def test_wrong_module_or_forged_import_hash_refuses(self):
        owner, dependency = 'ZesuSsz.Automation.Switches.ReturnBundle', 'ZesuSsz.Automation.PureFacts'
        self.pair(owner, dependency)
        data = json.loads(Path(self.receipts[owner]['path']).read_text())
        data['import_provenance']['module'] = dependency
        self.receipts[owner] = self.save(owner + '-receipt.json', data)
        self.assertIn(owner, self.check(owner)['rebuild_modules'])
        data['import_provenance']['module'] = owner
        data['import_provenance']['imported_objects'][0]['object']['sha256'] = '0' * 64
        self.receipts[owner] = self.save(owner + '-receipt.json', data)
        self.assertIn(owner, self.check(owner)['rebuild_modules'])

    def test_pinned_external_objects_remain_compiler_inputs(self):
        owner, dependency = 'ZesuSsz.Automation.Switches.ReturnBundle', 'Coq.ZArith.BinInt'
        self.module(owner)
        self.record(owner, [])
        external = self.root / 'installed/BinInt.v'
        external.parent.mkdir()
        external.write_text('(* Pinned installed source. *)')
        external.with_suffix('.vo').write_bytes(b'installed compiler input')
        self.modules[dependency] = str(external)
        self.edges.append({'from': owner, 'to': dependency})
        self.assertEqual(self.check(owner)['rebuild_modules'], [])

    def stage(self, owner, planned):
        config = {'cache_import_graph': self.save('graph.json', {'import_edges': self.edges}),
                  'object_imports': self.receipts, 'jobs': [{'target': {'module': owner}}]}
        runtime = {'module_files': self.modules, 'ordered_modules': planned,
                   'physical_compiler': self.compiler, 'physical_flags': self.flags}
        return require_reuse(config, runtime, self.current)

    def test_final_stage_accepts_matching_retained_objects(self):
        owner, dependency = 'ZesuSsz.Automation.Switches.ReturnBundle', 'ZesuSsz.Automation.PureFacts'
        self.pair(owner, dependency)
        self.assertEqual(self.stage(owner, [])['rebuild_modules'], [])

    def test_final_stage_refuses_unknown_inherited_objects(self):
        owner = 'ZesuSsz.Automation.Switches.ReturnBundle'
        self.module(owner)
        with self.assertRaisesRegex(ValueError, 'staged plan must rebuild'):
            self.stage(owner, [])
        self.assertEqual(self.stage(owner, [owner])['rebuild_modules'], [])

    def test_final_stage_refuses_omitted_dependent_recompile(self):
        owner, dependency = 'ZesuSsz.Automation.Switches.ReturnBundle', 'ZesuSsz.Automation.PureFacts'
        self.pair(owner, dependency)
        with self.assertRaisesRegex(ValueError, 'scheduled source compilation'):
            self.stage(owner, [dependency])
        self.assertEqual(self.stage(owner, [dependency, owner])['rebuild_modules'], [])


if __name__ == '__main__':
    unittest.main()
