"""Check the combined barrier without a Rocq server or native primary."""
from contextlib import asynccontextmanager
from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / 'block'))
import launch_entries as E
import launch_preflight as L
from tools import test_launch_resources as resource_fixtures


class LaunchTests(unittest.IsolatedAsyncioTestCase):
    def setUp(self):
        self.fixture = resource_fixtures.ResourceTests('test_complete_resource_probe_keeps_original_and_owned_closure')
        self.fixture.setUp()
        self.addCleanup(self.fixture.temporary.cleanup)
        self.root = self.fixture.root
        self.rows = [{'entry': self.fixture.entry, 'resource': self.fixture.resource}]
        self.manifest = self.root/'MANIFEST.json'

    def write_manifest(self):
        self.manifest.write_text(json.dumps({'schema': 1, 'workspace': str(self.root),
                                            'function': 'test.function', 'rows': self.rows}))
        return self.manifest

    async def check(self):
        with patch.object(E, 'process_identity', side_effect=self.fixture.identity):
            return await L.check_launch(self.write_manifest(), self.root/'launch', self.fixture.factory)

    def release(self):
        return L.verify_release(E.file_reference(self.root/'launch/REPORT.json'), self.root,
                                {row['entry']['id']: row['resource'] for row in self.rows})

    def rewrite(self, name, mutate):
        path = self.root/'launch'/name
        value = json.loads(path.read_bytes())
        mutate(value)
        path.write_text(json.dumps(value))
        if name != 'REPORT.json':
            parent = self.root/'launch/REPORT.json'
            top = json.loads(parent.read_bytes())
            top[name.split('/')[0]] = E.file_reference(path)
            parent.write_text(json.dumps(top))

    async def test_both_stages_pass_before_release(self):
        result = await self.check()
        self.assertTrue(result['passed'])
        self.assertTrue(self.release()['passed'])
        self.assertEqual(len(self.fixture.opened), 2)
        self.assertTrue((self.root/'launch/declarations/REPORT.json').is_file())
        self.assertTrue((self.root/'launch/resources/REPORT.json').is_file())
        self.assertFalse(any(tool == 'rocq_check' and 'zesu_block' in args['body']
                             for tool, args in self.fixture.calls))

    async def test_declaration_failure_starts_no_resource_session(self):
        self.fixture.behavior['refuse_start'] = True
        result = await self.check()
        self.assertFalse(result['passed'])
        self.assertIsNone(result['resources'])
        self.assertEqual(len(self.fixture.opened), 1)
        self.assertFalse(any(tool == 'rocq_check' for tool, _ in self.fixture.calls))
        with self.assertRaises(ValueError): self.release()

    async def test_resource_failure_blocks_release_after_declaration_success(self):
        self.fixture.behavior['refuse'] = 'lookup-bound'
        result = await self.check()
        self.assertFalse(result['passed'])
        self.assertIsNotNone(result['resources'])
        raw = sorted((self.root/'launch/resources/block_1000/calls').glob('*-rocq_check-raw.json'))[-1]
        self.assertIn('lookup-bound', json.loads(raw.read_bytes())['structuredContent']['error'])
        with self.assertRaises(ValueError): self.release()

    async def test_invalid_later_map_starts_no_session(self):
        bad = deepcopy(self.rows[0]);bad['entry']['id'] = 'later';bad['resource']['pc'] = '0x1004'
        self.rows.append(bad)
        with self.assertRaisesRegex(ValueError, 'differs from the primary'):
            await self.check()
        self.assertEqual(self.fixture.opened, [])

    async def test_later_resource_failure_blocks_the_complete_set(self):
        second = deepcopy(self.rows[0]);second['entry']['id'] = 'later';self.rows.append(second)
        factory = self.fixture.factory
        @asynccontextmanager
        async def select(directory):
            if directory.parent.name == 'resources' and directory.name == 'later':
                self.fixture.behavior['refuse'] = 'lookup-bound'
            async with factory(directory) as session: yield session
        with patch.object(E, 'process_identity', side_effect=self.fixture.identity):
            result = await L.check_launch(self.write_manifest(), self.root/'launch', select)
        self.assertFalse(result['passed'])
        self.assertEqual(len(self.fixture.opened), 4)
        with self.assertRaises(ValueError): self.release()

    async def test_worker_rejects_a_declaration_only_receipt(self):
        await self.check()
        self.rewrite('REPORT.json', lambda v: v.update(resources=None, passed=True))
        with self.assertRaises(ValueError): self.release()

    async def test_worker_rejects_a_forged_success_over_failed_resources(self):
        self.fixture.behavior['refuse'] = 'lookup'
        await self.check()
        self.rewrite('REPORT.json', lambda v: v.update(passed=True))
        with self.assertRaisesRegex(ValueError, 'incomplete or refused'): self.release()

    async def test_worker_rejects_substituted_resource_declarations(self):
        await self.check()
        self.rewrite('resources/REPORT.json', lambda v: v['declarations']['binding'].update(sha256='0'*64))
        with self.assertRaisesRegex(ValueError, 'different declarations'): self.release()

    async def test_worker_rejects_substituted_selected_instruction(self):
        await self.check()
        self.rewrite('resources/REPORT.json', lambda v: v['entries'][0].update(expected_instruction='Other.a1000'))
        with self.assertRaisesRegex(ValueError, 'different instruction'): self.release()

    async def test_worker_rejects_missing_membership_export(self):
        await self.check()
        self.rewrite('resources/REPORT.json', lambda v: v['entries'][0]['exports'].pop(7))
        with self.assertRaisesRegex(ValueError, 'required structural stage'): self.release()

    async def test_worker_rejects_index_mutation(self):
        await self.check()
        self.fixture.index.write_text('changed index')
        with self.assertRaises(ValueError): self.release()

    async def test_worker_rejects_changed_diagnostic_source(self):
        result = await self.check()
        resource = json.loads(Path(result['resources']['path']).read_bytes())
        Path(resource['entries'][0]['source']['binding']['path']).write_text('changed diagnostic')
        with self.assertRaises(ValueError): self.release()

    async def test_worker_rejects_changed_complete_export(self):
        result = await self.check()
        resource = json.loads(Path(result['resources']['path']).read_bytes())
        Path(resource['entries'][0]['exports'][-1]['export']['binding']['path']).write_text('{}')
        with self.assertRaises(ValueError): self.release()

    async def test_worker_rejects_boolean_stage_schema(self):
        await self.check()
        self.rewrite('resources/REPORT.json', lambda v: v.update(schema=True))
        with self.assertRaises(ValueError): self.release()

    async def test_receipt_binds_exact_manifest_function_and_entry(self):
        result = await self.check()
        self.assertEqual(result['function'], 'test.function')
        self.assertEqual(result['workspace'], str(self.root))
        self.assertEqual(result['manifest']['binding'], E.file_reference(self.manifest))
        self.assertEqual(result['entries'][0]['id'], self.rows[0]['entry']['id'])

    async def test_worker_rejects_changed_manifest(self):
        await self.check()
        self.manifest.write_text('{}')
        with self.assertRaises(ValueError): self.release()

    async def test_worker_rejects_substituted_function(self):
        await self.check()
        self.rewrite('REPORT.json', lambda v: v.update(function='other.function'))
        with self.assertRaisesRegex(ValueError, 'manifest or function'): self.release()

    async def test_worker_rejects_missing_owned_closure(self):
        await self.check()
        self.rewrite('resources/REPORT.json', lambda v: v['entries'][0].update(owned_pet_exited=False))
        with self.assertRaises(ValueError): self.release()


if __name__ == '__main__':
    unittest.main()
