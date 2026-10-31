"""Check shared coqdep answers without compiling or admitting a proof."""
import hashlib
import json
import multiprocessing
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import scratch
from installed_mappings import InstalledMappings
import supplier_resolution_cache as cache


def binding(path):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


class SupplierResolutionCacheTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.library = self.root / 'library'
        self.library.mkdir()
        self.flags = ['-Q', str(self.library), 'Example']
        self.supplier_path = self.root / 'SUPPLIER.json'
        self.supplier_path.write_text('{"fixture": true}\n')
        self.supplier = binding(self.supplier_path)
        self.addCleanup(patch.stopall)
        patch.object(cache, 'CACHE_ROOT', self.root / 'cache').start()
        self.source = self.module('Alpha.v')

    def module(self, name):
        path = self.library / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('Definition placeholder := 0.\n')
        path.with_suffix('.vo').write_bytes(b'object')
        return path

    def resolver(self, flags=None, supplier=None, coqdep=None):
        return InstalledMappings(self.flags if flags is None else flags,
                                 supplier=self.supplier if supplier is None else supplier,
                                 coqdep=coqdep)

    def events(self):
        root = cache.CACHE_ROOT / self.supplier['sha256']
        return [json.loads(line) for path in root.glob('events-*.jsonl')
                for line in path.read_text().splitlines()]

    def counts(self):
        rows = self.events()
        return {kind: sum(row['event'] == kind for row in rows)
                for kind in ['logical_lookups', 'cache_hits', 'cache_misses', 'coqdep_invocations']}

    def test_two_instances_share_exact_answer_and_actual_counters(self):
        self.assertEqual(self.resolver().resolve('Example.Alpha'), self.source)
        self.assertEqual(self.resolver().resolve('Example.Alpha'), self.source)
        self.assertEqual(self.counts(), dict(logical_lookups=2, cache_hits=1,
                                            cache_misses=1, coqdep_invocations=1))

    def test_same_instance_hit_rechecks_selected_object(self):
        resolver = self.resolver()
        resolver.resolve('Example.Alpha')
        self.source.with_suffix('.vo').write_bytes(b'new object')
        resolver.resolve('Example.Alpha')
        self.assertEqual(self.counts()['cache_hits'], 0)
        self.assertEqual(self.counts()['coqdep_invocations'], 2)

    def test_changed_selected_source_is_not_a_hit(self):
        self.resolver().resolve('Example.Alpha')
        self.source.write_text('Definition placeholder := 1.\n')
        self.resolver().resolve('Example.Alpha')
        self.assertEqual(self.counts()['cache_hits'], 0)

    def test_different_requesting_sources_do_not_share(self):
        for name in ['First.v', 'Second.v']:
            origin = self.root / name
            origin.write_text('From Example Require Import Alpha.\n')
            resolver = self.resolver()
            resolver.register_source(origin.read_text(), origin)
            resolver.resolve('Example.Alpha', origin=origin)
        self.assertEqual(self.counts()['coqdep_invocations'], 2)

    def test_changed_requesting_source_refuses_before_hit(self):
        origin = self.root / 'First.v'
        origin.write_text('From Example Require Import Alpha.\n')
        resolver = self.resolver()
        resolver.register_source(origin.read_text(), origin)
        resolver.resolve('Example.Alpha', origin=origin)
        origin.write_text('Require Import Example.Alpha.\n')
        with self.assertRaisesRegex(ValueError, 'request source changed'):
            resolver.resolve('Example.Alpha', origin=origin)
        self.assertEqual(self.counts()['cache_hits'], 0)

    def test_new_require_syntax_has_distinct_context(self):
        origin = self.root / 'First.v'
        for text in ['From Example Require Import Alpha.\n', 'Require Import Example.Alpha.\n']:
            origin.write_text(text)
            resolver = self.resolver()
            resolver.register_source(text, origin)
            resolver.resolve('Example.Alpha', origin=origin)
        self.assertEqual(self.counts()['coqdep_invocations'], 2)

    def test_sail_inside_hit_cannot_suppress_outside_refusal(self):
        flags = ['-Q', str(self.library), 'SailStdpp']
        inside = self.library / 'Current.v'
        outside = self.root / 'Outside.v'
        for path in [inside, outside]:
            path.write_text('Require Import Alpha.\n')
        resolver = self.resolver(flags=flags)
        resolver.register_source(inside.read_text(), inside)
        self.assertEqual(resolver.resolve('Alpha', origin=inside), self.source)
        resolver = self.resolver(flags=flags)
        resolver.register_source(inside.read_text(), inside)
        self.assertEqual(resolver.resolve('Alpha', origin=inside), self.source)
        resolver.register_source(outside.read_text(), outside)
        with self.assertRaisesRegex(ValueError, 'no actual installed mapping'):
            resolver.resolve('Alpha', origin=outside)
        self.assertEqual(self.counts()['cache_hits'], 1)
        self.assertEqual(self.counts()['coqdep_invocations'], 2)

    def test_added_source_only_shadow_cannot_use_old_answer(self):
        self.source.unlink()
        self.source.with_suffix('.vo').unlink()
        self.module('one/Alpha.v')
        origin = self.root / 'First.v'
        origin.write_text('From Example Require Import Alpha.\n')
        resolver = self.resolver()
        resolver.register_source(origin.read_text(), origin)
        resolver.resolve('Example.Alpha', origin=origin)
        shadow = self.library / 'two/Alpha.v'
        shadow.parent.mkdir()
        shadow.write_text('Definition placeholder := 2.\n')
        with self.assertRaises(ValueError):
            resolver.resolve('Example.Alpha', origin=origin)
        self.assertEqual(self.counts()['cache_hits'], 0)

    def test_added_object_shadow_cannot_use_old_answer(self):
        self.resolver().resolve('Example.Alpha')
        self.module('other/New.v')
        self.resolver().resolve('Example.Alpha')
        self.assertEqual(self.counts()['cache_hits'], 0)
        self.assertEqual(self.counts()['coqdep_invocations'], 2)

    def test_removed_object_cannot_use_old_answer(self):
        self.resolver().resolve('Example.Alpha')
        self.source.with_suffix('.vo').unlink()
        with self.assertRaises(ValueError):
            self.resolver().resolve('Example.Alpha')
        self.assertEqual(self.counts()['cache_hits'], 0)

    def test_symlink_retarget_changes_the_context(self):
        first, second = self.root / 'first.dat', self.root / 'second.dat'
        first.write_text(self.source.read_text())
        second.write_text(first.read_text())
        self.source.unlink()
        self.source.symlink_to(first)
        self.resolver().resolve('Example.Alpha')
        self.source.unlink()
        self.source.symlink_to(second)
        self.resolver().resolve('Example.Alpha')
        self.assertEqual(self.counts()['cache_hits'], 0)

    def test_directory_alias_keeps_the_strict_uncached_resolver(self):
        target = self.root / 'alias-target'
        target.mkdir()
        (self.library / 'alias').symlink_to(target, target_is_directory=True)
        self.resolver().resolve('Example.Alpha')
        self.resolver().resolve('Example.Alpha')
        self.assertEqual(self.counts()['cache_hits'], 0)
        self.assertEqual(self.counts()['coqdep_invocations'], 2)

    def test_ordered_flags_are_not_normalized(self):
        other = self.root / 'other'
        other.mkdir()
        flags = self.flags + ['-Q', str(other), 'Other']
        self.resolver(flags=flags).resolve('Example.Alpha')
        self.resolver(flags=flags[3:] + flags[:3]).resolve('Example.Alpha')
        self.assertEqual(self.counts()['coqdep_invocations'], 2)

    def test_different_workspace_roots_are_not_normalized(self):
        self.resolver().resolve('Example.Alpha')
        other = self.root / 'other'
        other.mkdir()
        source = other / 'Alpha.v'
        source.write_bytes(self.source.read_bytes())
        source.with_suffix('.vo').write_bytes(self.source.with_suffix('.vo').read_bytes())
        self.resolver(flags=['-Q', str(other), 'Example']).resolve('Example.Alpha')
        self.assertEqual(self.counts()['coqdep_invocations'], 2)

    def test_supplier_namespaces_remain_separate(self):
        self.resolver().resolve('Example.Alpha')
        other = self.root / 'OTHER.json'
        other.write_text('{"other":true}')
        resolver = self.resolver(supplier=binding(other))
        resolver.resolve('Example.Alpha')
        self.assertEqual(resolver.shared_cache.counters['coqdep_invocations'], 1)

    def test_changed_bound_supplier_refuses(self):
        resolver = self.resolver()
        resolver.resolve('Example.Alpha')
        self.supplier_path.write_text('{"fixture": false}')
        with self.assertRaisesRegex(ValueError, 'cache binding changed'):
            resolver.resolve('Example.Alpha')

    def test_changed_resolver_executable_cannot_hit(self):
        tool = self.root / 'coqdep'
        original = Path(os.environ['OPAM_SWITCH_PREFIX']) / 'bin/coqdep'
        tool.write_text('#!/bin/sh\nexec ' + str(original) + ' "$@"\n')
        tool.chmod(0o755)
        self.resolver(coqdep=tool).resolve('Example.Alpha')
        tool.write_text(tool.read_text() + '# changed executable\n')
        self.resolver(coqdep=tool).resolve('Example.Alpha')
        self.assertEqual(self.counts()['cache_hits'], 0)

    def test_changed_parser_identity_cannot_hit(self):
        self.resolver().resolve('Example.Alpha')
        original = cache.file_binding
        def changed(path):
            row = original(path)
            if Path(path).name == 'check_data_only_lemmas.py':
                row['sha256'] = '0' * 64
            return row
        with patch.object(cache, 'file_binding', side_effect=changed):
            self.resolver().resolve('Example.Alpha')
        self.assertEqual(self.counts()['cache_hits'], 0)

    def test_malformed_and_interrupted_records_do_not_supply_answers(self):
        self.resolver().resolve('Example.Alpha')
        root = cache.CACHE_ROOT / self.supplier['sha256']
        row = next(path for path in root.glob('*.json'))
        row.write_text('{')
        (root / 'incomplete.tmp').write_text('partial')
        self.resolver().resolve('Example.Alpha')
        self.assertEqual(self.counts()['cache_hits'], 0)
        self.assertEqual(self.counts()['coqdep_invocations'], 2)

    def test_changed_cached_pair_hash_is_not_a_hit(self):
        self.resolver().resolve('Example.Alpha')
        root = cache.CACHE_ROOT / self.supplier['sha256']
        path = next(root.glob('*.json'))
        row = json.loads(path.read_text())
        row['selected']['object']['sha256'] = '0' * 64
        path.write_text(json.dumps(row))
        self.resolver().resolve('Example.Alpha')
        self.assertEqual(self.counts()['cache_hits'], 0)
        self.assertEqual(self.counts()['coqdep_invocations'], 2)

    def test_spawn_failure_is_not_an_actual_invocation(self):
        with patch('installed_mappings.subprocess.Popen', side_effect=OSError('fixture spawn failure')):
            with self.assertRaisesRegex(OSError, 'fixture spawn failure'):
                self.resolver().resolve('Example.Alpha')
        self.assertEqual(self.counts()['logical_lookups'], 1)
        self.assertEqual(self.counts()['cache_misses'], 1)
        self.assertEqual(self.counts()['coqdep_invocations'], 0)

    def test_two_processes_issue_one_coqdep_query(self):
        context = multiprocessing.get_context('fork')
        ready = context.Barrier(2)
        def consume():
            ready.wait()
            self.resolver().resolve('Example.Alpha')
        processes = [context.Process(target=consume) for _ in range(2)]
        for process in processes:
            process.start()
        for process in processes:
            process.join(15)
            self.assertEqual(process.exitcode, 0)
        self.assertEqual(self.counts()['coqdep_invocations'], 1)
        self.assertEqual(self.counts()['cache_hits'], 1)

    def test_overlapping_roots_keep_the_same_pair(self):
        source = self.module('nested/Module.v')
        flags = self.flags + ['-Q', str(source.parent), 'Example.nested']
        for _ in range(2):
            self.assertEqual(self.resolver(flags=flags).resolve('Example.nested.Module'), source)
        self.assertEqual(self.counts()['cache_hits'], 1)

    def test_default_resolver_stays_uncached(self):
        resolver = InstalledMappings(self.flags)
        self.assertIsNone(resolver.shared_cache)
        self.assertEqual(resolver.resolve('Example.Alpha'), self.source)
        self.assertFalse((self.root / 'cache').exists())

    def test_tool_layout_stages_the_cache_dependency(self):
        layout = json.loads((Path(scratch.__file__).parent / 'TOOL-LAYOUT.json').read_text())
        self.assertEqual(layout['block/supplier_resolution_cache.py'], 'code/supplier_resolution_cache.py')


if __name__ == '__main__':
    unittest.main()
