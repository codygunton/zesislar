"""Exercise both production constructor sites with the governing profile."""
import ast
import hashlib
import inspect
import json
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch
import os
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE / 'code'), str(HERE)]
import scratch
import stage1_runtime
import supplier_resolution_cache as cache
from entry_chain import binding


class PreparationResolutionCache(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.workspace = self.root / 'workspace'
        self.library = self.workspace / 'library'
        self.library.mkdir(parents=True)
        self.source = self.library / 'Alpha.v'
        self.source.write_text('Definition alpha := 0.\n')
        self.source.with_suffix('.vo').write_bytes(b'nonproof object fixture')
        self.supplier = self.root / 'SUPPLIER.json'
        self.supplier.write_text('{"validation_only_test_data":true}\n')
        self.profile = self.root / 'PROFILE.json'
        self.profile.write_text(json.dumps({'supplier_ready': binding(self.supplier)}))
        self.flags = ['-Q', str(self.library), 'Example']
        self.addCleanup(patch.stopall)
        patch.object(cache, 'CACHE_ROOT', self.root / 'cache').start()

    def construct(self, owner, names):
        tree = ast.parse(inspect.getsource(owner))
        node = next(node for node in ast.walk(tree) if isinstance(node, ast.Assign)
                    and any(isinstance(target, ast.Name) and target.id == 'installed' for target in node.targets)
                    and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name)
                    and node.value.func.id == 'InstalledMappings')
        exec(compile(ast.Module(body=[node], type_ignores=[]), inspect.getsourcefile(owner), 'exec'), names)
        return names['installed']

    def scratch_constructor(self, *, profile=None, inherited=None):
        source = self.root / 'old-workspace'
        flags = [word.replace(str(self.workspace), str(source)) for word in self.flags]
        return self.construct(scratch.prepare, dict(vars(scratch),
            a=SimpleNamespace(admission_profile=profile), source=source, workspace=self.workspace,
            c={'physical_flags': flags, 'admission_profile': inherited}, out=self.root / 'prepare'))

    def stage_constructor(self, profile):
        return self.construct(stage1_runtime.build_collection, dict(vars(stage1_runtime),
            config={'admission_profile': profile}, runtime={'physical_flags': self.flags},
            out=self.root / 'stage1'))

    def test_prepare_uses_selected_profile_and_exact_relocated_flags(self):
        resolver = self.scratch_constructor(profile=self.profile, inherited={'path': 'unused', 'sha256': 'bad'})
        self.assertEqual(resolver.shared_cache.supplier, binding(self.supplier))
        self.assertEqual(resolver.flags, ['-boot', '-dyndep', 'no', *self.flags])
        self.assertEqual(resolver.receipt_dir, self.root / 'prepare/IMPORT-RESOLUTION')

    def test_prepare_inherited_profile_remains_bound(self):
        resolver = self.scratch_constructor(inherited=binding(self.profile))
        self.assertEqual(resolver.shared_cache.supplier, binding(self.supplier))

    def test_stage1_preserves_explicit_resolver_flags_and_receipts(self):
        resolver = self.stage_constructor(binding(self.profile))
        self.assertEqual(resolver.shared_cache.supplier, binding(self.supplier))
        self.assertEqual(resolver.coqdep, stage1_runtime.OPAM / 'bin/coqdep')
        self.assertEqual(resolver.flags, ['-boot', '-dyndep', 'no', *self.flags])
        self.assertEqual(resolver.receipt_dir, self.root / 'stage1/prospective/import-resolution')

    def test_both_sites_share_answers_with_exact_request_origin(self):
        origin = self.root / 'Consumer.v'
        origin.write_text('From Example Require Import Alpha.\n')
        resolvers = [self.scratch_constructor(profile=self.profile), self.stage_constructor(binding(self.profile))]
        for resolver in resolvers:
            resolver.register_source(origin.read_text(), origin)
            self.assertEqual(resolver.resolve('Example.Alpha', origin=origin), self.source)
        self.assertEqual(resolvers[0].shared_cache.counters['coqdep_invocations'], 1)
        self.assertEqual(resolvers[1].shared_cache.counters['coqdep_invocations'], 0)
        self.assertEqual(resolvers[1].shared_cache.counters['cache_hits'], 1)
        self.assertEqual(resolvers[1].source_records[str(origin)]['source'], binding(origin))

    def test_missing_supplier_preserves_uncached_resolution(self):
        self.assertIsNone(self.scratch_constructor().shared_cache)
        self.assertIsNone(self.stage_constructor(None).shared_cache)
        self.profile.write_text('{}')
        self.assertIsNone(self.scratch_constructor(profile=self.profile).shared_cache)
        self.assertIsNone(self.stage_constructor(binding(self.profile)).shared_cache)

    def test_changed_bound_profile_refuses(self):
        original = binding(self.profile)
        self.profile.write_text('{}')
        with self.assertRaisesRegex(ValueError, 'chain input changed'):
            self.stage_constructor(original)
        with self.assertRaisesRegex(ValueError, 'chain input changed'):
            self.scratch_constructor(inherited=original)

    def test_cache_wiring_does_not_call_supplier_validation(self):
        with patch('supplier_ready.validate', side_effect=AssertionError('unexpected full validation')):
            self.scratch_constructor(profile=self.profile)
            self.stage_constructor(binding(self.profile))
