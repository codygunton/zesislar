"""Check the shared harness without starting a prover or admission request."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[3]
HARNESS = ROOT / 'tools/block/harness'
sys.path[:0] = [str(ROOT), str(HARNESS / 'code'), str(HARNESS), str(ROOT / 'tools/block')]
from tools.block import check_export_scopes, render_support
import scratch
import scratch_limits
import harness_commit
import transport_mapping
import binding_cache
import memory_policy
import supplier_release


class SharedHarnessTests(unittest.TestCase):
    def test_second_target_and_generated_dependencies_are_checked(self):
        with tempfile.TemporaryDirectory() as directory:
            workspace = Path(directory)
            graph = {'First': {'Shared'}, 'Second': {'SecondOwner'},
                     'Generated': {'GeneratedOwner'}}
            modules = {name: name + '.v' for name in
                       ['First', 'Second', 'Shared', 'SecondOwner', 'Generated', 'GeneratedOwner']}
            for name in ['Shared', 'First', 'Second', 'Generated']:
                (workspace / (name + '.vo')).write_bytes(b'object')
            missing = scratch.missing_prerequisite_objects(
                ['First', 'Second', 'Generated'], graph, modules, workspace)
            self.assertEqual(set(missing), {'SecondOwner', 'GeneratedOwner'})

    def test_actual_headers_restore_omitted_edges_for_every_target(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = {'First': 'Require Import Shared.',
                       'Second': 'Require Import Generated.',
                       'Generated': 'Require Import MissingOwner.',
                       'Shared': '', 'MissingOwner': ''}
            modules = {name: name + '.v' for name in sources}
            for name, source in sources.items():
                (root / modules[name]).write_text(source)
            class Resolver:
                def register_source(self, *args): pass
            edges = scratch.reconcile_import_closure(
                ['First', 'Second', 'Generated'], [], modules, root, Resolver())
            self.assertEqual({(row['from'], row['to']) for row in edges},
                             {('First', 'Shared'), ('Second', 'Generated'),
                              ('Generated', 'MissingOwner')})
            (root / modules['MissingOwner']).unlink()
            with self.assertRaisesRegex(ValueError, 'closure source is absent'):
                scratch.reconcile_import_closure(['Second'], edges, modules, root, Resolver())

    def test_unchanged_header_uses_pinned_canonical_resolution(self):
        text = 'From Coq Require Import List.'
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'Consumer.v'
            source.write_text(text)
            class Resolver:
                def register_source(inner, actual, origin):
                    self.assertEqual((actual, origin), (text, source))
                def resolution(inner, name, *, origin):
                    self.assertEqual((name, origin), ('Coq.List', source))
                    return {'canonical': 'Coq.Lists.List'}
            self.assertEqual(scratch.canonical_edges('A', text, text, [], {}, Resolver(), source),
                             [{'from': 'A', 'to': 'Coq.Lists.List'}])

    def test_setup_and_compile_have_no_cpu_stop(self):
        for phase in ['prerequisites', 'native']:
            self.assertIsNone(scratch_limits.stop_reason(100000, 1, 1, phase=phase))

    def test_search_stop_still_uses_search_origin(self):
        self.assertEqual(scratch_limits.stop_reason(
            17200, 1, 1, origin_cpu=10000), 'external_CPU_stop')
        self.assertIsNone(scratch_limits.stop_reason(17199, 1, 1, origin_cpu=10000))

    def test_actual_consumers_pass_static_commit_time_audit(self):
        reports = [transport_mapping.audit(HARNESS / 'code' / name)
                   for name in ['entry_chain_provider.py', 'entry_chain_compiler.py',
                                'entry_chain_resources.py']]
        fields = {row['field'] for report in reports for row in report['field_reads']}
        self.assertTrue(transport_mapping.assert_covered(
            reports, {name: transport_mapping.FIELD_MAPPING[name] for name in fields}))

    def test_launch_does_not_run_static_audit(self):
        source = (HARNESS / 'code/stage1_runtime.py').read_text()
        self.assertNotIn('transport_mapping.audit(', source)
        self.assertIn('runtime-semantic-projection.v1', source)

    def test_harness_has_no_private_implementation_import(self):
        for path in (HARNESS / 'code').rglob('*.py'):
            for line in path.read_text().splitlines():
                if 'sys.path' in line:
                    self.assertNotIn('/.worktrees/', line, str(path))
                    self.assertNotIn('/_build/', line, str(path))

    def test_wrong_or_dirty_commit_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            harness = root / 'tools/block/harness'
            harness.mkdir(parents=True)
            (harness / 'sample.py').write_text('pass\n')
            def git(*args):
                return subprocess.run(['git', '-C', directory, *args], check=True,
                                      capture_output=True, text=True).stdout.strip()
            git('init', '-q')
            git('add', '.')
            git('-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', '-c', 'commit.gpgsign=false', '-c', 'core.hooksPath=/dev/null', 'commit', '-qm', 'fixture')
            commit = git('rev-parse', 'HEAD')
            self.assertEqual(harness_commit.pin(commit, root)['commit'], commit)
            with self.assertRaises(ValueError):
                harness_commit.pin('0' * 40, root)
            (harness / 'sample.py').write_text('changed\n')
            with self.assertRaises(ValueError):
                harness_commit.pin(commit, root)

    def test_owner_imports_follow_referenced_bound_symbols(self):
        imports = render_support.owner_imports('Definition x := Example.Owner.value.',
                                              [{'Example/Owner.v': 'hash', 'Unused.v': 'hash'}])
        self.assertEqual(imports, ['Require Import Example.Owner.'])

    def test_export_scope_lint_ignores_comments_and_accepts_local(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            p = root / 'ZesuSsz/Generated/Owner.v'
            p.parent.mkdir(parents=True)
            p.write_text('(* Open Scope ignored. *)\nLocal Open Scope string_scope.\n')
            self.assertEqual(check_export_scopes.violations(root), [])
            p.write_text('Open Scope string_scope.\n')
            self.assertEqual(len(check_export_scopes.violations(root)), 1)


class BindingCacheTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.path = self.root / 'input.v'
        self.path.write_bytes(b'first')
        binding_cache._DIGESTS.clear()

    def test_unchanged_identity_reuses_hash(self):
        with patch.object(binding_cache.hashlib, 'file_digest', wraps=binding_cache.hashlib.file_digest) as hashed:
            first = binding_cache.digest(self.path)
            self.assertEqual(binding_cache.digest(self.path), first)
            self.assertEqual(hashed.call_count, 1)

    def test_same_size_replacement_invalidates_cache(self):
        first = binding_cache.digest(self.path)
        replacement = self.root / 'replacement'
        replacement.write_bytes(b'other')
        replacement.replace(self.path)
        self.assertNotEqual(binding_cache.digest(self.path), first)

    def test_write_with_restored_mtime_invalidates_cache(self):
        first = binding_cache.digest(self.path)
        before = self.path.stat()
        self.path.write_bytes(b'other')
        os.utime(self.path, ns=(before.st_atime_ns, before.st_mtime_ns))
        self.assertNotEqual(binding_cache.digest(self.path), first)

    def test_permission_change_forces_hash(self):
        with patch.object(binding_cache.hashlib, 'file_digest', wraps=binding_cache.hashlib.file_digest) as hashed:
            binding_cache.digest(self.path)
            self.path.chmod(0o400)
            binding_cache.digest(self.path)
            self.assertEqual(hashed.call_count, 2)

    def test_symlink_change_invalidates_cache(self):
        second = self.root / 'second.v'
        second.write_bytes(b'other')
        link = self.root / 'input-link'
        link.symlink_to(self.path)
        first = binding_cache.digest(link)
        link.unlink()
        link.symlink_to(second)
        self.assertNotEqual(binding_cache.digest(link), first)

    def test_hashing_race_refuses(self):
        original = binding_cache.hashlib.file_digest
        def racing(stream, algorithm):
            result = original(stream, algorithm)
            self.path.write_bytes(b'other')
            return result
        with patch.object(binding_cache.hashlib, 'file_digest', side_effect=racing):
            with self.assertRaisesRegex(ValueError, 'changed during validation'):
                binding_cache.digest(self.path)

    def test_force_full_hash_ignores_cache(self):
        with patch.object(binding_cache.hashlib, 'file_digest', wraps=binding_cache.hashlib.file_digest) as hashed:
            binding_cache.digest(self.path)
            with binding_cache.force_hashing():
                binding_cache.digest(self.path)
            self.assertEqual(hashed.call_count, 2)

    def test_parent_alias_resolution_is_fresh_each_operation(self):
        a = self.root / 'a'; b = self.root / 'b'
        a.mkdir(); b.mkdir()
        (a / 'source.v').write_bytes(b'first')
        (b / 'source.v').write_bytes(b'other')
        alias = self.root / 'parent'
        alias.symlink_to(a)
        first = binding_cache.resolve_input(alias / 'source.v', {})
        alias.unlink(); alias.symlink_to(b)
        second = binding_cache.resolve_input(alias / 'source.v', {})
        self.assertNotEqual(first, second)


class AuthorityRelocationTests(unittest.TestCase):
    def setUp(self):
        self.directory=tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root=Path(self.directory.name)
        self.allowed=self.root/'allowed';self.allowed.mkdir()
        self.source=self.allowed/'authority.json';self.source.write_text('{"cases":[]}\n')
        self.expected=scratch.binding(self.source)

    def test_identical_bytes_in_approved_root_pass(self):
        other=self.allowed/'relocated.json';other.write_bytes(self.source.read_bytes())
        self.assertTrue(memory_policy.relocated_authority(scratch.binding(other),self.expected))

    def test_changed_bytes_and_wrong_digest_refuse(self):
        other=self.allowed/'relocated.json';other.write_text('{ "cases": [] }\n')
        self.assertFalse(memory_policy.relocated_authority(scratch.binding(other),self.expected))
        row=scratch.binding(other);row['sha256']=self.expected['sha256']
        with self.assertRaises(ValueError):memory_policy.relocated_authority(row,self.expected)

    def test_outside_path_and_symlink_escape_refuse(self):
        outside=self.root/'outside.json';outside.write_bytes(self.source.read_bytes())
        for path in [outside,self.allowed/'alias.json']:
            if path.name=='alias.json':path.symlink_to(outside)
            with self.assertRaisesRegex(ValueError,'approved roots'):
                memory_policy.relocated_authority(scratch.binding(path),self.expected)


class BeforeStopTests(unittest.TestCase):
    def setUp(self):
        self.directory=tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root=Path(self.directory.name);(self.root/'native').mkdir()
        groups={'goals':[{'info':{'evar':1},'hyps':[],'ty':'SyntheticGoal'}],
                'stack':[],'shelf':[],'given_up':[]}
        state=dict(groups,kernel_groups=groups,
                   local_definition_export={'original_state_preserved':True})
        path=self.root/'state.json';scratch.save(path,state)
        export=dict(scratch.binding(path),success=True)
        scratch.save(self.root/'native/LAST-COMPLETED-STATE.json',
                     {'export':export,'state_source':'completed_checkpoint'})

    def test_complete_checkpoint_keeps_inflight_progress_unknown(self):
        value=scratch_limits.capture_before_stop(self.root)
        self.assertEqual(value['group_counts']['active'],1)
        self.assertEqual(value['state_source'],'completed_checkpoint')
        self.assertIsNone(value['current_internal_group_counts'])
        self.assertEqual(scratch.read_bound(value['residual'])['kernel_groups']['goals'][0]['ty'],
                         'SyntheticGoal')

    def test_missing_or_changed_checkpoint_remains_unknown(self):
        (self.root/'state.json').write_text('{}')
        value=scratch_limits.capture_before_stop(self.root)
        self.assertIsNone(value['group_counts'])
        self.assertIn('unavailable_reason',value)

    def test_actual_stop_exports_before_signal(self):
        from types import SimpleNamespace
        scratch.save(self.root/'BATCH-IDENTITY.json',{})
        sample={'CPU_seconds':7200,'raw_cpu_stat':{},'memory_current_bytes':1,
                'memory_peak_bytes':1,'memory_events':{}}
        accounting={'origin_cpu':0,'end_cpu':None,'search_active':True,
                    'search_CPU_seconds':7200,'setup_CPU_seconds':0}
        def stop(argv,**kwargs):
            value=json.loads((self.root/'BEFORE-STOP-STATE.json').read_text())
            self.assertEqual(value['group_counts']['active'],1)
            self.assertIsNone(value['current_internal_group_counts'])
            return SimpleNamespace(returncode=0,stdout='',stderr='')
        child=SimpleNamespace(poll=lambda:None,wait=lambda:143)
        with patch.object(scratch_limits,'exact_aggregate',return_value=self.root/'fake.slice'),\
             patch.object(scratch_limits,'sample_aggregate',return_value=sample),\
             patch.object(scratch_limits,'search_accounting',return_value=accounting),\
             patch.object(scratch_limits.subprocess,'run',side_effect=stop),\
             patch.object(scratch_limits,'finish_growth',return_value=143):
            self.assertEqual(scratch_limits.wait_with_limits(child,self.root,64*1024**3),143)


if __name__ == '__main__':
    unittest.main()
