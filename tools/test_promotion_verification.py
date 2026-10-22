"""Check exact statement extraction and mandatory verification failures."""
import asyncio
from contextlib import asynccontextmanager
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from types import ModuleType, SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / 'block'))
import promotion_verification as verification


class PromotionVerificationTests(unittest.TestCase):
    def test_retained_compile_requires_exact_source_and_private_object(self):
        with tempfile.TemporaryDirectory() as temp:
            source, artifact = Path(temp) / 'Source.v', Path(temp) / 'Source.vo'
            source.write_text('Lemma kept : True. Proof. exact I. Qed.')
            artifact.write_bytes(b'owned object')
            retained = {'source': str(source), 'source_sha256': verification.digest(source),
                        'private_artifact': str(artifact),
                        'private_artifact_sha256': verification.digest(artifact),
                        'compile_file': {'success': True}}
            self.assertEqual(verification.retained_compile_result(source, artifact, retained),
                             {'success': True})
            for field, value in [('source', str(source) + '.other'),
                                 ('source_sha256', 'wrong'),
                                 ('private_artifact', str(artifact) + '.other'),
                                 ('private_artifact_sha256', 'wrong'),
                                 ('compile_file', {'success': False})]:
                with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'identity differs'):
                    verification.retained_compile_result(source, artifact, {**retained, field: value})

    def test_changed_import_refreshes_transitive_prerequisites(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            modules = {
                'Changed': '',
                'Stable': '',
                'Composition': 'Require Import Changed Stable.\n',
                'NativeComposition': 'Require Import Composition.\n',
                'Consumer': 'Require Import NativeComposition Changed.\n',
            }
            for name, source in modules.items():
                (root / (name + '.v')).write_text(source)
            self.assertEqual(verification.compilation_sources(root,
                [root / 'Consumer.v', root / 'Changed.v']),
                [root / (name + '.v') for name in
                 ['Changed', 'Composition', 'NativeComposition', 'Consumer']])

    def test_import_cycle_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'A.v').write_text('Require Import B.\n')
            (root / 'B.v').write_text('Require Import A.\n')
            with self.assertRaisesRegex(ValueError, 'import graph contains a cycle'):
                verification.compilation_sources(root, [root / 'A.v'])

    def test_each_lemma_keeps_prior_scope_and_exact_header(self):
        source = 'Definition kept := 3.\nLemma first : kept = 3.\nProof. reflexivity. Qed.\nLemma second : True.\nProof. exact I. Qed.\n'
        checks = verification.statements(source, 0x800d6974)
        self.assertEqual([x[0] for x in checks], ['first', 'second'])
        self.assertEqual(checks[0][1], 'Definition kept := 3.\nLemma first : kept = 3.\n')
        self.assertTrue(checks[1][1].endswith('Lemma second : True.\n'))
        self.assertTrue(all(x[2] == source for x in checks))

    def test_multiline_proof_using_uses_exact_compiled_section_type(self):
        source = ('Section kept.\nContext (premise : True).\nLemma result : True.\n'
                  'Proof using\n  premise.\nexact premise. Qed.\nEnd kept.\n')
        self.assertEqual(verification.statements(source, 0x800d6b08, 'Project.Module'),
                         [('result', 'Require Import Project.Module.\nLemma result :\n'
                           '  ltac:(let statement := type of @Project.Module.result in exact statement).\n', source + '\nArguments result : clear implicits.\n')])

    def test_unused_section_context_is_not_added_to_expected_type(self):
        source = ('Section kept.\nContext (unused : False).\n'
                  'Lemma result : True.\nProof. exact I. Qed.\nEnd kept.\n')
        statement = verification.statements(source, 0x800d6b08, 'Project.Module')[0][1]
        self.assertNotIn('unused', statement)
        self.assertNotIn('False', statement)
        self.assertIn('type of @Project.Module.result', statement)
        proof = verification.statements(source, 0x800d6b08, 'Project.Module')[0][2]
        self.assertTrue(proof.startswith(source))
        self.assertTrue(proof.endswith('Arguments result : clear implicits.\n'))
        with self.assertRaisesRegex(ValueError, 'compiled logical module'):
            verification.statements(source, 0x800d6b08)

    def test_promoted_definition_gets_its_exact_table_signature(self):
        source = ('Require Import isla.riscv64.riscv64.\nSection promoted_block_bodies.\n'
                  'Context `{!islaG Sigma} `{!threadG}.\n'
                  'Definition decodeItemPromotedBody800d6974 :\n'
                  '  ⊢ block_table_pre table -∗ instr_body 0x800d6974 entry := native.\n'
                  'End promoted_block_bodies.\n')
        checks = verification.statements(source, 0x800d6974)
        self.assertEqual(len(checks), 1)
        self.assertIn('⊢ block_table_pre table -∗ instr_body 0x800d6974 entry.', checks[0][1])
        self.assertIn('exact decodeItemPromotedBody800d6974.', checks[0][2])

    def test_unchecked_module_shape_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'no supported statement'):
            verification.statements('Definition untyped := 1.', 0x800d6974)

    def test_other_function_definition_keeps_its_exact_table_signature(self):
        source = ('Require Import isla.riscv64.riscv64.\nSection promoted_block_bodies.\n'
                  'Context `{!islaG Sigma} `{!threadG}.\n'
                  'Definition freePromotedBody1000 :\n'
                  '  ⊢ block_table_pre freeTable -∗ instr_body 0x1000 freeEntry := native.\n'
                  'End promoted_block_bodies.\n')
        checks = verification.statements(source, 0x1000, name_prefix="free")
        self.assertEqual(len(checks), 1)
        self.assertIn('⊢ block_table_pre freeTable -∗ instr_body 0x1000 freeEntry.', checks[0][1])
        self.assertIn('exact freePromotedBody1000.', checks[0][2])
        with self.assertRaisesRegex(ValueError, 'no supported statement'):
            verification.statements(source, 0x1000)

    def test_source_artifact_detection_preserves_existing_objects(self):
        with tempfile.TemporaryDirectory() as temp:
            source = Path(temp) / 'Fixture.v'
            source.write_text('Lemma fixture : True. Proof. exact I. Qed.')
            verification.require_clean_source(source)
            for artifact in verification.source_artifacts(source):
                artifact.write_text('foreign retained bytes')
                with self.assertRaisesRegex(ValueError, 'source tree'):
                    verification.require_clean_source(source)
                self.assertEqual(artifact.read_text(), 'foreign retained bytes')
                artifact.unlink()
            verification.require_clean_source(source)

    def test_missing_pinned_environment_opens_no_transport(self):
        with patch.dict(os.environ, {}, clear=True), patch.object(verification.subprocess, 'run') as run:
            with self.assertRaisesRegex(ValueError, 'pinned opam'):
                verification.verify_generated(Path('/workspace'), [], 0x800d6974, '/unused')
        run.assert_not_called()

    def test_failed_subprocess_is_not_a_verified_result(self):
        with tempfile.TemporaryDirectory() as temp, \
             patch.dict(os.environ, {'OPAM_SWITCH_PREFIX': '/pinned'}), \
             patch.object(verification.shutil, 'which', return_value='/pinned/bin/pet'), \
             patch.object(verification.subprocess, 'run', side_effect=subprocess.CalledProcessError(1, ['MCP'])):
            with self.assertRaises(subprocess.CalledProcessError):
                verification.verify_generated(Path(temp), [], 0x800d6974, Path(temp) / 'verification')

    def test_failed_report_is_not_a_verified_result(self):
        with tempfile.TemporaryDirectory() as temp, \
             patch.dict(os.environ, {'OPAM_SWITCH_PREFIX': '/pinned'}), \
             patch.object(verification.shutil, 'which', return_value='/pinned/bin/pet'):
            directory = Path(temp) / 'verification'
            def emit_failure(*args, **kwargs):
                directory.mkdir()
                (directory / 'RESULT.json').write_text(json.dumps({'success': False}))
            with patch.object(verification.subprocess, 'run', side_effect=emit_failure), \
                 self.assertRaisesRegex(ValueError, 'failed verification'):
                verification.verify_generated(Path(temp), [], 0x800d6974, directory)


class LauncherSelectionTests(unittest.TestCase):
    def launchers(self, root):
        tools = root / 'tools'
        tools.mkdir()
        for name in ('rocq_mcp_guarded.sh', 'rocq_coqc_guarded.sh'):
            path = tools / name
            path.write_text('#!/bin/sh\nexit 0\n')
            path.chmod(0o755)
        return tools

    def test_default_bindings_keep_stock_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tools = self.launchers(root)
            bindings = verification.launcher_bindings(root)
            for label, name in [('mcp', 'rocq_mcp_guarded.sh'), ('compiler', 'rocq_coqc_guarded.sh')]:
                self.assertEqual(bindings[label]['path'], str(tools / name))
                self.assertEqual(bindings[label]['sha256'], verification.digest(tools / name))

    def test_override_keeps_declared_symlink_path_and_checks_changes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tools = self.launchers(root)
            selected = root / 'virtual-launcher'
            selected.symlink_to(tools / 'rocq_mcp_guarded.sh')
            bindings = verification.launcher_bindings(root, selected, tools / 'rocq_coqc_guarded.sh')
            self.assertEqual(bindings['mcp']['path'], str(selected))
            self.assertNotEqual(bindings['mcp']['path'], bindings['mcp']['resolved_path'])
            verification.unchanged_launchers(bindings)
            (tools / 'rocq_mcp_guarded.sh').write_text('#!/bin/sh\nexit 1\n')
            with self.assertRaisesRegex(ValueError, 'changed during verification'):
                verification.unchanged_launchers(bindings)

    def test_missing_and_nonexecutable_launchers_refuse_before_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tools = self.launchers(root)
            for selected in (root / 'missing', root / 'not-executable'):
                if selected.name == 'not-executable':
                    selected.write_text('#!/bin/sh\nexit 0\n')
                for label in ('mcp_launcher', 'compiler_launcher'):
                    with self.subTest(label=label, selected=selected), self.assertRaisesRegex(ValueError, 'missing or not executable'):
                        asyncio.run(verification.verify(root, [], 0, root / 'unused', **{label: selected}))
                    self.assertFalse((root / 'unused').exists())

    def fake_verification(self, root, overrides=False, wrong_health=False):
        tools = self.launchers(root)
        private = root / '_build/default'
        private.mkdir(parents=True)
        source = root / 'Fixture.v'
        source.write_text('Lemma checked : True.\nProof. exact I. Qed.\n')
        selected = {}
        if overrides:
            for label in ('mcp', 'compiler'):
                path = root / (label + '-override.sh')
                path.write_text('#!/bin/sh\nexit 0\n')
                path.chmod(0o755)
                selected[label + '_launcher'] = path
        seen, calls, active = [], [], [False]
        def parameters(**values):
            seen.append(values)
            return SimpleNamespace(**values)
        @asynccontextmanager
        async def transport(values):
            active[0] = True
            try:
                yield (None, None)
            finally:
                active[0] = False
        class Session:
            async def __aenter__(self):
                return self
            async def __aexit__(self, *args):
                return False
            async def initialize(self):
                return None
            async def call_tool(self, tool, arguments):
                calls.append(tool)
                if tool == 'rocq_health':
                    compiler = '/different/compiler' if wrong_health else seen[-1]['env']['ZESU_ROCQ_COQC_WRAPPER']
                    result = dict(ok=True, pet=dict(running=False), toolchain=dict(coqc=dict(path=compiler)))
                elif tool == 'rocq_promotion_owner':
                    result = dict(success=True, pid=123, start_ticks=456)
                elif tool == 'rocq_compile_file':
                    (private / 'Fixture.vo').write_bytes(b'owned fixture object')
                    result = dict(success=True)
                else:
                    result = dict(success=True, assumptions=[])
                return SimpleNamespace(payload=result, model_dump=lambda **kwargs: result)
        mcp = ModuleType('mcp')
        mcp.ClientSession = lambda *args: Session()
        mcp.StdioServerParameters = parameters
        client = ModuleType('mcp.client')
        stdio = ModuleType('mcp.client.stdio')
        stdio.stdio_client = transport
        with patch.dict(sys.modules, {'mcp': mcp, 'mcp.client': client, 'mcp.client.stdio': stdio}), \
                patch.object(verification, '_result', side_effect=lambda response: response.payload), \
                patch.object(verification, 'live', side_effect=lambda identity: bool(identity) and active[0]):
            if wrong_health:
                with self.assertRaisesRegex(ValueError, 'different compiler launcher'):
                    asyncio.run(verification.verify(root, [source], 0x800d6a08, root / 'result', **selected))
            else:
                asyncio.run(verification.verify(root, [source], 0x800d6a08, root / 'result', **selected))
        return json.loads((root / 'result/RESULT.json').read_text()), seen, calls, selected

    def test_default_verification_uses_stock_launchers_and_owner_checks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            report, seen, calls, _ = self.fake_verification(root)
            self.assertTrue(report['success'])
            self.assertTrue(all(row['command'] == str(root / 'tools/rocq_mcp_guarded.sh') for row in seen))
            self.assertTrue(all(row['env']['ZESU_ROCQ_COQC_WRAPPER'] == str(root / 'tools/rocq_coqc_guarded.sh') for row in seen))
            self.assertEqual(calls.count('rocq_promotion_owner'), 2)
            self.assertTrue(all(row['server_exited'] for row in report['closures']))

    def test_explicit_verification_binds_and_uses_both_launchers(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            report, seen, calls, selected = self.fake_verification(root, overrides=True)
            self.assertTrue(report['success'])
            self.assertTrue(all(row['command'] == str(selected['mcp_launcher']) for row in seen))
            self.assertTrue(all(row['env']['ZESU_ROCQ_COQC_WRAPPER'] == str(selected['compiler_launcher']) for row in seen))
            self.assertEqual(report['launchers'], verification.launcher_bindings(root, **selected))
            self.assertEqual(calls.count('rocq_promotion_owner'), 2)
            self.assertEqual(report['checks'][0]['statements'][0]['verification']['assumptions'], [])

    def test_override_cannot_silently_select_a_different_compiler(self):
        with tempfile.TemporaryDirectory() as directory:
            report, _, calls, _ = self.fake_verification(Path(directory), overrides=True, wrong_health=True)
            self.assertFalse(report['success'])
            self.assertNotIn('rocq_compile_file', calls)


if __name__ == '__main__':
    unittest.main()
