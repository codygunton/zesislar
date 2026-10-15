"""Check exact statement extraction and mandatory verification failures."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
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


if __name__ == '__main__':
    unittest.main()
