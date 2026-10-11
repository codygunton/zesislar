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
    def test_each_lemma_keeps_prior_scope_and_exact_header(self):
        source = 'Definition kept := 3.\nLemma first : kept = 3.\nProof. reflexivity. Qed.\nLemma second : True.\nProof. exact I. Qed.\n'
        checks = verification.statements(source, 0x800d6974)
        self.assertEqual([x[0] for x in checks], ['first', 'second'])
        self.assertEqual(checks[0][1], 'Definition kept := 3.\nLemma first : kept = 3.\n')
        self.assertTrue(checks[1][1].endswith('Lemma second : True.\n'))
        self.assertTrue(all(x[2] == source for x in checks))

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
