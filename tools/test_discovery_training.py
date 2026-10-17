"""Check training admission and report labels without starting a proof."""
import argparse
import ast
import contextlib
import copy
import io
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / 'block'))
import discovery
from tools import test_native_boundary_discovery as fixtures


class TrainingTests(unittest.TestCase):
    def setUp(self):
        self.fixture = fixtures.FirstNativeRunTests('test_first_native_valid')
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.root, self.sha = self.fixture.root, self.fixture.sha

    def arguments(self):
        return ['--designed-successors', '--training-root', self.sha,
                '--terminal-descriptor', str(self.root / 'terminal.json')]

    def git(self, command, **kwargs):
        if command[1:3] == ['rev-parse', 'HEAD']:
            return self.sha + '\n'
        if command[1:] == ['diff', '--binary', 'HEAD']:
            return b''
        raise AssertionError(command)

    def invoke(self, extra=None, **kwargs):
        return self.fixture.invoke(self.arguments() if extra is None else extra,
                                   head_results=kwargs.pop('head_results', self.git), **kwargs)

    def validate(self, **changes):
        values = dict(training_root=self.sha, first_native_run=None, designed_successors=True,
                      native_baseline_report=None, native_resume_report=None,
                      resume_report=None, entries=None, out=self.root / 'out')
        values.update(changes)
        with patch('discovery.subprocess.check_output', side_effect=self.git), \
                contextlib.redirect_stderr(io.StringIO()):
            return discovery.training_native_root(argparse.Namespace(**values),
                                                  argparse.ArgumentParser(), self.root)

    def test_training_label_and_identity(self):
        result, report, pool, renderer, validator, _ = self.invoke()
        self.assertEqual(result, 0)
        self.assertEqual(report['label'], discovery.TRAINING_LABEL)
        self.assertEqual(report['experiment_kind'], 'training')
        self.assertEqual(report['training_root'], self.sha)
        self.assertEqual(report['measurement_root'], self.sha)
        self.assertIs(report['first_native_run'], False)
        self.assertIs(report['inputs_unchanged'], True)
        self.assertIsNone(report['frozen_baseline_report'])
        self.assertEqual(report['new_block_runs'], 1)
        self.assertEqual(report['reused_block_runs'], 0)
        validator.assert_called_once()
        renderer.assert_not_called()
        self.assertTrue(pool.return_value.__enter__.return_value.map.called)

    def test_training_requires_designed_successors(self):
        with self.assertRaises(SystemExit):
            self.validate(designed_successors=False)

    def test_training_forbids_first_baseline_resume_and_legacy_modes(self):
        for name in ('first_native_run', 'native_baseline_report', 'native_resume_report',
                     'resume_report', 'entries'):
            with self.subTest(name=name), self.assertRaises(SystemExit):
                self.validate(**{name: self.sha if name == 'first_native_run' else Path('old.json')})

    def test_malformed_and_wrong_roots_reject(self):
        for root in ('', 'a' * 39, 'A' * 40, 'g' * 40, 'b' * 40):
            with self.subTest(root=root), self.assertRaises(SystemExit):
                self.validate(training_root=root)

    def test_existing_output_rejects_even_when_empty(self):
        (self.root / 'out').mkdir()
        with self.assertRaises(SystemExit):
            self.validate()

    def test_broken_output_link_rejects(self):
        (self.root / 'out').symlink_to(self.root / 'missing')
        with self.assertRaises(SystemExit):
            self.validate()

    def test_dirty_tracked_source_rejects(self):
        def dirty(command, **kwargs):
            return b'changed tracked source' if command[1] == 'diff' else self.git(command, **kwargs)
        with patch('discovery.subprocess.check_output', side_effect=dirty), \
                contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            discovery.training_native_root(argparse.Namespace(training_root=self.sha,
                first_native_run=None, designed_successors=True, native_baseline_report=None,
                native_resume_report=None, resume_report=None, entries=None, out=self.root / 'out'),
                argparse.ArgumentParser(), self.root)

    def test_binding_failure_remains_a_failure(self):
        with self.assertRaisesRegex(ValueError, 'invalid entry binding'):
            self.invoke(binding_error=ValueError('invalid entry binding'))

    def test_manifest_identity_check_remains_active(self):
        self.fixture.write_json('cfg.json', {'artifact_identity': 'foreign-code'})
        with self.assertRaisesRegex(ValueError, 'different artifact identity'):
            self.invoke()

    def test_selected_elf_check_remains_active(self):
        self.fixture.design['hashes']['selected_elf_sha256'] = 'foreign-elf'
        self.fixture.write_json('design.json', self.fixture.design)
        with self.assertRaisesRegex(ValueError, 'different selected ELF'):
            self.invoke()

    def test_control_change_during_validation_rejects_before_workers(self):
        def changed(*args):
            self.fixture.write_json('manifest.json', {'artifact_identity': 'changed-after-parse',
                                                     'elf_sha256': 'elf'})
        with self.assertRaisesRegex(ValueError, 'training input changed'):
            self.invoke(binding_error=changed)

    def test_output_race_rejects_before_workers(self):
        def created(*args):
            (self.root / 'out').mkdir()
        with self.assertRaises(FileExistsError):
            self.invoke(binding_error=created)

    def test_final_input_change_rejects_before_report(self):
        def changed(worker, arguments):
            self.fixture.owner.write_text('Definition changed := 0.\n')
            return [copy.deepcopy(self.fixture.record)]
        with self.assertRaisesRegex(ValueError, 'training input changed'):
            self.invoke(pool_effect=changed)
        self.assertFalse((self.root / 'out/report.json').exists())

    def test_final_missing_input_rejects_before_report(self):
        def missing(worker, arguments):
            self.fixture.owner.unlink()
            return [copy.deepcopy(self.fixture.record)]
        with self.assertRaisesRegex(ValueError, 'training input became unavailable'):
            self.invoke(pool_effect=missing)
        self.assertFalse((self.root / 'out/report.json').exists())

    def test_final_head_change_rejects(self):
        heads = 0
        def changed(command, **kwargs):
            nonlocal heads
            if command[1] == 'rev-parse':
                heads += 1
                return ('b' * 40 if heads == 4 else self.sha) + '\n'
            return self.git(command, **kwargs)
        with self.assertRaisesRegex(ValueError, 'training root differs'):
            self.invoke(head_results=changed)

    def test_absent_training_policy_does_not_change_legacy_helpers(self):
        source = subprocess.check_output(['git', 'show', 'df9600c2:tools/block/discovery.py'],
                                         cwd=Path(discovery.__file__).parents[2], text=True)
        old, new = ast.parse(source), ast.parse(Path(discovery.__file__).read_text())
        # Native launch admission now has a separate manifest/import preflight.
        # test_launch_imports checks that path before any MCP or compiler call.
        for name in ('first_native_root', 'native_boundary_closed',
                     'reuse_native_capture', 'worker'):
            def function(tree):
                return next(row for row in tree.body if isinstance(row, (ast.FunctionDef, ast.AsyncFunctionDef))
                            and row.name == name)
            self.assertEqual(ast.dump(function(old)), ast.dump(function(new)), name)

    def test_absent_training_mode_keeps_all_serialized_legacy_reports_exact(self):
        source = subprocess.check_output(['git', 'show', 'df9600c2:tools/block/discovery.py'],
                                         cwd=Path(discovery.__file__).parents[2], text=True)
        # Accept the new admission argument in the old serializer only. Its report code stays exact.
        source = source.replace("    parser.add_argument('--design', type=Path, required=True)",
            "    parser.add_argument('--entry-artifacts', type=Path)\n    parser.add_argument('--design', type=Path, required=True)")
        legacy = {'__name__': 'legacy_discovery', '__file__': discovery.__file__}
        exec(compile(source, discovery.__file__, 'exec'), legacy)
        for name in ('machine', 'prepare', 'ProcessPoolExecutor'):
            legacy[name] = lambda *args, _name=name, **kwargs: getattr(discovery, _name)(*args, **kwargs)
        modes = (self.fixture.first_arguments(),
                 ['--designed-successors', '--native-baseline-report', str(self.root / 'baseline.json')], [])
        for arguments in modes:
            with self.subTest(arguments=arguments):
                with patch.object(discovery, 'main', legacy['main']), \
                        patch('discovery.time.monotonic', side_effect=[100.0, 101.0]):
                    self.fixture.invoke(arguments)
                before = (self.root / 'out/report.json').read_bytes()
                with patch('discovery.time.monotonic', side_effect=[100.0, 101.0]):
                    self.fixture.invoke(arguments)
                self.assertEqual((self.root / 'out/report.json').read_bytes(), before)


if __name__ == '__main__':
    unittest.main()
