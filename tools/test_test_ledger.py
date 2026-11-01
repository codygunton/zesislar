"""Keep test descendants outside live accounting unless they opt in explicitly."""
import json
import os
from pathlib import Path
import subprocess
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

from block.harness.code import admission_memory as A
import correctness_gate

TOOLS = Path(__file__).resolve().parent


class TestLedgerIsolation(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.live = self.root / 'production/LEDGER.json'
        self.live.parent.mkdir()
        self.live.write_text(json.dumps({'fixed_claims': {}}))
        self.live.chmod(0o600)
        self.environment = {k: v for k, v in os.environ.items() if not k.startswith('ZESU_')}
        self.environment['ZESU_GATE_LOCK'] = str(self.root / 'guard')
        self.enterContext(patch.dict(os.environ, self.environment, clear=True))
        self.enterContext(patch.object(A, 'DEFAULT_LEDGER', self.live))

    def assert_no_locks(self):
        self.assertFalse((self.root / 'guard.mutex').exists())
        self.assertFalse(self.live.with_name('LEDGER.lock').exists())

    def test_current_unittest_process_is_detected(self):
        self.assertTrue(A.test_process())

    def test_live_transaction_refuses_before_locks(self):
        before = self.live.read_bytes()
        with self.assertRaisesRegex(ValueError, 'Tests refuse the live ledger'):
            with A.ledger_transaction(self.live):
                self.fail('The test entered the live transaction.')
        self.assertEqual(self.live.read_bytes(), before)
        self.assert_no_locks()

    def test_direct_live_write_refuses(self):
        before = self.live.read_bytes()
        with self.assertRaises(ValueError):
            A.write_ledger(self.live, {'fixed_claims': {'bad': 1}})
        self.assertEqual(self.live.read_bytes(), before)
        self.assert_no_locks()

    def test_symlink_and_hardlink_aliases_refuse(self):
        symbolic = self.root / 'alias.json'
        symbolic.symlink_to(self.live)
        hard = self.root / 'hard.json'
        os.link(self.live, hard)
        for path in [symbolic, hard, self.live.parent / '../production/LEDGER.json']:
            with self.subTest(path=path), self.assertRaises(ValueError):
                A.check_test_ledger(path)
        self.assert_no_locks()

    def test_private_temporary_ledger_remains_usable(self):
        private = self.root / 'private/LEDGER.json'
        private.parent.mkdir()
        private.write_text('{"fixed_claims":{}}')
        with A.ledger_transaction(private) as value:
            value['fixed_claims']['temporary'] = 3
            A.write_ledger(private, value)
        self.assertEqual(json.loads(private.read_text())['fixed_claims'], {'temporary': 3})
        self.assertEqual(json.loads(self.live.read_text()), {'fixed_claims': {}})

    def test_explicit_live_mode_works_only_on_temporary_substitute(self):
        with patch.dict(os.environ, ZESU_TEST_ALLOW_LIVE_LEDGER='1'):
            with A.ledger_transaction(self.live) as value:
                value['fixed_claims']['authorized'] = 7
                A.write_ledger(self.live, value)
        self.assertEqual(json.loads(self.live.read_text())['fixed_claims'], {'authorized': 7})

    def test_invalid_live_mode_does_not_authorize(self):
        for value in ['true', 'yes', '0', '']:
            with self.subTest(value=value), patch.dict(os.environ, ZESU_TEST_ALLOW_LIVE_LEDGER=value):
                with self.assertRaises(ValueError): A.check_test_ledger(self.live)
        self.assert_no_locks()

    def child(self, code, environment=None):
        return subprocess.run([sys.executable, '-B', '-c', code], cwd=TOOLS,
                              env=environment or os.environ, capture_output=True, text=True, timeout=5)

    def test_real_child_detects_unittest_ancestor_without_flags(self):
        code = ('from pathlib import Path; from block.harness.code import admission_memory as a; '
                f'a.DEFAULT_LEDGER=Path({str(self.live)!r}); '
                'assert a.test_process(); a.check_test_ledger(a.DEFAULT_LEDGER)')
        result = self.child(code)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Tests refuse the live ledger', result.stderr)
        self.assert_no_locks()

    def test_stock_gate_drops_inherited_live_mode_for_real_child(self):
        environment = correctness_gate.gate_environment(dict(os.environ, ZESU_TEST_ALLOW_LIVE_LEDGER='1'))
        self.assertNotIn('ZESU_TEST_ALLOW_LIVE_LEDGER', environment)
        code = ('from pathlib import Path; from block.harness.code import admission_memory as a; '
                f'a.DEFAULT_LEDGER=Path({str(self.live)!r}); a.check_test_ledger(a.DEFAULT_LEDGER)')
        result = self.child(code, environment)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Tests refuse the live ledger', result.stderr)
        self.assert_no_locks()

    def test_staged_wrapper_import_and_private_cli(self):
        tools = self.root / 'staged/tools'
        (tools / 'block').mkdir(parents=True)
        (tools / 'det').mkdir()
        shutil.copy2(TOOLS / 'block/harness/code/module_memory.py', tools / 'block/module_memory.py')
        shutil.copy2(TOOLS / 'block/harness/code/admission_memory.py', tools / 'block/admission_memory.py')
        shutil.copy2(TOOLS / 'det/coqc_slots.py', tools / 'det/coqc_slots.py')
        environment = dict(os.environ, ZESU_CANONICAL_LEDGER=str(self.live))
        result = subprocess.run([sys.executable, '-B', str(tools / 'block/module_memory.py'),
                                 'test-ledger-policy'], env=environment,
                                capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_no_locks()

    def test_unstaged_wrapper_import_and_private_cli(self):
        environment = dict(os.environ, ZESU_CANONICAL_LEDGER=str(self.live), PYTHONPATH=str(TOOLS))
        result = subprocess.run([sys.executable, '-B', str(TOOLS / 'block/harness/code/module_memory.py'),
                                 'test-ledger-policy'], env=environment,
                                capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_no_locks()

    def test_guard_refuses_default_live_ledger_before_state_or_locks(self):
        environment = dict(os.environ, ZESU_GUARD_STATE=str(self.root / 'guard-state'),
                           ZESU_RUN_REGISTRY=str(self.root / 'registry'))
        result = subprocess.run([str(TOOLS / 'resource_guard.sh'), 'reserve-coqc', str(os.getpid())],
                                env=environment, capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn('Tests refuse the live ledger', result.stderr)
        self.assertFalse((self.root / 'guard-state').exists())
        self.assertFalse((self.root / 'registry').exists())
        self.assert_no_locks()


if __name__ == '__main__':
    unittest.main()
