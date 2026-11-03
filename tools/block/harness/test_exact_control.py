"""Check the two released exact controls without starting a proof process."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

path = Path(__file__).with_name('exact_control.py')
spec = importlib.util.spec_from_file_location('exact_control', path)
control = importlib.util.module_from_spec(spec)
spec.loader.exec_module(control)


class ExactControlTests(unittest.TestCase):
    def setUp(self):
        self.authority = control.read({'path': str(control.POLICY), 'sha256': control.POLICY_SHA})
        self.directory = Path(self.authority['cases']['resource023']['spec']['path']).parent

    def output(self, case):
        return self.directory / ('test-uncreated-' + case)

    def changed(self, case, change):
        original = control.read
        ref = self.authority['cases'][case]['spec']
        def read(reference):
            value = original(reference)
            if reference == ref:
                value = copy.deepcopy(value)
                change(value)
            return value
        with patch.object(control, 'read', side_effect=read):
            with self.assertRaises(ValueError):
                control.validate(case, self.output(case))

    def test_both_exact_commands(self):
        for case, claim in [('predecessor', 8589934592), ('resource023', 38174650368)]:
            with self.subTest(case=case):
                command = control.validate(case, self.output(case))
                self.assertEqual(command['claim_bytes'], claim)
                self.assertEqual(command['physical_fence_bytes'], 68719476736)
                self.assertIn('--inside-guard', command['argv'])
                self.assertEqual(command['argv'].count('batch'), 1)
                self.assertEqual(command['argv'].count('scope'), 1)
                self.assertFalse(command['proof_acceptance'])
                self.assertTrue(command['fresh_canonical_projection_required'])

    def test_reject_boundary_changes(self):
        for field, value in [('claim_bytes', 8589934592), ('physical_fence_bytes', 8589934592),
                             ('CPU_policy', '60'), ('subject', {}), ('helper', {}), ('client', {}),
                             ('identity', {})]:
            with self.subTest(field=field):
                self.changed('resource023', lambda s: s.update({field: value}))

    def test_reject_changed_kernel_export(self):
        self.changed('resource023', lambda s: s['identity'].update(kernel_target_sha256='0' * 64))

    def test_reject_predecessor_baseline_tactic(self):
        self.changed('predecessor', lambda s: s.update(prefix=[{'body': 'idtac.'}]))

    def test_reject_changed_preserved_prefix(self):
        self.changed('resource023', lambda s: s['prefix'][0].update(body='idtac.'))

    def test_reject_changed_dependency(self):
        self.changed('predecessor', lambda s: s['bindings'][0].update(sha256='0' * 64))

    def test_reject_unknown_case(self):
        with self.assertRaises(ValueError):
            control.validate('other', self.output('other'))

    def test_reject_existing_or_external_output(self):
        with self.assertRaises(ValueError):
            control.validate('resource023', self.directory)
        with self.assertRaises(ValueError):
            control.validate('resource023', Path('/tmp/unreleased-output'))

    def test_policy_is_authenticated(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / 'changed.json'
            p.write_text(json.dumps(self.authority) + ' ')
            with patch.object(control, 'POLICY', p):
                with self.assertRaises(ValueError):
                    control.validate('resource023', self.output('resource023'))


if __name__ == '__main__':
    unittest.main()
