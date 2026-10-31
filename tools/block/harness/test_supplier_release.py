"""Test supplier evidence policy with synthetic data, never admission evidence."""
from copy import deepcopy
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE / 'code'), str(HERE.parents[0])]
from entry_chain import binding, save
import supplier_release


class SupplierReleaseTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.old = self.root / 'old.v'
        self.new = self.root / 'new.v'
        self.control = self.root / 'control.v'
        self.old.write_text('(* Old test-only supplier. *)\n')
        self.new.write_text('(* New test-only supplier. *)\n')
        self.control.write_text('Lemma activation : True.\nProof.\nzesu_block.\nQed.\n')
        self.record = {'module': 'Test.Supplier', 'activation_command': 'zesu_block.'}
        for name, source in [('before', self.old), ('after', self.new)]:
            receipt = {'module': 'Test.Supplier', 'activation_command': 'zesu_block.',
                       'source_sha256': binding(self.control)['sha256'],
                       'statement_sha256': 'a' * 64,
                       'export': {'test_groups': {'active': ['goal'] if name == 'before' else []}},
                       'outcome': 'open' if name == 'before' else 'closed',
                       'compile_file_success': True, 'verification_success': True, 'verification_method': 'module_m',
                       'assumptions': [], 'Qed': True}
            path = self.root / (name + '.json')
            save(path, receipt)
            self.record[name] = {'supplier_source': binding(source),
                                 'control_source': binding(self.control),
                                 'control_receipt': binding(path)}
        # Complete export validation has independent controls. This mock isolates
        # the release policy. These payloads certify no theorem or real supplier.
        self.groups = patch.object(supplier_release, 'complete_groups',
                                   side_effect=lambda row: row['test_groups'])
        self.groups.start()
        self.addCleanup(self.groups.stop)

    def mutate_receipt(self, side, **changes):
        import json
        path = Path(self.record[side]['control_receipt']['path'])
        row = json.loads(path.read_text())
        row.update(changes)
        save(path, row)
        self.record[side]['control_receipt'] = binding(path)

    def test_unchanged_control_old_open_new_accepted(self):
        self.assertTrue(supplier_release.validate(self.record)['accepted'])

    def test_old_closed_or_missing_export_refuses(self):
        for change in [{'outcome': 'closed'}, {'export': {'test_groups': {'active': []}}}]:
            with self.subTest(change=change):
                self.mutate_receipt('before', **change)
                with self.assertRaises(ValueError): supplier_release.validate(self.record)

    def test_each_kernel_acceptance_field_is_required(self):
        for key, value in [('compile_file_success', False), ('verification_success', False), ('verification_method', 'other'),
                           ('assumptions', ['axiom']), ('Qed', False),
                           ('export', {'test_groups': {'active': ['goal']}})]:
            with self.subTest(key=key):
                original = deepcopy(self.record)
                self.mutate_receipt('after', **{key: value})
                with self.assertRaises(ValueError): supplier_release.validate(self.record)
                self.record = original
                # Restore the receipt and its binding for the next case.
                self.set_receipt_accepted()

    def set_receipt_accepted(self):
        self.mutate_receipt('after', compile_file_success=True, verification_success=True,
                            verification_method='module_m', assumptions=[], Qed=True,
                            export={'test_groups': {'active': []}})

    def test_missing_verification_success_refuses(self):
        import json
        path = Path(self.record['after']['control_receipt']['path'])
        row = json.loads(path.read_text())
        row.pop('verification_success')
        save(path, row)
        self.record['after']['control_receipt'] = binding(path)
        with self.assertRaises(ValueError): supplier_release.validate(self.record)

    def test_changed_statement_refuses(self):
        self.mutate_receipt('after', statement_sha256='b' * 64)
        with self.assertRaises(ValueError): supplier_release.validate(self.record)

    def test_changed_control_bytes_refuse(self):
        self.control.write_text('Proof. exact I. Qed.\n')
        with self.assertRaises(ValueError): supplier_release.validate(self.record)

    def test_import_only_control_refuses(self):
        self.control.write_text('Require Import Test.Supplier.\n')
        for side in ['before', 'after']:
            self.record[side]['control_source'] = binding(self.control)
            self.mutate_receipt(side, source_sha256=binding(self.control)['sha256'])
        with self.assertRaisesRegex(ValueError, 'does not execute'):
            supplier_release.validate(self.record)

    def test_same_supplier_refuses(self):
        self.record['after']['supplier_source'] = self.record['before']['supplier_source']
        with self.assertRaisesRegex(ValueError, 'did not change'):
            supplier_release.validate(self.record)

    def test_duplicate_supplier_refuses(self):
        with self.assertRaisesRegex(ValueError, 'repeats'):
            supplier_release.releases([self.record, self.record])

    def test_missing_activation_evidence_refuses(self):
        self.record.pop('before')
        with self.assertRaises(ValueError): supplier_release.validate(self.record)


if __name__ == '__main__':
    unittest.main()
