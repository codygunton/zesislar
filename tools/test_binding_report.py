"""Production discovery rejects stale or unsuccessful application checks."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from entry_bindings import application_source
from check_entry_bindings import validate_report


class BindingReportTests(unittest.TestCase):
    def fixture(self, root):
        source = root/'Fixture.v'
        source.write_text('Definition entry (n cursor : Z) : iProp Sigma := True.')
        row = {'entry_pc': '0x10', 'entry_definition': 'Fixture.entry', 'resource_predicate': 'Fixture.entry',
               'binders': [{'name': 'n', 'type': 'Z'}, {'name': 'cursor', 'type': 'Z'}],
               'arguments': ['n', 'cursor'], 'source_hashes': {'Fixture.v': hashlib.sha256(source.read_bytes()).hexdigest()}}
        design = {'blocks': [row]}
        path = root/'design.json';path.write_text(json.dumps(design))
        report = {'result': {'success': True}, 'health': {'ok': True}, 'row_count': 1,
                  'fields': sorted(row.keys()-{'entry_pc'}),
                  'source': {'sha256': hashlib.sha256(application_source(design).encode()).hexdigest()},
                  'inputs': {'Fixture.v': hashlib.sha256(source.read_bytes()).hexdigest(),
                             'design.json': hashlib.sha256(path.read_bytes()).hexdigest()}}
        checked = root/'report.json'; checked.write_text(json.dumps(report))
        return design, path, report, checked

    def test_valid_report_binds_the_current_application(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); _, path, _, checked = self.fixture(root)
            self.assertEqual(validate_report(checked, path, root), hashlib.sha256(checked.read_bytes()).hexdigest())

    def test_changed_same_type_argument_order_requires_a_new_check(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); design, path, _, checked = self.fixture(root)
            design['blocks'][0]['arguments'].reverse();path.write_text(json.dumps(design))
            with self.assertRaisesRegex(ValueError, 'different ordered expressions'):
                validate_report(checked, path, root)

    def test_failed_type_check_cannot_authorize_discovery(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); _, path, report, checked = self.fixture(root)
            report['result']['success'] = False;checked.write_text(json.dumps(report))
            with self.assertRaisesRegex(ValueError, 'successful typing'):
                validate_report(checked, path, root)

    def test_changed_declaration_is_rejected_before_report_reuse(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); _, path, _, checked = self.fixture(root)
            (root/'Fixture.v').write_text('changed')
            with self.assertRaisesRegex(ValueError, 'source hash changed'):
                validate_report(checked, path, root)


if __name__ == '__main__':
    unittest.main()
