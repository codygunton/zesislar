"""Application receipts bind generated declarations separately from inputs."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import unittest

from tools import test_entry_bindings as fixtures

sys.path.insert(0, str(Path(__file__).resolve().parent/'block'))
import check_entry_bindings
from entry_bindings import application_source, rendered_entry_views
from entry_schema import FIELDS


class RenderedBindingReportTests(unittest.TestCase):
    def setUp(self):
        fixtures.RenderedEntryViewTests.setUp(self)
        self.views = rendered_entry_views(self.design, self.root)
        self.design_path = self.root/'design.json'
        self.design_path.write_text(json.dumps(self.design))
        inputs = dict(self.views['input_source_hashes'], **self.views['output_source_hashes'])
        for name in check_entry_bindings.SUPPORT_TOOLS+check_entry_bindings.APPLICATION_TOOLS+(
                'ZesuSsz/Contracts/RlpDecodeItemContract.v',):
            path = self.root/name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('# owned fixture\n')
            inputs[name] = hashlib.sha256(path.read_bytes()).hexdigest()
        inputs['design.json'] = hashlib.sha256(self.design_path.read_bytes()).hexdigest()
        self.report = dict(result=dict(success=True), health=dict(ok=True),
            fields=sorted(FIELDS), row_count=7, cfg_row_count=3,
            entry_bindings=check_entry_bindings.binding_record(self.views), inputs=inputs,
            source=dict(sha256=hashlib.sha256(application_source(
                self.views['application_design']).encode()).hexdigest()))
        self.report_path = self.root/'report.json'

    def check(self):
        self.report_path.write_text(json.dumps(self.report))
        return check_entry_bindings.validate_report(self.report_path, self.design_path, self.root)

    def test_all_declarations_are_required_without_inflating_cfg_rows(self):
        self.assertEqual(self.check(), hashlib.sha256(self.report_path.read_bytes()).hexdigest())
        self.assertEqual(self.report['row_count'], 7)
        self.assertEqual(self.report['cfg_row_count'], 3)

    def test_missing_auxiliary_check_is_rejected(self):
        self.report['row_count'] = 3
        with self.assertRaisesRegex(ValueError, 'different rows or fields'):
            self.check()

    def test_changed_output_mapping_is_rejected(self):
        self.report['entry_bindings'] = deepcopy(self.report['entry_bindings'])
        self.report['entry_bindings']['name_mapping'].pop('Handwritten.Body6a24')
        with self.assertRaisesRegex(ValueError, 'different rendered bindings'):
            self.check()

    def test_omitted_generated_output_binding_is_rejected(self):
        self.report['inputs'].pop('ZesuSsz/Generated/DecodeItem/Entries.v')
        with self.assertRaisesRegex(ValueError, 'omits a rendered input'):
            self.check()

    def test_changed_producer_is_rejected(self):
        (self.root/'ZesuSsz/Evidence/generate_block_design.py').write_text('# changed\n')
        with self.assertRaisesRegex(ValueError, 'omits a rendered input'):
            self.check()

    def test_omitted_application_helper_binding_is_rejected(self):
        self.report['inputs'].pop('tools/block/entry_schema.py')
        with self.assertRaisesRegex(ValueError, 'omits a rendered input'):
            self.check()

    def test_primary_only_query_hash_cannot_authorize_auxiliaries(self):
        self.report['source']['sha256'] = hashlib.sha256(application_source(
            self.views['table_design']).encode()).hexdigest()
        with self.assertRaisesRegex(ValueError, 'different ordered expressions'):
            self.check()


if __name__ == '__main__':
    unittest.main()
