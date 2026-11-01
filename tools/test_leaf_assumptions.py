"""Keep assumption audits reachable without putting them on importer chains."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]


class LeafAssumptionsTests(unittest.TestCase):
    def test_promoted_audit_covers_every_exported_body_once(self):
        source = (ROOT / 'ZesuSsz/Generated/DecodeItem/PromotedBodies.v').read_text()
        audit = (ROOT / 'ZesuSsz/Generated/DecodeItem/PromotedBodiesAssumptions.v').read_text()
        names = re.findall(r'^Definition (decodeItemPromotedBody\w+)\s*:', source, re.M)
        self.assertEqual(len(names), 24)
        targets = re.findall(r'^Print Assumptions (\S+)\.$', audit, re.M)
        self.assertEqual(targets, ['ZesuSsz.Generated.DecodeItem.PromotedBodies.' + name
                                   for name in names])
        self.assertNotIn('Print Assumptions', source)

    def test_compliance_audit_is_complete(self):
        source = (ROOT / 'ZesuSsz/Compliance/DecodeItemCompliance.v').read_text()
        audit = (ROOT / 'ZesuSsz/Compliance/DecodeItemComplianceAssumptions.v').read_text()
        self.assertNotIn('Print Assumptions', source)
        self.assertEqual(re.findall(r'^Print Assumptions (\S+)\.$', audit, re.M),
                         ['ZesuSsz.Compliance.DecodeItemCompliance.decodeItemSelectedCompliance'])

    def test_both_gates_include_both_leaf_files(self):
        makefile = (ROOT / 'Makefile').read_text()
        retained = makefile.split('RETAINED_TARGETS :=', 1)[1].split('.PHONY:', 1)[0]
        self.assertIn('ZesuSsz/Generated/DecodeItem/PromotedBodiesAssumptions.vo', retained)
        self.assertIn('@ZesuSsz/Compliance/all', retained)
        self.assertIn('@all', makefile.split('_check-iris:', 1)[1].split('#', 1)[0])

    def test_no_production_module_imports_either_audit(self):
        for source in (ROOT / 'ZesuSsz').rglob('*.v'):
            if source.name.endswith('Assumptions.v'):
                continue
            text = source.read_text()
            self.assertNotRegex(text, r'Require\s+(?:Import|Export)\s+[^\n]*'
                                r'(?:PromotedBodiesAssumptions|DecodeItemComplianceAssumptions)')


if __name__ == '__main__':
    unittest.main()
