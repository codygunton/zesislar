import json
import unittest

from tools.block.check_approved_switches import (
    MANIFEST, UMBRELLA, export_differences, inventory_modules,
)


class ApprovedSwitchCoverageTests(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads(MANIFEST.read_text())
        self.source = UMBRELLA.read_text()

    def test_current_pass_inventory_is_exported(self):
        self.assertEqual(export_differences(self.source, self.manifest), ([], []))
        self.assertEqual(len(inventory_modules(self.manifest)), 34)
        self.assertEqual(len(self.manifest["exclusions"]), 16)

    def test_new_approved_switch_requires_export(self):
        module = "ZesuSsz.Automation.Switches.NewApproved"
        self.manifest["approved_modules"].append(module)
        self.assertEqual(export_differences(self.source, self.manifest), ([module], []))

    def test_import_does_not_replace_export(self):
        module = self.manifest["approved_modules"][0]
        source = self.source.replace("Require Export " + module, "Require Import " + module)
        self.assertEqual(export_differences(source, self.manifest), ([module], []))

    def test_historical_export_is_rejected(self):
        module = "ZesuSsz.Automation.Switches." + self.manifest["exclusions"][0]["switch"]
        self.assertEqual(export_differences(self.source + "Require Export " + module + ".\n",
                                            self.manifest), ([], [module]))

    def test_duplicate_approved_module_is_rejected(self):
        self.manifest["approved_modules"].append(self.manifest["approved_modules"][0])
        with self.assertRaisesRegex(ValueError, "duplicate"):
            inventory_modules(self.manifest)

    def test_excluded_switch_cannot_be_approved(self):
        self.manifest["approved_modules"].append(
            "ZesuSsz.Automation.Switches." + self.manifest["exclusions"][0]["switch"])
        with self.assertRaisesRegex(ValueError, "excluded"):
            inventory_modules(self.manifest)


if __name__ == "__main__":
    unittest.main()
