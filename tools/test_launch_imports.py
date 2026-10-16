"""Check manifest-based launch admission without proof execution."""
import asyncio
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import AsyncMock, Mock, patch

sys.path.insert(0, str(Path(__file__).parent / "block"))
import coqc_primary
import discovery
import launch_imports
import successor_entailment


class LaunchImportTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.manifest = self.root / "ZesuSsz/Evidence/demo_function_text.json"
        self.manifest.parent.mkdir(parents=True)
        self.hints = self.root / "ZesuSsz/Compliance/DeclaredHints.v"
        self.hints.parent.mkdir(parents=True)
        self.hints.write_text("(* Declared function hints. *)\n")
        self.data = {"function": "demo.function", "umbrella": "Incorrect.Guess",
                     "registrations": ["ZesuSsz/Compliance/DeclaredHints.v"]}
        self.write_manifest()
        self.module = "ZesuSsz.Compliance.DeclaredHints"
        self.source = (f"Require Import {self.module}.\n"
                       "Require Import ZesuSsz.Automation.Approved.\n"
                       "Lemma boundary : True.\nProof.\nexact I.\nQed.\n")

    def write_manifest(self):
        self.manifest.write_text(json.dumps(self.data))

    def check(self, source):
        return launch_imports.validate_launch_imports(source, "demo.function", self.root)

    def missing_sources(self):
        return [(module, self.source.replace(f"Require Import {module}.\n", ""))
                for module in (self.module, launch_imports.APPROVED)]

    def test_registration_entry_selects_the_umbrella(self):
        checked = self.check(self.source)
        self.assertEqual(checked["required"], [self.module, launch_imports.APPROVED])
        self.assertEqual(set(checked["inputs"]), {str(self.manifest), str(self.hints)})

    def test_missing_function_umbrella_rejects(self):
        with self.assertRaisesRegex(ValueError, self.module):
            self.check(self.source.replace(f"Require Import {self.module}.\n", ""))

    def test_missing_approved_rejects(self):
        with self.assertRaisesRegex(ValueError, launch_imports.APPROVED):
            self.check(self.source.replace(f"Require Import {launch_imports.APPROVED}.\n", ""))

    def test_grouped_and_from_requires_pass(self):
        self.check("From ZesuSsz.Compliance Require Export DeclaredHints.\n"
                   "From ZesuSsz.Automation Require Import Approved.\n")
        self.check(f"Require Import {self.module} {launch_imports.APPROVED}.\n")
        self.check(f"Require {self.module}.\nRequire {launch_imports.APPROVED}.\n")

    def test_legacy_unqualified_manifest_name_matches_inventory_suffix(self):
        self.data["function"] = "function"
        self.write_manifest()
        self.check(self.source)

    def test_other_qualified_function_does_not_match_the_suffix(self):
        self.data["function"] = "other.function"
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "one function manifest"):
            self.check(self.source)

    def test_comments_strings_and_bare_imports_do_not_admit_launch(self):
        for module, source in self.missing_sources():
            with self.subTest(module=module):
                decoys = (f'(* outer (* Require Import {module}. *) *)\n'
                          f'Definition text := "Require Import {module}.".\n'
                          f'Import {module}.\n')
                with self.assertRaisesRegex(ValueError, module):
                    self.check(decoys + source)

    def test_require_after_the_proof_does_not_admit_launch(self):
        for module, source in self.missing_sources():
            with self.subTest(module=module), self.assertRaisesRegex(ValueError, module):
                self.check(source + f"Require Import {module}.\n")

    def test_another_function_umbrella_does_not_admit_launch(self):
        with self.assertRaisesRegex(ValueError, self.module):
            self.check(self.source.replace(self.module, "ZesuSsz.Compliance.OtherHints"))

    def test_missing_or_ambiguous_manifest_rejects(self):
        with self.assertRaisesRegex(ValueError, "one function manifest"):
            launch_imports.validate_launch_imports(self.source, "unknown", self.root)
        self.manifest.with_name("duplicate_function_text.json").write_text(json.dumps(self.data))
        with self.assertRaisesRegex(ValueError, "one function manifest"):
            self.check(self.source)

    def test_absent_function_identity_rejects(self):
        with self.assertRaisesRegex(ValueError, "explicit function"):
            launch_imports.validate_launch_imports(self.source, None, self.root)

    def test_registration_list_requires_exactly_one_hints_source(self):
        for registrations in (None, "Hints.v", [], [1],
                              ["ZesuSsz/Compliance/DeclaredHints.v"] * 2):
            self.data["registrations"] = registrations
            self.write_manifest()
            with self.subTest(registrations=registrations), self.assertRaises(ValueError):
                self.check(self.source)

    def test_umbrella_outside_compliance_rejects(self):
        other = self.root / "OtherHints.v"
        other.write_text("(* Wrong owner. *)")
        self.data["registrations"] = ["OtherHints.v"]
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "Compliance source"):
            self.check(self.source)

    def test_caller_rejects_both_omissions_before_tools_or_output(self):
        for module, source in self.missing_sources():
            session = Mock(call_tool=AsyncMock())
            output = self.root / "caller/Boundary.v"
            rendered = {"scope": "unproved native designed boundary",
                        "function": "demo.function", "source": source}
            with self.subTest(module=module), self.assertRaisesRegex(ValueError, module):
                asyncio.run(successor_entailment.check_boundary(
                    session, rendered, output, self.root, inherited_debts={}))
            session.call_tool.assert_not_called()
            self.assertFalse(output.parent.exists())

    def test_discovery_rejects_both_omissions_before_mcp_import(self):
        design = self.root / "design.json"
        design.write_text(json.dumps({"function": "demo.function"}))
        options = {"design": str(design), "workspace": str(self.root)}
        for module, source in self.missing_sources():
            with self.subTest(module=module), \
                    patch("successor_entailment.native_boundary_source", return_value={"source": source}), \
                    patch("discovery.designed_terminal", return_value=None), \
                    self.assertRaisesRegex(ValueError, module):
                asyncio.run(discovery.probe_designed_block({}, {}, {}, options))

    def test_compiler_rejects_both_omissions_before_compilation(self):
        for module, source in self.missing_sources():
            output = self.root / "compiler"
            rendered = {"source": source, "function": "demo.function"}
            with self.subTest(module=module), \
                    patch("coqc_primary.Path.cwd", return_value=self.root), \
                    patch("coqc_primary.compile_source") as compiler, \
                    self.assertRaisesRegex(ValueError, module):
                coqc_primary.run_primary(rendered, output, self.root / "build", inherited_debts={})
            compiler.assert_not_called()
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
