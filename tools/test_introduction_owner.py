"""Check logical ownership when source declarations share a basename."""
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
from check_data_only_lemmas import PredicateResolver
from render_support import introduction_predicate_owner


class IntroductionOwnerTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.sources = {}
        self.bind("Example.BaseEntries", "Definition shared : nat := 1.")
        self.bind("Example.LoweredEntries", "Definition shared : nat := 2.")

    def bind(self, name, text):
        path = self.root / (name.rsplit(".", 1)[-1] + ".v")
        path.write_text(text)
        self.sources[name] = dict(path=str(path),
                                 sha256=hashlib.sha256(path.read_bytes()).hexdigest())

    def resolve(self, imports, head="shared", instance="shared_intro"):
        resolver = PredicateResolver(self.root, set(), {}, source_bindings=self.sources)
        source = ("#[export] Instance " + instance + " : "
                  "@ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (" +
                  head + " args) True := constructor.")
        return introduction_predicate_owner(source, "Example.Structural", imports, resolver)

    def test_import_selects_logical_owner_not_changed_basename(self):
        result = self.resolve(["Example.LoweredEntries"])
        self.assertEqual(result["qualified_predicate"], "Example.LoweredEntries.shared")
        self.assertEqual(result["owner_module"], "Example.LoweredEntries")

    def test_unchanged_sibling_keeps_its_owner(self):
        self.bind("Example.BaseEntries", "Definition shared : nat := 3.")
        self.assertEqual(self.resolve(["Example.LoweredEntries"])["owner_module"],
                         "Example.LoweredEntries")

    def test_qualified_head_disambiguates_both_imports(self):
        result = self.resolve(["Example.BaseEntries", "Example.LoweredEntries"],
                              "Example.BaseEntries.shared")
        self.assertEqual(result["qualified_predicate"], "Example.BaseEntries.shared")

    def test_ambiguous_short_head_refuses(self):
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            self.resolve(["Example.BaseEntries", "Example.LoweredEntries"])

    def test_exports_use_the_existing_resolver(self):
        self.bind("Example.Wrapper", "Require Export Example.LoweredEntries.")
        self.assertEqual(self.resolve(["Example.Wrapper"])["owner_module"],
                         "Example.LoweredEntries")

    def test_dependency_without_export_is_not_imported(self):
        self.bind("Example.Wrapper", "Require Import Example.LoweredEntries.")
        with self.assertRaisesRegex(ValueError, "unresolved registration key"):
            self.resolve(["Example.Wrapper"])

    def test_changed_bound_source_refuses(self):
        Path(self.sources["Example.LoweredEntries"]["path"]).write_text("Definition shared := 4.")
        with self.assertRaisesRegex(ValueError, "bound predicate source changed"):
            self.resolve(["Example.LoweredEntries"])

    def test_missing_owner_refuses(self):
        with self.assertRaisesRegex(ValueError, "unresolved registration key"):
            self.resolve(["Example.Missing"])

    def test_instance_name_cannot_override_the_target_head(self):
        with self.assertRaisesRegex(ValueError, "does not match"):
            self.resolve(["Example.LoweredEntries"], instance="other_intro")


if __name__ == "__main__":
    unittest.main()
