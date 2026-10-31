import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from render_support import retain_definition_facts, definition_introduction_source
from source_retention import certified_execution_facts, decoder_owner, typed_nat_literals


class BoundLowerer:
    """A fixed lowerer result. These tests exercise retention, not proof search."""

    owned_lists = ()

    def lower(self, original, binders):
        return ["length (bytes) = size"], [{"term": self.decoder}], self.expansion

    def _values(self, values, scope):
        if "unknown" in values:
            raise ValueError("An unsupported source symbol remains.")


class SourceRetention(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / "source.json"
        self.provenance = {"source": "Example.original_source"}
        self.scope = [{"name": "bytes", "type": "list (bv 8)"}]
        self.document = {"entries": [{"body": {"at": "entry", "additional_definitions": [
            {"suffix": "Primary", "body": {"existentials": self.scope, "lets": [],
             "components": [{"kind": "byte_array", "address": "base", "value": "bytes"},
                            {"kind": "pure", "terms": [{
                 "term": {"value": "source_fact bytes"}, "provenance": self.provenance}]}]}}
        ]}}]}
        self.path.write_text(json.dumps(self.document))
        self.source = {"input": {"path": str(self.path),
                                  "sha256": hashlib.sha256(self.path.read_bytes()).hexdigest()},
                       "pc": "entry", "definition": "Primary", "component": 1,
                       "term_index": 0, "original_term": "source_fact bytes",
                       "provenance": self.provenance}
        self.catalog = BoundLowerer()
        self.catalog.decoder = "littleEndian (firstn count (skipn offset bytes)) = value"
        self.catalog.expansion = [{"declaration": "source_fact", "source": "bound", "line": 1}]
        self.owner = {"kind": "byte_array", "address": "base", "value": "bytes"}
        self.row = {"pc": "entry", "definition": "Primary", "parameters": [
            {"name": name, "type": "Z"} for name in ["base", "size", "value"]] + [
            {"name": name, "type": "nat"} for name in ["count", "offset"]],
            "existentials": self.scope, "resources": [self.owner], "execution_facts": [
                {"term": "length (bytes) = size", "source": self.source,
                 "expansion": self.catalog.expansion}]}
        self.report = {"unsupported": [{"source": self.source,
            "unsupported": {"term": self.catalog.decoder}, "expansion": self.catalog.expansion}]}

    def facts(self):
        return certified_execution_facts(self.report, self.row, self.catalog)

    def declaration(self, *, width="8%N", fraction=""):
        return ("Definition sample `{!islaG Sigma} `{!threadG}\n"
                " (base size value : Z) (count offset : nat) (K : iProp Sigma) : iProp Sigma :=\n"
                " ((∃ (bytes : list (bv " + width + ")), "
                "(base) ↦ₘ" + fraction + "∗ (bytes) ∗ True) ∗ K)%I.\n")

    def test_execution_and_decoder_replay_preserve_provenance(self):
        facts = self.facts()
        self.assertEqual([item["kind"] for item in facts], ["execution", "decoder"])
        self.assertTrue(all(item["owners"] == [self.owner] for item in facts))
        self.assertEqual(facts[1]["source_references"][0]["source"], self.source)
        self.assertEqual(self.catalog.owned_lists, ())

    def test_changed_source_bytes_refuse(self):
        self.path.write_text("{}")
        with self.assertRaisesRegex(ValueError, "document changed"):
            self.facts()

    def test_changed_original_clause_refuses(self):
        self.source["original_term"] = "invented_fact bytes"
        with self.assertRaisesRegex(ValueError, "clause or provenance"):
            self.facts()

    def test_changed_expansion_refuses(self):
        self.row["execution_facts"][0]["expansion"] = []
        with self.assertRaisesRegex(ValueError, "expansion certificate"):
            self.facts()

    def test_unreproduced_execution_leaf_refuses(self):
        self.row["execution_facts"][0]["term"] = "length bytes = invented"
        with self.assertRaisesRegex(ValueError, "does not reproduce"):
            self.facts()

    def test_replayed_integer_scope_is_preserved(self):
        self.catalog.lower = lambda original, binders: (
            ["value = (0%Z)"], [], self.catalog.expansion)
        self.report["unsupported"] = []
        self.row["execution_facts"][0]["term"] = "value = (0)"
        self.assertEqual(self.facts()[0]["term"], "value = (0%Z)")
        self.row["execution_facts"][0]["term"] = "value = (0%nat)"
        with self.assertRaisesRegex(ValueError, "does not reproduce"):
            self.facts()

    def test_unowned_decoder_remains_an_explicit_refusal(self):
        self.row["resources"] = []
        refusals = []
        selected = certified_execution_facts(self.report, self.row, self.catalog,
                                             refusals=refusals)
        self.assertEqual(len(selected), 1)
        self.assertEqual(refusals[0]["pointer"], "/unsupported/0")
        self.assertEqual(refusals[0]["source"], self.source)

    def test_wrong_source_scope_refuses(self):
        self.row["existentials"] = [{"name": "bytes", "type": "list (bv 64)"}]
        with self.assertRaisesRegex(ValueError, "binder scope"):
            self.facts()

    def test_missing_or_duplicate_decoder_owner_refuses(self):
        for owners in [[], [self.owner, self.owner]]:
            with self.subTest(owners=owners), self.assertRaisesRegex(ValueError, "one exact owned"):
                decoder_owner(self.catalog.decoder, owners)

    def test_unknown_decoder_value_refuses(self):
        self.catalog.decoder = self.catalog.decoder.replace("value", "unknown")
        self.report["unsupported"][0]["unsupported"]["term"] = self.catalog.decoder
        with self.assertRaisesRegex(ValueError, "unsupported source symbol"):
            self.facts()

    def test_implication_is_not_a_decoder_leaf(self):
        self.assertIsNone(decoder_owner("condition -> " + self.catalog.decoder, [self.owner]))
        self.assertIsNone(decoder_owner(self.catalog.decoder + " -> value > 0", [self.owner]))
        self.assertIsNone(decoder_owner(self.catalog.decoder + " /\\ value > 0", [self.owner]))

    def test_changed_source_owner_refuses(self):
        self.owner["fraction"] = "q"
        with self.assertRaisesRegex(ValueError, "source owner or fraction"):
            self.facts()

    def test_renderer_preserves_scope_resources_and_continuation(self):
        old = self.declaration()
        new, additions = retain_definition_facts(old, "sample", self.row, self.facts())
        self.assertEqual(len(additions), 2)
        for item in additions:
            new = new.replace("⌜" + item["term"] + "⌝ ∗ ", "", 1)
        self.assertEqual(new, old)

    def test_wrong_width_or_fraction_refuses(self):
        for source in [self.declaration(width="64%N"), self.declaration(fraction="{q}")]:
            with self.subTest(source=source), self.assertRaises(ValueError):
                retain_definition_facts(source, "sample", self.row, self.facts())

    def test_renderer_refuses_another_entry_certificate(self):
        facts = self.facts()
        facts[0]["source_references"][0]["source"]["pc"] = "sibling"
        with self.assertRaisesRegex(ValueError, "another entry scope"):
            retain_definition_facts(self.declaration(), "sample", self.row, facts)

    def test_existing_fact_is_not_duplicated(self):
        new, _ = retain_definition_facts(self.declaration(), "sample", self.row, self.facts())
        again, additions = retain_definition_facts(new, "sample", self.row, self.facts())
        self.assertEqual(again, new)
        self.assertEqual(additions, [])

    def test_introduction_uses_complete_retained_body(self):
        new, _ = retain_definition_facts(self.declaration(), "sample", self.row, self.facts())
        introduction = definition_introduction_source(new, "sample")
        self.assertIn("⌜" + self.catalog.decoder + "⌝", introduction)
        self.assertIn("@PreOrder_Reflexive _ _ bi.entails_po _", introduction)
        self.assertNotIn("Proof.", introduction)

    def test_nat_length_literal_has_its_source_type(self):
        rendered, changes = typed_nat_literals("length (bytes) = 16")
        self.assertEqual(rendered, "length (bytes) = (16%nat)")
        self.assertEqual(changes[0]["position"], "list length equality")

    def test_nested_slice_literals_keep_nat_scope(self):
        rendered, changes = typed_nat_literals(
            "littleEndian (firstn 8 (skipn (0) bytes)) = value")
        self.assertEqual(rendered,
            "littleEndian (firstn (8%nat) (skipn ((0%nat)) bytes)) = value")
        self.assertEqual(len(changes), 2)
        self.assertEqual(typed_nat_literals(rendered), (rendered, []))

    def test_explicit_scopes_and_symbolic_indices_remain_exact(self):
        for term in ("firstn 8%nat bytes", "firstn (8%nat) bytes",
                     "firstn (8%Z) bytes", "length bytes = size",
                     "value = 16%Z", "firstn count (skipn offset bytes)",
                     "(length bytes = 16)%Z",
                     "firstn (Z.to_nat (value + 1)) bytes"):
            self.assertEqual(typed_nat_literals(term), (term, []))

    def test_unrelated_source_bytes_and_reversed_equality_remain_exact(self):
        rendered, changes = typed_nat_literals(
            "littleEndian(firstn 8 bytes) = (value + 16)%Z")
        self.assertEqual(rendered,
            "littleEndian(firstn (8%nat) bytes) = (value + 16)%Z")
        self.assertEqual(len(changes), 1)
        self.assertEqual(typed_nat_literals("16 = List.length bytes")[0],
                         "(16%nat) = List.length bytes")

    def test_typed_rendering_keeps_original_certificate(self):
        facts = self.facts()
        facts[0]["term"] = "length (bytes) = 16"
        new, additions = retain_definition_facts(self.declaration(), "sample", self.row, facts)
        self.assertIn("⌜length (bytes) = (16%nat)⌝", new)
        self.assertEqual(additions[0]["source_term"], facts[0]["term"])
        self.assertEqual(additions[0]["source_references"], facts[0]["source_references"])
        self.assertNotIn("source_term", facts[0])


if __name__ == "__main__":
    unittest.main()
