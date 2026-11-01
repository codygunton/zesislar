"""Unverified source controls for certified predecessor retention."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from render_support import retain_definition_facts
from source_retention import certified_execution_facts, certified_predecessor_facts


class PredecessorRetentionTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / "source.json"
        self.term = "248 <= bv_unsigned (List.nth 0%nat (data) (BV 8%N 0%Z))"
        self.owner = dict(kind="byte_array", address="base", fraction="", value="data")
        self.scope = [dict(name="data", type="list (bv 8%N)")]
        self.provenance = dict(from_block="predecessor", from_instruction="branch")
        self.rows = [dict(pc=pc, definition="forward",
                          parameters=[dict(name="base", type="Z")],
                          existentials=deepcopy(self.scope), resources=[deepcopy(self.owner)],
                          execution_facts=[]) for pc in ("left", "right")]
        entries = [dict(body=dict(at=row["pc"], additional_definitions=[dict(
            suffix="forward", body=dict(existentials=deepcopy(self.scope), components=[
                deepcopy(self.owner), dict(kind="pure", terms=[dict(
                    term=dict(value=self.term), provenance=deepcopy(self.provenance))])]))]))
                   for row in self.rows]
        self.path.write_text(json.dumps(dict(entries=entries)))
        identity = dict(path=str(self.path), sha256=hashlib.sha256(self.path.read_bytes()).hexdigest())
        self.report = dict(unsupported=[dict(source=dict(
            input=identity, pc=row["pc"], definition="forward", component=1, term_index=0,
            original_term=self.term, provenance=deepcopy(self.provenance)), expansion=[])
                                       for row in self.rows])

    def test_one_collector_preserves_the_same_fact_at_both_entries(self):
        class Catalog:
            owned_lists = ()
        for row in self.rows:
            facts = certified_execution_facts(self.report, row, Catalog())
            self.assertEqual(len(facts), 1)
            self.assertEqual(facts[0]["term"], self.term)
            self.assertEqual(facts[0]["kind"], "predecessor")
            self.assertEqual(facts[0]["owners"], [self.owner])

    def test_duplicate_references_keep_one_fact(self):
        self.report["unsupported"].append(deepcopy(self.report["unsupported"][0]))
        facts = certified_predecessor_facts(self.report, self.rows[0])
        self.assertEqual(len(facts), 1)
        self.assertEqual(len(facts[0]["source_references"]), 2)

    def test_missing_predecessor_provenance_refuses(self):
        del self.report["unsupported"][0]["source"]["provenance"]["from_instruction"]
        self.assertEqual(certified_predecessor_facts(self.report, self.rows[0]), [])

    def test_semantic_expansion_refuses(self):
        self.report["unsupported"][0]["expansion"] = [dict(declaration="opaque")]
        self.assertEqual(certified_predecessor_facts(self.report, self.rows[0]), [])

    def test_changed_source_clause_refuses(self):
        self.report["unsupported"][0]["source"]["original_term"] = self.term.replace("248", "249")
        with self.assertRaisesRegex(ValueError, "clause or provenance"):
            certified_predecessor_facts(self.report, self.rows[0])

    def test_changed_source_fraction_refuses(self):
        self.rows[0]["resources"][0]["fraction"] = "q"
        with self.assertRaisesRegex(ValueError, "owner or fraction"):
            certified_predecessor_facts(self.report, self.rows[0])

    def test_unowned_lookup_refuses(self):
        self.report["unsupported"][0]["source"]["original_term"] = self.term.replace("data", "other")
        self.assertEqual(certified_predecessor_facts(self.report, self.rows[0]), [])

    def definition(self, element="8%N", address="base"):
        return ("Definition entry `{!islaG Sigma} `{!threadG} (base : Z) (K : iProp Sigma)"
                " : iProp Sigma := ((∃ (data : list (bv " + element + ")), (" + address +
                ") ↦ₘ∗ (data) ∗ True)) ∗ K)%I.\n")

    def test_renderer_preserves_the_owner_frame_and_existing_bytes(self):
        facts = certified_predecessor_facts(self.report, self.rows[0])
        original = self.definition()
        rendered, added = retain_definition_facts(original, "entry", self.rows[0], facts)
        self.assertEqual(len(added), 1)
        self.assertEqual(rendered.replace("⌜" + added[0]["term"] + "⌝ ∗ ", ""), original)

    def test_renderer_rejects_changed_binder_width(self):
        facts = certified_predecessor_facts(self.report, self.rows[0])
        with self.assertRaisesRegex(ValueError, "typed source binder"):
            retain_definition_facts(self.definition(element="16%N"), "entry", self.rows[0], facts)

    def test_renderer_rejects_changed_owner_address(self):
        facts = certified_predecessor_facts(self.report, self.rows[0])
        with self.assertRaisesRegex(ValueError, "owner or fraction"):
            retain_definition_facts(self.definition(address="base + 1"), "entry", self.rows[0], facts)

    def test_renderer_requires_owner_and_exact_path_provenance(self):
        fact = certified_predecessor_facts(self.report, self.rows[0])[0]
        missing_owner = deepcopy(fact)
        missing_owner["owners"] = []
        with self.assertRaisesRegex(ValueError, "owned array lookup"):
            retain_definition_facts(self.definition(), "entry", self.rows[0], [missing_owner])
        fact["source_references"][0]["expansion"] = [dict(declaration="opaque")]
        with self.assertRaisesRegex(ValueError, "path provenance"):
            retain_definition_facts(self.definition(), "entry", self.rows[0], [fact])


if __name__ == "__main__":
    unittest.main()
