"""Keep native acceptance separate from inventory and pure certificates."""
import json
import unittest
from check_decode_item_route_repair import (INDEX, SITES, acceptance, closed_groups,
                                           declaration, response)


class RouteRepairAcceptanceTests(unittest.TestCase):
    def test_exact_nine_site_inventory(self):
        index = json.loads(INDEX.read_text())
        self.assertEqual([case["block"] for case in index["cases"]], SITES)
        self.assertEqual(sum("terminal" in case["capture_kind"] for case in index["cases"]), 3)
        self.assertEqual(index["reject_controls"],
                         ["s119_literal_committed_witness_conflict",
                          "s119_successor_committed_witness_conflict"])

    def test_no_results_cannot_accept_repair(self):
        index = json.loads(INDEX.read_text())
        bundle = {"repair_identity": {key: index["repair_identity"][key]
                  for key in ("module", "class", "instance")}}
        with self.assertRaises(ValueError):
            acceptance(index, bundle)

    def test_every_actual_group_must_close(self):
        closed_groups({"goals": [], "stack": [], "shelf": [], "given_up": []})
        for group in ("goals", "stack", "shelf", "given_up"):
            data = {"goals": [], "stack": [], "shelf": [], "given_up": []}
            data[group] = ["remaining"]
            with self.subTest(group=group), self.assertRaises(ValueError):
                closed_groups(data)
        with self.assertRaises(ValueError):
            closed_groups({"goals": []})

    def test_pure_certificate_is_not_native_declaration(self):
        with self.assertRaises(ValueError):
            declaration("Lemma pure_fact : True.\nProof. exact I. Qed.",
                        "DesignedBoundary_800d6a24")

    def test_tool_success_does_not_invent_assumptions(self):
        result = response({"raw_response": {"content": [{"type": "text",
                         "text": '{"success":true}'}]}})
        self.assertNotIn("assumptions", result)


if __name__ == "__main__":
    unittest.main()
