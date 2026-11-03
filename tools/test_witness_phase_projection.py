import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / "block"))
from witness_data import declared_witness_slots
from witness_phase_projection import project_witness_phase


class WitnessPhaseProjectionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "Entries.v"
        self.source.write_text(r'''Definition source : iProp Sigma := True.
Definition target : iProp Sigma :=
  ∃ (a b dead c : bv 64) (i : lvar "index" Z)
    (d dead_two dead_three e f g h j k : bv 64),
    ⌜a=a /\ b=b /\ c=c /\ i=i /\ d=d /\ e=e /\ f=f /\ g=g /\ h=h /\ j=j /\ k=k⌝ ∗ True.
''')
        self.fragment = self.root / "Data.vpart"
        self.fragment.write_text("Definition full_data (values : unit) := values.\n")
        layout = declared_witness_slots(self.source.read_text(), "target")
        vacuous = {slot["name"] for slot in layout["vacuous"]}
        self.slots = [dict(slot, vacuous=slot["name"] in vacuous)
                      for slot in layout["declared"]]
        self.full = {"schema": "source.full-witness-mapping.v1",
                     "source_declaration": dict(self.bind(self.source), declaration="source"),
                     "target_declaration": dict(self.bind(self.source), declaration="target"),
                     "mapping_fragment": self.bind(self.fragment), "slots": self.slots}
        self.phase = {"schema": "source.witness-phase.v1", "full_metadata": None,
                      "retained": [{"source_index": i, "name": self.slots[i]["name"]}
                                   for i in [2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]],
                      "resolved": [{"source_index": i, "name": self.slots[i]["name"]}
                                   for i in [0, 1, 3]]}

    @staticmethod
    def bind(path):
        return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}

    def run_projection(self, full=None, phase=None):
        full = copy.deepcopy(self.full if full is None else full)
        phase = copy.deepcopy(self.phase if phase is None else phase)
        full_path = self.root / "Full.json"
        full_path.write_text(json.dumps({"full": full}))
        full_binding = dict(self.bind(full_path), pointer="/full")
        phase["full_metadata"] = full_binding
        phase_path = self.root / "Phase.json"
        phase_path.write_text(json.dumps({"phase": phase}))
        return project_witness_phase(full_binding, dict(self.bind(phase_path), pointer="/phase"))

    def test_full_fourteen_to_eleven(self):
        result = self.run_projection()
        self.assertEqual(result["source_indices"], [2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13])
        self.assertEqual(len(self.slots), 14)
        self.assertEqual(len(result["slots"]), 11)
        self.assertEqual(sum(slot["vacuous"] for slot in result["slots"]), 3)
        self.assertEqual(result["internal_order"][9]["name"], "i")
        self.assertFalse(result["values_inferred_from_types"])

    def test_same_type_name_swap_refuses(self):
        self.phase["retained"][0]["name"], self.phase["retained"][2]["name"] = (
            self.phase["retained"][2]["name"], self.phase["retained"][0]["name"])
        with self.assertRaisesRegex(ValueError, "name differs"):
            self.run_projection()

    def test_second_reversal_refuses(self):
        self.phase["retained"].reverse()
        with self.assertRaisesRegex(ValueError, "source order"):
            self.run_projection()

    def test_missing_full_slot_refuses(self):
        self.full["slots"].pop()
        with self.assertRaisesRegex(ValueError, "slot count"):
            self.run_projection()

    def test_missing_phase_slot_refuses(self):
        self.phase["retained"].pop()
        with self.assertRaisesRegex(ValueError, "omits or duplicates"):
            self.run_projection()

    def test_vacuous_slot_cannot_disappear(self):
        slot = self.phase["retained"].pop(0)
        self.phase["resolved"].append(slot)
        self.phase["resolved"].sort(key=lambda value: value["source_index"])
        with self.assertRaisesRegex(ValueError, "retain every vacuous"):
            self.run_projection()

    def test_target_only_provenance_refuses(self):
        self.full["source_declaration"] = self.full["target_declaration"]
        with self.assertRaisesRegex(ValueError, "Target-only provenance"):
            self.run_projection()

    def test_changed_type_refuses(self):
        self.full["slots"][0]["type"] = "bv 32"
        with self.assertRaisesRegex(ValueError, "type"):
            self.run_projection()

    def test_false_vacuous_flag_refuses(self):
        self.full["slots"][2]["vacuous"] = False
        with self.assertRaisesRegex(ValueError, "vacuous flag"):
            self.run_projection()

    def test_boolean_index_refuses(self):
        self.phase["retained"][0]["source_index"] = True
        with self.assertRaisesRegex(ValueError, "source index"):
            self.run_projection()


if __name__ == "__main__":
    unittest.main()
