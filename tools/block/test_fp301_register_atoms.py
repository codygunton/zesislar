"""Check that computed entry register values render as atoms with separate facts."""
import json
from pathlib import Path
import re
import unittest

from render_fp301_statements import render_register_atoms, selected_loop_declaration

ROOT = Path(__file__).resolve().parents[2]
FACT = re.compile(r" ∗ ⌜\(bv_unsigned (entry_\w+) = bv_unsigned \((.*?)\)\)%Z⌝(?= ∗ ⌜\(bv_unsigned entry_|\)\))")
HEADER = "Definition d `{!islaG Sigma} (args : DecodeItemArgs) (returnAddress : Z) : iProp Sigma := "


def declarations():
    """Yield forward entry sources; loop heads render from their own fixture."""
    for name in ["fp301-generation.json", "fp301-loop-successors.json"]:
        rows = json.loads((ROOT / "tools/block/fixtures" / name).read_text())["declarations"]
        yield from (row for row in rows if "∃" in row["canonical_source"]
                    and selected_loop_declaration(row["canonical_source"], "") is None)


def restore(rendered):
    """Put each fact's value back into its register and drop the atom."""
    for atom, value in FACT.findall(rendered):
        rendered = rendered.replace(" ∗ ⌜(bv_unsigned " + atom + " = bv_unsigned (" + value + "))%Z⌝", "", 1)
        rendered = rendered.replace("(" + atom + " : bv 64) ", "", 1)
        rendered = rendered.replace("(RVal_Bits (" + atom + " : bv 64%N))",
                                    "(RVal_Bits ((" + value + ") : bv 64%N))", 1)
    return rendered


class RegisterAtoms(unittest.TestCase):
    def test_only_computed_values_change_and_their_facts_restore_the_source(self):
        changed = {}
        for row in declarations():
            source = row["canonical_source"]
            rendered = render_register_atoms(source)
            with self.subTest(output=row["output"]):
                self.assertEqual(restore(rendered), source)
                self.assertEqual(render_register_atoms(rendered), rendered)
            if rendered != source and row["output"].endswith("Entries.v"):
                changed[row["output"].rsplit("Pilot", 1)[1][:4]] = re.findall(r"\(entry_(\w+) : bv 64\)", rendered)
        self.assertEqual(len(changed), 17)
        self.assertEqual(changed["6a78"], ["x13"])
        self.assertEqual(changed["6a14"], ["x13", "x14"])
        self.assertEqual(changed["6a40"], ["x13", "x14", "x15"])

    def test_plain_values_stay(self):
        values = ["a5", "(BV 64%N 248%Z)", "decodeItemSavedFramePointer args",
                  "((Z_to_bv 64%N (decodeItemInputPointer args)))",
                  "(bv_add ((Z_to_bv 64%N (decodeItemStackPointer args))) (BV 64%N 16%Z))"]
        for value in values:
            source = HEADER + '(∃ (a5 : bv 64), ("x9" ↦ᵣ (RVal_Bits (' + value + " : bv 64%N)) ∗ ⌜True⌝))%I.\n"
            self.assertEqual(render_register_atoms(source), source)

    def test_computed_value_outside_an_existential_is_refused(self):
        source = HEADER + '("x9" ↦ᵣ (RVal_Bits ((bv_and a5 (BV 64%N 1%Z)) : bv 64%N)))%I.\n'
        with self.assertRaisesRegex(ValueError, "outside an existential body"):
            render_register_atoms(source)


if __name__ == "__main__":
    unittest.main()
