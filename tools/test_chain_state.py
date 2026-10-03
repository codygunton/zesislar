"""Native successor normalization preserves ownership and provenance."""

import copy
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
import chain_state

BINDERS = '`{!islaG Sigma} `{!threadG} (sp : bv 64)'


class ChainStateTests(unittest.TestCase):
    def normalize(self, capture, **kwargs):
        capture = copy.deepcopy(capture)
        sorts = capture.setdefault("local_sorts", {})
        for name, kind in capture.get("coq", []):
            sorts.setdefault(name, "Prop" if name.startswith("H") else "Type")
        return chain_state.normalize_successor(
            capture, entry="0x15930", binders=BINDERS, name="Native_15930", **kwargs)

    def test_exact_registers_persistent_mmio_and_bounds_survive(self):
        capture = {"coq": [["saved", "bv 64"], ["Hbound", "bv_unsigned sp + 48 < 1073741824"]],
                   "spatial": ['"x8" ↦ᵣ RVal_Bits saved', '"x5" ↦ᵣ RVal_Bits (BV 64 7)',
                               '(bv_unsigned sp) ↦ₘ? 48'],
                   "persistent": ['mmio_range 0 8', 'instr 1 None']}
        original = copy.deepcopy(capture)
        state = self.normalize(capture)
        self.assertEqual(capture, original)
        self.assertEqual(state["spatial"], capture["spatial"] + ['mmio_range 0 8'])
        self.assertIn(('Hbound', 'bv_unsigned sp + 48 < 1073741824'), state["coq"])
        self.assertIn(('saved', 'bv 64'), state["coq"])
        source = chain_state.render_successor(state)
        self.assertIn('"x5" ↦ᵣ RVal_Bits (BV 64 7)', source)
        self.assertNotIn('BitsShape 64', source)
        self.assertIn('mmio_range 0 8', source)

    def test_prune_only_unreferenced_locals(self):
        capture = {"coq": [["saved", "bv 64"], ["ghost", "bv 64"],
                           ["Hghost", "ghost = BV 64 0"]],
                   "spatial": ['"x8" ↦ᵣ RVal_Bits saved']}
        self.assertEqual(self.normalize(capture)["coq"], [('saved', 'bv 64')])
        state = self.normalize(capture, provenance={"substitution": "ghost"})
        self.assertIn(('ghost', 'bv 64'), state["coq"])

    def test_strict_bound_keeps_its_actual_local(self):
        capture = {"coq": [["offset", "Z"], ["Hbound", "offset < 48"]],
                   "spatial": ['(bv_unsigned sp) ↦ₘ? 48']}
        state = self.normalize(capture)
        self.assertIn(("offset", "Z"), state["coq"])
        self.assertIn(("Hbound", "offset < 48"), state["coq"])

    def test_fact_about_owned_value_keeps_its_dependency(self):
        capture = {"coq": [["saved", "bv 64"], ["other", "bv 64"],
                           ["Hsame", "saved = other"]],
                   "spatial": ['"x8" ↦ᵣ RVal_Bits saved']}
        self.assertEqual(len(self.normalize(capture)["coq"]), 3)

    def test_dependent_local_type_keeps_its_index(self):
        capture = {"coq": [["width", "N"], ["bits", "bv width"]],
                   "spatial": ['"x8" ↦ᵣ RVal_Bits bits']}
        self.assertEqual(len(self.normalize(capture)["coq"]), 2)

    def test_existing_opaque_equality_is_preserved(self):
        capture = {"coq": [["words", "list (bv 64)"],
                           ["Hpacked", "packed_words_equal words object"]],
                   "local_sorts": {"Hpacked": "Prop"},
                   "spatial": ['(0%Z) ↦ₘ∗ words']}
        source = chain_state.render_successor(self.normalize(capture))
        self.assertIn('packed_words_equal words object', source)

    def test_no_stack_or_unreached_capture_is_accepted(self):
        with self.assertRaisesRegex(ValueError, 'manufacture'):
            self.normalize({"stack_size": 48})
        with self.assertRaisesRegex(ValueError, 'not reached'):
            self.normalize({"outcome": "stalled"})

    def test_explicit_unreachable_successor_is_false(self):
        source = chain_state.render_successor(
            self.normalize({"outcome": "unreachable-successor"}))
        self.assertIn(':= False%I', source)
        self.assertNotIn('↦ₘ?', source)

    def test_explicit_memory_and_trace_widths_are_independent(self):
        capture = {"coq": [], "spatial": ['(0%Z) ↦ₘ 90%bv',
                    'spec_trace (scons (SWriteMem (BV 64 0) 90%bv) tail)'],
                   "memory_word_widths": {'0%Z': 8},
                   "trace_value_widths": {'(BV 64 0)': 64}}
        state = self.normalize(capture)
        source = chain_state.render_successor(state)
        self.assertIn('↦ₘ (BV 8 90)', source)
        self.assertIn('SWriteMem (BV 64 0) (BV 64 90)', source)
        self.assertEqual(state['memory_word_widths'], capture['memory_word_widths'])
        self.assertEqual(state['trace_value_widths'], capture['trace_value_widths'])

    def test_missing_literal_width_is_rejected(self):
        for atom in ['0 ↦ₘ 90%bv', '0 ↦ₘ∗ [90%bv]',
                     'spec_trace (scons (SWriteMem 0 90%bv) tail)']:
            with self.assertRaisesRegex(ValueError, 'missing captured bit width'):
                chain_state.render_successor(self.normalize({'spatial': [atom]}))

    def test_explicit_bitvector_widths_stay_unchanged(self):
        atom = '0 ↦ₘ∗ [(BV 8 90); (83%bv : bv 8)]'
        source = chain_state.render_successor(self.normalize({'spatial': [atom]}))
        self.assertIn(atom, source)

    def test_seal_option_preserves_actual_resources(self):
        capture = {"coq": [], "spatial": ['(bv_unsigned sp) ↦ₘ? 48'],
                   "seal_memory": True, "call_resources": False}
        source = chain_state.render_successor(self.normalize(capture))
        self.assertIn('(bv_unsigned sp) ↦ₘ? 48', source)
        self.assertIn('Native_15930Memory', source)


if __name__ == '__main__':
    unittest.main()
