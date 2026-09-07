import importlib.util
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "ZesuSsz/Evidence/generate_write_success_segments.py"
SPEC = importlib.util.spec_from_file_location("generate_write_success_segments", SCRIPT)
GENERATOR = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(GENERATOR)


class WriteSuccessSegmentGeneratorTest(unittest.TestCase):
    def test_iteration_has_410_pcs(self):
        self.assertEqual(len(GENERATOR.ITERATION_PCS), 410)

    def test_15698_regenerates_checked_pair(self):
        target = ROOT / "ZesuSsz/Experiments/WriteSuccessSegment15698.v"
        rendered = GENERATOR.render_constant_write(
            target, ROOT / "generated/isla-traces", 0x15698
        )
        self.assertEqual(rendered, target.read_text())
        self.assertIn("Lemma segment_15698 ", rendered)
        self.assertIn("Lemma segment_15698_covered ", rendered)

    def test_15694_rejects_unsupported_shape(self):
        target = ROOT / "ZesuSsz/Experiments/WriteSuccessSegment15698.v"
        with self.assertRaisesRegex(ValueError, "unsupported trace shape"):
            GENERATOR.render_constant_write(
                target, ROOT / "generated/isla-traces", 0x15694
            )

    def test_101d4_generates_a_distinct_pair(self):
        target = ROOT / "ZesuSsz/Experiments/WriteSuccessSegment15698.v"
        rendered = GENERATOR.render_constant_write(
            target, ROOT / "generated/isla-traces", 0x101D4
        )
        self.assertIn("Lemma segment_101d4 ", rendered)
        self.assertIn("Lemma segment_101d4_covered ", rendered)
        self.assertIn('"x15"', rendered)
        self.assertIn("BV 64 0", rendered)

    def test_1569c_regenerates_register_add_pair(self):
        template = ROOT / "ZesuSsz/Experiments/WriteSuccessSegment15694.v"
        target = ROOT / "ZesuSsz/Experiments/WriteSuccessSegment1569c.v"
        rendered = GENERATOR.render_register_add(
            template, ROOT / "generated/isla-traces", 0x1569C
        )
        self.assertEqual(rendered, target.read_text())
        self.assertIn("Lemma segment_1569c ", rendered)
        self.assertIn("Lemma segment_1569c_covered ", rendered)
        self.assertIn('"x8"', rendered)
        self.assertIn('"x11"', rendered)

    def test_156a0_regenerates_pc_add_write_pair(self):
        target = ROOT / "ZesuSsz/Experiments/WriteSuccessSegment156a0.v"
        rendered = GENERATOR.render_pc_add_write(
            target, ROOT / "generated/isla-traces", 0x156A0
        )
        self.assertEqual(rendered, target.read_text())
        self.assertIn("Lemma segment_156a0_mstatus ", rendered)
        self.assertIn("Lemma segment_156a0_mstatus_covered ", rendered)
        self.assertIn("writeSuccess156a0Link", rendered)

    def test_156a4_regenerates_indirect_jump_pair(self):
        names = [
            "WriteSuccessSegment156a4.v",
            "WriteSuccessSegment156a4CoveragePrefix.v",
            "WriteSuccessSegment156a4CoverageSuffixFirst.v",
            "WriteSuccessSegment156a4CoverageSuffixLast.v",
            "WriteSuccessSegment156a4Coverage.v",
        ]
        rendered = []
        for name in names:
            target = ROOT / "ZesuSsz/Experiments" / name
            text = GENERATOR.render_indirect_jump(
                target, ROOT / "generated/isla-traces", 0x156A4
            )
            self.assertEqual(text, target.read_text())
            rendered.append(text)
        self.assertIn("Lemma segment_156a4_mstatus ", rendered[0])
        self.assertIn("Lemma segment_156a4_mstatus_covered ", rendered[-1])

    def test_indirect_jump_rejects_other_trace_shape(self):
        target = ROOT / "ZesuSsz/Experiments/WriteSuccessSegment156a4.v"
        with self.assertRaisesRegex(ValueError, "supports only 0x156a4"):
            GENERATOR.render_indirect_jump(
                target, ROOT / "generated/isla-traces", 0x156A0
            )


if __name__ == "__main__":
    unittest.main()
