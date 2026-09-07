import importlib.util
import tempfile
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
        template = ROOT / "ZesuSsz/Evidence/templates/constant_write/constant_write.v.tmpl"
        rendered = GENERATOR.render_constant_write(
            template, ROOT / "generated/isla-traces", 0x15698
        )
        self.assertEqual(rendered, target.read_text())
        self.assertIn("Lemma segment_15698 ", rendered)
        self.assertIn("Lemma segment_15698_covered ", rendered)

    def test_15694_rejects_unsupported_shape(self):
        template = ROOT / "ZesuSsz/Evidence/templates/constant_write/constant_write.v.tmpl"
        with self.assertRaisesRegex(ValueError, "unsupported trace shape"):
            GENERATOR.render_constant_write(
                template, ROOT / "generated/isla-traces", 0x15694
            )

    def test_101d4_generates_a_distinct_pair(self):
        template = ROOT / "ZesuSsz/Evidence/templates/constant_write/constant_write.v.tmpl"
        target = ROOT / "ZesuSsz/Experiments/WriteSuccessSegment101d4.v"
        rendered = GENERATOR.render_constant_write(
            template, ROOT / "generated/isla-traces", 0x101D4
        )
        self.assertEqual(rendered, target.read_text())
        self.assertIn("Lemma segment_101d4 ", rendered)
        self.assertIn("Lemma segment_101d4_covered ", rendered)
        self.assertIn('"x15"', rendered)
        self.assertIn("BV 64 0", rendered)

    def test_constant_write_regenerates_remaining_pairs(self):
        template = ROOT / "ZesuSsz/Evidence/templates/constant_write/constant_write.v.tmpl"
        expected = {
            0x15D20: ("WriteSuccessSegment15d20.v", '"x11"', "BV 64 8", 3),
            0x156C0: ("WriteSuccessSegment156c0.v", '"x11"', "BV 64 20", 1),
        }
        for pc, (name, register, constant, occurrences) in expected.items():
            target = ROOT / "ZesuSsz/Experiments" / name
            rendered = GENERATOR.render_constant_write(
                template, ROOT / "generated/isla-traces", pc
            )
            self.assertEqual(rendered, target.read_text())
            self.assertIn(f"Lemma segment_{pc:x} ", rendered)
            self.assertIn(f"Lemma segment_{pc:x}_covered ", rendered)
            self.assertIn(register, rendered)
            self.assertIn(constant, rendered)
            self.assertEqual(GENERATOR.ITERATION_PCS.count(pc), occurrences)

    def test_1569c_regenerates_register_add_pair(self):
        template = ROOT / "ZesuSsz/Evidence/templates/register_add/register_add.v.tmpl"
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
        template = ROOT / "ZesuSsz/Evidence/templates/pc_add_write/pc_add_write.v.tmpl"
        rendered = GENERATOR.render_pc_add_write(
            template, ROOT / "generated/isla-traces", 0x156A0
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
            template_name = name.replace("156a4", "IndirectJump") + ".tmpl"
            template = ROOT / "ZesuSsz/Evidence/templates/indirect_jump" / template_name
            text = GENERATOR.render_indirect_jump(
                template, ROOT / "generated/isla-traces", 0x156A4
            )
            self.assertEqual(text, target.read_text())
            rendered.append(text)
        self.assertIn("Lemma segment_156a4_mstatus ", rendered[0])
        self.assertIn("Lemma segment_156a4_mstatus_covered ", rendered[-1])

    def test_indirect_jump_rejects_other_trace_shape(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/indirect_jump/"
            "WriteSuccessSegmentIndirectJump.v.tmpl"
        )
        with self.assertRaisesRegex(ValueError, "supports only 0x156a4"):
            GENERATOR.render_indirect_jump(
                template, ROOT / "generated/isla-traces", 0x156A0
            )

    def test_101d8_conditional_branch_metadata(self):
        path, left, right = GENERATOR.conditional_branch_metadata(
            ROOT / "generated/isla-traces", 0x101D8
        )
        self.assertEqual(path.parent.name, "write_success_02")
        self.assertEqual((left, right), ("x15", "x12"))

    def test_101d8_regenerates_conditional_branch_pair(self):
        names = [
            "WriteSuccessSegment101d8.v",
            "WriteSuccessSegment101d8CoveragePrefix6.v",
            "WriteSuccessSegment101d8CoveragePrefix12.v",
            "WriteSuccessSegment101d8CoverageTaken.v",
            "WriteSuccessSegment101d8CoverageFallthrough.v",
            "WriteSuccessSegment101d8Coverage.v",
        ]
        rendered = []
        for name in names:
            target = ROOT / "ZesuSsz/Experiments" / name
            template_name = name.replace("101d8", "ConditionalBranch") + ".tmpl"
            template = ROOT / "ZesuSsz/Evidence/templates/conditional_branch" / template_name
            text = GENERATOR.render_conditional_branch(
                template, ROOT / "generated/isla-traces", 0x101D8
            )
            self.assertEqual(text, target.read_text())
            rendered.append(text)
        self.assertIn("Lemma segment_101d8_mstatus ", rendered[0])
        self.assertIn("Lemma segment_101d8_mstatus_covered ", rendered[-1])

    def test_conditional_branch_rejects_linear_trace(self):
        with self.assertRaisesRegex(ValueError, "unsupported trace shape"):
            GENERATOR.conditional_branch_metadata(
                ROOT / "generated/isla-traces", 0x101D4
            )

    def test_conditional_branch_renderer_rejects_other_pc(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/conditional_branch/"
            "WriteSuccessSegmentConditionalBranch.v.tmpl"
        )
        with self.assertRaisesRegex(ValueError, "supports only 0x101d8"):
            GENERATOR.render_conditional_branch(
                template, ROOT / "generated/isla-traces", 0x101E0
            )

    def test_101f4_regenerates_direct_jump_pair(self):
        names = [
            "WriteSuccessSegment101f4.v",
            "WriteSuccessSegment101f4CoveragePrefix.v",
            "WriteSuccessSegment101f4CoverageSuffix.v",
            "WriteSuccessSegment101f4Coverage.v",
        ]
        rendered = []
        for name in names:
            target = ROOT / "ZesuSsz/Experiments" / name
            template_name = name.replace("101f4", "DirectJump") + ".tmpl"
            template = ROOT / "ZesuSsz/Evidence/templates/direct_jump" / template_name
            text = GENERATOR.render_direct_jump(
                template, ROOT / "generated/isla-traces", 0x101F4
            )
            self.assertEqual(text, target.read_text())
            rendered.append(text)
        self.assertEqual(GENERATOR.ITERATION_PCS.count(0x101F4), 48)
        self.assertIn("Lemma segment_101f4 ", rendered[0])
        self.assertIn("Lemma segment_101f4_covered ", rendered[-1])

    def test_direct_jump_rejects_other_trace_shape(self):
        with self.assertRaisesRegex(ValueError, "unsupported trace shape"):
            GENERATOR.direct_jump_metadata(
                ROOT / "generated/isla-traces", 0x101D4
            )

    def test_direct_jump_renderer_rejects_other_pc(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/direct_jump/"
            "WriteSuccessSegmentDirectJump.v.tmpl"
        )
        with self.assertRaisesRegex(ValueError, "supports only 0x101f4"):
            GENERATOR.render_direct_jump(
                template, ROOT / "generated/isla-traces", 0x101E0
            )

    def test_two_register_add_metadata(self):
        expected = {
            0x101E0: ("x11", "x15", "x13"),
            0x101E8: ("x10", "x15", "x14"),
        }
        for pc, registers in expected.items():
            path, left, right, destination = (
                GENERATOR.two_register_add_metadata(
                    ROOT / "generated/isla-traces", pc
                )
            )
            self.assertEqual(path.parent.name, "write_success_02")
            self.assertEqual((left, right, destination), registers)

    def test_two_register_add_rejects_linear_constant_write(self):
        with self.assertRaisesRegex(ValueError, "unsupported trace shape"):
            GENERATOR.two_register_add_metadata(
                ROOT / "generated/isla-traces", 0x101D4
            )

    def test_two_register_add_generates_complete_pairs(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/two_register_add"
        components = [
            "WriteSuccessSegmentTwoRegisterAdd.v.tmpl",
            "WriteSuccessSegmentTwoRegisterAddCoveragePrefix.v.tmpl",
            "WriteSuccessSegmentTwoRegisterAddCoverageSuffix.v.tmpl",
            "WriteSuccessSegmentTwoRegisterAddCoverage.v.tmpl",
        ]
        for pc in (0x101E0, 0x101E8):
            for component in components:
                template = templates / component
                target_name = component.replace("TwoRegisterAdd", f"{pc:x}")
                target_name = target_name.removesuffix(".tmpl")
                target = ROOT / "ZesuSsz/Experiments" / target_name
                rendered = GENERATOR.render_two_register_add(
                    template, ROOT / "generated/isla-traces", pc
                )
                self.assertEqual(rendered, target.read_text())
            self.assertEqual(GENERATOR.ITERATION_PCS.count(pc), 48)

    def test_two_register_add_rejects_altered_proof_output(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/two_register_add/"
            "WriteSuccessSegmentTwoRegisterAdd.v.tmpl"
        )
        rendered = GENERATOR.render_two_register_add(
            template, ROOT / "generated/isla-traces", 0x101E0
        )
        with tempfile.TemporaryDirectory() as temporary_directory:
            altered = Path(temporary_directory) / "WriteSuccessSegment101e0.v"
            altered.write_text(rendered.replace("segment_101e0", "segment_bad", 1))
            with self.assertRaisesRegex(ValueError, "generated segment differs"):
                GENERATOR.check_generated_output(altered, rendered)

    def test_two_register_add_rejects_output_as_template(self):
        output = ROOT / "ZesuSsz/Experiments/WriteSuccessSegment101e0.v"
        with self.assertRaisesRegex(ValueError, "requires a generic template"):
            GENERATOR.render_two_register_add(
                output, ROOT / "generated/isla-traces", 0x101E0
            )


if __name__ == "__main__":
    unittest.main()
