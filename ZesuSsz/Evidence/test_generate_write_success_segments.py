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
    def check_constant_write_components(self, pc):
        templates = ROOT / "ZesuSsz/Evidence/templates/constant_write"
        components = {
            "constant_write.v.tmpl": "",
            "constant_write_existence.v.tmpl": "Existence",
            "constant_write_coverage.v.tmpl": "Coverage",
        }
        rendered = {}
        for template_name, suffix in components.items():
            rendered[suffix] = GENERATOR.render_constant_write(
                templates / template_name,
                ROOT / "generated/isla-traces",
                pc,
            )
            target = (
                ROOT / "ZesuSsz/Experiments" /
                f"WriteSuccessSegment{pc:x}{suffix}.v"
            )
            self.assertEqual(rendered[suffix], target.read_text())
        return rendered

    def test_iteration_has_410_pcs(self):
        self.assertEqual(len(GENERATOR.ITERATION_PCS), 410)

    def test_all_45_pilot_pairs_exist_without_global_trace_premises(self):
        self.assertEqual(len(GENERATOR.PILOT_PCS), 45)
        self.assertEqual(len(set(GENERATOR.PILOT_PCS)), 45)
        for pc in GENERATOR.PILOT_PCS:
            files = list(
                (ROOT / "ZesuSsz/Experiments").glob(
                    f"WriteSuccessSegment{pc:x}*.v"
                )
            )
            text = "\n".join(path.read_text() for path in files)
            self.assertIn(f"Lemma segment_{pc:x} ", text)
            self.assertIn(f"Lemma segment_{pc:x}_covered ", text)
            self.assertNotIn("writeSuccessTraceAssumptions", text)

    def test_15698_regenerates_checked_pair(self):
        rendered = self.check_constant_write_components(0x15698)
        self.assertIn("Lemma segment_15698 ", rendered["Existence"])
        self.assertIn("Lemma segment_15698_covered ", rendered["Coverage"])

    def test_15694_rejects_unsupported_shape(self):
        template = ROOT / "ZesuSsz/Evidence/templates/constant_write/constant_write.v.tmpl"
        with self.assertRaisesRegex(ValueError, "unsupported trace shape"):
            GENERATOR.render_constant_write(
                template, ROOT / "generated/isla-traces", 0x15694
            )

    def test_101d4_generates_a_distinct_pair(self):
        rendered = self.check_constant_write_components(0x101D4)
        self.assertIn("Lemma segment_101d4 ", rendered["Existence"])
        self.assertIn("Lemma segment_101d4_covered ", rendered["Coverage"])
        self.assertIn('"x15"', rendered["Existence"])
        self.assertIn("BV 64 0", rendered["Existence"])

    def test_constant_write_regenerates_remaining_pairs(self):
        expected = {
            0x15D20: ("WriteSuccessSegment15d20.v", '"x11"', "BV 64 8", 3),
            0x156C0: ("WriteSuccessSegment156c0.v", '"x11"', "BV 64 20", 1),
        }
        for pc, (name, register, constant, occurrences) in expected.items():
            rendered = self.check_constant_write_components(pc)
            self.assertIn(f"Lemma segment_{pc:x} ", rendered["Existence"])
            self.assertIn(
                f"Lemma segment_{pc:x}_covered ", rendered["Coverage"]
            )
            self.assertIn(register, rendered["Existence"])
            self.assertIn(constant, rendered["Existence"])
            self.assertEqual(GENERATOR.ITERATION_PCS.count(pc), occurrences)

    def test_1569c_regenerates_register_add_pair(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/register_add"
        components = {
            "register_add.v.tmpl": "",
            "register_add_coverage_prefix.v.tmpl": "CoveragePrefix",
            "register_add_coverage_suffix.v.tmpl": "CoverageSuffix",
            "register_add_coverage.v.tmpl": "Coverage",
        }
        rendered = {}
        for template_name, suffix in components.items():
            rendered[suffix] = GENERATOR.render_register_add(
                templates / template_name,
                ROOT / "generated/isla-traces",
                0x1569C,
            )
            target = (
                ROOT / "ZesuSsz/Experiments" /
                f"WriteSuccessSegment1569c{suffix}.v"
            )
            self.assertEqual(rendered[suffix], target.read_text())
        self.assertIn("Lemma segment_1569c ", rendered[""])
        self.assertIn("Lemma segment_1569c_covered ", rendered["Coverage"])
        self.assertIn('"x8"', rendered[""])
        self.assertIn('"x11"', rendered[""])

    def test_15694_regenerates_register_add_pair(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/register_add"
        components = {
            "register_add.v.tmpl": "",
            "register_add_coverage_prefix.v.tmpl": "CoveragePrefix",
            "register_add_coverage_suffix.v.tmpl": "CoverageSuffix",
            "register_add_coverage.v.tmpl": "Coverage",
        }
        rendered = {}
        for template_name, suffix in components.items():
            rendered[suffix] = GENERATOR.render_register_add(
                templates / template_name,
                ROOT / "generated/isla-traces",
                0x15694,
            )
            target = (
                ROOT / "ZesuSsz/Experiments" /
                f"WriteSuccessSegment15694{suffix}.v"
            )
            self.assertEqual(rendered[suffix], target.read_text())
        self.assertIn("Lemma segment_15694 ", rendered[""])
        self.assertIn("Lemma segment_15694_covered ", rendered["Coverage"])
        self.assertNotIn(
            "writeSuccessTraceAssumptions", "".join(rendered.values())
        )

    def test_register_add_generates_remaining_complete_pairs(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/register_add"
        components = {
            "register_add.v.tmpl": "",
            "register_add_coverage_prefix.v.tmpl": "CoveragePrefix",
            "register_add_coverage_suffix.v.tmpl": "CoverageSuffix",
            "register_add_coverage.v.tmpl": "Coverage",
        }
        pcs = (0x101EC, 0x15D10, 0x15D1C, 0x10194,
               0x15D30, 0x156C4, 0x156DC, 0x156E0)
        for pc in pcs:
            for template_name, suffix in components.items():
                rendered = GENERATOR.render_register_add(
                    templates / template_name,
                    ROOT / "generated/isla-traces", pc
                )
                target = (
                    ROOT / "ZesuSsz/Experiments" /
                    f"WriteSuccessSegment{pc:x}{suffix}.v"
                )
                self.assertEqual(rendered, target.read_text())
            public = (
                ROOT / "ZesuSsz/Experiments" /
                f"WriteSuccessSegment{pc:x}Coverage.v"
            ).read_text()
            self.assertIn(f"Lemma segment_{pc:x}_covered ", public)

    def test_156a0_regenerates_pc_add_write_pair(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/pc_add_write"
        components = {
            "pc_add_write_legacy_defs.v.tmpl": "Defs",
            "pc_add_write_legacy_existence_prefix.v.tmpl": "ExistencePrefix",
            "pc_add_write_legacy_existence_suffix.v.tmpl": "ExistenceSuffix",
            "pc_add_write_legacy_existence.v.tmpl": "Existence",
            "pc_add_write_legacy.v.tmpl": "",
            "pc_add_write_legacy_coverage_prefix.v.tmpl": "CoveragePrefix",
            "pc_add_write_legacy_coverage_suffix.v.tmpl": "CoverageSuffix",
            "pc_add_write_legacy_coverage.v.tmpl": "Coverage",
        }
        rendered = {}
        for template_name, suffix in components.items():
            text = GENERATOR.render_pc_add_write(
                templates / template_name,
                ROOT / "generated/isla-traces", 0x156A0
            )
            target = (
                ROOT / "ZesuSsz/Experiments" /
                f"WriteSuccessSegment156a0{suffix}.v"
            )
            self.assertEqual(text, target.read_text())
            rendered[suffix] = text
        self.assertIn("Lemma segment_156a0_mstatus ", rendered["Existence"])
        self.assertIn("Lemma segment_156a0_mstatus_covered ", rendered["Coverage"])
        self.assertIn("writeSuccess156a0Link", rendered["Defs"])

    def test_pc_add_write_generates_remaining_complete_pairs(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/pc_add_write"
        components = {
            "pc_add_write.v.tmpl": "",
            "pc_add_write_coverage_prefix.v.tmpl": "CoveragePrefix",
            "pc_add_write_coverage_suffix.v.tmpl": "CoverageSuffix",
            "pc_add_write_coverage.v.tmpl": "Coverage",
        }
        pcs = (0x156AC, 0x15D24, 0x10190, 0x156B8, 0x156C8, 0x156D4)
        for pc in pcs:
            for template_name, suffix in components.items():
                rendered = GENERATOR.render_pc_add_write(
                    templates / template_name,
                    ROOT / "generated/isla-traces", pc
                )
                target = (
                    ROOT / "ZesuSsz/Experiments" /
                    f"WriteSuccessSegment{pc:x}{suffix}.v"
                )
                self.assertEqual(rendered, target.read_text())
            public = (
                ROOT / "ZesuSsz/Experiments" /
                f"WriteSuccessSegment{pc:x}Coverage.v"
            ).read_text()
            self.assertIn(f"Lemma segment_{pc:x}_covered ", public)

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
            if "CoverageSuffixFirst" in name:
                template_name = "WriteSuccessSegmentIndirectJumpCoverageSuffixFirstLegacy.v.tmpl"
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
        with self.assertRaisesRegex(ValueError, "unsupported trace shape"):
            GENERATOR.render_indirect_jump(
                template, ROOT / "generated/isla-traces", 0x156A0
            )

    def test_indirect_jump_generates_remaining_complete_pairs(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/indirect_jump"
        components = {
            "WriteSuccessSegmentIndirectJump.v.tmpl": "",
            "WriteSuccessSegmentIndirectJumpCoveragePrefix.v.tmpl":
                "CoveragePrefix",
            "WriteSuccessSegmentIndirectJumpCoverageSuffixFirst.v.tmpl":
                "CoverageSuffixFirst",
            "WriteSuccessSegmentIndirectJumpCoverageSuffixFirstOne.v.tmpl":
                "CoverageSuffixFirstOne",
            "WriteSuccessSegmentIndirectJumpCoverageSuffixSecondOne.v.tmpl":
                "CoverageSuffixSecondOne",
            "WriteSuccessSegmentIndirectJumpCoverageSuffixLast.v.tmpl":
                "CoverageSuffixLast",
            "WriteSuccessSegmentIndirectJumpCoverage.v.tmpl": "Coverage",
        }
        for pc in (0x156B0, 0x15D28, 0x156BC, 0x156CC, 0x156D8):
            for template_name, suffix in components.items():
                rendered = GENERATOR.render_indirect_jump(
                    templates / template_name,
                    ROOT / "generated/isla-traces", pc
                )
                target = (
                    ROOT / "ZesuSsz/Experiments" /
                    f"WriteSuccessSegment{pc:x}{suffix}.v"
                )
                self.assertEqual(rendered, target.read_text())
            public = (
                ROOT / "ZesuSsz/Experiments" /
                f"WriteSuccessSegment{pc:x}Coverage.v"
            ).read_text()
            self.assertIn(f"Lemma segment_{pc:x}_covered ", public)

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

    def test_long_memory_read_generates_complete_pair(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/memory_read_long"
        for template in templates.glob("*.tmpl"):
            target_name = template.name.replace("MemoryReadLong", "101e4")
            target = ROOT / "ZesuSsz/Experiments" / target_name.removesuffix(".tmpl")
            rendered = GENERATOR.render_memory_read_long(
                template, ROOT / "generated/isla-traces", 0x101E4
            )
            self.assertEqual(rendered, target.read_text())
        self.assertEqual(GENERATOR.ITERATION_PCS.count(0x101E4), 48)

    def test_long_memory_read_rejects_other_shape(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/memory_read_long/"
            "WriteSuccessSegmentMemoryReadLong.v.tmpl"
        )
        with self.assertRaisesRegex(ValueError, "unsupported long memory-read"):
            GENERATOR.render_memory_read_long(
                template, ROOT / "generated/isla-traces", 0x101F0
            )

    def test_long_memory_read_rejects_altered_proof_output(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/memory_read_long/"
            "WriteSuccessSegmentMemoryReadLong.v.tmpl"
        )
        rendered = GENERATOR.render_memory_read_long(
            template, ROOT / "generated/isla-traces", 0x101E4
        )
        with tempfile.TemporaryDirectory() as temporary_directory:
            altered = Path(temporary_directory) / "WriteSuccessSegment101e4.v"
            altered.write_text(rendered.replace("segment_101e4", "segment_bad", 1))
            with self.assertRaisesRegex(ValueError, "generated segment differs"):
                GENERATOR.check_generated_output(altered, rendered)

    def test_byte_memory_write_generates_complete_pair(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/memory_write_byte"
        for template in templates.glob("*.tmpl"):
            target_name = template.name.replace("MemoryWriteByte", "101f0")
            target = ROOT / "ZesuSsz/Experiments" / target_name.removesuffix(".tmpl")
            rendered = GENERATOR.render_memory_write_byte(
                template, ROOT / "generated/isla-traces", 0x101F0
            )
            self.assertEqual(rendered, target.read_text())
        self.assertEqual(GENERATOR.ITERATION_PCS.count(0x101F0), 48)

    def test_byte_memory_write_rejects_other_shape(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/memory_write_byte/"
            "WriteSuccessSegmentMemoryWriteByte.v.tmpl"
        )
        with self.assertRaisesRegex(ValueError, "unsupported byte memory-write"):
            GENERATOR.render_memory_write_byte(
                template, ROOT / "generated/isla-traces", 0x101E4
            )

    def test_byte_memory_write_rejects_altered_proof_output(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/memory_write_byte/"
            "WriteSuccessSegmentMemoryWriteByte.v.tmpl"
        )
        rendered = GENERATOR.render_memory_write_byte(
            template, ROOT / "generated/isla-traces", 0x101F0
        )
        with tempfile.TemporaryDirectory() as temporary_directory:
            altered = Path(temporary_directory) / "WriteSuccessSegment101f0.v"
            altered.write_text(rendered.replace("segment_101f0", "segment_bad", 1))
            with self.assertRaisesRegex(ValueError, "generated segment differs"):
                GENERATOR.check_generated_output(altered, rendered)

    def test_output_memory_write_generates_complete_pairs(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/memory_write_output"
        for pc in (0x10198, 0x1019C):
            for template in templates.glob("*.tmpl"):
                target_name = template.name.replace("MemoryWriteOutput", f"{pc:x}")
                target = ROOT / "ZesuSsz/Experiments" / target_name.removesuffix(".tmpl")
                rendered = GENERATOR.render_memory_write_output(
                    template, ROOT / "generated/isla-traces", pc
                )
                self.assertEqual(rendered, target.read_text())

    def test_output_memory_write_rejects_byte_store(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/memory_write_output/"
            "WriteSuccessSegmentMemoryWriteOutput.v.tmpl"
        )
        with self.assertRaisesRegex(ValueError, "supports only"):
            GENERATOR.render_memory_write_output(
                template, ROOT / "generated/isla-traces", 0x101F0
            )

    def test_output_memory_write_rejects_altered_proof_output(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/memory_write_output/"
            "WriteSuccessSegmentMemoryWriteOutput.v.tmpl"
        )
        rendered = GENERATOR.render_memory_write_output(
            template, ROOT / "generated/isla-traces", 0x10198
        )
        with tempfile.TemporaryDirectory() as temporary_directory:
            altered = Path(temporary_directory) / "WriteSuccessSegment10198.v"
            altered.write_text(rendered.replace("segment_10198", "segment_bad", 1))
            with self.assertRaisesRegex(ValueError, "generated segment differs"):
                GENERATOR.check_generated_output(altered, rendered)

    def test_stack_memory_write_generates_complete_pairs(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/memory_write_stack"
        self.assertEqual(len(list(templates.glob("*.tmpl"))), 15)
        for pc in (0x15D14, 0x15D18):
            for template in templates.glob("*.tmpl"):
                target_name = template.name.replace("MemoryWriteStack", f"{pc:x}")
                target = ROOT / "ZesuSsz/Experiments" / target_name.removesuffix(".tmpl")
                rendered = GENERATOR.render_memory_write_stack(
                    template, ROOT / "generated/isla-traces", pc
                )
                self.assertEqual(rendered, target.read_text())

    def test_stack_memory_write_rejects_other_shape(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/memory_write_stack/"
            "WriteSuccessSegmentMemoryWriteStack.v.tmpl"
        )
        with self.assertRaisesRegex(ValueError, "unsupported long memory-write"):
            GENERATOR.render_memory_write_stack(
                template, ROOT / "generated/isla-traces", 0x101E4
            )

    def test_stack_memory_write_rejects_output_store(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/memory_write_stack/"
            "WriteSuccessSegmentMemoryWriteStack.v.tmpl"
        )
        with self.assertRaisesRegex(ValueError, "unsupported stack memory-write"):
            GENERATOR.render_memory_write_stack(
                template, ROOT / "generated/isla-traces", 0x10198
            )

    def test_stack_memory_write_rejects_altered_proof_output(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/memory_write_stack/"
            "WriteSuccessSegmentMemoryWriteStack.v.tmpl"
        )
        rendered = GENERATOR.render_memory_write_stack(
            template, ROOT / "generated/isla-traces", 0x15D14
        )
        with tempfile.TemporaryDirectory() as temporary_directory:
            altered = Path(temporary_directory) / "WriteSuccessSegment15d14.v"
            altered.write_text(rendered.replace("segment_15d14", "segment_bad", 1))
            with self.assertRaisesRegex(ValueError, "generated segment differs"):
                GENERATOR.check_generated_output(altered, rendered)

    def test_stack_memory_read_generates_complete_pairs(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/memory_read_stack"
        self.assertEqual(len(list(templates.glob("*.tmpl"))), 19)
        expected = {
            0x156A8: ("write_success_91", "x2", "x10", 0x6D0),
            0x156B4: ("write_success_92", "x2", "x10", 0x6D8),
            0x156D0: ("write_success_94", "x2", "x10", 0x6E0),
            0x15D2C: ("write_success_07", "x2", "x1", 0x8),
        }
        for pc, metadata in expected.items():
            path, base, destination, offset = GENERATOR.memory_read_stack_metadata(
                ROOT / "generated/isla-traces", pc
            )
            self.assertEqual((path.parent.name, base, destination, offset), metadata)
            for template in templates.glob("*.tmpl"):
                target_name = template.name.replace("MemoryReadStack", f"{pc:x}")
                target = ROOT / "ZesuSsz/Experiments" / target_name.removesuffix(".tmpl")
                rendered = GENERATOR.render_memory_read_stack(
                    template, ROOT / "generated/isla-traces", pc
                )
                self.assertEqual(rendered, target.read_text())

    def test_stack_memory_read_rejects_other_shape(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/memory_read_stack/"
            "WriteSuccessSegmentMemoryReadStack.v.tmpl"
        )
        with self.assertRaisesRegex(ValueError, "unsupported stack memory-read"):
            GENERATOR.render_memory_read_stack(
                template, ROOT / "generated/isla-traces", 0x101E4
            )

    def test_stack_memory_read_rejects_altered_proof_output(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/memory_read_stack/"
            "WriteSuccessSegmentMemoryReadStack.v.tmpl"
        )
        rendered = GENERATOR.render_memory_read_stack(
            template, ROOT / "generated/isla-traces", 0x156A8
        )
        with tempfile.TemporaryDirectory() as temporary_directory:
            altered = Path(temporary_directory) / "WriteSuccessSegment156a8.v"
            altered.write_text(rendered.replace("segment_156a8", "segment_bad", 1))
            with self.assertRaisesRegex(ValueError, "generated segment differs"):
                GENERATOR.check_generated_output(altered, rendered)

    def test_return_generates_complete_pairs(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/return"
        self.assertEqual(len(list(templates.glob("*.tmpl"))), 7)
        for pc in GENERATOR.RETURN_PCS:
            for template in templates.glob("*.tmpl"):
                target_name = template.name.replace("Return", f"{pc:x}")
                target = ROOT / "ZesuSsz/Experiments" / target_name.removesuffix(".tmpl")
                rendered = GENERATOR.render_return(
                    template, ROOT / "generated/isla-traces", pc
                )
                self.assertEqual(rendered, target.read_text())

    def test_return_rejects_other_shape(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/return/"
            "WriteSuccessSegmentReturn.v.tmpl"
        )
        with self.assertRaisesRegex(ValueError, "unsupported return PC"):
            GENERATOR.render_return(
                template, ROOT / "generated/isla-traces", 0x101F4
            )

    def test_return_rejects_altered_proof_output(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/return/"
            "WriteSuccessSegmentReturn.v.tmpl"
        )
        rendered = GENERATOR.render_return(
            template, ROOT / "generated/isla-traces", 0x101A0
        )
        with tempfile.TemporaryDirectory() as temporary_directory:
            altered = Path(temporary_directory) / "WriteSuccessSegment101a0.v"
            altered.write_text(rendered.replace("segment_101a0", "segment_bad", 1))
            with self.assertRaisesRegex(ValueError, "generated segment differs"):
                GENERATOR.check_generated_output(altered, rendered)

    def test_return_rejects_output_as_template(self):
        output = ROOT / "ZesuSsz/Experiments/WriteSuccessSegment101a0.v"
        with self.assertRaisesRegex(ValueError, "requires a generic template"):
            GENERATOR.render_return(
                output, ROOT / "generated/isla-traces", 0x101A0
            )

    def test_bnez_generates_complete_pair(self):
        templates = ROOT / "ZesuSsz/Evidence/templates/bnez"
        self.assertEqual(len(list(templates.glob("*.tmpl"))), 6)
        for template in templates.glob("*.tmpl"):
            target_name = template.name.replace("Bnez", "156e4")
            target = ROOT / "ZesuSsz/Experiments" / target_name.removesuffix(".tmpl")
            rendered = GENERATOR.render_bnez(
                template, ROOT / "generated/isla-traces", 0x156E4
            )
            self.assertEqual(rendered, target.read_text())

    def test_bnez_rejects_unsupported_shape(self):
        with tempfile.TemporaryDirectory() as temporary_directory:
            trace_dir = Path(temporary_directory) / "write_success_bad"
            trace_dir.mkdir()
            (trace_dir / "a156e4.v").write_text(
                "From isla Require Import opsem.\nDefinition a156e4 := tnil.\n"
            )
            with self.assertRaisesRegex(ValueError, "unsupported bnez trace"):
                GENERATOR.bnez_metadata(Path(temporary_directory), 0x156E4)

    def test_bnez_rejects_altered_proof_output(self):
        template = (
            ROOT / "ZesuSsz/Evidence/templates/bnez/"
            "WriteSuccessSegmentBnez.v.tmpl"
        )
        rendered = GENERATOR.render_bnez(
            template, ROOT / "generated/isla-traces", 0x156E4
        )
        with tempfile.TemporaryDirectory() as temporary_directory:
            altered = Path(temporary_directory) / "WriteSuccessSegment156e4.v"
            altered.write_text(rendered.replace("segment_156e4", "segment_bad", 1))
            with self.assertRaisesRegex(ValueError, "generated segment differs"):
                GENERATOR.check_generated_output(altered, rendered)


if __name__ == "__main__":
    unittest.main()
