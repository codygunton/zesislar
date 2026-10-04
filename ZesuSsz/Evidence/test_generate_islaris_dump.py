import unittest

from generate_islaris_dump import (
    control_flow_constraints,
    cfg_ranges,
    configured_spec_annotations,
    effective_address_constraints,
    load_store_spec_annotations,
    jump_spec_annotations,
    split_control_flow_range,
)


class EffectiveAddressConstraintsTest(unittest.TestCase):
    def test_generates_configured_instruction_specs(self):
        profile = {
            "instructionSpecs": {
                "0x15680": {
                    "spec": "a15680_addi_spec pc",
                    "tactic": "all: bv_solve.",
                },
            },
        }
        self.assertEqual(
            configured_spec_annotations(0x15680, profile),
            [
                "//@import: InstrSpecs.Specs",
                "//@spec: a15680_addi_spec pc",
                "//@spec_tactic: all: bv_solve.",
            ],
        )
        self.assertEqual(configured_spec_annotations(0x15684, profile), [])

    def test_generates_load_store_specs_from_abi_names(self):
        self.assertEqual(
            load_store_spec_annotations("ld a0,8(s0)"),
            [
                "//@import: InstrSpecs.Specs",
                '//@spec: zesu_ld_spec pc "x10" "x8" (8)',
                "//@spec_tactic: all: (try bv_solve; try lia).",
            ],
        )
        self.assertEqual(load_store_spec_annotations("ld a0,-8(s0)"), [])
        self.assertEqual(
            load_store_spec_annotations("ld a0,0(s1)", {"s0": "x8"}), []
        )
        self.assertEqual(
            load_store_spec_annotations("sd ra,1992(sp)"),
            [
                "//@import: InstrSpecs.Specs",
                '//@spec: zesu_sd_spec pc "x1" "x2" (1992)',
                "//@spec_tactic: all: (try bv_solve; try lia).",
            ],
        )
        self.assertEqual(
            load_store_spec_annotations("ld a0,256(a0)"),
            [
                "//@import: InstrSpecs.Specs",
                '//@spec: zesu_ld_same_spec pc "x10" (256)',
                "//@spec_tactic: all: (try bv_solve; try lia).",
            ],
        )
        self.assertEqual(load_store_spec_annotations("lw a0,0(s0)"), [])

    def test_array_loads_keep_raw_traces(self):
        view = {"base": "a0", "offset": 0, "kind": "byte"}
        for instruction in ("ld a5,120(a0)", "ld a0,256(a0)", "lbu t2,268(a0)"):
            self.assertEqual(
                load_store_spec_annotations(instruction, array_view=view), [])
        self.assertEqual(
            load_store_spec_annotations(
                "ld a5,8(a0)", array_view={"base": "a0", "offset": 0, "kind": "word"}),
            [])

    def test_generates_same_register_jalr_spec(self):
        self.assertEqual(
            jump_spec_annotations("jalr 1116(ra)", {"ra": "x1"}),
            [
                "//@import: InstrSpecs.Specs",
                '//@spec: zesu_jalr_same_spec pc "x1" (BV 64 1116)',
                "//@spec_tactic: all: bv_solve.",
            ],
        )
        self.assertEqual(jump_spec_annotations("jr 0(ra)", {"ra": "x1"}), [])

    def test_generates_exact_store_address_constraints(self):
        self.assertEqual(
            effective_address_constraints("sd ra,1992(sp)", {"sp": "x2"}),
            [
                "= ((_ extract 2 0) (bvadd x2 0x00000000000007c8)) 0b000",
                "bvuge (bvadd x2 0x00000000000007c8) rv_ram_base",
                "bvule (bvadd x2 0x00000000000007c8) "
                "(bvsub (bvadd rv_ram_base rv_ram_size) 0x0000000000000008)",
            ],
        )

    def test_encodes_negative_offsets_as_64_bit_values(self):
        constraints = effective_address_constraints(
            "ld a0,-8(s0)", {"s0": "x8"}
        )
        self.assertIn("(bvadd x8 0xfffffffffffffff8)", constraints[0])

    def test_ignores_unconfigured_bases_and_non_memory_instructions(self):
        self.assertEqual(effective_address_constraints("ld a0,0(s0)", {}), [])
        self.assertEqual(
            effective_address_constraints("addi sp,sp,-16", {"sp": "x2"}), []
        )

    def test_generates_control_flow_alignment_constraints(self):
        self.assertEqual(
            control_flow_constraints("ret", "x1", "PC"),
            ["= ((_ extract 1 0) x1) 0b00"],
        )
        self.assertEqual(
            control_flow_constraints("bne a0,a1,100", "x1", "PC"),
            ["= ((_ extract 1 0) PC) 0b00"],
        )
        self.assertEqual(
            control_flow_constraints("j 100", "x1", "PC"),
            ["= ((_ extract 1 0) PC) 0b00"],
        )
        self.assertEqual(
            control_flow_constraints(
                "jalr 8(ra)", "x1", "PC", {"ra": "x1"}
            ),
            ["= ((_ extract 1 0) (bvadd x1 0x0000000000000008)) 0b00"],
        )
        self.assertEqual(
            control_flow_constraints("jr -108(t1)", "x1", "PC", {"t1": "x6"}),
            ["= ((_ extract 1 0) (bvadd x6 0xffffffffffffff94)) 0b00"],
        )

    def test_splits_ranges_at_branches_calls_and_size_checkpoints(self):
        instructions = [
            (0x100, "addi a0,a0,1"),
            (0x104, "bnez a0,110 <loop>"),
            (0x108, "addi a1,a1,1"),
            (0x10c, "jalr 8(ra)"),
            (0x110, "ret"),
        ]
        self.assertEqual(
            split_control_flow_range(instructions, 0x100, 0x114, 2),
            [(0x100, 0x108), (0x108, 0x110), (0x110, 0x114)],
        )

    def test_selects_reviewed_regions_and_blocks_from_cfg(self):
        cfg = {"functions": [
            {"name": "caller", "start": 0x100, "size": 0x20,
             "blocks": [
                 {"start": 0x100, "end": 0x108, "instructions": [
                     {"pc": 0x100}, {"pc": 0x104}]},
                 {"start": 0x108, "end": 0x120, "instructions": [
                     {"pc": 0x108}, {"pc": 0x10c}, {"pc": 0x110}]},
             ]},
            {"name": "helper", "start": 0x200, "size": 0x10,
             "blocks": [{"start": 0x200, "end": 0x210,
                         "instructions": [{"pc": 0x200}]}]},
        ]}
        profile = {
            "cfgRegions": [
                {"function": "caller", "block": 0},
                {"function": "helper"},
            ],
            "cfgBlockFunctions": [
                {"function": "caller", "maxInstructions": 2}],
            "cfgPostRegions": [
                {"function": "helper"},
                {"function": "caller", "block": 0},
            ],
        }
        self.assertEqual(cfg_ranges(cfg, profile), (
            [(0x100, 0x108), (0x200, 0x210),
             (0x100, 0x108), (0x108, 0x110), (0x110, 0x120),
             (0x200, 0x210), (0x100, 0x108)],
            2,
        ))


if __name__ == "__main__":
    unittest.main()
