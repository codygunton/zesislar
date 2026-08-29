import unittest

from generate_islaris_dump import control_flow_constraints, effective_address_constraints


class EffectiveAddressConstraintsTest(unittest.TestCase):
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

    def test_constrains_only_return_instructions(self):
        self.assertEqual(
            control_flow_constraints("ret", "x1"),
            ["= ((_ extract 1 0) x1) 0b00"],
        )
        self.assertEqual(control_flow_constraints("jalr 8(ra)", "x1"), [])


if __name__ == "__main__":
    unittest.main()
