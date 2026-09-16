Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.

Lemma test_byte_assembly (b0 b1 b2 b3 b4 b5 b6 b7 : bv 8) :
  bv_or
    (bv_shiftl
      (bv_or
        (bv_or
          (bv_shiftl (bv_zero_extend 64 b7) (BV 64 24))
          (bv_shiftl (bv_zero_extend 64 b6) (BV 64 16)))
        (bv_or
          (bv_shiftl (bv_zero_extend 64 b5) (BV 64 8))
          (bv_zero_extend 64 b4)))
      (BV 64 32))
    (bv_or
      (bv_or
        (bv_shiftl (bv_zero_extend 64 b3) (BV 64 24))
        (bv_shiftl (bv_zero_extend 64 b2) (BV 64 16)))
      (bv_or
        (bv_shiftl (bv_zero_extend 64 b1) (BV 64 8))
        (bv_zero_extend 64 b0))) =
  Z_to_bv 64 (little_endian_to_bv 8 [b0; b1; b2; b3; b4; b5; b6; b7]).
Proof. autorewrite with zesu_byte_assembly. reflexivity. Qed.

Print Assumptions test_byte_assembly.
