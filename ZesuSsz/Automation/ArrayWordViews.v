Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma array_byte_four_register_width (a b c d : bv 8) :
  Z_to_bv 64 (little_endian_to_bv 8 [a; b; c; d]) =
    bv_zero_extend 64 (Z_to_bv 32 (little_endian_to_bv 8 [a; b; c; d])).
Proof.
  pose proof (little_endian_to_bv_bound 8 [a; b; c; d]) as Hbound.
  change (0 <= little_endian_to_bv 8 [a; b; c; d] < 2 ^ 32)%Z in Hbound.
  bv_solve.
Qed.
Print Assumptions array_byte_four_register_width.

Ltac zesu_array_byte_four_register_views :=
  repeat iSelect (_ ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [_; _; _; _])))%I
    ltac:(fun Hreg => iEval (rewrite array_byte_four_register_width) in Hreg).

