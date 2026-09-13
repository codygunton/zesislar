Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayWordValues.
Require Import isla.riscv64.riscv64.

Lemma test_array_word_nested (a b c d : bv 8) :
  bv_or
    (bv_or (Z_to_bv 64 (bv_unsigned d * 16777216))
      (Z_to_bv 64 (bv_unsigned c * 65536)))
    (bv_or (Z_to_bv 64 (bv_unsigned b * 256)) (bv_zero_extend 64 a)) =
  Z_to_bv 64 (little_endian_to_bv 8 [a; b; c; d]).
Proof. zesu_array_word_value. Qed.
Print Assumptions test_array_word_nested.
