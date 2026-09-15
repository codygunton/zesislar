Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma integer_array_byte_hint (base offset : Z)
    (bytes : list (bv 8)) :
  Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat (base + offset - base)) bytes))) =
  Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat offset) bytes))).
Proof. done. Qed.
Print Assumptions integer_array_byte_hint.

Lemma integer_array_word_instance (base offset : Z)
    (bytes : list (bv 8)) :
  RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat (base + offset - base)) bytes)))) =
  RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat offset) bytes)))).
Proof. exact inhabitant. Qed.
Print Assumptions integer_array_word_instance.
