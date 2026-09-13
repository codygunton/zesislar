Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import isla.riscv64.riscv64.

Lemma stack_array_indices_four_words (sp : bv 64) :
  (0x20000000 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp + 1896 < 0x40000000)%Z ->
  [Z.to_nat (bv_unsigned (sp + BV 64 1744)%bv - (bv_unsigned sp + 1744));
   Z.to_nat (bv_unsigned (sp + BV 64 1752)%bv - (bv_unsigned sp + 1744));
   Z.to_nat (bv_unsigned (sp + BV 64 1760)%bv - (bv_unsigned sp + 1744));
   Z.to_nat (bv_unsigned (sp + BV 64 1768)%bv - (bv_unsigned sp + 1744))] =
  [0; 8; 16; 24]%nat.
Proof. intros Hlow Hhigh. zesu_normalize_stack_array_indices. reflexivity. Qed.
Print Assumptions stack_array_indices_four_words.
