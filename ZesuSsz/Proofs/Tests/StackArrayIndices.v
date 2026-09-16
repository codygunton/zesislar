Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import isla.riscv64.riscv64.

Lemma stack_array_indices_four_words (sp : bv 64) :
  ((mapRamBase defaultMap) <= bv_unsigned sp)%Z ->
  (bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z ->
  [Z.to_nat (bv_unsigned (sp + BV 64 1744)%bv - (bv_unsigned sp + 1744));
   Z.to_nat (bv_unsigned (sp + BV 64 1752)%bv - (bv_unsigned sp + 1744));
   Z.to_nat (bv_unsigned (sp + BV 64 1760)%bv - (bv_unsigned sp + 1744));
   Z.to_nat (bv_unsigned (sp + BV 64 1768)%bv - (bv_unsigned sp + 1744))] =
  [0; 8; 16; 24]%nat.
Proof. intros Hlow Hhigh. zesu_normalize_stack_array_indices. reflexivity. Qed.
Print Assumptions stack_array_indices_four_words.

Lemma stack_array_index_with_callee_range (sp : bv 64) :
  ((mapRamBase defaultMap) <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z ->
  Z.to_nat (bv_unsigned (sp + BV 64 1840)%bv - (bv_unsigned sp + 1744)) = 96%nat.
Proof. intros Hlow Hhigh. zesu_normalize_stack_array_indices. reflexivity. Qed.
Print Assumptions stack_array_index_with_callee_range.
