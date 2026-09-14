Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.

Lemma stack_array_index (sp : bv 64) (start offset extent : Z) :
  (0 <= start /\ start <= offset <= extent)%Z ->
  ((mapRamBase defaultMap) <= bv_unsigned sp)%Z ->
  (bv_unsigned sp + extent < (machineRamEnd defaultMap))%Z ->
  Z.to_nat (bv_unsigned (sp + Z_to_bv 64 offset)%bv -
    (bv_unsigned sp + start)) = Z.to_nat (offset - start).
Proof.
  intros Hoffset Hlow Hhigh.
  cbv [mapRamBase mapRamSize defaultMap machineRamEnd] in *.
  have Hsum : bv_unsigned (sp + Z_to_bv 64 offset)%bv =
    (bv_unsigned sp + offset)%Z by bv_solve.
  rewrite Hsum. f_equal. lia.
Qed.

Ltac zesu_normalize_stack_array_indices :=
 repeat match goal with
 | |- context[Z.to_nat (bv_unsigned (bv_add ?sp ?offset) - (bv_unsigned ?sp + ?start))] =>
   let integer := eval vm_compute in (bv_unsigned offset) in
   let Hindex := fresh "HstackArrayIndex" in
   assert (Hindex : (bv_unsigned (bv_add sp offset) - (bv_unsigned sp + start))%Z = (integer - start)%Z) by bv_solve;
   rewrite Hindex; clear Hindex
 end.

Print Assumptions stack_array_index.
