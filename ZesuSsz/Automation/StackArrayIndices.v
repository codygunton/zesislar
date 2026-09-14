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
  try match goal with
  | Hlow : ((mapRamBase defaultMap) <= bv_unsigned ?sp - ?amount)%Z |- _ =>
      let Hlower := fresh "HstackArrayLower" in
      assert (Hlower : ((mapRamBase defaultMap) <= bv_unsigned sp)%Z) by lia
  end;
  repeat match goal with
  | Hlow : ((mapRamBase defaultMap) <= bv_unsigned ?sp)%Z,
    Hhigh : (bv_unsigned ?sp + ?extent < (machineRamEnd defaultMap))%Z
    |- context[Z.to_nat (bv_unsigned (bv_add ?sp ?offset) -
      (bv_unsigned ?sp + ?start))] =>
      let integer := eval vm_compute in (bv_unsigned offset) in
      let Hindex := fresh "HstackArrayIndex" in
      assert (Hindex : Z.to_nat (bv_unsigned (bv_add sp offset) -
        (bv_unsigned sp + start)) = Z.to_nat (integer - start)) by
        (replace offset with (Z_to_bv 64 integer) by bv_solve;
         apply (stack_array_index sp start integer extent);
         [lia | exact Hlow | exact Hhigh]);
      rewrite Hindex; clear Hindex
  end.

Print Assumptions stack_array_index.
