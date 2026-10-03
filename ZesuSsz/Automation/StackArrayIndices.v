Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMemory.

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
   assert (Hindex : (bv_unsigned (bv_add sp offset) - (bv_unsigned sp + start))%Z = (integer - start)%Z) by
     (cbv [mapRamBase mapRamSize defaultMap machineRamEnd] in *; bv_solve);
   rewrite Hindex; clear Hindex
 end.

Print Assumptions stack_array_index.

Lemma zesu_word_array_index_offset (base start offset : Z) :
 array_region_start 64 (base + start) (base + offset) =
 Z.to_nat ((offset - start) / 8).
Proof.
 unfold array_region_start.
 change (Z.to_nat ((base + offset - (base + start)) / 8) =
         Z.to_nat ((offset - start) / 8)).
 replace (base + offset - (base + start)) with (offset - start) by lia.
 reflexivity.
Qed.
Ltac zesu_word_cursor_index_normalize :=
  repeat lazymatch goal with
  | |- context[Z.to_nat ((bv_unsigned (bv_add ?sp ?offset) -
                         (bv_unsigned ?sp + ?start)) / 8)] =>
    lazymatch type of sp with bv 64 => idtac end;
    let startValue := eval vm_compute in start in
    lazymatch startValue with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
    let offsetValue := eval vm_compute in (bv_unsigned offset) in
    lazymatch offsetValue with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
    let signedOffset := eval vm_compute in (bv_signed offset) in
    lazymatch signedOffset with Z0 => idtac | Zpos _ => idtac end;
    let Hsum := fresh "HcursorSum" in
    assert (Hsum : bv_unsigned (bv_add sp offset) =
                   (bv_unsigned sp + offsetValue)%Z) by
      (cbv [mapRamBase mapRamSize defaultMap machineRamEnd] in *; bv_solve);
    rewrite Hsum;
    let original := constr:(Z.to_nat
      ((bv_unsigned sp + offsetValue - (bv_unsigned sp + start)) / 8)) in
    let reduced := constr:(Z.to_nat ((offsetValue - start) / 8)) in
    replace original with reduced by (f_equal; f_equal; lia);
    let result := eval vm_compute in reduced in
    change reduced with result;
    clear Hsum
  end.

Ltac zesu_word_array_index_normalize :=
 zesu_word_cursor_index_normalize;
 repeat match goal with
 | |- context[array_region_start 64 (?base + ?start) (?base + ?offset)] =>
   let startValue := eval vm_compute in start in
   lazymatch startValue with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
   let offsetValue := eval vm_compute in offset in
   lazymatch offsetValue with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
   rewrite (zesu_word_array_index_offset base start offset);
   let index := constr:(Z.to_nat ((offset - start) / 8)) in
   let value := eval vm_compute in index in
   change index with value
 end.
