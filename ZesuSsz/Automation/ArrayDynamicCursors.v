Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
From Coq Require Import ZArith.ZArith.

Lemma array_cursor_dynamic_range (row offset limit : bv 64) base index count
    (bytes : list (bv 8)) :
  bv_unsigned row = (base + Z.of_nat index)%Z ->
  bv_unsigned limit = Z.of_nat count ->
  offset <> limit -> (bv_unsigned offset <= bv_unsigned limit)%Z ->
  (index + count <= length bytes)%nat ->
  ((mapRamBase defaultMap) <= base)%Z ->
  (base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z ->
  (base <= bv_unsigned (row + offset)%bv < base + Z.of_nat (length bytes))%Z.
Proof.
  intros Hrow Hlimit Hne Hle Hbound Hlow Hhigh.
  cbv [mapRamBase mapRamSize defaultMap machineRamEnd] in *.
  apply Nat2Z.inj_le in Hbound. rewrite Nat2Z.inj_add in Hbound.
  have Hoff : bv_unsigned offset < Z.of_nat count.
  { have HneZ : bv_unsigned offset <> bv_unsigned limit.
    { intros Heq. apply Hne. apply bv_eq. exact Heq. }
    lia. }
  have Hsum : bv_unsigned (row + offset)%bv =
    (base + Z.of_nat index + bv_unsigned offset)%Z by bv_solve.
  rewrite Hsum. bv_saturate. lia.
Qed.
Print Assumptions array_cursor_dynamic_range.
#[global] Hint Extern 9
  (FindHypEqual (FICMemMapstoSemantic (bv_unsigned (bv_add ?row ?offset)))
    (?base ↦ₘ∗ ?bytes) (mem_mapsto_kind_prop _ _) _) =>
  (apply tac_mem_mapsto_array_eq; left;
   change (base <= bv_unsigned (row + offset)%bv < base + Z.of_nat (length bytes) * 1)%Z;
   rewrite Z.mul_1_r;
   eapply (array_cursor_dynamic_range row offset _ base _ _ bytes); eassumption)
  : typeclass_instances.

#[global] Hint Extern 8
  (FindHypEqual (FICMemMapstoSemantic (bv_unsigned (bv_add ?row ?offset) + 0))
    (?base ↦ₘ∗ ?bytes) (mem_mapsto_kind_prop _ _) _) =>
  (apply tac_mem_mapsto_array_eq; left;
   change (base <= bv_unsigned (row + offset)%bv + 0 < base + Z.of_nat (length bytes) * 1)%Z;
   rewrite Z.add_0_r Z.mul_1_r;
   eapply (array_cursor_dynamic_range row offset _ base _ _ bytes); eassumption)
  : typeclass_instances.
