Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Lemma array_destination_dynamic_range (row offset limit : bv 64) (bytes : list (bv 8)) :
  bv_unsigned limit = Z.of_nat (length bytes) ->
  offset <> limit -> (bv_unsigned offset <= bv_unsigned limit)%Z ->
  (0x20000000 <= bv_unsigned row)%Z ->
  (bv_unsigned row + bv_unsigned limit < 0x40000000)%Z ->
  (bv_unsigned row <= bv_unsigned (row + offset)%bv <
    bv_unsigned row + Z.of_nat (length bytes))%Z.
Proof.
  intros Hlimit Hne Hle Hlow Hhigh.
  have HneZ : bv_unsigned offset <> bv_unsigned limit.
  { intros Heq. apply Hne. apply bv_eq. exact Heq. }
  bv_solve.
Qed.
Print Assumptions array_destination_dynamic_range.
#[global] Hint Extern 8
  (FindHypEqual (FICMemMapstoSemantic (bv_unsigned (bv_add ?row ?offset)))
    (bv_unsigned ?row ↦ₘ∗ ?bytes) (mem_mapsto_kind_prop _ _) _) =>
  (apply tac_mem_mapsto_array_eq; left;
   change (bv_unsigned row <= bv_unsigned (row + offset)%bv <
     bv_unsigned row + Z.of_nat (length bytes) * 1)%Z;
   rewrite Z.mul_1_r;
   eapply (array_destination_dynamic_range row offset _ bytes); eassumption)
  : typeclass_instances.

