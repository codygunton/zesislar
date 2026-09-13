Require Import isla.riscv64.riscv64.
Lemma array_counter_index_lt (offset limit : bv 64) (bytes : list (bv 8)) :
  bv_unsigned limit = Z.of_nat (length bytes) ->
  offset <> limit -> (bv_unsigned offset <= bv_unsigned limit)%Z ->
  (Z.to_nat (bv_unsigned offset `div` 1) < length bytes)%nat.
Proof.
  intros Hlimit Hne Hle.
  have HneZ : bv_unsigned offset <> bv_unsigned limit.
  { intros Heq. apply Hne. apply bv_eq. exact Heq. }
  rewrite Z.div_1_r. apply Nat2Z.inj_lt. rewrite Z2Nat.id; [lia|bv_solve].
Qed.
Print Assumptions array_counter_index_lt.
