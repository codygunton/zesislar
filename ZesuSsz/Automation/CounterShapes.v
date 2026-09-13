Require Import isla.riscv64.riscv64.

Lemma zesu_counter_succ_decrement remaining :
  (Z_to_bv 64 (Z.of_nat (S remaining)) + BV 64 18446744073709551615)%bv =
  Z_to_bv 64 (Z.of_nat remaining).
Proof. rewrite Nat2Z.inj_succ. bv_solve. Qed.

Global Instance zesu_counter_succ_nonzero remaining :
  SimplImplUnsafe true
    ((Z_to_bv 64 (Z.of_nat (S remaining)) + BV 64 18446744073709551615)%bv <> BV 64 0)
    (exists n, remaining = S n).
Proof.
  intros Hnonzero. destruct remaining as [|remaining]; [|eauto].
  exfalso. apply Hnonzero. apply bv_eq. vm_compute. reflexivity.
Qed.

#[export] Hint Rewrite zesu_counter_succ_decrement : isla_coq_rewrite.
Global Instance zesu_counter_nonzero remaining :
  SimplImplUnsafe true (Z_to_bv 64 (Z.of_nat remaining) <> BV 64 0)
    (exists n, remaining = S n).
Proof.
  intros Hnonzero. destruct remaining as [|remaining]; [|eauto].
  exfalso. apply Hnonzero. apply bv_eq. vm_compute. reflexivity.
Qed.
Print Assumptions zesu_counter_succ_decrement.
Print Assumptions zesu_counter_succ_nonzero.
Print Assumptions zesu_counter_nonzero.
