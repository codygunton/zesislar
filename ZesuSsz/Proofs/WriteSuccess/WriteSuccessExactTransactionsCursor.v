Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Import ListNotations.

Lemma transaction_cursor_increment {A : Type} (processed : list A) (row : A) :
  (Z_to_bv 64 (Z.of_nat (length processed)) + BV 64 1)%bv =
  Z_to_bv 64 (Z.of_nat (length (processed ++ [row]))).
Proof.
  rewrite app_length /=.
  replace (Z.of_nat (length processed + 1)) with (Z.of_nat (length processed) + 1)%Z by lia.
  bv_solve.
Qed.

Lemma transaction_cursor_advance {A : Type} (processed : list A) (row : A) rest :
  (length (processed ++ row :: rest) < 2 ^ 64)%nat ->
  bv_unsigned (Z_to_bv 64 (Z.of_nat (length (processed ++ [row])))) =
    Z.of_nat (length (processed ++ [row])).
Proof.
  intros Hbound. apply Nat2Z.inj_lt in Hbound.
  rewrite app_length Nat2Z.inj_pow in Hbound. cbn in Hbound.
  rewrite app_length /=.
  rewrite Z_to_bv_unsigned bv_wrap_small; first reflexivity.
  unfold bv_modulus. split; first lia.
  lia.
Qed.
Print Assumptions transaction_cursor_increment.
Print Assumptions transaction_cursor_advance.
