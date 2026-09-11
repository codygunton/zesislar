Require Import ZesuSsz.Automation.All.
From Coq Require Import Lia Lists.List ZArith.ZArith.

Definition writeSuccessWithdrawalsMeasure {A} (suffix : list A) : nat :=
  length suffix.

Lemma writeSuccessWithdrawalsIterationUpdate {A}
    (suffix rest : list A) (remaining : nat) :
  length suffix = (48 * S remaining)%nat ->
  rest = skipn 48 suffix ->
  length rest = (48 * remaining)%nat /\
  (writeSuccessWithdrawalsMeasure rest <
   writeSuccessWithdrawalsMeasure suffix)%nat.
Proof.
  intros Hlength ->. unfold writeSuccessWithdrawalsMeasure.
  rewrite skipn_length. rewrite Hlength. split; lia.
Qed.

Lemma writeSuccessWithdrawalsPointerStride base processed :
  (base + 48 * Z.of_nat (S processed) =
   (base + 48 * Z.of_nat processed) + 48)%Z.
Proof. rewrite Nat2Z.inj_succ. lia. Qed.

Lemma writeSuccessWithdrawalsUnchangedDoesNotDecrease {A}
    (suffix : list A) :
  ~ (writeSuccessWithdrawalsMeasure suffix <
     writeSuccessWithdrawalsMeasure suffix)%nat.
Proof. lia. Qed.
