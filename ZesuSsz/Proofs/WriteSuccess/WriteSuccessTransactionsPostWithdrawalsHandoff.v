From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.

Definition writeSuccessTransactionsPostWithdrawalsHandoff
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  writeSuccessWithdrawalsLoopSpec P.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostWithdrawalsHandoff) := I.

Lemma write_success_transactions_post_withdrawals_handoff_unfold
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsPostWithdrawalsHandoff P -∗
  writeSuccessWithdrawalsLoopSpec P.
Proof.
  iStartProof. iIntros "Hhandoff".
  iExact "Hhandoff".
Qed.

Lemma write_success_withdrawals_remaining_nonzero (remaining : nat) :
  (S remaining < 2 ^ 64)%nat ->
  Z_to_bv 64 (Z.of_nat (S remaining)) <> BV 64 0.
Proof.
  intros Hbound Hz.
  have Hrange : 0 ≤ Z.of_nat (S remaining) < bv_modulus 64.
  { have HboundZ := (proj1 (Nat2Z.inj_lt (S remaining) (2 ^ 64))) Hbound.
    unfold bv_modulus. rewrite Nat2Z.inj_pow in HboundZ. lia. }
  have Hu := f_equal bv_unsigned Hz.
  rewrite Z_to_bv_small in Hu; [|exact Hrange].
  change (Z.of_nat (S remaining) = 0) in Hu.
  rewrite Nat2Z.inj_succ in Hu. lia.
Qed.
