Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.NatBitvectors.
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
Proof. exact (zesu_nat_successor_bv64_nonzero remaining).
Qed.
