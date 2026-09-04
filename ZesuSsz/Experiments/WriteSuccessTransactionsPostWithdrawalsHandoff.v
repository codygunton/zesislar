From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsSpec.

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
