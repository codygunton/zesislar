Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190SavedAdapterASpec.

Lemma write_success_transactions_10190_saved_adapter_a_middle
    `{!islaG Sigma} `{!threadG} (transaction : writeSuccessTransaction) :
  reg_col (writeSuccessTransactions10190SavedMiddle transaction) -∗
  "x19" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 224) ∗
  "x20" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) ∗
  "x21" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 72).
Proof.
  iIntros "Hsaved".
  iEval (rewrite /writeSuccessTransactions10190SavedMiddle /= !reg_col_cons)
    in "Hsaved".
  iDestruct "Hsaved" as "(H19 & H20 & H21 & _)".
  iDestruct "H19" as (v19) "(-> & H19)".
  iDestruct "H20" as (v20) "(-> & H20)".
  iDestruct "H21" as (v21) "(-> & H21)".
  iFrame.
Qed.
