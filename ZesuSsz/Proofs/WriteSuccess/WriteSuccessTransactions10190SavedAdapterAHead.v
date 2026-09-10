Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190SavedAdapterASpec.

Lemma write_success_transactions_10190_saved_adapter_a_head
    `{!islaG Sigma} `{!threadG} (transaction : writeSuccessTransaction) :
  reg_col (writeSuccessTransactions10190SavedAll transaction) -∗
  "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
  "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
  "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
  reg_col (writeSuccessTransactions10190SavedMiddle transaction) ∗
  reg_col (writeSuccessTransactions10190SavedTail transaction).
Proof.
  iIntros "Hsaved".
  iEval (rewrite /writeSuccessTransactions10190SavedAll /reg_col
    !big_sepL_app) in "Hsaved".
  iDestruct "Hsaved" as "(Hhead & Hmiddle & Htail)".
  iEval (rewrite /writeSuccessTransactions10190SavedHead /reg_col /=)
    in "Hhead".
  iDestruct "Hhead" as "(H8 & H9 & H18 & _)".
  iDestruct "H8" as (v8) "(-> & H8)".
  iDestruct "H9" as (v9) "(-> & H9)".
  iDestruct "H18" as (v18) "(-> & H18)".
  iFrame.
Qed.
