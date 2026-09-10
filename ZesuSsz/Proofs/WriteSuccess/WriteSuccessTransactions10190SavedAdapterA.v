From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190SavedAdapterASpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190SavedAdapterAHead.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions10190SavedAdapterAMiddle.

Lemma write_success_transactions_10190_saved_adapter_a
    `{!islaG Sigma} `{!threadG} (transaction : writeSuccessTransaction) :
  reg_col (writeSuccessTransactions10190SavedAll transaction) -∗
  "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
  "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
  "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
  "x19" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 224) ∗
  "x20" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) ∗
  "x21" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 72) ∗
  reg_col (writeSuccessTransactions10190SavedTail transaction) ∗ True.
Proof.
  iIntros "Hsaved".
  iPoseProof (write_success_transactions_10190_saved_adapter_a_head transaction
    with "Hsaved") as "(H8 & H9 & H18 & Hmiddle & Htail)".
  iPoseProof (write_success_transactions_10190_saved_adapter_a_middle transaction
    with "Hmiddle") as "(H19 & H20 & H21)".
  iFrame.
Qed.
