From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactions10190SavedAdapterA.
Require Import ZesuSsz.Experiments.WriteSuccessTransactions10190SavedAdapterASpec.

Lemma write_success_transactions_10190_saved_adapter_b
    `{!islaG Sigma} `{!threadG} (transaction : writeSuccessTransaction) :
  reg_col (writeSuccessTransactions10190SavedTail transaction) -∗
  "x22" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 200) ∗
  "x23" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 24) ∗
  "x24" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 8) ∗
  "x25" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 0) ∗
  "x26" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 184) ∗
  "x27" ↦ᵣ RVal_Bits
    (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32)) ∗ True.
Proof.
  rewrite /writeSuccessTransactions10190SavedTail !reg_col_cons reg_col_nil.
  iIntros "(H22 & H23 & H24 & H25 & H26 & H27 & _)".
  iDestruct "H22" as (v22) "(-> & H22)".
  iDestruct "H23" as (v23) "(-> & H23)".
  iDestruct "H24" as (v24) "(-> & H24)".
  iDestruct "H25" as (v25) "(-> & H25)".
  iDestruct "H26" as (v26) "(-> & H26)".
  iDestruct "H27" as (v27) "(-> & H27)".
  iFrame.
Qed.
