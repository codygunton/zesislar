From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactions10190SavedTail
    (transaction : writeSuccessTransaction) : list (reg_kind * valu_shape) :=
  [(KindReg "x22",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 200)));
   (KindReg "x23",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 24)));
   (KindReg "x24",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 8)));
   (KindReg "x25",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 0)));
   (KindReg "x26",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 184)));
   (KindReg "x27",
    ExactShape
      (RVal_Bits
        (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))))].

Lemma write_success_transactions_10190_saved_adapter_a
    `{!islaG Sigma} `{!threadG} (transaction : writeSuccessTransaction) :
  reg_col
    [(KindReg "x8",
      ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 192)));
     (KindReg "x9",
      ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 16)));
     (KindReg "x18",
      ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 48)));
     (KindReg "x19",
      ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 224)));
     (KindReg "x20",
      ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 56)));
     (KindReg "x21",
      ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 72)));
     (KindReg "x22",
      ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 200)));
     (KindReg "x23",
      ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 24)));
     (KindReg "x24",
      ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 8)));
     (KindReg "x25",
      ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 0)));
     (KindReg "x26",
      ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 184)));
     (KindReg "x27",
      ExactShape
        (RVal_Bits
          (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))))] -∗
  "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
  "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
  "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
  "x19" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 224) ∗
  "x20" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) ∗
  "x21" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 72) ∗
  reg_col (writeSuccessTransactions10190SavedTail transaction) ∗ True.
Proof.
  iIntros "Hsaved".
  iEval (rewrite reg_col_cons) in "Hsaved".
  iDestruct "Hsaved" as "(H8 & Hsaved)".
  iEval (rewrite reg_col_cons) in "Hsaved".
  iDestruct "Hsaved" as "(H9 & Hsaved)".
  iEval (rewrite reg_col_cons) in "Hsaved".
  iDestruct "Hsaved" as "(H18 & Hsaved)".
  iEval (rewrite reg_col_cons) in "Hsaved".
  iDestruct "Hsaved" as "(H19 & Hsaved)".
  iEval (rewrite reg_col_cons) in "Hsaved".
  iDestruct "Hsaved" as "(H20 & Hsaved)".
  iEval (rewrite reg_col_cons) in "Hsaved".
  iDestruct "Hsaved" as "(H21 & Hsaved)".
  iDestruct "H8" as (v8) "(-> & H8)".
  iDestruct "H9" as (v9) "(-> & H9)".
  iDestruct "H18" as (v18) "(-> & H18)".
  iDestruct "H19" as (v19) "(-> & H19)".
  iDestruct "H20" as (v20) "(-> & H20)".
  iDestruct "H21" as (v21) "(-> & H21)".
  rewrite /writeSuccessTransactions10190SavedTail.
  iFrame.
Qed.
