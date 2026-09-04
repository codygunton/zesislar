From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150e8.
Import ListNotations.

Definition writeSuccessTransactionsScratchRest150f8
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   (bv_unsigned sp + 120) ↦ₘ bv_zero_extend 64
     (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 285) ∗
   (bv_unsigned sp + 128) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64 ∗
   (bv_unsigned sp + 136) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232 ∗
   (bv_unsigned sp + 144) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 88 ∗
   (bv_unsigned sp + 152) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 80 ∗
   (bv_unsigned sp + 160) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 248 ∗
   (bv_unsigned sp + 168) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 240 ∗
   (bv_unsigned sp + 176) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 256 ∗
   (bv_unsigned sp + 184) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 120 ∗
   (bv_unsigned sp + 192) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 112 ∗
   (bv_unsigned sp + 200) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 104 ∗
   (bv_unsigned sp + 208) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 128 ∗
   (bv_unsigned sp + 216) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 96 ∗
   (bv_unsigned sp + 224) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat (length processed)) ∗
   (bv_unsigned sp + 256) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208 ∗
   (bv_unsigned sp + 264) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 216 ∗
   (bv_unsigned sp + 272) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176 ∗
   (bv_unsigned sp + 280) ↦ₘ? 1360 ∗
   (bv_unsigned sp + 1640) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 265 ∗
   (bv_unsigned sp + 1648) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 273 ∗
   (bv_unsigned sp + 1656) ↦ₘ bv_extract 0 32
     (bv_or (bv_or
       (bv_shiftl (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 284)) (BV 64 24))
       (bv_shiftl (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 283)) (BV 64 16)))
       (bv_or (bv_shiftl (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 282)) (BV 64 8))
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 281)))) ∗
   (bv_unsigned sp + 1660) ↦ₘ? 4 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 64 ∗
   (bv_unsigned sp + 1744) ↦ₘ WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 264 ∗
   (bv_unsigned sp + 1745) ↦ₘ? 151 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsScratchRest150f8) := I.
Global Typeclasses Opaque writeSuccessTransactionsScratchRest150f8.

Lemma write_success_transactions_scratch_150f8_split
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
  writeSuccessTransactionsScratch150e8 sp base transactions processed transaction -∗
  writeSuccessTransactionsScratchRest150f8 sp base transactions processed transaction ∗
  (bv_unsigned sp + 1664) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 160 ∗
  (bv_unsigned sp + 1672) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168.
Proof.
  iIntros "Hscratch".
  iEval (unfold writeSuccessTransactionsScratch150e8) in "Hscratch".
  iDestruct "Hscratch" as
    "(Hlower & Hbase & Hlength & H120 & H128 & H136 & H144 & H152 &
      H160 & H168 & H176 & H184 & H192 & H200 & H208 & H216 & H224 &
      H232 & H240 & H248 & H256 & H264 & H272 & H280 & H1640 & H1648 &
      H1656 & H1660 & Hvalue & Htag & H1680 & H1744 & H1745 & _)".
  iSplitL "Hlower Hbase Hlength H120 H128 H136 H144 H152 H160 H168 H176
    H184 H192 H200 H208 H216 H224 H232 H240 H248 H256 H264 H272 H280
    H1640 H1648 H1656 H1660 H1680 H1744 H1745".
  - rewrite /writeSuccessTransactionsScratchRest150f8.
    iFrame.
  - iFrame.
Qed.
