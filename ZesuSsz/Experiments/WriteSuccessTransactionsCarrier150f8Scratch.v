From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState150ec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState15098.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactions150f8CarrierScratchRest
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 16 ∗
   bv_unsigned sp ↦ₘ? 104 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ
     bv_zero_extend 64 (writeSuccessTransactionByte transaction 285) ∗
   (bv_unsigned sp + 128) ↦ₘ? 8 ∗
   (bv_unsigned sp + 136) ↦ₘ writeSuccessTransactionWord transaction 232 ∗
   (bv_unsigned sp + 144) ↦ₘ writeSuccessTransactionWord transaction 88 ∗
   (bv_unsigned sp + 152) ↦ₘ writeSuccessTransactionWord transaction 80 ∗
   (bv_unsigned sp + 160) ↦ₘ writeSuccessTransactionWord transaction 248 ∗
   (bv_unsigned sp + 168) ↦ₘ writeSuccessTransactionWord transaction 240 ∗
   (bv_unsigned sp + 176) ↦ₘ writeSuccessTransactionWord transaction 256 ∗
   (bv_unsigned sp + 184) ↦ₘ writeSuccessTransactionWord transaction 120 ∗
   (bv_unsigned sp + 192) ↦ₘ writeSuccessTransactionWord transaction 112 ∗
   (bv_unsigned sp + 200) ↦ₘ writeSuccessTransactionWord transaction 104 ∗
   (bv_unsigned sp + 208) ↦ₘ writeSuccessTransactionWord transaction 128 ∗
   (bv_unsigned sp + 216) ↦ₘ writeSuccessTransactionWord transaction 96 ∗
   (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
   (bv_unsigned sp + 256) ↦ₘ writeSuccessTransactionWord transaction 208 ∗
   (bv_unsigned sp + 264) ↦ₘ writeSuccessTransactionWord transaction 216 ∗
   (bv_unsigned sp + 272) ↦ₘ writeSuccessTransactionWord transaction 176 ∗
   (bv_unsigned sp + 280) ↦ₘ? 824 ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
   (bv_unsigned sp + 1136) ↦ₘ? 504 ∗
   (bv_unsigned sp + 1640) ↦ₘ writeSuccessTransactions15098X12 transaction ∗
   (bv_unsigned sp + 1648) ↦ₘ
     (bv_or
       (bv_shiftl
         (bv_or
           (bv_or
             (bv_shiftl (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 280)) (BV 64 24))
             (bv_shiftl (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 279)) (BV 64 16)))
           (bv_or
             (bv_shiftl (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 278)) (BV 64 8))
             (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 277)))) (BV 64 32))
       (bv_or
         (bv_or
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 276)) (BV 64 24))
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 275)) (BV 64 16)))
         (bv_or
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 274)) (BV 64 8))
           (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 273))))) ∗
   (bv_unsigned sp + 1656) ↦ₘ
     bv_extract 0 32
       (bv_or
         (bv_or
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 284)) (BV 64 24))
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 283)) (BV 64 16)))
         (bv_or
           (bv_shiftl (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 282)) (BV 64 8))
           (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 281)))) ∗
   (bv_unsigned sp + 1660) ↦ₘ? 4 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 64 ∗
   (bv_unsigned sp + 1744) ↦ₘ writeSuccessTransactionByte transaction 264 ∗
   (bv_unsigned sp + 1745) ↦ₘ? 47 ∗
   (bv_unsigned sp + 1792) ↦ₘ? 104)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions150f8CarrierScratchRest) := I.
Global Typeclasses Opaque writeSuccessTransactions150f8CarrierScratchRest.

Lemma write_success_transactions_150f8_carrier_scratch_split
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions150ecCarrierScratch sp base total processed transaction
    first second third fourth items -∗
  writeSuccessTransactions150f8CarrierScratchRest sp base total processed
      transaction first second third fourth items ∗
  (bv_unsigned sp - 32) ↦ₘ? 32 ∗
  (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 ∗
  (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168.
Proof.
  iIntros "Hscratch".
  iEval (unfold writeSuccessTransactions150ecCarrierScratch) in "Hscratch".
  iDestruct "Hscratch" as
    "(Hlower & Hbase & Htotal & H120 & H128 & H136 & H144 & H152 & H160 &
      H168 & H176 & H184 & H192 & H200 & H208 & H216 & H224 & H232 & H240 &
      H248 & H256 & H264 & H272 & H280 & Hcarrier & H1136 & H1640 & H1648 &
      H1656 & H1660 & Hvalue & Htag & H1680 & H1744 & H1745 & H1792)".
  iDestruct (mem_mapsto_uninit_split 16 with "Hlower") as
    "[Hlower16 HlowerRest]"; first lia.
  iDestruct (mem_mapsto_uninit_split 32 with "HlowerRest") as
    "[Hstack Hupper104]"; first lia.
  have HstackAddr : bv_unsigned sp - 48 + 16 = bv_unsigned sp - 32 by lia.
  have HupperAddr : bv_unsigned sp - 48 + 16 + 32 = bv_unsigned sp by lia.
  iEval (rewrite HstackAddr) in "Hstack".
  iEval (rewrite HupperAddr) in "Hupper104".
  iSplitL "Hlower16 Hupper104 Hbase Htotal H120 H128 H136 H144 H152 H160
    H168 H176 H184 H192 H200 H208 H216 H224 H232 H240 H248 H256 H264 H272
    H280 Hcarrier H1136 H1640 H1648 H1656 H1660 H1680 H1744 H1745 H1792".
  - rewrite /writeSuccessTransactions150f8CarrierScratchRest. iFrame.
  - iFrame.
Qed.
