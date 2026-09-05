From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopExitEvents.

(* The 0x150f0 handoff uses the ordinary 0x150e8 scratch.  Split its
   uninitialized range around the carrier words and retain the event data. *)
Definition writeSuccessTransactions150f0CarrierScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ
     bv_zero_extend 64 (writeSuccessTransactionByte transaction 285) ∗
   (bv_unsigned sp + 128) ↦ₘ writeSuccessTransactionWord transaction 64 ∗
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
   (bv_unsigned sp + 1640) ↦ₘ writeSuccessTransactionWord transaction 265 ∗
   (bv_unsigned sp + 1648) ↦ₘ writeSuccessTransactionWord transaction 273 ∗
   (bv_unsigned sp + 1656) ↦ₘ
     bv_extract 0 32
       (bv_or
         (bv_or
           (bv_shiftl
             (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 284))
             (BV 64 24))
           (bv_shiftl
             (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 283))
             (BV 64 16)))
         (bv_or
           (bv_shiftl
             (bv_zero_extend 64
               (writeSuccessTransactionByte transaction 282))
             (BV 64 8))
           (bv_zero_extend 64
             (writeSuccessTransactionByte transaction 281)))) ∗
   (bv_unsigned sp + 1660) ↦ₘ? 4 ∗
   (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 ∗
   (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 64 ∗
   (bv_unsigned sp + 1744) ↦ₘ writeSuccessTransactionByte transaction 264 ∗
   (bv_unsigned sp + 1745) ↦ₘ? 151)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions150f0CarrierScratch) := I.
Global Typeclasses Opaque writeSuccessTransactions150f0CarrierScratch.

Lemma write_success_transactions_150f0_carrier_scratch_pack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  (bv_unsigned sp - 48) ↦ₘ? 152 -∗
  (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base -∗
  (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) -∗
  (bv_unsigned sp + 120) ↦ₘ
    bv_zero_extend 64 (writeSuccessTransactionByte transaction 285) -∗
  (bv_unsigned sp + 128) ↦ₘ writeSuccessTransactionWord transaction 64 -∗
  (bv_unsigned sp + 136) ↦ₘ writeSuccessTransactionWord transaction 232 -∗
  (bv_unsigned sp + 144) ↦ₘ writeSuccessTransactionWord transaction 88 -∗
  (bv_unsigned sp + 152) ↦ₘ writeSuccessTransactionWord transaction 80 -∗
  (bv_unsigned sp + 160) ↦ₘ writeSuccessTransactionWord transaction 248 -∗
  (bv_unsigned sp + 168) ↦ₘ writeSuccessTransactionWord transaction 240 -∗
  (bv_unsigned sp + 176) ↦ₘ writeSuccessTransactionWord transaction 256 -∗
  (bv_unsigned sp + 184) ↦ₘ writeSuccessTransactionWord transaction 120 -∗
  (bv_unsigned sp + 192) ↦ₘ writeSuccessTransactionWord transaction 112 -∗
  (bv_unsigned sp + 200) ↦ₘ writeSuccessTransactionWord transaction 104 -∗
  (bv_unsigned sp + 208) ↦ₘ writeSuccessTransactionWord transaction 128 -∗
  (bv_unsigned sp + 216) ↦ₘ writeSuccessTransactionWord transaction 96 -∗
  (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 -∗
  (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 -∗
  (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 -∗
  (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) -∗
  (bv_unsigned sp + 256) ↦ₘ writeSuccessTransactionWord transaction 208 -∗
  (bv_unsigned sp + 264) ↦ₘ writeSuccessTransactionWord transaction 216 -∗
  (bv_unsigned sp + 272) ↦ₘ writeSuccessTransactionWord transaction 176 -∗
  (bv_unsigned sp + 280) ↦ₘ? 824 -∗
  writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items -∗
  (bv_unsigned sp + 1136) ↦ₘ? 504 -∗
  (bv_unsigned sp + 1640) ↦ₘ writeSuccessTransactionWord transaction 265 -∗
  (bv_unsigned sp + 1648) ↦ₘ writeSuccessTransactionWord transaction 273 -∗
  (bv_unsigned sp + 1656) ↦ₘ
    bv_extract 0 32
      (bv_or
        (bv_or
          (bv_shiftl
            (bv_zero_extend 64
              (writeSuccessTransactionByte transaction 284))
            (BV 64 24))
          (bv_shiftl
            (bv_zero_extend 64
              (writeSuccessTransactionByte transaction 283))
            (BV 64 16)))
        (bv_or
          (bv_shiftl
            (bv_zero_extend 64
              (writeSuccessTransactionByte transaction 282))
            (BV 64 8))
          (bv_zero_extend 64
            (writeSuccessTransactionByte transaction 281)))) -∗
  (bv_unsigned sp + 1660) ↦ₘ? 4 -∗
  (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 -∗
  (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168 -∗
  (bv_unsigned sp + 1680) ↦ₘ? 64 -∗
  (bv_unsigned sp + 1744) ↦ₘ writeSuccessTransactionByte transaction 264 -∗
  (bv_unsigned sp + 1745) ↦ₘ? 151 -∗
  writeSuccessTransactions150f0CarrierScratch
    sp base total processed transaction first second third fourth items.
Proof.
  iIntros "Hlower Hbase Htotal H285 H64 H232 H88 H80 H248 H240 H256 H120
    H112 H104 H128 H96 H152 H144 H136 Hprocessed H208 H216 H176 Hupper
    Hcarrier Hmiddle H265 H273 Hextract Hgap4 H160 H168 Hgap64 H264 Htail".
  rewrite /writeSuccessTransactions150f0CarrierScratch.
  iFrame.
Qed.

Lemma write_success_transactions_150f0_carrier_scratch_unpack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions150f0CarrierScratch
    sp base total processed transaction first second third fourth items -∗
  (bv_unsigned sp - 48) ↦ₘ? 152 ∗
  (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
  (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
  (bv_unsigned sp + 120) ↦ₘ
    bv_zero_extend 64 (writeSuccessTransactionByte transaction 285) ∗
  (bv_unsigned sp + 128) ↦ₘ writeSuccessTransactionWord transaction 64 ∗
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
  (bv_unsigned sp + 1640) ↦ₘ writeSuccessTransactionWord transaction 265 ∗
  (bv_unsigned sp + 1648) ↦ₘ writeSuccessTransactionWord transaction 273 ∗
  (bv_unsigned sp + 1656) ↦ₘ
    bv_extract 0 32
      (bv_or
        (bv_or
          (bv_shiftl
            (bv_zero_extend 64
              (writeSuccessTransactionByte transaction 284))
            (BV 64 24))
          (bv_shiftl
            (bv_zero_extend 64
              (writeSuccessTransactionByte transaction 283))
            (BV 64 16)))
        (bv_or
          (bv_shiftl
            (bv_zero_extend 64
              (writeSuccessTransactionByte transaction 282))
            (BV 64 8))
          (bv_zero_extend 64
            (writeSuccessTransactionByte transaction 281)))) ∗
  (bv_unsigned sp + 1660) ↦ₘ? 4 ∗
  (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 ∗
  (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168 ∗
  (bv_unsigned sp + 1680) ↦ₘ? 64 ∗
  (bv_unsigned sp + 1744) ↦ₘ writeSuccessTransactionByte transaction 264 ∗
  (bv_unsigned sp + 1745) ↦ₘ? 151.
Proof.
  iIntros "Hscratch".
  iEval (rewrite /writeSuccessTransactions150f0CarrierScratch) in "Hscratch".
  iExact "Hscratch".
Qed.
