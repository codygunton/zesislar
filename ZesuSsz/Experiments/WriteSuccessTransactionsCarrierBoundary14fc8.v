From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopExitEvents.

(* The carrier words occupy the middle of the ordinary 0x14fc8 scratch.
   This split keeps those words owned while the surrounding phase scratch
   changes from uninitialized storage to the values loaded by the code. *)
Definition writeSuccessTransactions14fc8CarrierScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ
     bv_zero_extend 64 (writeSuccessTransactionByte transaction 285) ∗
   (bv_unsigned sp + 128) ↦ₘ? 96 ∗
   (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
   (bv_unsigned sp + 256) ↦ₘ? 16 ∗
   (bv_unsigned sp + 272) ↦ₘ writeSuccessTransactionWord transaction 176 ∗
   (bv_unsigned sp + 280) ↦ₘ? 824 ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
   (bv_unsigned sp + 1136) ↦ₘ? 528 ∗
   (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 ∗
   (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 64 ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp + 1792) ↦ₘ? 104)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions14fc8CarrierScratch) := I.
Global Typeclasses Opaque writeSuccessTransactions14fc8CarrierScratch.

Lemma write_success_transactions_14fc8_carrier_scratch_pack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  (bv_unsigned sp - 48) ↦ₘ? 152 -∗
  (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base -∗
  (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) -∗
  (bv_unsigned sp + 120) ↦ₘ
    bv_zero_extend 64 (writeSuccessTransactionByte transaction 285) -∗
  (bv_unsigned sp + 128) ↦ₘ? 96 -∗
  (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 -∗
  (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 -∗
  (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 -∗
  (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) -∗
  (bv_unsigned sp + 256) ↦ₘ? 16 -∗
  (bv_unsigned sp + 272) ↦ₘ writeSuccessTransactionWord transaction 176 -∗
  (bv_unsigned sp + 280) ↦ₘ? 824 -∗
  writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items -∗
  (bv_unsigned sp + 1136) ↦ₘ? 528 -∗
  (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 -∗
  (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168 -∗
  (bv_unsigned sp + 1680) ↦ₘ? 64 -∗
  (bv_unsigned sp + 1744) ↦ₘ? 48 -∗
  (bv_unsigned sp + 1792) ↦ₘ? 104 -∗
  writeSuccessTransactions14fc8CarrierScratch
    sp base total processed transaction first second third fourth items.
Proof.
  iIntros "Hlower Hbase Htotal H285 H128 H152 H144 H136 Hprocessed Hgap16
    H176 Hupper Hcarrier Hmiddle H160 H168 Hgap1680 Hwithdrawals Htail".
  rewrite /writeSuccessTransactions14fc8CarrierScratch.
  iFrame.
Qed.

Lemma write_success_transactions_14fc8_carrier_scratch_unpack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions14fc8CarrierScratch
    sp base total processed transaction first second third fourth items -∗
  (bv_unsigned sp - 48) ↦ₘ? 152 ∗
  (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
  (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
  (bv_unsigned sp + 120) ↦ₘ
    bv_zero_extend 64 (writeSuccessTransactionByte transaction 285) ∗
  (bv_unsigned sp + 128) ↦ₘ? 96 ∗
  (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 ∗
  (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 ∗
  (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 ∗
  (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
  (bv_unsigned sp + 256) ↦ₘ? 16 ∗
  (bv_unsigned sp + 272) ↦ₘ writeSuccessTransactionWord transaction 176 ∗
  (bv_unsigned sp + 280) ↦ₘ? 824 ∗
  writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
  (bv_unsigned sp + 1136) ↦ₘ? 528 ∗
  (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 ∗
  (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168 ∗
  (bv_unsigned sp + 1680) ↦ₘ? 64 ∗
  (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
  (bv_unsigned sp + 1792) ↦ₘ? 104.
Proof.
  iIntros "Hscratch".
  iEval (rewrite /writeSuccessTransactions14fc8CarrierScratch) in "Hscratch".
  iExact "Hscratch".
Qed.
