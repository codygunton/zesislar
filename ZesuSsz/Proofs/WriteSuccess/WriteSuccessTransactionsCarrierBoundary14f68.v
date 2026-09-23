Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.

Definition writeSuccessTransactions14f68CarrierScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ? 104 ∗
   (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
   (bv_unsigned sp + 256) ↦ₘ? 16 ∗
   (bv_unsigned sp + 272) ↦ₘ writeSuccessTransactionWord transaction 176 ∗
   (bv_unsigned sp + 280) ↦ₘ? 824 ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
   (bv_unsigned sp + 1136) ↦ₘ? 608 ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp + 1792) ↦ₘ? 104)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactions14f68CarrierScratch) := I.
Global Typeclasses Opaque writeSuccessTransactions14f68CarrierScratch.

Lemma write_success_transactions_14f68_carrier_scratch_pack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  (bv_unsigned sp - 48) ↦ₘ? 152 -∗
  (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base -∗
  (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) -∗
  (bv_unsigned sp + 120) ↦ₘ? 104 -∗
  (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 -∗
  (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 -∗
  (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 -∗
  (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) -∗
  (bv_unsigned sp + 256) ↦ₘ? 16 -∗
  (bv_unsigned sp + 272) ↦ₘ writeSuccessTransactionWord transaction 176 -∗
  (bv_unsigned sp + 280) ↦ₘ? 824 -∗
  writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items -∗
  (bv_unsigned sp + 1136) ↦ₘ? 608 -∗
  (bv_unsigned sp + 1744) ↦ₘ? 48 -∗
  (bv_unsigned sp + 1792) ↦ₘ? 104 -∗
  writeSuccessTransactions14f68CarrierScratch
    sp base total processed transaction first second third fourth items.
Proof.
  iIntros "Hlower Hbase Htotal Hprefix H152 H144 H136 Hprocessed Hgap16
    H176 Hupper Hcarrier Hmiddle Hwithdrawals Htail".
  rewrite /writeSuccessTransactions14f68CarrierScratch.
  iFrame.
Qed.

Lemma write_success_transactions_14f68_carrier_scratch_unpack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions14f68CarrierScratch
    sp base total processed transaction first second third fourth items -∗
  (bv_unsigned sp - 48) ↦ₘ? 152 ∗
  (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
  (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
  (bv_unsigned sp + 120) ↦ₘ? 104 ∗
  (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 ∗
  (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 ∗
  (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 ∗
  (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
  (bv_unsigned sp + 256) ↦ₘ? 16 ∗
  (bv_unsigned sp + 272) ↦ₘ writeSuccessTransactionWord transaction 176 ∗
  (bv_unsigned sp + 280) ↦ₘ? 824 ∗
  writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
  (bv_unsigned sp + 1136) ↦ₘ? 608 ∗
  (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
  (bv_unsigned sp + 1792) ↦ₘ? 104.
Proof. move => *. zesu_block. Qed.
