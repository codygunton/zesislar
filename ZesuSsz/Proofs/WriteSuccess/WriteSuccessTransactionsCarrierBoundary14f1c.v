Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPuncturedScratch.

Definition writeSuccessTransactions14f1cCarrierScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ? 128 ∗
   (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
   (bv_unsigned sp + 256) ↦ₘ? 848 ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
   (bv_unsigned sp + 1136) ↦ₘ? 608 ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp + 1792) ↦ₘ? 104)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactions14f1cCarrierScratch) := I.
Global Typeclasses Opaque writeSuccessTransactions14f1cCarrierScratch.

Lemma write_success_transactions_14f1c_carrier_scratch_pack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  (bv_unsigned sp - 48) ↦ₘ? 152 -∗
  (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base -∗
  (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) -∗
  (bv_unsigned sp + 120) ↦ₘ? 128 -∗
  (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) -∗
  (bv_unsigned sp + 256) ↦ₘ? 848 -∗
  writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items -∗
  (bv_unsigned sp + 1744) ↦ₘ? 48 -∗
  (bv_unsigned sp + 1136) ↦ₘ? 608 -∗
  (bv_unsigned sp + 1792) ↦ₘ? 104 -∗
  writeSuccessTransactions14f1cCarrierScratch
    sp base total processed first second third fourth items.
Proof.
  iIntros "Hlower Hbase Htotal Hprefix Hprocessed Hupper Hcarrier
    Hwithdrawals Hmiddle Htail".
  rewrite /writeSuccessTransactions14f1cCarrierScratch.
  iFrame.
Qed.
