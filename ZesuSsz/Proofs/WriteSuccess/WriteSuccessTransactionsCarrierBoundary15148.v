Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierBoundary15118.

(* The gas-limit entry at 0x15148 keeps the priority-fee handoff scratch.
   The phase contract changes registers only and hands control to 0x15154. *)
Definition writeSuccessTransactions15148CarrierScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  writeSuccessTransactions15118CarrierScratch
    sp base total processed transaction first second third fourth items.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions15148CarrierScratch) := I.
Global Typeclasses Opaque writeSuccessTransactions15148CarrierScratch.

Lemma write_success_transactions_15148_carrier_scratch_pack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions15118CarrierScratch
    sp base total processed transaction first second third fourth items -∗
  writeSuccessTransactions15148CarrierScratch
    sp base total processed transaction first second third fourth items.
Proof. move => *. zesu_block. Qed.

Lemma write_success_transactions_15148_carrier_scratch_unpack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions15148CarrierScratch
    sp base total processed transaction first second third fourth items -∗
  writeSuccessTransactions15118CarrierScratch
    sp base total processed transaction first second third fourth items.
Proof. move => *. zesu_block. Qed.
