Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierBoundary150fc.

(* The gas-price entry at 0x15108 keeps the optional-U64 return scratch.
   The encoder call changes registers only and hands control to 0x15118. *)
Definition writeSuccessTransactions15108CarrierScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  writeSuccessTransactions150fcCarrierScratch
    sp base total processed transaction first second third fourth items.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions15108CarrierScratch) := I.
Global Typeclasses Opaque writeSuccessTransactions15108CarrierScratch.

Lemma write_success_transactions_15108_carrier_scratch_pack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions150fcCarrierScratch
    sp base total processed transaction first second third fourth items -∗
  writeSuccessTransactions15108CarrierScratch
    sp base total processed transaction first second third fourth items.
Proof.
  iIntros "Hscratch".
  iExact "Hscratch".
Qed.

Lemma write_success_transactions_15108_carrier_scratch_unpack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions15108CarrierScratch
    sp base total processed transaction first second third fourth items -∗
  writeSuccessTransactions150fcCarrierScratch
    sp base total processed transaction first second third fourth items.
Proof.
  iIntros "Hscratch".
  iExact "Hscratch".
Qed.
