Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierBoundary150f0.

(* The optional-U64 return at 0x150fc does not change transaction scratch.
   Keep the carrier split available for the nonce field at 0x15108. *)
Definition writeSuccessTransactions150fcCarrierScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  writeSuccessTransactions150f0CarrierScratch
    sp base total processed transaction first second third fourth items.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions150fcCarrierScratch) := I.
Global Typeclasses Opaque writeSuccessTransactions150fcCarrierScratch.

Lemma write_success_transactions_150fc_carrier_scratch_pack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions150f0CarrierScratch
    sp base total processed transaction first second third fourth items -∗
  writeSuccessTransactions150fcCarrierScratch
    sp base total processed transaction first second third fourth items.
Proof.
  iIntros "Hscratch".
  iExact "Hscratch".
Qed.

Lemma write_success_transactions_150fc_carrier_scratch_unpack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions150fcCarrierScratch
    sp base total processed transaction first second third fourth items -∗
  writeSuccessTransactions150f0CarrierScratch
    sp base total processed transaction first second third fourth items.
Proof.
  iIntros "Hscratch".
  iExact "Hscratch".
Qed.
