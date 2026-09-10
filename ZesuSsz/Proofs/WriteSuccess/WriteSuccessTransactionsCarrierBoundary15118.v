From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierBoundary15108.

(* The priority-fee entry at 0x15118 keeps the gas-price handoff scratch.
   The encoder call changes registers only and hands control to 0x15148. *)
Definition writeSuccessTransactions15118CarrierScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  writeSuccessTransactions15108CarrierScratch
    sp base total processed transaction first second third fourth items.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions15118CarrierScratch) := I.
Global Typeclasses Opaque writeSuccessTransactions15118CarrierScratch.

Lemma write_success_transactions_15118_carrier_scratch_pack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions15108CarrierScratch
    sp base total processed transaction first second third fourth items -∗
  writeSuccessTransactions15118CarrierScratch
    sp base total processed transaction first second third fourth items.
Proof.
  iIntros "Hscratch".
  iExact "Hscratch".
Qed.

Lemma write_success_transactions_15118_carrier_scratch_unpack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions15118CarrierScratch
    sp base total processed transaction first second third fourth items -∗
  writeSuccessTransactions15108CarrierScratch
    sp base total processed transaction first second third fourth items.
Proof.
  iIntros "Hscratch".
  iExact "Hscratch".
Qed.
