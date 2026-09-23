Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierBoundary1519c.

(* The value phase at 0x1519c joins both address branches.  It preserves
   their branch-specific address scratch and hands the same carrier to 0x151b4. *)
Definition writeSuccessTransactions151b4CarrierScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  writeSuccessTransactions1519cCarrierScratch
    sp base total processed transaction first second third fourth items.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions151b4CarrierScratch) := I.
Global Typeclasses Opaque writeSuccessTransactions151b4CarrierScratch.

Lemma write_success_transactions_151b4_carrier_scratch_pack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions1519cCarrierScratch
    sp base total processed transaction first second third fourth items -∗
  writeSuccessTransactions151b4CarrierScratch
    sp base total processed transaction first second third fourth items.
Proof. move => *. zesu_block. Qed.

Lemma write_success_transactions_151b4_carrier_scratch_unpack
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total processed : nat)
    (transaction : writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions151b4CarrierScratch
    sp base total processed transaction first second third fourth items -∗
  writeSuccessTransactions1519cCarrierScratch
    sp base total processed transaction first second third fourth items.
Proof. move => *. zesu_block. Qed.
