Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot01bcEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot01bcStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot01f8Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot01f8Structural.
Require Import ZesuSsz.Interfaces.KeysEnsureCapacity.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Import ZesuSsz.Contracts.TxAccessListLoopFacts.
Require Import ZesuSsz.Contracts.TxAccessListSelected.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges01bc.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_800001bc
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot01bcEntries.fp_machineAt01bc (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800001bc) := I.
Global Typeclasses Opaque DesignedEntry_800001bc.

Lemma DesignedBoundary_800001bc `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800001f8 (ZesuSsz.Generated.TxAccessList.FP301.Pilot01f8Entries.fp_machineAt01f8 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800cb40c (ZesuSsz.Interfaces.KeysEnsureCapacity.keysEnsureCapacityCallSpec2)%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x800001bc
    (DesignedEntry_800001bc args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800001bc.
