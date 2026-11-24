Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot018cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot018cStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot01a0Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot01a0Structural.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Import ZesuSsz.Contracts.TxAccessListLoopFacts.
Require Import ZesuSsz.Contracts.TxAccessListSelected.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges018c.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_8000018c
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot018cEntries.fp_machineAt018c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_8000018c) := I.
Global Typeclasses Opaque DesignedEntry_8000018c.

Lemma DesignedBoundary_8000018c `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800001a0 (ZesuSsz.Generated.TxAccessList.FP301.Pilot01a0Entries.fp_machineAt01a0 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6960 (ZesuSsz.Interfaces.DecodeItem.decodeItemCallSpec2)%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x8000018c
    (DesignedEntry_8000018c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_8000018c.
