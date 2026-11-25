Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot048cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot048cStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04a0Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04a0Structural.
Require Import ZesuSsz.Interfaces.EntriesToOwnedSlice.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Import ZesuSsz.Contracts.TxAccessListLoopFacts.
Require Import ZesuSsz.Compliance.TxAccessListCallSlice.
Require Import ZesuSsz.Compliance.TxAccessListLoopIntro.
Require Import ZesuSsz.Contracts.TxAccessListSelected.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges048c.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.txAccessList.Block048c.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_8000048c
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot048cEntries.fp_machineAt048c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_8000048c) := I.
Global Typeclasses Opaque DesignedEntry_8000048c.

Lemma DesignedBoundary_8000048c `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800004a0 (ZesuSsz.Generated.TxAccessList.FP301.Pilot04a0Entries.fp_machineAt04a0 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6554 (ZesuSsz.Interfaces.EntriesToOwnedSlice.entriesToOwnedSliceCallSpec2)%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x8000048c
    (DesignedEntry_8000048c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_8000048c.
