Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00e0Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00e0Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00ecEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00ecStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04a8Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04a8Structural.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges00e0.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.txAccessList.Block00e0.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_800000e0
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot00e0Entries.fp_machineAt00e0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800000e0) := I.
Global Typeclasses Opaque DesignedEntry_800000e0.

Lemma DesignedBoundary_800000e0 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800000ec (ZesuSsz.Generated.TxAccessList.FP301.Pilot00ecEntries.fp_machineAt00ec (args) (returnAddress) (K))%I -∗
  instr_pre 0x800004a8 (ZesuSsz.Generated.TxAccessList.FP301.Pilot04a8Entries.fp_machineAt04a8 (args) (returnAddress) (K))%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x800000e0
    (DesignedEntry_800000e0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800000e0.
