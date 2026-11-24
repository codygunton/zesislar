Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0264Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0264Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot02a0Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot02a0Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0448Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0448Structural.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges0264.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_80000264
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot0264Entries.fp_machineAt0264 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80000264) := I.
Global Typeclasses Opaque DesignedEntry_80000264.

Lemma DesignedBoundary_80000264 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800002a0 (ZesuSsz.Generated.TxAccessList.FP301.Pilot02a0Entries.fp_machineAt02a0 (args) (returnAddress) (K))%I -∗
  instr_pre 0x80000448 (ZesuSsz.Generated.TxAccessList.FP301.Pilot0448Entries.fp_machineAt0448 (args) (returnAddress) (K))%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x80000264
    (DesignedEntry_80000264 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80000264.
