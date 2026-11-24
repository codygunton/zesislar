Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0400Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0400Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0404Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0404Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot042cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot042cStructural.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges0400.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_80000400
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot0400Entries.fp_machineAt0400 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80000400) := I.
Global Typeclasses Opaque DesignedEntry_80000400.

Lemma DesignedBoundary_80000400 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80000404 (ZesuSsz.Generated.TxAccessList.FP301.Pilot0404Entries.fp_machineAt0404 (args) (returnAddress) (K))%I -∗
  instr_pre 0x8000042c (ZesuSsz.Generated.TxAccessList.FP301.Pilot042cEntries.fp_machineAt042c (args) (returnAddress) (K))%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x80000400
    (DesignedEntry_80000400 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80000400.
