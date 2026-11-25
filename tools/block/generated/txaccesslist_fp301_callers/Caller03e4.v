Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot03e4Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot03e4Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0400Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0400Structural.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges03e4.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_800003e4
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot03e4Entries.fp_machineAt03e4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800003e4) := I.
Global Typeclasses Opaque DesignedEntry_800003e4.

Lemma DesignedBoundary_800003e4 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80000400 (ZesuSsz.Generated.TxAccessList.FP301.Pilot0400Entries.fp_machineAt0400 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800e06c0 (ZesuSsz.Contracts.ZiskMemcpyPremise.ziskMemcpyCallSpec)%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x800003e4
    (DesignedEntry_800003e4 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800003e4.
