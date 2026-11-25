Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot039cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot039cStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot03c0Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot03c0Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot03e0Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot03e0Structural.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges039c.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_8000039c
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot039cEntries.fp_machineAt039c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_8000039c) := I.
Global Typeclasses Opaque DesignedEntry_8000039c.

Lemma DesignedBoundary_8000039c `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800003c0 (ZesuSsz.Generated.TxAccessList.FP301.Pilot03c0Entries.fp_machineAt03c0 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800003e0 (ZesuSsz.Generated.TxAccessList.FP301.Pilot03e0Entries.fp_machineAt03e0 (args) (returnAddress) (K))%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x8000039c
    (DesignedEntry_8000039c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_8000039c.
