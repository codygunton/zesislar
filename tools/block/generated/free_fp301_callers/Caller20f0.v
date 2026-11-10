Require Import ZesuSsz.Generated.Free.FP301.Pilot20f0Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot20f0Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot210cEntries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot210cStructural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2130Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2130Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.FreeSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800420f0
    `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.Free.FP301.Pilot20f0Entries.fp_machineAt20f0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800420f0) := I.
Global Typeclasses Opaque DesignedEntry_800420f0.

Lemma DesignedBoundary_800420f0 `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x8004210c (ZesuSsz.Generated.Free.FP301.Pilot210cEntries.fp_machineAt210c (args) (returnAddress) (K))%I -∗
  instr_pre 0x80042130 (ZesuSsz.Generated.Free.FP301.Pilot2130Entries.fp_machineAt2130 (args) (returnAddress) (K))%I -∗
  freeSelectedCode -∗
  instr_body 0x800420f0
    (DesignedEntry_800420f0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800420f0.
