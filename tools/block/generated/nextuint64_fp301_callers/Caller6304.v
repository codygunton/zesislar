Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot6304Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot6304Structural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot6310Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot6310Structural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot632cEntries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot632cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64Contract.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d6304
    `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.NextUint64.FP301.Pilot6304Entries.fp_machineAt6304 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6304) := I.
Global Typeclasses Opaque DesignedEntry_800d6304.

Lemma DesignedBoundary_800d6304 `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6310 (ZesuSsz.Generated.NextUint64.FP301.Pilot6310Entries.fp_machineAt6310 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d632c (ZesuSsz.Generated.NextUint64.FP301.Pilot632cEntries.fp_machineAt632c (args) (returnAddress) (K))%I -∗
  nextUint64SelectedCode -∗
  instr_body 0x800d6304
    (DesignedEntry_800d6304 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6304.
