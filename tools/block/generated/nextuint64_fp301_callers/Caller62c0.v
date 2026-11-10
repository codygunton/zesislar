Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot62c0Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot62c0Structural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot62ccEntries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot62ccStructural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot62d8Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot62d8Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64Contract.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d62c0
    `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.NextUint64.FP301.Pilot62c0Entries.fp_machineAt62c0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d62c0) := I.
Global Typeclasses Opaque DesignedEntry_800d62c0.

Lemma DesignedBoundary_800d62c0 `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d62cc (ZesuSsz.Generated.NextUint64.FP301.Pilot62ccEntries.fp_machineAt62cc (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d62d8 (ZesuSsz.Generated.NextUint64.FP301.Pilot62d8Entries.fp_machineAt62d8 (args) (returnAddress) (K))%I -∗
  nextUint64SelectedCode -∗
  instr_body 0x800d62c0
    (DesignedEntry_800d62c0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d62c0.
