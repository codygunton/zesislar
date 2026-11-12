Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0090Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0090Structural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot009cEntries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot009cStructural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00b8Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00b8Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d6304
    `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.NextUint64.FP301.Pilot0090Entries.fp_machineAt0090 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6304) := I.
Global Typeclasses Opaque DesignedEntry_800d6304.

Lemma DesignedBoundary_800d6304 `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6310 (ZesuSsz.Generated.NextUint64.FP301.Pilot009cEntries.fp_machineAt009c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d632c (ZesuSsz.Generated.NextUint64.FP301.Pilot00b8Entries.fp_machineAt00b8 (args) (returnAddress) (K))%I -∗
  nextUint64SelectedCode -∗
  instr_body 0x800d6304
    (DesignedEntry_800d6304 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6304.
