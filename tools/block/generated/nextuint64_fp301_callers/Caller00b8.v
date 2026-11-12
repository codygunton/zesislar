Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00b8Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00b8Structural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0070Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0070Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d632c
    `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.NextUint64.FP301.Pilot00b8Entries.fp_machineAt00b8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d632c) := I.
Global Typeclasses Opaque DesignedEntry_800d632c.

Lemma DesignedBoundary_800d632c `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d62e4 (ZesuSsz.Generated.NextUint64.FP301.Pilot0070Entries.fp_machineAt0070 (args) (returnAddress) (K))%I -∗
  nextUint64SelectedCode -∗
  instr_body 0x800d632c
    (DesignedEntry_800d632c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d632c.
