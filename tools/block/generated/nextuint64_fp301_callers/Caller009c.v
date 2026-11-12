Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot009cEntries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot009cStructural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00a4Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00a4Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d6310
    `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.NextUint64.FP301.Pilot009cEntries.fp_machineAt009c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6310) := I.
Global Typeclasses Opaque DesignedEntry_800d6310.

Lemma DesignedBoundary_800d6310 `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6318 (ZesuSsz.Generated.NextUint64.FP301.Pilot00a4Entries.fp_machineAt00a4 (args) (returnAddress) (K))%I -∗
  nextUint64SelectedCode -∗
  instr_body 0x800d6310
    (DesignedEntry_800d6310 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6310.
