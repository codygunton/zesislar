Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot6274Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot6274Structural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot62b8Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot62b8Structural.
Require Import ZesuSsz.Contracts.DecodeItemCallSpec2.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d6274
    `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.NextUint64.FP301.Pilot6274Entries.fp_machineAt6274 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6274) := I.
Global Typeclasses Opaque DesignedEntry_800d6274.

Lemma DesignedBoundary_800d6274 `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d62b8 (ZesuSsz.Generated.NextUint64.FP301.Pilot62b8Entries.fp_machineAt62b8 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6960 (ZesuSsz.Contracts.DecodeItemCallSpec2.decodeItemCallSpec2)%I -∗
  nextUint64SelectedCode -∗
  instr_body 0x800d6274
    (DesignedEntry_800d6274 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6274.
