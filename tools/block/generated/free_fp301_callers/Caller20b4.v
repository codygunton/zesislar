Require Import ZesuSsz.Generated.Free.FP301.Pilot20b4Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot20b4Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot20ccEntries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot20ccStructural.
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

Definition DesignedEntry_800420b4
    `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.Free.FP301.Pilot20b4Entries.fp_machineAt20b4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800420b4) := I.
Global Typeclasses Opaque DesignedEntry_800420b4.

Lemma DesignedBoundary_800420b4 `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800420cc (ZesuSsz.Generated.Free.FP301.Pilot20ccEntries.fp_machineAt20cc (args) (returnAddress) (K))%I -∗
  instr_pre 0x80042130 (ZesuSsz.Generated.Free.FP301.Pilot2130Entries.fp_machineAt2130 (args) (returnAddress) (K))%I -∗
  freeSelectedCode -∗
  instr_body 0x800420b4
    (DesignedEntry_800420b4 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800420b4.
