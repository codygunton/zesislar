Require Import ZesuSsz.Generated.Free.FP301.Pilot2080Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2080Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2090Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2090Structural.
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

Definition DesignedEntry_80042080
    `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.Free.FP301.Pilot2080Entries.fp_machineAt2080 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80042080) := I.
Global Typeclasses Opaque DesignedEntry_80042080.

Lemma DesignedBoundary_80042080 `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80042090 (ZesuSsz.Generated.Free.FP301.Pilot2090Entries.fp_machineAt2090 (args) (returnAddress) (K))%I -∗
  instr_pre 0x80042130 (ZesuSsz.Generated.Free.FP301.Pilot2130Entries.fp_machineAt2130 (args) (returnAddress) (K))%I -∗
  freeSelectedCode -∗
  instr_body 0x80042080
    (DesignedEntry_80042080 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80042080.
