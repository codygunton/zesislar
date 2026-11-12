Require Import ZesuSsz.Generated.Free.FP301.Pilot1fa4Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1fa4Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1fb4Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1fb4Structural.
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

Definition DesignedEntry_80041fa4
    `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.Free.FP301.Pilot1fa4Entries.fp_machineAt1fa4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80041fa4) := I.
Global Typeclasses Opaque DesignedEntry_80041fa4.

Lemma DesignedBoundary_80041fa4 `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80041fb4 (ZesuSsz.Generated.Free.FP301.Pilot1fb4Entries.fp_machineAt1fb4 (args) (returnAddress) (K))%I -∗
  instr_pre 0x80042130 (ZesuSsz.Generated.Free.FP301.Pilot2130Entries.fp_machineAt2130 (args) (returnAddress) (K))%I -∗
  freeSelectedCode -∗
  instr_body 0x80041fa4
    (DesignedEntry_80041fa4 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80041fa4.
