Require Import ZesuSsz.Generated.Free.FP301.Pilot1fb8Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1fb8Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1fc0Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1fc0Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2058Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2058Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.FreeSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_80041fb8
    `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.Free.FP301.Pilot1fb8Entries.fp_machineAt1fb8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80041fb8) := I.
Global Typeclasses Opaque DesignedEntry_80041fb8.

Lemma DesignedBoundary_80041fb8 `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80041fc0 (ZesuSsz.Generated.Free.FP301.Pilot1fc0Entries.fp_machineAt1fc0 (args) (returnAddress) (K))%I -∗
  instr_pre 0x80042058 (ZesuSsz.Generated.Free.FP301.Pilot2058Entries.fp_machineAt2058 (args) (returnAddress) (K))%I -∗
  freeSelectedCode -∗
  instr_body 0x80041fb8
    (DesignedEntry_80041fb8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80041fb8.
