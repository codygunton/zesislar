Require Import ZesuSsz.Generated.Free.FP301.Pilot1fe8Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1fe8Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1ff4Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1ff4Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot20d0Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot20d0Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.FreeSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_80041fe8
    `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.Free.FP301.Pilot1fe8Entries.fp_machineAt1fe8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80041fe8) := I.
Global Typeclasses Opaque DesignedEntry_80041fe8.

Lemma DesignedBoundary_80041fe8 `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80041ff4 (ZesuSsz.Generated.Free.FP301.Pilot1ff4Entries.fp_machineAt1ff4 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800420d0 (ZesuSsz.Generated.Free.FP301.Pilot20d0Entries.fp_machineAt20d0 (args) (returnAddress) (K))%I -∗
  freeSelectedCode -∗
  instr_body 0x80041fe8
    (DesignedEntry_80041fe8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80041fe8.
