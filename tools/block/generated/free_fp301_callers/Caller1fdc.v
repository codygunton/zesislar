Require Import ZesuSsz.Generated.Free.FP301.Pilot1fdcEntries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1fdcStructural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1fe8Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1fe8Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2074Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2074Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.FreeSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_80041fdc
    `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.Free.FP301.Pilot1fdcEntries.fp_machineAt1fdc (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80041fdc) := I.
Global Typeclasses Opaque DesignedEntry_80041fdc.

Lemma DesignedBoundary_80041fdc `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80041fe8 (ZesuSsz.Generated.Free.FP301.Pilot1fe8Entries.fp_machineAt1fe8 (args) (returnAddress) (K))%I -∗
  instr_pre 0x80042074 (ZesuSsz.Generated.Free.FP301.Pilot2074Entries.fp_machineAt2074 (args) (returnAddress) (K))%I -∗
  freeSelectedCode -∗
  instr_body 0x80041fdc
    (DesignedEntry_80041fdc args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80041fdc.
