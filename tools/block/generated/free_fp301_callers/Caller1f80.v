Require Import ZesuSsz.Generated.Free.FP301.Pilot1f80Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1f80Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1f8cEntries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1f8cStructural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1fdcEntries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1fdcStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.FreeSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_80041f80
    `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.Free.FP301.Pilot1f80Entries.fp_machineAt1f80 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80041f80) := I.
Global Typeclasses Opaque DesignedEntry_80041f80.

Lemma DesignedBoundary_80041f80 `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80041f8c (ZesuSsz.Generated.Free.FP301.Pilot1f8cEntries.fp_machineAt1f8c (args) (returnAddress) (K))%I -∗
  instr_pre 0x80041fdc (ZesuSsz.Generated.Free.FP301.Pilot1fdcEntries.fp_machineAt1fdc (args) (returnAddress) (K))%I -∗
  freeSelectedCode -∗
  instr_body 0x80041f80
    (DesignedEntry_80041f80 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80041f80.
