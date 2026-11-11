Require Import ZesuSsz.Generated.Free.FP301.Pilot202cEntries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot202cStructural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2038Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2038Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot20f0Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot20f0Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.FreeSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_8004202c
    `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.Free.FP301.Pilot202cEntries.fp_machineAt202c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_8004202c) := I.
Global Typeclasses Opaque DesignedEntry_8004202c.

Lemma DesignedBoundary_8004202c `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80042038 (ZesuSsz.Generated.Free.FP301.Pilot2038Entries.fp_machineAt2038 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800420f0 (ZesuSsz.Generated.Free.FP301.Pilot20f0Entries.fp_machineAt20f0 (args) (returnAddress) (K))%I -∗
  freeSelectedCode -∗
  instr_body 0x8004202c
    (DesignedEntry_8004202c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_8004202c.
