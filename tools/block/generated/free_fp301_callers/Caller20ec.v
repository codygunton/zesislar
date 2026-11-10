Require Import ZesuSsz.Generated.Free.FP301.Pilot20ecEntries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot20ecStructural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2134Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2134Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.FreeSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800420ec
    `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.Free.FP301.Pilot20ecEntries.fp_machineAt20ec (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800420ec) := I.
Global Typeclasses Opaque DesignedEntry_800420ec.

Lemma DesignedBoundary_800420ec `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80042134 (ZesuSsz.Generated.Free.FP301.Pilot2134Entries.fp_machineAt2134 (args) (returnAddress) (K))%I -∗
  freeSelectedCode -∗
  instr_body 0x800420ec
    (DesignedEntry_800420ec args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800420ec.
