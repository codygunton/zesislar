Require Import ZesuSsz.Generated.Free.FP301.Pilot2074Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2074Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2080Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2080Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2110Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2110Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.FreeSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_80042074
    `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.Free.FP301.Pilot2074Entries.fp_machineAt2074 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80042074) := I.
Global Typeclasses Opaque DesignedEntry_80042074.

Lemma DesignedBoundary_80042074 `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80042080 (ZesuSsz.Generated.Free.FP301.Pilot2080Entries.fp_machineAt2080 (args) (returnAddress) (K))%I -∗
  instr_pre 0x80042110 (ZesuSsz.Generated.Free.FP301.Pilot2110Entries.fp_machineAt2110 (args) (returnAddress) (K))%I -∗
  freeSelectedCode -∗
  instr_body 0x80042074
    (DesignedEntry_80042074 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80042074.
