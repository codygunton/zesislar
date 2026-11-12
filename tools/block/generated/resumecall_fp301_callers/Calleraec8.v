Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaec8Entries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaec8Structural.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaf28Entries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaf28Structural.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaf54Entries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaf54Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ResumeCallContract.
Require Import ZesuSsz.Contracts.ResumeCallSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800aaec8
    `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.ResumeCall.FP301.Pilotaec8Entries.fp_machineAtaec8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800aaec8) := I.
Global Typeclasses Opaque DesignedEntry_800aaec8.

Lemma DesignedBoundary_800aaec8 `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800aaf28 (ZesuSsz.Generated.ResumeCall.FP301.Pilotaf28Entries.fp_machineAtaf28 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800aaf54 (ZesuSsz.Generated.ResumeCall.FP301.Pilotaf54Entries.fp_machineAtaf54 (args) (returnAddress) (K))%I -∗
  resumeCallSelectedCode -∗
  instr_body 0x800aaec8
    (DesignedEntry_800aaec8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800aaec8.
