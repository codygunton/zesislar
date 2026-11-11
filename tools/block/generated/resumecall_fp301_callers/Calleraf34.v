Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaf34Entries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaf34Structural.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaf38Entries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaf38Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ResumeCallContract.
Require Import ZesuSsz.Contracts.ResumeCallSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800aaf34
    `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.ResumeCall.FP301.Pilotaf34Entries.fp_machineAtaf34 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800aaf34) := I.
Global Typeclasses Opaque DesignedEntry_800aaf34.

Lemma DesignedBoundary_800aaf34 `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800aaf38 (ZesuSsz.Generated.ResumeCall.FP301.Pilotaf38Entries.fp_machineAtaf38 (args) (returnAddress) (K))%I -∗
  resumeCallSelectedCode -∗
  instr_body 0x800aaf34
    (DesignedEntry_800aaf34 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800aaf34.
