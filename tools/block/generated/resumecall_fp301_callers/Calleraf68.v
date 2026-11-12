Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaf68Entries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaf68Structural.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotafb0Entries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotafb0Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ResumeCallContract.
Require Import ZesuSsz.Contracts.ResumeCallSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800aaf68
    `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.ResumeCall.FP301.Pilotaf68Entries.fp_machineAtaf68 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800aaf68) := I.
Global Typeclasses Opaque DesignedEntry_800aaf68.

Lemma DesignedBoundary_800aaf68 `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800aafb0 (ZesuSsz.Generated.ResumeCall.FP301.Pilotafb0Entries.fp_machineAtafb0 (args) (returnAddress) (K))%I -∗
  resumeCallSelectedCode -∗
  instr_body 0x800aaf68
    (DesignedEntry_800aaf68 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800aaf68.
