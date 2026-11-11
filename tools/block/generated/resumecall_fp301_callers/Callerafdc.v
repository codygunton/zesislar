Require Import ZesuSsz.Generated.ResumeCall.FP301.PilotafdcEntries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.PilotafdcStructural.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaff4Entries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotaff4Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ResumeCallContract.
Require Import ZesuSsz.Contracts.ResumeCallSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800aafdc
    `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.ResumeCall.FP301.PilotafdcEntries.fp_machineAtafdc (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800aafdc) := I.
Global Typeclasses Opaque DesignedEntry_800aafdc.

Lemma DesignedBoundary_800aafdc `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800aaff4 (ZesuSsz.Generated.ResumeCall.FP301.Pilotaff4Entries.fp_machineAtaff4 (args) (returnAddress) (K))%I -∗
  resumeCallSelectedCode -∗
  instr_body 0x800aafdc
    (DesignedEntry_800aafdc args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800aafdc.
