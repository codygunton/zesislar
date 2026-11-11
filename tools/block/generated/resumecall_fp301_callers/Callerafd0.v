Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotafd0Entries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotafd0Structural.
Require Import ZesuSsz.Generated.ResumeCall.FP301.PilotafdcEntries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.PilotafdcStructural.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotb010Entries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotb010Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ResumeCallContract.
Require Import ZesuSsz.Contracts.ResumeCallSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800aafd0
    `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.ResumeCall.FP301.Pilotafd0Entries.fp_machineAtafd0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800aafd0) := I.
Global Typeclasses Opaque DesignedEntry_800aafd0.

Lemma DesignedBoundary_800aafd0 `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800aafdc (ZesuSsz.Generated.ResumeCall.FP301.PilotafdcEntries.fp_machineAtafdc (args) (returnAddress) (K))%I -∗
  instr_pre 0x800ab010 (ZesuSsz.Generated.ResumeCall.FP301.Pilotb010Entries.fp_machineAtb010 (args) (returnAddress) (K))%I -∗
  resumeCallSelectedCode -∗
  instr_body 0x800aafd0
    (DesignedEntry_800aafd0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800aafd0.
