Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotb010Entries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotb010Structural.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotb018Entries.
Require Import ZesuSsz.Generated.ResumeCall.FP301.Pilotb018Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.ResumeCallContract.
Require Import ZesuSsz.Contracts.ResumeCallSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800ab010
    `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.ResumeCall.FP301.Pilotb010Entries.fp_machineAtb010 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800ab010) := I.
Global Typeclasses Opaque DesignedEntry_800ab010.

Lemma DesignedBoundary_800ab010 `{!islaG Sigma} `{!threadG} (args : ResumeCallArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800ab018 (ZesuSsz.Generated.ResumeCall.FP301.Pilotb018Entries.fp_machineAtb018 (args) (returnAddress) (K))%I -∗
  resumeCallSelectedCode -∗
  instr_body 0x800ab010
    (DesignedEntry_800ab010 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800ab010.
