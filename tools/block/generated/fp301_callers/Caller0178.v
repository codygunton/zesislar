Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0178Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0178Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot01a8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot01a8Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0180Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0180Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.Block800d6ad8.
Local Open Scope Z_scope.

Definition DesignedEntry_800d6ad8
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot0178Entries.fp_machineAt0178 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6ad8) := I.
Global Typeclasses Opaque DesignedEntry_800d6ad8.

Lemma DesignedBoundary_800d6ad8 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6b08 (ZesuSsz.Generated.DecodeItem.FP301.Pilot01a8Entries.fp_machineAt01a8 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6ae0 (ZesuSsz.Generated.DecodeItem.FP301.Pilot0180Entries.fp_machineAt0180 (args) (returnAddress) (K))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6ad8
    (DesignedEntry_800d6ad8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6ad8.
