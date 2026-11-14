Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0000Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0000Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0180Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0014Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0180Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0014Entries.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.Block800d6960.
Local Open Scope Z_scope.

Definition DesignedEntry_800d6960
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot0000Entries.fp_machineAt0000 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6960) := I.
Global Typeclasses Opaque DesignedEntry_800d6960.

Lemma DesignedBoundary_800d6960 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)   :
  instr_pre 0x800d6974 (ZesuSsz.Generated.DecodeItem.FP301.Pilot0014Entries.fp_machineAt0014 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6ae0 (ZesuSsz.Generated.DecodeItem.FP301.Pilot0180Entries.fp_machineAt0180 (args) (returnAddress) (K))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6960
    (DesignedEntry_800d6960 args returnAddress K).
Proof.
  zesu_block2.
Qed.
