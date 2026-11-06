Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a6cEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a6cStructural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ae0Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a78Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ae0Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a78Entries.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d6a6c
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6a6cEntries.fp_machineAt6a6c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6a6c) := I.
Global Typeclasses Opaque DesignedEntry_800d6a6c.

Lemma DesignedBoundary_800d6a6c `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)   :
  instr_pre 0x800d6a78 (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a78Entries.fp_machineAt6a78 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6ae0 (ZesuSsz.Generated.DecodeItem.FP301.Pilot6ae0Entries.fp_machineAt6ae0 (args) (returnAddress) (K))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a6c
    (DesignedEntry_800d6a6c args returnAddress K).
Proof.
  zesu_block2.
Qed.
