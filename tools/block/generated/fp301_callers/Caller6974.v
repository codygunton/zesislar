Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6974Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6974Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69a4Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot697cStructural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69a4Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot697cEntries.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d6974
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6974Entries.fp_machineAt6974 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6974) := I.
Global Typeclasses Opaque DesignedEntry_800d6974.

Lemma DesignedBoundary_800d6974 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)   :
  instr_pre 0x800d697c (ZesuSsz.Generated.DecodeItem.FP301.Pilot697cEntries.fp_machineAt697c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d69a4 (ZesuSsz.Generated.DecodeItem.FP301.Pilot69a4Entries.fp_machineAt69a4 (args) (returnAddress) (K))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6974
    (DesignedEntry_800d6974 args returnAddress K).
Proof.
  zesu_block2.
Qed.
