Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0088Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0088Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot002cStructural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot002cEntries.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.Block800d69e8.
Local Open Scope Z_scope.

Definition DesignedEntry_800d69e8
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot0088Entries.fp_machineAt0088 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d69e8) := I.
Global Typeclasses Opaque DesignedEntry_800d69e8.

Lemma DesignedBoundary_800d69e8 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d698c (ZesuSsz.Generated.DecodeItem.FP301.Pilot002cEntries.fp_machineAt002c (args) (returnAddress) (K))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d69e8
    (DesignedEntry_800d69e8 args returnAddress K).
Proof.
  zesu_block2.
Qed.
