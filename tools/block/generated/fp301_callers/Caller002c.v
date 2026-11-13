Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot002cEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot002cStructural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Compliance.DecodeItemMeaningPorted.
Require Import ZesuSsz.Residuals.Block800d698c.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent decodeItemSelectedCode.

Definition DesignedEntry_800d698c
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot002cEntries.fp_machineAt002c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d698c) := I.
Global Typeclasses Opaque DesignedEntry_800d698c.

Lemma DesignedBoundary_800d698c `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre returnAddress (ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries.fp_machineReturn args returnAddress K) -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d698c
    (DesignedEntry_800d698c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d698c.
