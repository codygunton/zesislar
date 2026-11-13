Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a40Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a40Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Compliance.DecodeItemMeaningPorted.
Require Import ZesuSsz.Residuals.Block800d6a40.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent decodeItemSelectedCode.

Definition DesignedEntry_800d6a40
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6a40Entries.fp_machineAt6a40 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6a40) := I.
Global Typeclasses Opaque DesignedEntry_800d6a40.

Lemma DesignedBoundary_800d6a40 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre returnAddress (ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries.fp_machineReturn args returnAddress K) -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a40
    (DesignedEntry_800d6a40 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6a40.
