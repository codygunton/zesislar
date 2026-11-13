Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ac4Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ac4Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ad8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ad8Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent decodeItemSelectedCode.

Definition DesignedEntry_800d6ac4
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6ac4Entries.fp_machineAt6ac4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6ac4) := I.
Global Typeclasses Opaque DesignedEntry_800d6ac4.

Lemma DesignedBoundary_800d6ac4 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6ac4 (ZesuSsz.Generated.DecodeItem.FP301.Pilot6ac4Entries.fp_machineAt6ac4 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6ad8 (ZesuSsz.Generated.DecodeItem.FP301.Pilot6ad8Entries.fp_machineAt6ad8 (args) (returnAddress) (K))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6ac4
    (DesignedEntry_800d6ac4 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d6ac4.
