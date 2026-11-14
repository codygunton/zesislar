Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0078Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0078Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot00a0Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0080Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot00a0Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0080Entries.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d69d8
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot0078Entries.fp_machineAt0078 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d69d8) := I.
Global Typeclasses Opaque DesignedEntry_800d69d8.

Lemma DesignedBoundary_800d69d8 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)   :
  instr_pre 0x800d69e0 (ZesuSsz.Generated.DecodeItem.FP301.Pilot0080Entries.fp_machineAt0080 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6a00 (ZesuSsz.Generated.DecodeItem.FP301.Pilot00a0Entries.fp_machineAt00a0 (args) (returnAddress) (K))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d69d8
    (DesignedEntry_800d69d8 args returnAddress K).
Proof.
  zesu_block2.
Qed.
