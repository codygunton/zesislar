Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69a4Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69a4Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69d8Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69b0Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69d8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69b0Entries.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition Fp301Entry_800d69a4
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot69a4Entries.fp_machineAt69a4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d69a4) := I.
Global Typeclasses Opaque Fp301Entry_800d69a4.

Lemma Fp301Boundary_800d69a4 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)   :
  instr_pre 0x800d69b0 (ZesuSsz.Generated.DecodeItem.FP301.Pilot69b0Entries.fp_machineAt69b0 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d69d8 (ZesuSsz.Generated.DecodeItem.FP301.Pilot69d8Entries.fp_machineAt69d8 (args) (returnAddress) (K))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d69a4
    (Fp301Entry_800d69a4 args returnAddress K).
Proof.
  zesu_block2.
Qed.
