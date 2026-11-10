Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69d8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69d8Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a00Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69e0Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a00Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69e0Entries.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition Fp301Entry_800d69d8
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot69d8Entries.fp_machineAt69d8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d69d8) := I.
Global Typeclasses Opaque Fp301Entry_800d69d8.

Lemma Fp301Boundary_800d69d8 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)   :
  instr_pre 0x800d69e0 (ZesuSsz.Generated.DecodeItem.FP301.Pilot69e0Entries.fp_machineAt69e0 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6a00 (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a00Entries.fp_machineAt6a00 (args) (returnAddress) (K))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d69d8
    (Fp301Entry_800d69d8 args returnAddress K).
Proof.
  zesu_block2.
Qed.
