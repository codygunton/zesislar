Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a64Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a64Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6aa8Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a6cStructural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6aa8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a6cEntries.
Require Import ZesuSsz.Compliance.DecodeItemFp301Hints.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Lemma Fp301Boundary_800d6a64 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)   :
  instr_pre 0x800d6a6c (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a6cEntries.fp_machineAt6a6c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6aa8 (ZesuSsz.Generated.DecodeItem.FP301.Pilot6aa8Entries.fp_machineAt6aa8 (args) (returnAddress) (K))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a64
    (Fp301Entry_800d6a64 args returnAddress K).
Proof.
  zesu_block2.
Qed.
