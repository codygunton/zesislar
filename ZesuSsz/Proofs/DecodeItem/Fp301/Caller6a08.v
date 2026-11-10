Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a08Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a08Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ae0Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a14Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ae0Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a14Entries.
Require Import ZesuSsz.Compliance.DecodeItemFp301Hints.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Lemma Fp301Boundary_800d6a08 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)   :
  instr_pre 0x800d6a14 (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a14Entries.fp_machineAt6a14 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6ae0 (ZesuSsz.Generated.DecodeItem.FP301.Pilot6ae0Entries.fp_machineAt6ae0 (args) (returnAddress) (K))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a08
    (Fp301Entry_800d6a08 args returnAddress K).
Proof.
  zesu_block2.
Qed.
