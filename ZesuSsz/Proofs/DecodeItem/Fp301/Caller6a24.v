Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a24Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a24Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a38Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a38Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.FP301.CallerUnfolds.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Lemma Fp301Boundary_800d6a24 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6a24 (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a24Entries.fp_machineAt6a24 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6a38 (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a38Entries.fp_machineAt6a38 (args) (returnAddress) (K))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a24
    (Fp301Entry_800d6a24 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions Fp301Boundary_800d6a24.
