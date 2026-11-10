Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69e8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69e8Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot698cStructural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot698cEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.CallerUnfolds.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.Block800d69e8.
Local Open Scope Z_scope.

Lemma Fp301Boundary_800d69e8 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d698c (ZesuSsz.Generated.DecodeItem.FP301.Pilot698cEntries.fp_machineAt698c (args) (returnAddress) (K))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d69e8
    (Fp301Entry_800d69e8 args returnAddress K).
Proof.
  zesu_block2.
Qed.
