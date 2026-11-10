Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69b0Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69b0Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnStructural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.CallerUnfolds.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Compliance.DecodeItemMeaningPorted.
Require Import ZesuSsz.Residuals.Block800d69b0.
Local Open Scope Z_scope.

Lemma Fp301Boundary_800d69b0 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre returnAddress (ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries.fp_machineReturn args returnAddress K) -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d69b0
    (Fp301Entry_800d69b0 args returnAddress K).
Proof.
  zesu_block2.
Qed.
