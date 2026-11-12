Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3f00Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3f00Structural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3f04Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3f04Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.BerlinGasCalcContract.
Require Import ZesuSsz.Contracts.BerlinGasCalcSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d3f00
    `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3f00Entries.fp_machineAt3f00 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d3f00) := I.
Global Typeclasses Opaque DesignedEntry_800d3f00.

Lemma DesignedBoundary_800d3f00 `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d3f04 (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3f04Entries.fp_machineAt3f04 (args) (returnAddress) (K))%I -∗
  berlinGasCalcSelectedCode -∗
  instr_body 0x800d3f00
    (DesignedEntry_800d3f00 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d3f00.
