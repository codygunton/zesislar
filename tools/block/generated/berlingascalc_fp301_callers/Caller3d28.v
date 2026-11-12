Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3d28Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3d28Structural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3d48Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3d48Structural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3ec8Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3ec8Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.BerlinGasCalcContract.
Require Import ZesuSsz.Contracts.BerlinGasCalcSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d3d28
    `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3d28Entries.fp_machineAt3d28 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d3d28) := I.
Global Typeclasses Opaque DesignedEntry_800d3d28.

Lemma DesignedBoundary_800d3d28 `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d3d48 (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3d48Entries.fp_machineAt3d48 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d3ec8 (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3ec8Entries.fp_machineAt3ec8 (args) (returnAddress) (K))%I -∗
  berlinGasCalcSelectedCode -∗
  instr_body 0x800d3d28
    (DesignedEntry_800d3d28 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d3d28.
