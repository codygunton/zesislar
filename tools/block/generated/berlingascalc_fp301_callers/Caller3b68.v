Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3b68Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3b68Structural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3bd4Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3bd4Structural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3db4Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3db4Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.BerlinGasCalcContract.
Require Import ZesuSsz.Contracts.BerlinGasCalcSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d3b68
    `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3b68Entries.fp_machineAt3b68 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d3b68) := I.
Global Typeclasses Opaque DesignedEntry_800d3b68.

Lemma DesignedBoundary_800d3b68 `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d3bd4 (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3bd4Entries.fp_machineAt3bd4 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d3db4 (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3db4Entries.fp_machineAt3db4 (args) (returnAddress) (K))%I -∗
  berlinGasCalcSelectedCode -∗
  instr_body 0x800d3b68
    (DesignedEntry_800d3b68 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d3b68.
