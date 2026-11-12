Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e44Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e44Structural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e68Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e68Structural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e80Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e80Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.BerlinGasCalcContract.
Require Import ZesuSsz.Contracts.BerlinGasCalcSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d3e44
    `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e44Entries.fp_machineAt3e44 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d3e44) := I.
Global Typeclasses Opaque DesignedEntry_800d3e44.

Lemma DesignedBoundary_800d3e44 `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d3e68 (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e68Entries.fp_machineAt3e68 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d3e80 (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e80Entries.fp_machineAt3e80 (args) (returnAddress) (K))%I -∗
  berlinGasCalcSelectedCode -∗
  instr_body 0x800d3e44
    (DesignedEntry_800d3e44 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d3e44.
