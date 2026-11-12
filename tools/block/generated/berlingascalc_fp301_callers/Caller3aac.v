Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3aacEntries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3aacStructural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3b18Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3b18Structural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3d1cEntries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3d1cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.BerlinGasCalcContract.
Require Import ZesuSsz.Contracts.BerlinGasCalcSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d3aac
    `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3aacEntries.fp_machineAt3aac (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d3aac) := I.
Global Typeclasses Opaque DesignedEntry_800d3aac.

Lemma DesignedBoundary_800d3aac `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d3b18 (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3b18Entries.fp_machineAt3b18 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d3d1c (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3d1cEntries.fp_machineAt3d1c (args) (returnAddress) (K))%I -∗
  berlinGasCalcSelectedCode -∗
  instr_body 0x800d3aac
    (DesignedEntry_800d3aac args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d3aac.
