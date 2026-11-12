Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39fcEntries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39fcStructural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3a40Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3a40Structural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3c44Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3c44Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.BerlinGasCalcContract.
Require Import ZesuSsz.Contracts.BerlinGasCalcSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d39fc
    `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39fcEntries.fp_machineAt39fc (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d39fc) := I.
Global Typeclasses Opaque DesignedEntry_800d39fc.

Lemma DesignedBoundary_800d39fc `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d3a40 (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3a40Entries.fp_machineAt3a40 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d3c44 (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3c44Entries.fp_machineAt3c44 (args) (returnAddress) (K))%I -∗
  berlinGasCalcSelectedCode -∗
  instr_body 0x800d39fc
    (DesignedEntry_800d39fc args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d39fc.
