Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3a40Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3a40Structural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3aacEntries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3aacStructural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3cacEntries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3cacStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.BerlinGasCalcContract.
Require Import ZesuSsz.Contracts.BerlinGasCalcSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d3a40
    `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3a40Entries.fp_machineAt3a40 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d3a40) := I.
Global Typeclasses Opaque DesignedEntry_800d3a40.

Lemma DesignedBoundary_800d3a40 `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d3aac (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3aacEntries.fp_machineAt3aac (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d3cac (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3cacEntries.fp_machineAt3cac (args) (returnAddress) (K))%I -∗
  berlinGasCalcSelectedCode -∗
  instr_body 0x800d3a40
    (DesignedEntry_800d3a40 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d3a40.
