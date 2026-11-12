Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3c44Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3c44Structural.
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

Definition DesignedEntry_800d3c44
    `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3c44Entries.fp_machineAt3c44 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d3c44) := I.
Global Typeclasses Opaque DesignedEntry_800d3c44.

Lemma DesignedBoundary_800d3c44 `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d3aac (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3aacEntries.fp_machineAt3aac (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d3cac (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3cacEntries.fp_machineAt3cac (args) (returnAddress) (K))%I -∗
  berlinGasCalcSelectedCode -∗
  instr_body 0x800d3c44
    (DesignedEntry_800d3c44 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d3c44.
