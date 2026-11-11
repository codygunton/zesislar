Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e98Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e98Structural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3eacEntries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3eacStructural.
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

Definition DesignedEntry_800d3e98
    `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e98Entries.fp_machineAt3e98 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d3e98) := I.
Global Typeclasses Opaque DesignedEntry_800d3e98.

Lemma DesignedBoundary_800d3e98 `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d3eac (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3eacEntries.fp_machineAt3eac (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d3ec8 (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3ec8Entries.fp_machineAt3ec8 (args) (returnAddress) (K))%I -∗
  berlinGasCalcSelectedCode -∗
  instr_body 0x800d3e98
    (DesignedEntry_800d3e98 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d3e98.
