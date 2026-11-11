Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3b1cEntries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3b1cStructural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3b24Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3b24Structural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e30Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e30Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.BerlinGasCalcContract.
Require Import ZesuSsz.Contracts.BerlinGasCalcSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d3b1c
    `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3b1cEntries.fp_machineAt3b1c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d3b1c) := I.
Global Typeclasses Opaque DesignedEntry_800d3b1c.

Lemma DesignedBoundary_800d3b1c `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d3b24 (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3b24Entries.fp_machineAt3b24 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d3e30 (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3e30Entries.fp_machineAt3e30 (args) (returnAddress) (K))%I -∗
  berlinGasCalcSelectedCode -∗
  instr_body 0x800d3b1c
    (DesignedEntry_800d3b1c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d3b1c.
