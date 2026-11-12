Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39bcEntries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39bcStructural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39ccEntries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39ccStructural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39ecEntries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39ecStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.BerlinGasCalcContract.
Require Import ZesuSsz.Contracts.BerlinGasCalcSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d39bc
    `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39bcEntries.fp_machineAt39bc (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d39bc) := I.
Global Typeclasses Opaque DesignedEntry_800d39bc.

Lemma DesignedBoundary_800d39bc `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d39cc (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39ccEntries.fp_machineAt39cc (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d39ec (ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39ecEntries.fp_machineAt39ec (args) (returnAddress) (K))%I -∗
  berlinGasCalcSelectedCode -∗
  instr_body 0x800d39bc
    (DesignedEntry_800d39bc args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d39bc.
