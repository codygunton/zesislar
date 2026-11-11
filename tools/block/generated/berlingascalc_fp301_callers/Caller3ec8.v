Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3ec8Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3ec8Structural.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.FunctionReturn3ed8Entries.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.FunctionReturn3ed8Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.BerlinGasCalcContract.
Require Import ZesuSsz.Contracts.BerlinGasCalcSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800d3ec8
    `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot3ec8Entries.fp_machineAt3ec8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d3ec8) := I.
Global Typeclasses Opaque DesignedEntry_800d3ec8.

Lemma DesignedBoundary_800d3ec8 `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre returnAddress (ZesuSsz.Generated.BerlinGasCalc.FP301.FunctionReturn3ed8Entries.fp_machineReturn3ed8 args returnAddress K) -∗
  berlinGasCalcSelectedCode -∗
  instr_body 0x800d3ec8
    (DesignedEntry_800d3ec8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d3ec8.
