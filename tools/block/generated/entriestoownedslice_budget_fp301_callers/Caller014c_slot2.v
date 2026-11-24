Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot014cEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot014cStructural.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnStructural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceChargedSelected.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Edges014c.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceChargedCode.

Definition DesignedEntry_800d66a0_slot2
    `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot014cEntries.fp_machineAt014c_slot2 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d66a0_slot2) := I.
Global Typeclasses Opaque DesignedEntry_800d66a0_slot2.

Lemma DesignedBoundary_800d66a0_slot2 `{!islaG Sigma} `{!threadG} (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre returnAddress (ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot2 args returnAddress K) -∗
  entriesToOwnedSliceChargedCode -∗
  instr_body 0x800d66a0
    (DesignedEntry_800d66a0_slot2 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d66a0_slot2.
