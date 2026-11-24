Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot017cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot017cStructural.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0180Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0180Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot019cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot019cStructural.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityChargedSelected.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Edges017c.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.keysEnsureCapacity.Block017c.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacityChargedCode.

Definition DesignedEntry_800cb588
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot017cEntries.fp_machineAt017c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb588) := I.
Global Typeclasses Opaque DesignedEntry_800cb588.

Lemma DesignedBoundary_800cb588 `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb58c (ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0180Entries.fp_machineAt0180 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800cb5a8 (ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot019cEntries.fp_machineAt019c (args) (returnAddress) (K))%I -∗
  keysEnsureCapacityChargedCode -∗
  instr_body 0x800cb588
    (DesignedEntry_800cb588 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb588.
