Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0164Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0164Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot017cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot017cStructural.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Edges0164.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.keysEnsureCapacity.Block0164.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacitySelectedCode.

Definition DesignedEntry_800cb570
    `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0164Entries.fp_machineAt0164 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800cb570) := I.
Global Typeclasses Opaque DesignedEntry_800cb570.

Lemma DesignedBoundary_800cb570 `{!islaG Sigma} `{!threadG} (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800cb588 (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot017cEntries.fp_machineAt017c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800e06c0 (ZesuSsz.Contracts.ZiskMemcpyPremise.ziskMemcpyCallSpec)%I -∗
  keysEnsureCapacitySelectedCode -∗
  instr_body 0x800cb570
    (DesignedEntry_800cb570 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800cb570.
