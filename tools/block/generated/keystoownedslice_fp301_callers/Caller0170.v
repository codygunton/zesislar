Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0170Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0170Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0184Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0184Structural.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Edges0170.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.keysToOwnedSlice.Block0170.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceSelectedCode.

Definition DesignedEntry_800d68ec
    `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0170Entries.fp_machineAt0170 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d68ec) := I.
Global Typeclasses Opaque DesignedEntry_800d68ec.

Lemma DesignedBoundary_800d68ec `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800d6900 (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0184Entries.fp_machineAt0184 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800e06c0 (ZesuSsz.Contracts.ZiskMemcpyPremise.ziskMemcpyCallSpec)%I -∗
  keysToOwnedSliceSelectedCode -∗
  instr_body 0x800d68ec
    (DesignedEntry_800d68ec args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800d68ec.
