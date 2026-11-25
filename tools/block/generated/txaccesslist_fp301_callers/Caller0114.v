Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0114Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0114Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0120Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0120Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04a8Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04a8Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Import ZesuSsz.Contracts.TxAccessListLoopFacts.
Require Import ZesuSsz.Compliance.TxAccessListCallSlice.
Require Import ZesuSsz.Compliance.TxAccessListLoopIntro.
Require Import ZesuSsz.Contracts.TxAccessListSelected.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges0114.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_80000114
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot0114Entries.fp_machineAt0114 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80000114) := I.
Global Typeclasses Opaque DesignedEntry_80000114.

Lemma DesignedBoundary_80000114 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80000120 (ZesuSsz.Generated.TxAccessList.FP301.Pilot0120Entries.fp_machineAt0120 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800004a8 (ZesuSsz.Generated.TxAccessList.FP301.Pilot04a8Entries.fp_machineAt04a8 (args) (returnAddress) (K))%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x80000114
    (DesignedEntry_80000114 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80000114.
