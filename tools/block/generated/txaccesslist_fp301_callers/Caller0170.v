Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0170Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0170Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0188Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0188Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0248Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0248Structural.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges0170.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_80000170
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot0170Entries.fp_machineAt0170 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80000170) := I.
Global Typeclasses Opaque DesignedEntry_80000170.

Lemma DesignedBoundary_80000170 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80000188 (ZesuSsz.Generated.TxAccessList.FP301.Pilot0188Entries.fp_machineAt0188 (args) (returnAddress) (K))%I -∗
  instr_pre 0x80000248 (ZesuSsz.Generated.TxAccessList.FP301.Pilot0248Entries.fp_machineAt0248 (args) (returnAddress) (K))%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x80000170
    (DesignedEntry_80000170 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80000170.
