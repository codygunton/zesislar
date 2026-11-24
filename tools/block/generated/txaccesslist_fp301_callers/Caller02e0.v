Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot02e0Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot02e0Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0390Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0390Structural.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges02e0.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_800002e0
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot02e0Entries.fp_machineAt02e0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800002e0) := I.
Global Typeclasses Opaque DesignedEntry_800002e0.

Lemma DesignedBoundary_800002e0 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80000390 (ZesuSsz.Generated.TxAccessList.FP301.Pilot0390Entries.fp_machineAt0390 (args) (returnAddress) (K))%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x800002e0
    (DesignedEntry_800002e0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800002e0.
