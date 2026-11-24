Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0340Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0340Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0344Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0344Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0364Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0364Structural.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges0340.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_80000340
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot0340Entries.fp_machineAt0340 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80000340) := I.
Global Typeclasses Opaque DesignedEntry_80000340.

Lemma DesignedBoundary_80000340 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80000344 (ZesuSsz.Generated.TxAccessList.FP301.Pilot0344Entries.fp_machineAt0344 (args) (returnAddress) (K))%I -∗
  instr_pre 0x80000364 (ZesuSsz.Generated.TxAccessList.FP301.Pilot0364Entries.fp_machineAt0364 (args) (returnAddress) (K))%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x80000340
    (DesignedEntry_80000340 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80000340.
