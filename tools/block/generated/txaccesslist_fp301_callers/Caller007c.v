Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot007cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot007cStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00acEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00acStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot048cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot048cStructural.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges007c.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_8000007c
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot007cEntries.fp_machineAt007c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_8000007c) := I.
Global Typeclasses Opaque DesignedEntry_8000007c.

Lemma DesignedBoundary_8000007c `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800000ac (ZesuSsz.Generated.TxAccessList.FP301.Pilot00acEntries.fp_machineAt00ac (args) (returnAddress) (K))%I -∗
  instr_pre 0x8000048c (ZesuSsz.Generated.TxAccessList.FP301.Pilot048cEntries.fp_machineAt048c (args) (returnAddress) (K))%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x8000007c
    (DesignedEntry_8000007c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_8000007c.
