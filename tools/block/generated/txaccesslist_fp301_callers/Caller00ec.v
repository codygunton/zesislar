Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00ecEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00ecStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot010cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot010cStructural.
Require Import ZesuSsz.Interfaces.DecodeItem.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges00ec.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_800000ec
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot00ecEntries.fp_machineAt00ec (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800000ec) := I.
Global Typeclasses Opaque DesignedEntry_800000ec.

Lemma DesignedBoundary_800000ec `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x8000010c (ZesuSsz.Generated.TxAccessList.FP301.Pilot010cEntries.fp_machineAt010c (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6960 (ZesuSsz.Interfaces.DecodeItem.decodeItemCallSpec2)%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x800000ec
    (DesignedEntry_800000ec args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800000ec.
