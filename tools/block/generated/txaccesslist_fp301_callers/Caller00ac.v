Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00acEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00acStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00c4Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00c4Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Import ZesuSsz.Contracts.TxAccessListSelected.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges00ac.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_800000ac
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot00acEntries.fp_machineAt00ac (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800000ac) := I.
Global Typeclasses Opaque DesignedEntry_800000ac.

Lemma DesignedBoundary_800000ac `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800000c4 (ZesuSsz.Generated.TxAccessList.FP301.Pilot00c4Entries.fp_machineAt00c4 (args) (returnAddress) (K))%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x800000ac
    (DesignedEntry_800000ac args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800000ac.
