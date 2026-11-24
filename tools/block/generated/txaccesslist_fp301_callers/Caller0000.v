Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0000Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0000Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0068Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0068Structural.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges0000.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_80000000
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot0000Entries.fp_machineAt0000 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80000000) := I.
Global Typeclasses Opaque DesignedEntry_80000000.

Lemma DesignedBoundary_80000000 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80000068 (ZesuSsz.Generated.TxAccessList.FP301.Pilot0068Entries.fp_machineAt0068 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800d6960 (ZesuSsz.Interfaces.DecodeItem.decodeItemCallSpec2)%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x80000000
    (DesignedEntry_80000000 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80000000.
