Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot02f4Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot02f4Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0340Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0340Structural.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges02f4.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_800002f4
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot02f4Entries.fp_machineAt02f4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800002f4) := I.
Global Typeclasses Opaque DesignedEntry_800002f4.

Lemma DesignedBoundary_800002f4 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80000340 (ZesuSsz.Generated.TxAccessList.FP301.Pilot0340Entries.fp_machineAt0340 (args) (returnAddress) (K))%I -∗
  instr_pre 0x8004218c (ZesuSsz.Contracts.AltFlAllocPremises.altFlRemapCallSpec)%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x800002f4
    (DesignedEntry_800002f4 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800002f4.
