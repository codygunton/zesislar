Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot02ecEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot02ecStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot043cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot043cStructural.
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
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_800002ec
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot02ecEntries.fp_machineAt02ec (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800002ec) := I.
Global Typeclasses Opaque DesignedEntry_800002ec.

Lemma DesignedBoundary_800002ec `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x8000043c (ZesuSsz.Generated.TxAccessList.FP301.Pilot043cEntries.fp_machineAt043c (args) (returnAddress) (K))%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x800002ec
    (DesignedEntry_800002ec args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800002ec.
