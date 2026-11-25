Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot01b4Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot01b4Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot01bcEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot01bcStructural.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges01b4.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.txAccessList.Block01b4.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_800001b4
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot01b4Entries.fp_machineAt01b4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800001b4) := I.
Global Typeclasses Opaque DesignedEntry_800001b4.

Lemma DesignedBoundary_800001b4 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800001bc (ZesuSsz.Generated.TxAccessList.FP301.Pilot01bcEntries.fp_machineAt01bc (args) (returnAddress) (K))%I -∗
  instr_pre 0x800004a8 (ZesuSsz.Generated.TxAccessList.FP301.Pilot04a8Entries.fp_machineAt04a8 (args) (returnAddress) (K))%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x800001b4
    (DesignedEntry_800001b4 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800001b4.
