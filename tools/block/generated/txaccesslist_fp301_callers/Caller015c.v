Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot015cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot015cStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0164Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0164Structural.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges015c.
Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Residuals.txAccessList.Block015c.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_8000015c
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot015cEntries.fp_machineAt015c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_8000015c) := I.
Global Typeclasses Opaque DesignedEntry_8000015c.

Lemma DesignedBoundary_8000015c `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80000164 (ZesuSsz.Generated.TxAccessList.FP301.Pilot0164Entries.fp_machineAt0164 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800004a8 (ZesuSsz.Generated.TxAccessList.FP301.Pilot04a8Entries.fp_machineAt04a8 (args) (returnAddress) (K))%I -∗
  txAccessListSelectedCode -∗
  instr_body 0x8000015c
    (DesignedEntry_8000015c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_8000015c.
