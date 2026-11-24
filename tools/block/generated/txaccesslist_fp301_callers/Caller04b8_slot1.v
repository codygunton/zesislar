Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04b8Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04b8Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.FunctionReturnEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.FunctionReturnStructural.
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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Edges04b8.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent txAccessListSelectedCode.

Definition DesignedEntry_800004b8_slot1
    `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.TxAccessList.FP301.Pilot04b8Entries.fp_machineAt04b8_slot1 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800004b8_slot1) := I.
Global Typeclasses Opaque DesignedEntry_800004b8_slot1.

Lemma DesignedBoundary_800004b8_slot1 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre returnAddress (ZesuSsz.Generated.TxAccessList.FP301.FunctionReturnEntries.fp_machineReturn_slot1 args returnAddress K) -∗
  txAccessListSelectedCode -∗
  instr_body 0x800004b8
    (DesignedEntry_800004b8_slot1 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800004b8_slot1.
