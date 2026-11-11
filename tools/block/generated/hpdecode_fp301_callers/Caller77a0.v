Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot77a0Entries.
Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot77a0Structural.
Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot77acEntries.
Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot77acStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.HpDecodeContract.
Require Import ZesuSsz.Contracts.HpDecodeSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_800677a0
    `{!islaG Sigma} `{!threadG} (args : HpDecodeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.HpDecode.FP301.Pilot77a0Entries.fp_machineAt77a0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800677a0) := I.
Global Typeclasses Opaque DesignedEntry_800677a0.

Lemma DesignedBoundary_800677a0 `{!islaG Sigma} `{!threadG} (args : HpDecodeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x800677ac (ZesuSsz.Generated.HpDecode.FP301.Pilot77acEntries.fp_machineAt77ac (args) (returnAddress) (K))%I -∗
  hpDecodeSelectedCode -∗
  instr_body 0x800677a0
    (DesignedEntry_800677a0 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_800677a0.
