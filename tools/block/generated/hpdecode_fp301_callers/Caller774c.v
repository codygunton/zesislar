Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot774cEntries.
Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot774cStructural.
Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot7754Entries.
Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot7754Structural.
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

Definition DesignedEntry_8006774c
    `{!islaG Sigma} `{!threadG} (args : HpDecodeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.HpDecode.FP301.Pilot774cEntries.fp_machineAt774c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_8006774c) := I.
Global Typeclasses Opaque DesignedEntry_8006774c.

Lemma DesignedBoundary_8006774c `{!islaG Sigma} `{!threadG} (args : HpDecodeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80067754 (ZesuSsz.Generated.HpDecode.FP301.Pilot7754Entries.fp_machineAt7754 (args) (returnAddress) (K))%I -∗
  instr_pre 0x800677ac (ZesuSsz.Generated.HpDecode.FP301.Pilot77acEntries.fp_machineAt77ac (args) (returnAddress) (K))%I -∗
  hpDecodeSelectedCode -∗
  instr_body 0x8006774c
    (DesignedEntry_8006774c args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_8006774c.
