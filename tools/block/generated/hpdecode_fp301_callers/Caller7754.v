Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot7754Entries.
Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot7754Structural.
Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot7780Entries.
Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot7780Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.HpDecodeContract.
Require Import ZesuSsz.Contracts.HpDecodeSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_80067754
    `{!islaG Sigma} `{!threadG} (args : HpDecodeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.HpDecode.FP301.Pilot7754Entries.fp_machineAt7754 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80067754) := I.
Global Typeclasses Opaque DesignedEntry_80067754.

Lemma DesignedBoundary_80067754 `{!islaG Sigma} `{!threadG} (args : HpDecodeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80067780 (ZesuSsz.Generated.HpDecode.FP301.Pilot7780Entries.fp_machineAt7780 (args) (returnAddress) (K))%I -∗
  hpDecodeSelectedCode -∗
  instr_body 0x80067754
    (DesignedEntry_80067754 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80067754.
