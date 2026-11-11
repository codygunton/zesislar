Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot7724Entries.
Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot7724Structural.
Require Import ZesuSsz.Generated.HpDecode.FP301.FunctionReturn7734Entries.
Require Import ZesuSsz.Generated.HpDecode.FP301.FunctionReturn7734Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.HpDecodeContract.
Require Import ZesuSsz.Contracts.HpDecodeSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_80067724
    `{!islaG Sigma} `{!threadG} (args : HpDecodeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.HpDecode.FP301.Pilot7724Entries.fp_machineAt7724 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80067724) := I.
Global Typeclasses Opaque DesignedEntry_80067724.

Lemma DesignedBoundary_80067724 `{!islaG Sigma} `{!threadG} (args : HpDecodeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre returnAddress (ZesuSsz.Generated.HpDecode.FP301.FunctionReturn7734Entries.fp_machineReturn7734 args returnAddress K) -∗
  hpDecodeSelectedCode -∗
  instr_body 0x80067724
    (DesignedEntry_80067724 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80067724.
