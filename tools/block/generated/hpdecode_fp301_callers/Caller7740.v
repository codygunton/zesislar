Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot7740Entries.
Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot7740Structural.
Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot774cEntries.
Require Import ZesuSsz.Generated.HpDecode.FP301.Pilot774cStructural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.HpDecodeContract.
Require Import ZesuSsz.Contracts.HpDecodeSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_80067740
    `{!islaG Sigma} `{!threadG} (args : HpDecodeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.HpDecode.FP301.Pilot7740Entries.fp_machineAt7740 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80067740) := I.
Global Typeclasses Opaque DesignedEntry_80067740.

Lemma DesignedBoundary_80067740 `{!islaG Sigma} `{!threadG} (args : HpDecodeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x8006774c (ZesuSsz.Generated.HpDecode.FP301.Pilot774cEntries.fp_machineAt774c (args) (returnAddress) (K))%I -∗
  hpDecodeSelectedCode -∗
  instr_body 0x80067740
    (DesignedEntry_80067740 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80067740.
