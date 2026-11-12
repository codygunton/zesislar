Require Import ZesuSsz.Generated.Free.FP301.Pilot1fd8Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot1fd8Structural.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2134Entries.
Require Import ZesuSsz.Generated.Free.FP301.Pilot2134Structural.
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.FreeSelected.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition DesignedEntry_80041fd8
    `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.Free.FP301.Pilot1fd8Entries.fp_machineAt1fd8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_80041fd8) := I.
Global Typeclasses Opaque DesignedEntry_80041fd8.

Lemma DesignedBoundary_80041fd8 `{!islaG Sigma} `{!threadG} (args : FreeArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre 0x80042134 (ZesuSsz.Generated.Free.FP301.Pilot2134Entries.fp_machineAt2134 (args) (returnAddress) (K))%I -∗
  freeSelectedCode -∗
  instr_body 0x80041fd8
    (DesignedEntry_80041fd8 args returnAddress K).
Proof.
  zesu_block2.
Qed.

Print Assumptions DesignedBoundary_80041fd8.
