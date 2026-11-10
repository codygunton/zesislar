Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a78Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a78Structural.
Require Import ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnStructural.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition Fp301Entry_800d6a78
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6a78Entries.fp_machineAt6a78 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6a78) := I.
Global Typeclasses Opaque Fp301Entry_800d6a78.

Lemma Fp301Boundary_800d6a78 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma)  :
  instr_pre returnAddress (ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries.fp_machineReturn args returnAddress K) -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a78
    (Fp301Entry_800d6a78 args returnAddress K).
Proof.
  zesu_block2.
Qed.
