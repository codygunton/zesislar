(* Generated caller entry aliases and their unfold instances. No proof script. *)
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6960Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6974Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot697cEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot698cEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69a4Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69b0Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69d8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69e0Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69e8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a00Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a08Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a14Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a24Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a38Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a40Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a64Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a6cEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a78Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6aa8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ab4Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ac4Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ad8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ae0Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6b08Entries.
Local Open Scope Z_scope.

Definition Fp301Entry_800d6960
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6960Entries.fp_machineAt6960 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6960) := I.
Global Typeclasses Opaque Fp301Entry_800d6960.

Definition Fp301Entry_800d6974
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6974Entries.fp_machineAt6974 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6974) := I.
Global Typeclasses Opaque Fp301Entry_800d6974.

Definition Fp301Entry_800d697c
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot697cEntries.fp_machineAt697c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d697c) := I.
Global Typeclasses Opaque Fp301Entry_800d697c.

Definition Fp301Entry_800d698c
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot698cEntries.fp_machineAt698c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d698c) := I.
Global Typeclasses Opaque Fp301Entry_800d698c.

Definition Fp301Entry_800d69a4
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot69a4Entries.fp_machineAt69a4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d69a4) := I.
Global Typeclasses Opaque Fp301Entry_800d69a4.

Definition Fp301Entry_800d69b0
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot69b0Entries.fp_machineAt69b0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d69b0) := I.
Global Typeclasses Opaque Fp301Entry_800d69b0.

Definition Fp301Entry_800d69d8
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot69d8Entries.fp_machineAt69d8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d69d8) := I.
Global Typeclasses Opaque Fp301Entry_800d69d8.

Definition Fp301Entry_800d69e0
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot69e0Entries.fp_machineAt69e0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d69e0) := I.
Global Typeclasses Opaque Fp301Entry_800d69e0.

Definition Fp301Entry_800d69e8
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot69e8Entries.fp_machineAt69e8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d69e8) := I.
Global Typeclasses Opaque Fp301Entry_800d69e8.

Definition Fp301Entry_800d6a00
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6a00Entries.fp_machineAt6a00 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6a00) := I.
Global Typeclasses Opaque Fp301Entry_800d6a00.

Definition Fp301Entry_800d6a08
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6a08Entries.fp_machineAt6a08 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6a08) := I.
Global Typeclasses Opaque Fp301Entry_800d6a08.

Definition Fp301Entry_800d6a14
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6a14Entries.fp_machineAt6a14 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6a14) := I.
Global Typeclasses Opaque Fp301Entry_800d6a14.

Definition Fp301Entry_800d6a24
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6a24Entries.fp_machineAt6a24 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6a24) := I.
Global Typeclasses Opaque Fp301Entry_800d6a24.

Definition Fp301Entry_800d6a38
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6a38Entries.fp_machineAt6a38 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6a38) := I.
Global Typeclasses Opaque Fp301Entry_800d6a38.

Definition Fp301Entry_800d6a40
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6a40Entries.fp_machineAt6a40 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6a40) := I.
Global Typeclasses Opaque Fp301Entry_800d6a40.

Definition Fp301Entry_800d6a64
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6a64Entries.fp_machineAt6a64 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6a64) := I.
Global Typeclasses Opaque Fp301Entry_800d6a64.

Definition Fp301Entry_800d6a6c
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6a6cEntries.fp_machineAt6a6c (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6a6c) := I.
Global Typeclasses Opaque Fp301Entry_800d6a6c.

Definition Fp301Entry_800d6a78
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6a78Entries.fp_machineAt6a78 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6a78) := I.
Global Typeclasses Opaque Fp301Entry_800d6a78.

Definition Fp301Entry_800d6aa8
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6aa8Entries.fp_machineAt6aa8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6aa8) := I.
Global Typeclasses Opaque Fp301Entry_800d6aa8.

Definition Fp301Entry_800d6ab4
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6ab4Entries.fp_machineAt6ab4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6ab4) := I.
Global Typeclasses Opaque Fp301Entry_800d6ab4.

Definition Fp301Entry_800d6ac4
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6ac4Entries.fp_machineAt6ac4 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6ac4) := I.
Global Typeclasses Opaque Fp301Entry_800d6ac4.

Definition Fp301Entry_800d6ad8
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6ad8Entries.fp_machineAt6ad8 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6ad8) := I.
Global Typeclasses Opaque Fp301Entry_800d6ad8.

Definition Fp301Entry_800d6ae0
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6ae0Entries.fp_machineAt6ae0 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6ae0) := I.
Global Typeclasses Opaque Fp301Entry_800d6ae0.

Definition Fp301Entry_800d6b08
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma :=
  ((ZesuSsz.Generated.DecodeItem.FP301.Pilot6b08Entries.fp_machineAt6b08 (args) (returnAddress) (K)) ∗
   True)%I.
Global Instance : LithiumUnfold (@Fp301Entry_800d6b08) := I.
Global Typeclasses Opaque Fp301Entry_800d6b08.
