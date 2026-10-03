Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import ZesuSsz.Automation.Switches.SealedOpen.
From iris.proofmode Require Import tactics.
Import ListNotations.
Open Scope Z_scope.
Section Tests.
Context `{!islaG Sigma} `{!threadG}.
Definition sourceRaw (address : Z) (bytes : list (bv 8)) : iProp Sigma :=
  (address ↦ₘ∗ bytes ∗ True)%I.
Definition sourceSeal (address : Z) (bytes : list (bv 8)) : iProp Sigma :=
  sourceRaw address bytes.
Definition targetRaw (address : Z) (bytes : list (bv 8)) : iProp Sigma :=
  (address ↦ₘ∗ bytes ∗ True)%I.
Definition targetSeal (address : Z) (bytes : list (bv 8)) : iProp Sigma :=
  targetRaw address bytes.
Global Instance sourceDecl address bytes :
  ZesuSealed (sourceSeal address bytes) (sourceRaw address bytes)
    [(address, address + Z.of_nat (length bytes))] [].
Proof. done. Qed.
Global Instance targetDecl address bytes :
  ZesuSealed (targetSeal address bytes) (targetRaw address bytes)
    [(address, address + Z.of_nat (length bytes))] [].
Proof. done. Qed.
Global Opaque sourceSeal targetSeal.
Lemma equivalent_declared address bytes :
  sourceSeal address bytes -∗ targetSeal address bytes ∗ True.
Proof. zesu_block. Qed.
Lemma raw_into_declared address bytes :
  address ↦ₘ∗ bytes -∗ targetSeal address bytes ∗ True.
Proof. zesu_block. Qed.
Definition unrelatedRaw (address : Z) (value : bv 64) : iProp Sigma :=
  (address ↦ₘ value ∗ True)%I.
Definition unrelatedSeal (address : Z) (value : bv 64) : iProp Sigma :=
  unrelatedRaw address value.
Global Instance unrelatedDecl address value :
  ZesuSealed (unrelatedSeal address value) (unrelatedRaw address value)
    [(address, address + 8)] [].
Proof. done. Qed.
Global Opaque unrelatedSeal.
Lemma unrelated_stays_sealed address bytes other value :
  sourceSeal address bytes -∗ unrelatedSeal other value -∗
  targetSeal address bytes ∗ unrelatedSeal other value.
Proof.
  iIntros "Hsource Hother".
  zesu_open_declared_memory_goal.
  iRename select (unrelatedSeal other value) into "Hprotected".
  zesu_run.
Qed.
End Tests.
