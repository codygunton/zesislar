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
Definition targetWordRaw (address : Z) (value : bv 64) : iProp Sigma :=
  (address ↦ₘ value ∗ True)%I.
Definition targetWordSeal (address : Z) (value : bv 64) : iProp Sigma :=
  targetWordRaw address value.
Global Instance targetWordDecl address value :
  ZesuSealed (targetWordSeal address value) (targetWordRaw address value)
    [(address, address + 8)] [].
Proof. done. Qed.
Global Opaque targetWordSeal.
Lemma declared_witness address value :
  unrelatedSeal address value -∗
  ∃ x : li_prod (bv 64) unit,
    targetWordSeal address x.1ₗ ∗ ⌜x.1ₗ = value⌝ ∗ True.
Proof. zesu_block. Qed.
Lemma declared_symbolic_pointer25 (pointer : bv 64) (base : Z)
    (processed remaining : nat) (bytes : list (bv 8)) (word : bv 64) :
  (base + Z.of_nat (length bytes) < machineRamEnd defaultMap)%Z ->
  (mapRamBase defaultMap <= base)%Z ->
  bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z ->
  length bytes = (32 * (processed + S remaining))%nat ->
  sourceSeal base bytes ∗ unrelatedSeal (-16) word -∗
  sourceSeal base bytes ∗ unrelatedSeal (-16) word.
Proof.
  intros Hram Hbase Hpointer Hlength.
  iIntros "[Hmemory Hother]".
  zesu_open_declared_cover (bv_unsigned (pointer + 25)).
  iRename select (unrelatedSeal (-16) word) into "Hpreserved".
  iEval (rewrite (zesu_sealed_unfold (ZesuSealed := sourceDecl base bytes))).
  iFrame.
Qed.
Lemma declared_closed_ranges : True.
Proof.
  zesu_declared_ranges_hold [(16,24);(32,48)] 40.
  assert_fails (zesu_declared_ranges_hold [(16,24)] 40).
  exact I.
Qed.
Lemma declared_into_raw_goal address bytes :
  sourceSeal address bytes -∗ address ↦ₘ∗ bytes ∗ True.
Proof.
  iIntros "Hsource".
  zesu_open_declared_memory_for_raw_goal.
  zesu_block.
Qed.
Lemma raw_goal_preserves_unrelated address bytes other value :
  sourceSeal address bytes -∗ unrelatedSeal other value -∗
  address ↦ₘ∗ bytes ∗ unrelatedSeal other value.
Proof.
  iIntros "Hsource Hother".
  zesu_open_declared_memory_for_raw_goal.
  iRename select (unrelatedSeal other value) into "Hprotected".
  zesu_block.
Qed.
End Tests.
