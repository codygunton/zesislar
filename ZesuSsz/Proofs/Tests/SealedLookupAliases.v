Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import ZesuSsz.Automation.Switches.SealedOpen.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import environments.
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
Definition unrelatedRaw (address : Z) (value : bv 64) : iProp Sigma :=
  (address ↦ₘ value ∗ True)%I.
Definition unrelatedSeal (address : Z) (value : bv 64) : iProp Sigma :=
  unrelatedRaw address value.
Global Instance unrelatedDecl address value :
  ZesuSealed (unrelatedSeal address value) (unrelatedRaw address value)
    [(address, address + 8)] [].
Proof. done. Qed.
Global Opaque unrelatedSeal.
Lemma declared_local_address (pointer : bv 64) (base : Z)
    (processed remaining : nat) (bytes : list (bv 8)) (word : bv 64) :
  (base + Z.of_nat (length bytes) < machineRamEnd defaultMap)%Z ->
  (mapRamBase defaultMap <= base)%Z ->
  bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z ->
  length bytes = (32 * (processed + S remaining))%nat ->
  sourceSeal base bytes -∗ unrelatedSeal (-16) word -∗
  find_in_context (FindMemMapsTo (bv_unsigned (pointer + 25)))
    (fun _ => unrelatedSeal (-16) word).
Proof.
  intros Hram Hbase Hpointer Hlength.
  iIntros "Hmemory Hother".
  pose (localAddress := (pointer + 25)%bv).
  fold localAddress.
  let_bind_envs.
  zesu_open_sealed_for_lookup.
  iRename select (unrelatedSeal (-16) word) into "Hpreserved".
  iRename select (base ↦ₘ∗ bytes)%I into "Harray".
  iApply find_in_context_mem_mapsto_semantic.
  iExists (MKArray 8 base bytes).
  iFrame "Hpreserved".
  cbn [mem_mapsto_kind_prop].
  iExact "Harray".
Qed.
Lemma declared_nested_address (pointer : bv 64) (base : Z)
    (processed remaining : nat) (bytes : list (bv 8)) (word : bv 64) :
  (base + Z.of_nat (length bytes) < machineRamEnd defaultMap)%Z ->
  (mapRamBase defaultMap <= base)%Z ->
  bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z ->
  length bytes = (32 * (processed + S remaining))%nat ->
  sourceSeal base bytes -∗ unrelatedSeal (-16) word -∗
  find_in_context (FindMemMapsTo (bv_unsigned (pointer + 25)))
    (fun _ => unrelatedSeal (-16) word).
Proof.
  intros Hram Hbase Hpointer Hlength.
  iIntros "Hmemory Hother".
  pose (innerAddress := (pointer + 25)%bv).
  pose (localAddress := innerAddress).
  fold innerAddress.
  fold localAddress.
  let_bind_envs.
  zesu_open_sealed_for_lookup.
  iRename select (unrelatedSeal (-16) word) into "Hpreserved".
  iRename select (base ↦ₘ∗ bytes)%I into "Harray".
  iApply find_in_context_mem_mapsto_semantic.
  iExists (MKArray 8 base bytes).
  iFrame "Hpreserved".
  cbn [mem_mapsto_kind_prop].
  iExact "Harray".
Qed.
End Tests.
Print Assumptions declared_local_address.
Print Assumptions declared_nested_address.
