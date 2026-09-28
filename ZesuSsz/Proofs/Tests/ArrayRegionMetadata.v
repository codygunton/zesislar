Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope Z_scope.
Lemma test_region_metadata_inactive (base : Z) : array_region_start 64 base base = 0%nat.
Proof.
  Fail zesu_array_region_metadata_if_enabled.
  apply array_region_start_64_same.
Qed.
Local Instance test_region_metadata_switch : ZesuStepArrayLoadPriority := I.
Lemma test_region_metadata_pure (base : Z) :
  base = base + 8 * Z.of_nat (array_region_start 64 base base) /\
  (array_region_start 64 base base < 8)%nat.
Proof.
  split; time "metadata pure" zesu_array_region_metadata_if_enabled; cbn; lia.
Qed.
Lemma test_region_metadata_suffix `{!islaG Sigma} (base address : Z)
    (words : list (bv 64)) (K : mem_mapsto_kind -> iProp Sigma) :
  (base + 8 * Z.of_nat (array_region_start 64 base base + 1))
    ↦ₘ∗ drop (array_region_start 64 base base + 1) words -∗
  (((base + 8) ↦ₘ∗ drop 1 words) -∗
    find_in_context (FindMemMapsTo address) K) -∗
  find_in_context (FindMemMapsTo address) K.
Proof.
  iIntros "Harray Hnext".
  time "metadata suffix" zesu_array_region_metadata_if_enabled.
  cbn.
  iApply ("Hnext" with "Harray").
Qed.
Print Assumptions test_region_metadata_inactive.
Print Assumptions test_region_metadata_pure.
Print Assumptions test_region_metadata_suffix.
