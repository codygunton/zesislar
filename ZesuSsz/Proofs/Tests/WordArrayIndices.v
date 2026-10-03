Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import ZesuSsz.Automation.PackedWordValues.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Definition test_u64_selector (values : list (bv 64)) index :=
  default (BV 64 0) (values !! index).

Lemma word_prefix_selector_14 (values : list (bv 64)) :
  take 69 values !!! 14%nat = test_u64_selector values 14.
Proof. zesu_finish_u64_prefix_lookup. Qed.

Lemma word_same_prefix_selector_13 (values : list (bv 64)) :
  take 69 values !!! 13%nat = test_u64_selector (take 69 values) 13.
Proof. zesu_finish_u64_prefix_lookup. Qed.

Lemma word_empty_selector (index : nat) :
  (@nil (bv 64)) !!! index = test_u64_selector nil index.
Proof. zesu_finish_u64_prefix_lookup. Qed.

Lemma word_prefix_selector_unrelated (values other : list (bv 64)) :
  True.
Proof.
  Fail assert (Hselector : take 69 values !!! 14%nat =
    test_u64_selector other 14) by zesu_finish_u64_prefix_lookup.
  exact I.
Qed.

Lemma word_prefix_selector_outside (values : list (bv 64)) :
  True.
Proof.
  Fail assert (Hselector : take 0 values !!! 0%nat =
    test_u64_selector values 0) by zesu_finish_u64_prefix_lookup.
  exact I.
Qed.

Lemma word_array_index_1120 (sp : bv 64) :
 array_region_start 64 (bv_unsigned sp + 1032) (bv_unsigned sp + 1120) = 11%nat.
Proof. zesu_word_array_index_normalize. reflexivity. Qed.
Lemma word_array_bound_1120 (sp : bv 64) (values : list (bv 64))
 (Hlength : length values = 74%nat) :
 (array_region_start 64 (bv_unsigned sp + 1032) (bv_unsigned sp + 1120)
 < length (take 69 values))%nat.
Proof. zesu_word_array_index_normalize. rewrite length_take. lia. Qed.

Lemma word_array_index_1136 (sp : bv 64) :
 array_region_start 64 (bv_unsigned sp + 1032) (bv_unsigned sp + 1136) = 13%nat.
Proof. zesu_word_array_index_normalize. reflexivity. Qed.
Lemma word_array_bound_1136 (sp : bv 64) (values : list (bv 64))
 (Hlength : length values = 74%nat) :
 (array_region_start 64 (bv_unsigned sp + 1032) (bv_unsigned sp + 1136)
 < length (take 69 values))%nat.
Proof. zesu_word_array_index_normalize. rewrite length_take. lia. Qed.

Lemma word_array_index_1144 (sp : bv 64) :
 array_region_start 64 (bv_unsigned sp + 1032) (bv_unsigned sp + 1144) = 14%nat.
Proof. zesu_word_array_index_normalize. reflexivity. Qed.
Lemma word_array_bound_1144 (sp : bv 64) (values : list (bv 64))
 (Hlength : length values = 74%nat) :
 (array_region_start 64 (bv_unsigned sp + 1032) (bv_unsigned sp + 1144)
 < length (take 69 values))%nat.
Proof. zesu_word_array_index_normalize. rewrite length_take. lia. Qed.

Lemma word_array_index_symbolic_guard (base offset : Z) :
 array_region_start 64 (base + 1032) (base + offset) = Z.to_nat ((offset - 1032) / 8).
Proof.
 Fail progress zesu_word_array_index_normalize.
 apply zesu_word_array_index_offset.
Qed.
Print Assumptions zesu_word_array_index_offset.
