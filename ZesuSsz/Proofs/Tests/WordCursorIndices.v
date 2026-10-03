Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import isla.riscv64.riscv64.

Lemma word_cursor_1120 (sp : bv 64) :
  0 <= bv_unsigned sp -> bv_unsigned sp + 1896 < 1073741824 ->
  Z.to_nat ((bv_unsigned (sp + BV 64 1120) - (bv_unsigned sp + 1032)) / 8) = 11%nat.
Proof. intros Hlow Hhigh. zesu_word_cursor_index_normalize. reflexivity. Qed.

Lemma word_cursor_1136 (sp : bv 64) :
  0 <= bv_unsigned sp -> bv_unsigned sp + 1896 < 1073741824 ->
  Z.to_nat ((bv_unsigned (sp + BV 64 1136) - (bv_unsigned sp + 1032)) / 8) = 13%nat.
Proof. intros Hlow Hhigh. zesu_word_cursor_index_normalize. reflexivity. Qed.

Lemma word_cursor_1144 (sp : bv 64) :
  0 <= bv_unsigned sp -> bv_unsigned sp + 1896 < 1073741824 ->
  Z.to_nat ((bv_unsigned (sp + BV 64 1144) - (bv_unsigned sp + 1032)) / 8) = 14%nat.
Proof. intros Hlow Hhigh. zesu_word_cursor_index_normalize. reflexivity. Qed.

Lemma word_cursor_nested (sp : bv 64) (values : list (bv 64)) :
  0 <= bv_unsigned sp -> bv_unsigned sp + 1896 < 1073741824 ->
  default (BV 64 0) (take 69 values !! Z.to_nat
    ((bv_unsigned (sp + BV 64 1136) - (bv_unsigned sp + 1032)) / 8)) =
  default (BV 64 0) (take 69 values !! 13%nat).
Proof. intros Hlow Hhigh. zesu_word_cursor_index_normalize. reflexivity. Qed.

Lemma word_cursor_symbolic_offset (sp offset : bv 64) :
  Z.to_nat ((bv_unsigned (sp + offset) - (bv_unsigned sp + 1032)) / 8) =
  Z.to_nat ((bv_unsigned (sp + offset) - (bv_unsigned sp + 1032)) / 8).
Proof. Fail progress zesu_word_cursor_index_normalize. reflexivity. Qed.

Lemma word_cursor_symbolic_start (sp : bv 64) (start : Z) :
  Z.to_nat ((bv_unsigned (sp + BV 64 1136) - (bv_unsigned sp + start)) / 8) =
  Z.to_nat ((bv_unsigned (sp + BV 64 1136) - (bv_unsigned sp + start)) / 8).
Proof. Fail progress zesu_word_cursor_index_normalize. reflexivity. Qed.

Lemma word_cursor_without_bounds (sp : bv 64) :
  Z.to_nat ((bv_unsigned (sp + BV 64 1136) - (bv_unsigned sp + 1032)) / 8) =
  Z.to_nat ((bv_unsigned (sp + BV 64 1136) - (bv_unsigned sp + 1032)) / 8).
Proof. Fail progress zesu_word_cursor_index_normalize. reflexivity. Qed.

Lemma word_cursor_wrong_width (sp : bv 32) :
  Z.to_nat ((bv_unsigned (sp + BV 32 1136) - (bv_unsigned sp + 1032)) / 8) =
  Z.to_nat ((bv_unsigned (sp + BV 32 1136) - (bv_unsigned sp + 1032)) / 8).
Proof. Fail progress zesu_word_cursor_index_normalize. reflexivity. Qed.

Lemma word_cursor_wrap :
  Z.to_nat ((bv_unsigned (BV 64 (2^64 - 8) + BV 64 16) -
    (bv_unsigned (BV 64 (2^64 - 8)) + 0)) / 8) = 0%nat.
Proof. Fail progress zesu_word_cursor_index_normalize. vm_compute. reflexivity. Qed.

Lemma word_cursor_negative_offset :
  Z.to_nat ((bv_unsigned (BV 64 0 + Z_to_bv 64 (-8)) -
    (bv_unsigned (BV 64 0) + 0)) / 8) =
  Z.to_nat ((bv_unsigned (BV 64 0 + Z_to_bv 64 (-8)) -
    (bv_unsigned (BV 64 0) + 0)) / 8).
Proof. Fail progress zesu_word_cursor_index_normalize. reflexivity. Qed.

Print Assumptions word_cursor_nested.
Print Assumptions word_cursor_wrap.
