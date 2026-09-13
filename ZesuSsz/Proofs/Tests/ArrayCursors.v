Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayCursors.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma test_array_cursor_zero (row : bv 64) (base : Z) (index : nat) :
  bv_unsigned row = (base + Z.of_nat index)%Z ->
  Z.to_nat (bv_unsigned row - base) = index.
Proof. intros Hcursor. zesu_normalize_array_cursors. reflexivity. Qed.

Lemma test_array_cursor_offset (row : bv 64) (base : Z)
    (bytes : list (bv 8)) (index : nat) :
  bv_unsigned row = (base + Z.of_nat index)%Z ->
  (0x20000000 <= base)%Z ->
  (base + Z.of_nat (length bytes) < 0x40000000)%Z ->
  (index + 32 <= length bytes)%nat ->
  Z.to_nat (bv_unsigned (row + BV 64 24)%bv - base) = (index + 24)%nat.
Proof. intros. zesu_normalize_array_cursors. reflexivity. Qed.

Lemma test_array_cursor_word (row : bv 64) (base : Z)
    (bytes : list (bv 8)) (index : nat) :
  bv_unsigned row = (base + Z.of_nat index)%Z ->
  (0x20000000 <= base)%Z ->
  (base + Z.of_nat (length bytes) < 0x40000000)%Z ->
  (index + 32 <= length bytes)%nat ->
  Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat (bv_unsigned (row + BV 64 16)%bv - base)) bytes))) =
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (index + 16)%nat bytes))).
Proof. intros. zesu_normalize_array_cursors. reflexivity. Qed.

Print Assumptions array_cursor_base_index.
Print Assumptions array_cursor_index.
Print Assumptions test_array_cursor_zero.
Print Assumptions test_array_cursor_offset.
Print Assumptions test_array_cursor_word.
