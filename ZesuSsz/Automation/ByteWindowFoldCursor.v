From Coq Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation.ByteWindowFold.
Require Import ZesuSsz.Automation.ByteWindowFoldIndex.
Open Scope Z_scope.

Lemma zesu_byte_window_cursor_index (base cursor : bv 64) (start : nat) (index : Z) :
  0 <= index ->
  bv_unsigned cursor = bv_unsigned base + Z.of_nat start + index ->
  Z.to_nat (bv_unsigned cursor - bv_unsigned base) = (start + Z.to_nat index)%nat.
Proof.
  intros Hindex Hcursor. rewrite Hcursor.
  replace (bv_unsigned base + Z.of_nat start + index - bv_unsigned base)
    with (Z.of_nat start + index) by lia.
  rewrite Z2Nat.inj_add by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma zesu_byte_window_cursor_step (bytes : list (bv 8)) (base cursor : bv 64)
    (start : nat) (index limit : Z) (acc : bv 64) (next : bv 8) :
  0 <= index -> index < limit -> limit <= 8 ->
  bv_unsigned cursor = bv_unsigned base + Z.of_nat start + index ->
  bv_unsigned acc = zesu_byte_window_fold bytes start (Z.to_nat index) ->
  nth_error bytes (Z.to_nat (bv_unsigned cursor - bv_unsigned base)) = Some next ->
  bv_unsigned (bv_or (bv_shiftl acc (BV 64 8)) (bv_zero_extend 64 next)) =
    zesu_byte_window_fold bytes start (Z.to_nat (index + 1)).
Proof.
  intros Hindex Hlimit Hwidth Hcursor Hacc Hnext.
  rewrite (zesu_byte_window_cursor_index base cursor start index Hindex Hcursor) in Hnext.
  eapply zesu_byte_window_index_step; eassumption.
Qed.
