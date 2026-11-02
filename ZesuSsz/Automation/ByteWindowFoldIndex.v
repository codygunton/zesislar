From Coq Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions bitvector.tactics.
Require Import ZesuSsz.Automation.ByteWindowFold.
Require Import ZesuSsz.Automation.ByteWindowFoldWord.
Open Scope Z_scope.

Lemma zesu_byte_window_index_zero (bytes : list (bv 8)) (start : nat) :
  bv_unsigned (BV 64 0) = zesu_byte_window_fold bytes start (Z.to_nat 0).
Proof.
  rewrite zesu_byte_window_zero. reflexivity.
Qed.

Lemma zesu_byte_window_index_step (bytes : list (bv 8)) (start : nat)
    (index limit : Z) (acc : bv 64) (next : bv 8) :
  0 <= index -> index < limit -> limit <= 8 ->
  bv_unsigned acc = zesu_byte_window_fold bytes start (Z.to_nat index) ->
  nth_error bytes (start + Z.to_nat index)%nat = Some next ->
  bv_unsigned (bv_or (bv_shiftl acc (BV 64 8)) (bv_zero_extend 64 next)) =
    zesu_byte_window_fold bytes start (Z.to_nat (index + 1)).
Proof.
  intros Hindex Hlimit Hwidth Hacc Hnext.
  assert (HaccWord : acc = Z_to_bv 64 (zesu_byte_window_fold bytes start (Z.to_nat index))).
  { apply bv_eq. rewrite Z_to_bv_unsigned. rewrite <- Hacc.
    symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. }
  assert (Hcount : (S (Z.to_nat index) <= 8)%nat).
  { apply Nat2Z.inj_le. rewrite Nat2Z.inj_succ. rewrite Z2Nat.id by exact Hindex. simpl. lia. }
  rewrite Z2Nat.inj_add by lia. simpl. rewrite Nat.add_1_r.
  rewrite HaccWord. apply zesu_byte_window_unsigned_step; assumption.
Qed.
