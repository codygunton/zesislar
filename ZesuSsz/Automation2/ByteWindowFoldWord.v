From Coq Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions bitvector.tactics.
From stdpp.unstable Require Import bitblast.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Import ListNotations.
Local Open Scope Z_scope.

Lemma zesu_byte_shift_or64 (acc : Z) (next : bv 8) :
  bv_or (bv_shiftl (Z_to_bv 64 acc) (BV 64 8)) (bv_zero_extend 64 next) =
    Z_to_bv 64 (256 * acc + bv_unsigned next).
Proof.
  assert (Hland : Z.land
    (bv_unsigned (bv_shiftl (Z_to_bv 64 acc) (BV 64 8)))
    (bv_unsigned (bv_zero_extend 64 next)) = 0).
  { bv_simplify. bitblast as index. all: (f_equal; lia). }
  pose proof (bv_unsigned_in_range 64
    (bv_or (bv_shiftl (Z_to_bv 64 acc) (BV 64 8)) (bv_zero_extend 64 next))) as Hsum.
  rewrite bv_or_unsigned in Hsum.
  rewrite <- Z.add_nocarry_lor in Hsum by exact Hland.
  apply bv_eq. rewrite bv_or_unsigned.
  rewrite <- Z.add_nocarry_lor by exact Hland.
  rewrite <- (bv_wrap_small 64 _ Hsum).
  rewrite bv_shiftl_unsigned, bv_zero_extend_unsigned by lia.
  rewrite Z_to_bv_unsigned, bv_unsigned_BV.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (bv_wrap 64 (bv_wrap 64 (bv_wrap 64 acc * 256) + bv_unsigned next) =
    bv_wrap 64 (256 * acc + bv_unsigned next)).
  rewrite bv_wrap_add_idemp_l.
  rewrite <- (bv_wrap_add_idemp_l 64 (bv_wrap 64 acc * 256) (bv_unsigned next)).
  rewrite bv_wrap_mul_idemp_l, bv_wrap_add_idemp_l.
  replace (acc * 256) with (256 * acc) by lia. reflexivity.
Qed.

Lemma zesu_byte_window_word_snoc (bytes : list (bv 8)) (start count : nat) (next : bv 8) :
  nth_error bytes (start + count)%nat = Some next ->
  bv_or (bv_shiftl (Z_to_bv 64 (zesu_byte_window_fold bytes start count)) (BV 64 8))
    (bv_zero_extend 64 next) =
  Z_to_bv 64 (zesu_byte_window_fold bytes start (S count)).
Proof.
  intros Hnext. rewrite (zesu_byte_window_snoc bytes start count next Hnext).
  apply zesu_byte_shift_or64.
Qed.

Lemma zesu_big_endian8_range (bytes : list (bv 8)) :
  0 <= zesu_big_endian8 bytes < 256 ^ Z.of_nat (length bytes).
Proof.
  induction bytes using rev_ind;
    [unfold zesu_big_endian8; simpl; lia |].
  rewrite zesu_big_endian8_snoc, app_length. simpl.
  rewrite Nat2Z.inj_add. simpl.
  rewrite Z.pow_add_r; try lia.
  pose proof (bv_unsigned_in_range 8 x) as Hbyte.
  change (0 <= bv_unsigned x < 256) in Hbyte.
  simpl. nia.
Qed.

Lemma zesu_byte_window_fits64 (bytes : list (bv 8)) (start count : nat) :
  (count <= 8)%nat ->
  0 <= zesu_byte_window_fold bytes start count < bv_modulus 64.
Proof.
  intros Hcount. unfold zesu_byte_window_fold.
  pose proof (zesu_big_endian8_range (firstn count (skipn start bytes))) as Hrange.
  pose proof (firstn_le_length count (skipn start bytes)) as Hlength.
  assert (Hpower : 256 ^ Z.of_nat (length (firstn count (skipn start bytes))) <= 256 ^ 8)
    by (apply Z.pow_le_mono_r; lia).
  change (0 <= zesu_big_endian8 (firstn count (skipn start bytes)) < 256 ^ 8).
  lia.
Qed.

Lemma zesu_byte_window_unsigned_step (bytes : list (bv 8)) (start count : nat) (next : bv 8) :
  (S count <= 8)%nat ->
  nth_error bytes (start + count)%nat = Some next ->
  bv_unsigned (bv_or
    (bv_shiftl (Z_to_bv 64 (zesu_byte_window_fold bytes start count)) (BV 64 8))
    (bv_zero_extend 64 next)) = zesu_byte_window_fold bytes start (S count).
Proof.
  intros Hcount Hnext. rewrite (zesu_byte_window_word_snoc bytes start count next Hnext).
  apply Z_to_bv_small. apply zesu_byte_window_fits64. exact Hcount.
Qed.
