Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SourceFactByteViews.
From Coq Require Import ZArith NArith Lia.
From stdpp Require Import bitvector.definitions.
From Coq Require Import Lists.List.
Local Open Scope Z_scope.

Lemma order_lower (byte : bv 8) (Hsource : bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 byte) (Z_to_bv 64 255))) >= bv_signed (Z_to_bv 128 192)) :
 192 <= bv_unsigned byte.
Proof. zesu_source_byte_order_goal. Qed.

Lemma order_negative (byte : bv 8) (Hsource : ~ (bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 byte) (Z_to_bv 64 255))) >= bv_signed (Z_to_bv 128 192))) :
 bv_unsigned byte <= 191.
Proof. zesu_source_byte_order_goal. Qed.

Lemma order_strict (byte : bv 8) (Hsource : bv_signed (bv_zero_extend 128 (Z_to_bv 64 183)) < bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 byte) (Z_to_bv 64 255)))) :
 184 <= bv_unsigned byte.
Proof. zesu_source_byte_order_goal. Qed.

Lemma order_alternate (byte : bv 8) (Hsource : bv_signed (bv_zero_extend 32 (bv_and (bv_sign_extend 16 byte) (Z_to_bv 16 255))) < bv_signed (Z_to_bv 32 248)) :
 bv_unsigned byte <= 247.
Proof. zesu_source_byte_order_goal. Qed.

Lemma order_symbolic_mask (byte : bv 8) (mask : bv 64) (Hsource : bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 byte) mask)) >= bv_signed (Z_to_bv 128 192)) : True.
Proof. assert_fails (assert (192 <= bv_unsigned byte) by (zesu_source_byte_order_goal)). exact I. Qed.

Lemma order_symbolic_bound (byte : bv 8) (bound : bv 128) (Hsource : bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 byte) (Z_to_bv 64 255))) >= bv_signed bound) : True.
Proof. assert_fails (assert (192 <= bv_unsigned byte) by (zesu_source_byte_order_goal)). exact I. Qed.

Lemma order_wrong_mask (byte : bv 8)  (Hsource : bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 byte) (Z_to_bv 64 127))) >= bv_signed (Z_to_bv 128 192)) : True.
Proof. assert_fails (assert (192 <= bv_unsigned byte) by (zesu_source_byte_order_goal)). exact I. Qed.

Lemma order_narrow_signed (byte : bv 8)  (Hsource : bv_signed (bv_zero_extend 8 (bv_and (bv_sign_extend 64 byte) (Z_to_bv 64 255))) >= bv_signed (Z_to_bv 8 192)) : True.
Proof. assert_fails (assert (192 <= bv_unsigned byte) by (zesu_source_byte_order_goal)). exact I. Qed.

Lemma order_changed_byte (byte : bv 8) (other : bv 8) (Hsource : bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 byte) (Z_to_bv 64 255))) >= bv_signed (Z_to_bv 128 192)) : True.
Proof. assert_fails (assert (192 <= bv_unsigned other) by (zesu_source_byte_order_goal)). exact I. Qed.


Lemma order_source_list (bytes : list (bv 8))
    (Hsource : bv_signed (bv_zero_extend 128 (BV 64 183)) <
      bv_signed (bv_zero_extend 128 (bv_and
        (bv_sign_extend 64 (nth 0 bytes (BV 8 0))) (BV 64 255)))) :
  184 <= bv_unsigned (nth 0 bytes (BV 8 0)).
Proof. zesu_source_byte_order_goal. Qed.

Lemma order_source_list_negative (bytes : list (bv 8))
    (Hsource : ~ (bv_signed (bv_zero_extend 128 (bv_and
      (bv_sign_extend 64 (nth 0 bytes (BV 8 0))) (BV 64 255))) >=
      bv_signed (bv_zero_extend 128 (BV 64 192)))) :
  bv_unsigned (nth 0 bytes (BV 8 0)) <= 191.
Proof. zesu_source_byte_order_goal. Qed.
