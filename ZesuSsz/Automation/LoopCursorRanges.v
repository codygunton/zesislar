From Coq Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions.
Open Scope Z_scope.

Lemma zesu_loop_read_range (base start cursor limit length : Z) :
  base <= start -> start <= cursor -> cursor < limit -> limit <= base + length ->
  0 <= cursor - base < length.
Proof. intros. lia. Qed.

Lemma zesu_loop_read_lookup {A} (bytes : list A) (offset : Z) (default : A) :
  0 <= offset < Z.of_nat (length bytes) ->
  nth_error bytes (Z.to_nat offset) = Some (nth (Z.to_nat offset) bytes default).
Proof. intros Hrange. apply nth_error_nth'. lia. Qed.

Lemma zesu_loop_cursor_backedge (start cursor limit : Z) :
  start <= cursor -> cursor < limit -> cursor + 1 <> limit ->
  start <= cursor + 1 < limit.
Proof. intros. lia. Qed.

Lemma zesu_loop_unsigned_step (width : N) (cursor limit : bv width) :
  bv_unsigned cursor < bv_unsigned limit ->
  bv_unsigned (bv_add cursor (Z_to_bv width 1)) = bv_unsigned cursor + 1.
Proof.
  intros Hless.
  pose proof (bv_unsigned_in_range width cursor) as Hcursor.
  pose proof (bv_unsigned_in_range width limit) as Hlimit.
  rewrite bv_add_unsigned.
  rewrite (Z_to_bv_small width 1) by lia.
  apply bv_wrap_small. lia.
Qed.

Lemma zesu_loop_index_step (width : N) (cursor limit : bv width) (origin : Z) :
  bv_unsigned cursor < bv_unsigned limit ->
  bv_unsigned (bv_add cursor (Z_to_bv width 1)) - origin =
    (bv_unsigned cursor - origin) + 1.
Proof. intros Hless. rewrite (zesu_loop_unsigned_step width cursor limit Hless). lia. Qed.
