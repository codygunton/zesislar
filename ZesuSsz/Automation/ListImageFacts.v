From Coq Require Import List Lia.
From stdpp Require Import list.

Section list_images.
Context {A : Type}.

Lemma image_nth_error_lookup (xs : list A) i :
  nth_error xs i = xs !! i.
Proof.
  revert i. induction xs as [|x xs IH]; intros [|i]; simpl; auto.
Qed.

Lemma image_prefix_overwrite_after (prefix xs : list A) i :
  (length prefix <= i)%nat ->
  (prefix ++ drop (length prefix) xs) !! i = xs !! i.
Proof.
  intros Hi. rewrite lookup_app_r by exact Hi.
  rewrite lookup_drop. f_equal. lia.
Qed.

Lemma image_prefix_overwrite_length (prefix xs : list A) :
  (length prefix <= length xs)%nat ->
  length (prefix ++ drop (length prefix) xs) = length xs.
Proof. intros Hlength. rewrite length_app, length_drop. lia. Qed.

Lemma image_splice_lookup_inside (xs field : list A) base i :
  (base <= length xs)%nat -> (i < length field)%nat ->
  (take base xs ++ field ++ drop (base + length field) xs) !! (base + i) = field !! i.
Proof.
  intros Hbase Hi.
  rewrite lookup_app_r by (rewrite length_take_le; lia).
  rewrite length_take_le by exact Hbase.
  replace (base + i - base)%nat with i by lia.
  rewrite lookup_app_l by exact Hi. reflexivity.
Qed.

Lemma image_splice_lookup_before (xs field : list A) base i :
  (base <= length xs)%nat -> (i < base)%nat ->
  (take base xs ++ field ++ drop (base + length field) xs) !! i = xs !! i.
Proof.
  intros Hbase Hi.
  rewrite lookup_app_l by (rewrite length_take_le; lia).
  apply lookup_take. exact Hi.
Qed.

Lemma image_splice_lookup_after (xs field : list A) base i :
  (base <= length xs)%nat -> (base + length field <= i)%nat ->
  (take base xs ++ field ++ drop (base + length field) xs) !! i = xs !! i.
Proof.
  intros Hbase Hi.
  rewrite lookup_app_r by (rewrite length_take_le; lia).
  rewrite length_take_le by exact Hbase.
  rewrite lookup_app_r by lia.
  rewrite lookup_drop. f_equal. lia.
Qed.

Lemma image_splice_length (xs field : list A) base :
  (base + length field <= length xs)%nat ->
  length (take base xs ++ field ++ drop (base + length field) xs) = length xs.
Proof.
  intros Hbound. rewrite !length_app, length_take_le by lia.
  rewrite length_drop. lia.
Qed.

Lemma image_splice_lookup_absolute (xs field : list A) base i :
  (base <= length xs)%nat -> (base <= i < base + length field)%nat ->
  (take base xs ++ field ++ drop (base + length field) xs) !! i = field !! (i - base).
Proof.
  intros Hbase [Hstart Hend].
  replace i with (base + (i - base))%nat at 1 by lia.
  apply image_splice_lookup_inside. exact Hbase. lia.
Qed.

End list_images.

Create HintDb zesu_image.
Global Hint Rewrite @image_nth_error_lookup @length_insert : zesu_image.
Global Hint Rewrite @image_prefix_overwrite_after @image_prefix_overwrite_length
  @image_splice_lookup_absolute @image_splice_lookup_before @image_splice_lookup_after
  @image_splice_length @take_insert @drop_insert_gt using (simpl; lia) : zesu_image.
