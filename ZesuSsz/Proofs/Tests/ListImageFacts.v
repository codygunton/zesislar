Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ListImageFacts.
From Coq Require Import List Lia.
From stdpp Require Import list.
Import ListNotations.

Lemma image_test_field_at_literal_offset (xs : list nat) :
  (34 <= length xs)%nat ->
  (take 32 xs ++ [0; 0] ++ drop 34 xs) !! 32 = Some 0.
Proof.
  intros Hlength.
  rewrite (image_splice_lookup_inside xs [0; 0] 32 0) by (simpl; lia).
  reflexivity.
Qed.

Lemma image_test_rewrite_bounded_splice (xs : list nat) :
  (34 <= length xs)%nat ->
  nth_error (take 32 xs ++ [0; 0] ++ drop 34 xs) 32 = Some 0.
Proof. intros Hlength. autorewrite with zesu_image. reflexivity. Qed.

Lemma image_test_padding_before (xs : list nat) i :
  (40 <= length xs)%nat -> (17 <= i < 24)%nat ->
  (take 32 xs ++ [0; 0] ++ drop 34 xs) !! i = xs !! i.
Proof.
  intros Hlength Hi. apply image_splice_lookup_before; simpl; lia.
Qed.

Lemma image_test_padding_after (xs : list nat) i :
  (40 <= length xs)%nat -> (34 <= i < 40)%nat ->
  (take 32 xs ++ [0; 0] ++ drop 34 xs) !! i = xs !! i.
Proof.
  intros Hlength Hi. apply image_splice_lookup_after; simpl; lia.
Qed.

Lemma image_test_two_field_overwrite (xs first second : list nat) i :
  length first = 8%nat -> length second = 8%nat -> (16 <= i)%nat ->
  ((first ++ second) ++ drop 16 xs) !! i = xs !! i.
Proof.
  intros Hfirst Hsecond Hi.
  replace 16%nat with (length (first ++ second)) by (rewrite length_app; lia).
  apply image_prefix_overwrite_after. rewrite length_app. lia.
Qed.

Lemma image_test_splice_at_end (xs field : list nat) :
  (length field <= length xs)%nat ->
  length (take (length xs - length field) xs ++ field ++
          drop (length xs - length field + length field) xs) = length xs.
Proof. intros Hbound. apply image_splice_length. lia. Qed.

Lemma image_test_empty_splice (xs : list nat) base :
  (base <= length xs)%nat ->
  length (take base xs ++ [] ++ drop base xs) = length xs.
Proof.
  intros Hbound. replace base with (base + length ([] : list nat))%nat at 2 by (simpl; lia).
  apply image_splice_length. simpl. lia.
Qed.

Lemma image_test_insert_preserves_disjoint_windows (xs : list nat) :
  take 8 (<[16 := 1]> xs) = take 8 xs /\
  drop 17 (<[16 := 1]> xs) = drop 17 xs.
Proof. split; autorewrite with zesu_image; reflexivity. Qed.

Lemma image_test_insert_preserves_extent (xs : list nat) :
  length (<[32 := 0]> xs) = length xs.
Proof. autorewrite with zesu_image. reflexivity. Qed.

Lemma image_test_invalid_extent :
  length (take 1 [0; 1] ++ [8; 9] ++ drop 3 [0; 1]) <> length [0; 1].
Proof. discriminate. Qed.

Lemma image_test_overlap_changes_value :
  (take 1 [0; 1; 2] ++ [9] ++ drop 2 [0; 1; 2]) !! 1 <> [0; 1; 2] !! 1.
Proof. discriminate. Qed.

Print Assumptions image_test_field_at_literal_offset.
Print Assumptions image_test_padding_before.
Print Assumptions image_test_padding_after.
Print Assumptions image_test_two_field_overwrite.
Print Assumptions image_test_splice_at_end.
Print Assumptions image_test_empty_splice.
Print Assumptions image_test_insert_preserves_disjoint_windows.
Print Assumptions image_test_insert_preserves_extent.
Print Assumptions image_test_invalid_extent.
Print Assumptions image_test_overlap_changes_value.

Print Assumptions image_test_rewrite_bounded_splice.
