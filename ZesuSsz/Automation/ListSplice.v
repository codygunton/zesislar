From Coq Require Import List.
From stdpp Require Import list.

Lemma image_adjacent_prefix_splice {A : Type} (xs prefix next : list A) n m :
  length prefix = n -> length next = m ->
  take n (prefix ++ drop n xs) ++ next ++
    drop (n + m) (prefix ++ drop n xs) =
  prefix ++ next ++ drop (n + m) xs.
Proof.
  intros <- <-.
  rewrite take_app_length.
  rewrite drop_app_add.
  rewrite drop_drop.
  reflexivity.
Qed.
