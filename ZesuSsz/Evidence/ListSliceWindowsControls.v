Require Import ZesuSsz.Automation.All.
From Coq Require Import List Lia Arith.
From stdpp Require Import list.
Require Import ZesuSsz.Automation.ListSliceWindows.

Lemma before_window {A : Type} (before suffix : list A) (prefix start count : nat) :
  (start + count <= prefix)%nat -> (prefix <= length before)%nat ->
  take count (drop start (take prefix before ++ suffix)) = take count (drop start before).
Proof. intros. solve [repeat zesu_list_slice_windows; reflexivity]. Qed.

Lemma suffix_window {A : Type} (before suffix : list A) (prefix : nat) :
  (prefix <= length before)%nat -> drop prefix (take prefix before ++ suffix) = suffix.
Proof. intros. solve [repeat zesu_list_slice_windows; reflexivity]. Qed.

Lemma whole_window {A : Type} (bytes : list A) (count : nat) :
  (length bytes <= count)%nat -> take count bytes = bytes.
Proof. intros. solve [repeat zesu_list_slice_windows; reflexivity]. Qed.

Lemma fixed_before {A : Type} (before suffix : list A) :
  length before = 40%nat ->
  take 7 (drop 17 (take 32 before ++ suffix)) = take 7 (drop 17 before).
Proof. intros. solve [repeat zesu_list_slice_windows; reflexivity]. Qed.

Lemma fixed_suffix {A : Type} (before suffix : list A) :
  length before = 40%nat -> drop 32 (take 32 before ++ suffix) = suffix.
Proof. intros. solve [repeat zesu_list_slice_windows; reflexivity]. Qed.

Lemma fixed_whole {A : Type} (before : list A) :
  length before = 40%nat -> take 6 (drop 34 before) = drop 34 before.
Proof. intros. solve [repeat zesu_list_slice_windows; reflexivity]. Qed.

Goal forall (before suffix : list nat) (prefix start count : nat),
  (prefix <= length before)%nat ->
  take count (drop start (take prefix before ++ suffix)) = take count (drop start before).
Proof. intros. Fail solve [repeat zesu_list_slice_windows; reflexivity]. Abort.

Goal forall (before suffix : list nat) (prefix start count : nat),
  (start + count <= prefix)%nat ->
  take count (drop start (take prefix before ++ suffix)) = take count (drop start before).
Proof. intros. Fail solve [repeat zesu_list_slice_windows; reflexivity]. Abort.

Goal forall (before suffix : list nat) (prefix : nat),
  (prefix <= length before)%nat ->
  take (prefix + 1) (drop 0 (take prefix before ++ suffix)) = take (prefix + 1) (drop 0 before).
Proof. intros. Fail solve [repeat zesu_list_slice_windows; reflexivity]. Abort.

Goal forall (suffix : list nat),
  take 1 (drop 0 (take 10 [] ++ suffix)) = take 1 (drop 0 []).
Proof. intros. Fail solve [repeat zesu_list_slice_windows; reflexivity]. Abort.
Print Assumptions before_window.
Print Assumptions suffix_window.
