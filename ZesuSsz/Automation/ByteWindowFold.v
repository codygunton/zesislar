From Coq Require Import Lists.List ZArith.ZArith.
From stdpp Require Import bitvector.definitions.
Import ListNotations.
Open Scope Z_scope.

Definition zesu_big_endian8 (bytes : list (bv 8)) : Z :=
  fold_left (fun acc byte => 256 * acc + bv_unsigned byte) bytes 0.

Definition zesu_byte_window_fold (bytes : list (bv 8)) (start count : nat) : Z :=
  zesu_big_endian8 (firstn count (skipn start bytes)).

Lemma zesu_big_endian8_zero : zesu_big_endian8 [] = 0.
Proof. reflexivity. Qed.

Lemma zesu_big_endian8_snoc (bytes : list (bv 8)) (next : bv 8) :
  zesu_big_endian8 (bytes ++ [next]) =
    256 * zesu_big_endian8 bytes + bv_unsigned next.
Proof. unfold zesu_big_endian8. rewrite fold_left_app. reflexivity. Qed.

Lemma zesu_window_firstn_snoc {A} (bytes : list A) (count : nat) (next : A) :
  nth_error bytes count = Some next ->
  firstn (S count) bytes = firstn count bytes ++ [next].
Proof.
  revert count. induction bytes as [|head tail IH]; intros [|count] Hnext;
    simpl in *; try discriminate;
    [inversion Hnext; reflexivity | f_equal; apply IH; exact Hnext].
Qed.

Lemma zesu_window_skipn_lookup {A} (bytes : list A) (start count : nat) :
  nth_error (skipn start bytes) count = nth_error bytes (start + count)%nat.
Proof.
  revert bytes. induction start as [|start IH]; intros bytes; [reflexivity|].
  destruct bytes as [|head tail]; simpl; [destruct count; reflexivity|].
  apply IH.
Qed.

Lemma zesu_byte_window_zero (bytes : list (bv 8)) (start : nat) :
  zesu_byte_window_fold bytes start 0 = 0.
Proof. reflexivity. Qed.

Lemma zesu_byte_window_snoc (bytes : list (bv 8)) (start count : nat) (next : bv 8) :
  nth_error bytes (start + count)%nat = Some next ->
  zesu_byte_window_fold bytes start (S count) =
    256 * zesu_byte_window_fold bytes start count + bv_unsigned next.
Proof.
  intros Hnext. unfold zesu_byte_window_fold.
  rewrite (zesu_window_firstn_snoc (skipn start bytes) count next);
    [apply zesu_big_endian8_snoc | rewrite zesu_window_skipn_lookup; exact Hnext].
Qed.
