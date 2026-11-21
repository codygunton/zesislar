From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* decodeParentHeader 046c, 04f8: a branch compares a kept register `x` with
   the word loaded from a call's outcome `l` at 24. The premise `x = w` holds
   the word as a load window `Z_to_bv 64 (little_endian_to_bv 8 (take 8
   (drop 24 l)))`; Lithium substitutes `x` by it everywhere, the block
   history included, while the successor and its edge instance state the
   word by byte positions `bv_concat … (nth k l 0)`. The premise step of
   `liImpl` (BytePositionEquations.zesu_le_window_var_premise) restates the
   window by byte positions before the substitution. *)

Notation word24 l :=
  (bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
     (bv_concat 16 (nth 31 l (BV 8 0)) (nth 30 l (BV 8 0))) (nth 29 l (BV 8 0)))
     (nth 28 l (BV 8 0))) (nth 27 l (BV 8 0))) (nth 26 l (BV 8 0))) (nth 25 l (BV 8 0)))
     (nth 24 l (BV 8 0))) (only parsing).

(* The step fires: `x` is substituted by the byte-position spelling, which
   the conclusion states syntactically. *)
Lemma test_window_var_premise (x : bv 64) (l : list (bv 8)) (P : bv 64 -> Prop) :
  P (word24 l) ->
  x = Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 l))) -> P x.
Proof.
  intros HP. liImpl.
  lazymatch goal with |- P (bv_concat 64 _ (nth 24 l (BV 8 0))) => idtac end.
  exact HP.
Qed.

(* The window on the left, its start a frame offset (literal 24 once the
   stack range is known). *)
Lemma test_window_var_premise_offset (sp x : bv 64) (l : list (bv 8)) (P : bv 64 -> Prop) :
  2684354560 <= bv_unsigned sp < 3221225472 ->
  P (word24 l) ->
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop
    (Z.to_nat (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400) - (bv_unsigned sp - 400 + 376)))
    l))) = x -> P x.
Proof.
  intros Hsp HP. liImpl.
  lazymatch goal with |- P (bv_concat 64 _ (nth 24 l (BV 8 0))) => idtac end.
  exact HP.
Qed.

(* The step is skipped: no side of the premise is a variable. The window
   stays in the introduced premise. *)
Lemma test_window_var_premise_skip (x y : bv 64) (l : list (bv 8)) :
  bv_add x y = Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 l))) -> True.
Proof.
  liImpl.
  lazymatch goal with
  | H : bv_add x y = Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 l))) |- _ => idtac
  end.
  exact I.
Qed.

(* The step is skipped: a variable equated with a term without a window. *)
Lemma test_window_var_premise_skip_plain (x y : bv 64) (P : bv 64 -> Prop) :
  P (bv_add y y) -> x = bv_add y y -> P x.
Proof. intros HP. liImpl. exact HP. Qed.

(* The step is skipped: the window's bytes compute to a list (an image of
   words, as nextUint64's slice image), whose own window lemmas apply. *)
Lemma test_window_var_premise_skip_computed (x : bv 64) (b : bv 8) (l : list (bv 8)) (P : bv 64 -> Prop) :
  P (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 0 (b :: l))))) ->
  x = Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 0 (b :: l)))) -> P x.
Proof.
  intros HP. liImpl.
  lazymatch goal with
  | |- context [nth _ _ _] => fail "the window was restated"
  | |- _ => idtac
  end.
  exact HP.
Qed.

(* The step is skipped: the window is not the head of the premise's side. *)
Lemma test_window_var_premise_skip_nested (x y : bv 64) (l : list (bv 8)) (P : bv 64 -> Prop) :
  P (bv_add y (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 l))))) ->
  x = bv_add y (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 l)))) -> P x.
Proof.
  intros HP. liImpl.
  lazymatch goal with
  | |- P (bv_add y (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 l))))) => idtac
  end.
  exact HP.
Qed.
