From Coq Require Import ZArith.ZArith Lists.List NArith.NArith.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Set Default Proof Using "Type".

(* HistWindow.v: the history step across a load window in the block's history
   and byte positions in the successor's history; and the frame-offset index
   literal of WrappedWord.v proved in a context over the `zesu_lia` budget. *)

(* Rigid families (inductives): the edge instance applies only when the word
   arguments are the same term, as for the generated histories. *)
Inductive hw_pre (l : list (bv 8)) (w : bv 64) : Prop :=
  hw_pre_intro : length l = 40%nat -> hw_pre l w.
Inductive hw_succ (l : list (bv 8)) (w : bv 64) : Prop :=
  hw_succ_intro : length l = 40%nat -> hw_succ l w.

Global Instance hw_edge {PROP : bi} (l : list (bv 8)) (w : bv 64) :
  ZesuHistEdge (PROP := PROP) (hw_pre l w) (hw_succ l w) True.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. iIntros "_". iPureIntro.
  apply zesu_hist_intro. destruct Hh as [Hl]. exact (hw_succ_intro l w Hl).
Qed.

(* The word at bytes 24 to 31 of [l] by byte positions. *)
Definition hw_positions (l : list (bv 8)) : bv 64 :=
  bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
    (bv_concat 16 (nth 31 l (BV 8 0)) (nth 30 l (BV 8 0))) (nth 29 l (BV 8 0)))
    (nth 28 l (BV 8 0))) (nth 27 l (BV 8 0))) (nth 26 l (BV 8 0))) (nth 25 l (BV 8 0)))
    (nth 24 l (BV 8 0)).

Section hist_window.
Context {PROP : bi}.

(* The window at a literal start. *)
Lemma hist_window_literal (l : list (bv 8)) (Q : PROP) :
  zesu_hist (hw_pre l (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 l))))) ->
  (⊢ Q) ->
  ⊢ ⌜zesu_hist (hw_succ l ltac:(let t := eval unfold hw_positions in (hw_positions l) in exact t))⌝ ∗ Q.
Proof.
  intros Hh HQ. iStartProof.
  assert_fails (idtac; zesu_hist_step).
  HistWindow.zesu_hist_step_respelled.
  iSplit; [done|iApply HQ].
Qed.

(* The window at a frame-offset start (`sp - 400 + 400 - 272` against the
   frame base `sp - 400 + 104`): the start becomes the literal 24, then the
   window becomes byte positions, also in the equation that defines it. *)
Lemma hist_window_frame (sp : bv 64) (l : list (bv 8)) (y : bv 64) (Q : PROP) :
  4096 <= bv_unsigned sp < 4294967296 ->
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat
    (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551344) -
     (bv_unsigned sp - 400 + 48 + 56))) l))) = y ->
  zesu_hist (hw_pre l (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat
    (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551344) -
     (bv_unsigned sp - 400 + 48 + 56))) l))))) ->
  (⊢ Q) ->
  ⊢ ⌜zesu_hist (hw_succ l ltac:(let t := eval unfold hw_positions in (hw_positions l) in exact t))⌝ ∗ Q.
Proof.
  intros Hsp Hy Hh HQ. iStartProof.
  assert_fails (idtac; zesu_hist_step).
  HistWindow.zesu_hist_step_respelled.
  lazymatch type of Hy with context [little_endian_to_bv] => fail | _ => idtac end.
  iSplit; [done|iApply HQ].
Qed.

(* Refused: the block's history holds no window. *)
Lemma hist_window_refused_no_window (l : list (bv 8)) (w : bv 64) (Q : PROP) :
  zesu_hist (hw_pre l w) -> (⊢ Q) ->
  ⊢ ⌜zesu_hist (hw_succ l ltac:(let t := eval unfold hw_positions in (hw_positions l) in exact t))⌝ ∗ Q.
Proof.
  intros Hh HQ. iStartProof.
  assert_fails (idtac; HistWindow.zesu_hist_step_respelled).
  apply zesu_hist_elim in Hh. destruct Hh as [Hl].
  iSplit; [iPureIntro; apply zesu_hist_intro; constructor; exact Hl|iApply HQ].
Qed.

(* Refused: the successor reads ANOTHER list by position. *)
Lemma hist_window_refused_other_list (l k : list (bv 8)) (Q : PROP) :
  zesu_hist (hw_pre l (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 l))))) ->
  length k = 40%nat -> (⊢ Q) ->
  ⊢ ⌜zesu_hist (hw_succ k ltac:(let t := eval unfold hw_positions in (hw_positions k) in exact t))⌝ ∗ Q.
Proof.
  intros Hh Hk HQ. iStartProof.
  assert_fails (idtac; HistWindow.zesu_hist_step_respelled).
  lazymatch type of Hh with context [little_endian_to_bv] => idtac end.
  iSplit; [iPureIntro; apply zesu_hist_intro; constructor; exact Hk|iApply HQ].
Qed.

(* Refused at the head test: the conjunct is not a history, and a pure goal. *)
Lemma hist_window_refused_not_history (l : list (bv 8)) (Q : PROP) :
  zesu_hist (hw_pre l (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 l))))) -> (⊢ Q) ->
  ⊢ ⌜nth 24 l (BV 8 0) = nth 24 l (BV 8 0)⌝ ∗ Q.
Proof.
  intros Hh HQ. iStartProof.
  assert_fails (idtac; HistWindow.zesu_hist_step_respelled).
  iSplit; [done|iApply HQ].
Qed.

Lemma hist_window_refused_pure (l : list (bv 8)) :
  zesu_hist (hw_pre l (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 l))))) ->
  zesu_hist (hw_succ l ltac:(let t := eval unfold hw_positions in (hw_positions l) in exact t)) ->
  True.
Proof.
  intros Hh Hs.
  assert_fails (idtac; HistWindow.zesu_hist_step_respelled).
  exact I.
Qed.

End hist_window.

(* The frame-offset index literal with a context over the `zesu_lia` node
   budget (a fact of about 2^16 nodes over another integer): proved in a
   cleared context. *)
Goal forall (sp : bv 64) (x : Z) (bytes : list (bv 8)) (P : list (bv 8) -> Prop),
  4096 <= bv_unsigned sp < 4294967296 -> P (take 8 (drop 24 bytes)) ->
  P (take 8 (drop (Z.to_nat (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400 +
    BV 64 18446744073709551344) - (bv_unsigned sp - 400 + 48 + 56))) bytes)).
Proof.
  intros sp x bytes P Hsp HP.
  let t0 := constr:(x) in
  let t1 := constr:(t0 + t0) in let t2 := constr:(t1 + t1) in let t3 := constr:(t2 + t2) in
  let t4 := constr:(t3 + t3) in let t5 := constr:(t4 + t4) in let t6 := constr:(t5 + t5) in
  let t7 := constr:(t6 + t6) in let t8 := constr:(t7 + t7) in let t9 := constr:(t8 + t8) in
  let t10 := constr:(t9 + t9) in let t11 := constr:(t10 + t10) in let t12 := constr:(t11 + t11) in
  let t13 := constr:(t12 + t12) in let t14 := constr:(t13 + t13) in let t15 := constr:(t14 + t14) in
  assert (Hbig : t15 <= t15) by apply Z.le_refl.
  ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_step.
  exact HP.
Qed.
