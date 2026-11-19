Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.

Set Default Proof Using "Type".

(* The hidden-history library of Hist.v: the edge and reveal steps of the run
   pass and their guards (each: one goal where it runs, one where it is
   skipped), the identity edge, the seal, the join history. *)

Definition test_pre (x : Z) : Prop := x = 3.
Definition test_succ (x : Z) : Prop := x + 1 = 4.

Global Instance test_edge {PROP : bi} (x : Z) :
  ZesuHistEdge (PROP := PROP) (test_pre x) (test_succ x) True.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. iIntros "_". iPureIntro.
  apply zesu_hist_intro. unfold test_pre, test_succ in *. lia.
Qed.

Global Instance test_reveal (x : Z) : ZesuHistReveal (test_pre x) (x < 5).
Proof. rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold test_pre in Hh. lia. Qed.

Ltac class_is c := let k := zesu_goal_class in constr_eq k c.

Section hist.
Context {PROP : bi}.

(* Edge step: a history conjunct with a context history and an instance. *)
Lemma edge_fires (x : Z) (Q : PROP) :
  zesu_hist (test_pre x) -> (⊢ Q) -> ⊢ ⌜zesu_hist (test_succ x)⌝ ∗ Q.
Proof.
  intros Hh HQ. iStartProof. class_is ZGsep_pure.
  zesu_hist_goal. zesu_hist_in_context. zesu_hist_step.
  iSplit; [done|iApply HQ].
Qed.

(* Edge step skipped: no history in the context. *)
Lemma edge_skipped_no_history (x : Z) (Q : PROP) :
  test_pre x -> (⊢ Q) -> ⊢ ⌜zesu_hist (test_succ x)⌝ ∗ Q.
Proof.
  intros Hp HQ. iStartProof. zesu_hist_goal.
  assert_fails (idtac; zesu_hist_in_context). assert_fails (idtac; zesu_hist_step).
  iSplit; [iPureIntro; apply zesu_hist_intro; unfold test_pre, test_succ in *; lia|iApply HQ].
Qed.

(* Edge guard skipped: the conjunct is not a history. *)
Lemma edge_skipped_not_history (x : Z) (Q : PROP) :
  zesu_hist (test_pre x) -> (⊢ Q) -> ⊢ ⌜x = x⌝ ∗ Q.
Proof.
  intros Hh HQ. iStartProof. class_is ZGsep_pure.
  assert_fails (idtac; zesu_hist_goal). assert_fails (idtac; zesu_hist_step).
  iSplit; [done|iApply HQ].
Qed.

(* Identity edge: the successor states the entry's own history. *)
Lemma edge_identity (x : Z) (Q : PROP) :
  zesu_hist (test_pre x) -> (⊢ Q) -> ⊢ ⌜zesu_hist (test_pre x)⌝ ∗ Q.
Proof.
  intros Hh HQ. iStartProof. zesu_hist_goal. zesu_hist_step.
  iSplit; [done|iApply HQ].
Qed.

(* Reveal step: a visible fact the history holds. *)
Lemma reveal_fires (x : Z) (Q : PROP) :
  zesu_hist (test_pre x) -> (⊢ Q) -> ⊢ ⌜x < 5⌝ ∗ Q.
Proof.
  intros Hh HQ. iStartProof. zesu_hist_in_context. zesu_hist_reveal_step. iApply HQ.
Qed.

(* Reveal guard skipped: no history in the context. *)
Lemma reveal_skipped_no_history (x : Z) (Q : PROP) :
  x = 3 -> (⊢ Q) -> ⊢ ⌜x < 5⌝ ∗ Q.
Proof.
  intros Hx HQ. iStartProof. class_is ZGsep_pure.
  assert_fails (idtac; zesu_hist_in_context). assert_fails (idtac; zesu_hist_reveal_step).
  iSplit; [iPureIntro; lia|iApply HQ].
Qed.

(* Reveal step skipped: no instance for the fact. *)
Lemma reveal_skipped_no_instance (x : Z) (Q : PROP) :
  zesu_hist (test_pre x) -> (⊢ Q) -> ⊢ ⌜x < 4⌝ ∗ Q.
Proof.
  intros Hh HQ. iStartProof. zesu_hist_in_context. assert_fails (idtac; zesu_hist_reveal_step).
  apply zesu_hist_elim in Hh. unfold test_pre in Hh.
  iSplit; [iPureIntro; lia|iApply HQ].
Qed.
End hist.

(* The seal: no reduction opens a history. *)
Lemma hist_sealed (x : Z) : zesu_hist (test_pre x) = test_pre x.
Proof.
  assert_fails reflexivity.
  assert_fails (progress simpl). assert_fails (progress cbn).
  assert_fails (simpl; reflexivity). assert_fails (cbn; reflexivity).
  assert_fails (vm_compute; reflexivity).
  rewrite zesu_hist_eq. reflexivity.
Qed.

Lemma hist_hypothesis_sealed (x : Z) : zesu_hist (test_pre x) -> x = 3.
Proof.
  intros Hh. simpl in Hh. cbn in Hh.
  lazymatch type of Hh with zesu_hist _ => idtac end.
  assert_fails lia.
  apply zesu_hist_elim in Hh. exact Hh.
Qed.

(* The join history is a plain definition: transparent to `lia` after `unfold`. *)
Lemma join_history_unfold (x : Z) : zesu_join_history (3 <= x)%Z -> (2 < x)%Z.
Proof.
  intros Hj. assert_fails lia.
  unfold zesu_join_history in Hj. lia.
Qed.

(* Loop exit view: the guard from the context, its unsigned view from the
   decided guard. *)
Lemma exit_view (v : bv 64) :
  bool_decide (bv_unsigned v < 8)%Z = true ->
  bool_decide (bv_unsigned v < 8)%Z = true /\ (bv_unsigned v < 8)%Z.
Proof. intros Hg. zesu_hist_exit_view. Qed.

Lemma exit_view_skipped (v : bv 64) :
  (bv_unsigned v < 8)%Z -> bool_decide (bv_unsigned v < 4)%Z = true /\ True.
Proof. intros Hv. assert_fails (idtac; zesu_hist_exit_view). Abort.

(* A negated bitvector guard is viewed as an unsigned disequation, and an
   edge proof's `zesu_hist_view` closes the guard with its unsigned view. *)
Lemma view_negated_guard (v : bv 64) :
  negb (bool_decide (bv_and v (BV 64 1) = BV 64 0)) = true ->
  negb (bool_decide (bv_and v (BV 64 1) = BV 64 0)) = true /\
  bv_unsigned (bv_and v (BV 64 1)) <> 0%Z.
Proof.
  intros Hg.
  assert (Hv := Hg). zesu_hist_view_fact Hv.
  lazymatch type of Hv with not (@eq Z _ 0%Z) => idtac end.
  zesu_hist_view Hg.
Qed.

(* A disequation on another type is left as it is. *)
Lemma view_other_disequation (n : Z) : (n <> 0)%Z -> (n <> 0)%Z.
Proof.
  intros Hn. zesu_hist_view_fact Hn.
  lazymatch type of Hn with (n <> 0)%Z => exact Hn end.
Qed.

(* First pass of a sealed loop class. *)
Lemma loop_first_pass_sealed `{!islaG Sigma} (n : Z) :
  (True : iProp Sigma) ∗ ⌜n = 0%Z⌝ ⊢
  ∃ a b c d e : Z, (True : iProp Sigma) ∗ ⌜(a = 0)%Z⌝ ∗ ⌜zesu_hist (b = 0)%Z⌝.
Proof.
  exact (zesu_loop_first_pass_intro_sealed (fun _ _ _ _ _ => True%I)
    (fun a _ _ _ _ => a = 0%Z) (fun _ b _ _ _ => zesu_hist (b = 0%Z))
    (n = 0%Z) n n n n n (fun Hn => conj Hn (zesu_hist_intro _ Hn))).
Qed.
