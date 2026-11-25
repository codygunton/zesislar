Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A leftover existential that only pure facts constrain, its spatial rest
   held (ExistsPure.v): the pure statement binds the tuple's components one
   by one, and a proof of it closes the goal. Refused when the spatial rest
   mentions the witness or is not held. *)

(* An opaque record fact over the witnesses, held as a hypothesis. *)
Definition exists_pure_record (x : Z) (l : list Z) : Prop := x = 3 /\ l = [].

(* Two histories and an edge between them with one new fact. *)
Definition exists_pure_hist_pre (a : Z) : Prop := 0 <= a.
Definition exists_pure_hist_succ (a : Z) : Prop := 0 <= a /\ a < 10.

Section exists_pure.
Context `{!islaG Sigma} `{!threadG}.

Lemma exists_pure_statement (K : iProp Sigma) (a : Z) :
  K -∗ ∃ x : Z *ₗ bool *ₗ unit, ⌜x.1ₗ = a⌝ ∗ (⌜x.2ₗ = true⌝ ∗ K).
Proof.
  iIntros "HK".
  ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_parts ltac:(fun E =>
    constr_eq E (exists (a0 : Z) (b : bool), a0 = a /\ b = true)).
  ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_close ltac:(exists a, true; split; reflexivity).
Qed.

(* A witness type that is not a tuple: one binder. *)
Lemma exists_pure_single (K : iProp Sigma) (a : Z) :
  K -∗ ∃ x : Z, ⌜x = a⌝ ∗ K.
Proof.
  iIntros "HK".
  ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_parts ltac:(fun E => constr_eq E (exists a0 : Z, a0 = a)).
  ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_close ltac:(exists a; reflexivity).
Qed.

(* The spatial rest mentions the witness. *)
Lemma exists_pure_refused_dependent (P : Z -> iProp Sigma) (a : Z) :
  P a -∗ ∃ x : Z, ⌜x = a⌝ ∗ P x.
Proof.
  iIntros "HP".
  Fail ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_parts ltac:(fun _ => idtac).
  iExists a. iFrame. done.
Qed.

(* The spatial rest is not held (`emp` is no hypothesis). *)
Lemma exists_pure_refused_not_held (K : iProp Sigma) (a : Z) :
  K -∗ ∃ x : Z, ⌜x = a⌝ ∗ K ∗ emp.
Proof.
  iIntros "HK".
  Fail ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_parts ltac:(fun _ => idtac).
  iExists a. iFrame. done.
Qed.

(* The pure statement restates a hypothesis over the witnesses: the context
   closer unifies the witnesses with the hypothesis's arguments. *)
Lemma exists_pure_from_hypotheses (K : iProp Sigma) (b : Z) (l : list Z) :
  exists_pure_record (b + 1) l ->
  K -∗ ∃ x : Z *ₗ list Z *ₗ unit, ⌜exists_pure_record (x.1ₗ + 1) x.2ₗ⌝ ∗ K.
Proof.
  intros Hrecord. iIntros "HK".
  ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_close ltac:(
    solve [ZesuSsz.Automation2.NamedEquations.zesu_finish_exists_from_hypotheses]).
Qed.

(* Witnesses fixed by the context in passes: the record fixes the first two
   components; `3 = y` fixes y, although `0 <= y` comes first and the
   context holds the lower bound `0 <= a` it would unify with; `[] = concat
   w` fixes w; a nested existential restates the record. *)
Lemma exists_pure_context_passes (K : iProp Sigma) (a b : Z) (l : list Z) :
  0 <= a -> exists_pure_record (b + 1) l ->
  K -∗ ∃ x : Z *ₗ list Z *ₗ Z *ₗ list (list Z) *ₗ unit,
    ⌜exists_pure_record (x.1ₗ + 1) x.2ₗ⌝ ∗ ⌜0 <= x.3ₗ⌝ ∗ ⌜3 = x.3ₗ⌝ ∗
    ⌜[] = concat x.4ₗ⌝ ∗ ⌜∃ m : Z, exists_pure_record (m + 1) l⌝ ∗ K.
Proof.
  intros Ha Hrecord. iIntros "HK".
  ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_close ltac:(
    solve [ZesuSsz.Automation2.Finish.zesu_exists_pure_from_context]).
Qed.

Global Instance exists_pure_hist_edge (a : Z) :
  ZesuHistEdge (PROP := iProp Sigma) (exists_pure_hist_pre a) (exists_pure_hist_succ a)
    (⌜a < 10⌝ ∗ ⌜True⌝).
Proof.
  rewrite /ZesuHistEdge => Hh. iIntros "[%Hlt _]". iPureIntro.
  apply zesu_hist_intro. split; [exact (zesu_hist_elim _ Hh) | exact Hlt].
Qed.

(* A restated successor history follows from the context history through
   the edge, whose new fact is a hypothesis. *)
Lemma exists_pure_history (K : iProp Sigma) (a : Z) :
  zesu_hist (exists_pure_hist_pre a) -> a < 10 ->
  K -∗ ∃ x : Z, ⌜x = a⌝ ∗ ⌜zesu_hist (exists_pure_hist_succ x)⌝ ∗ K.
Proof.
  intros Hpre Hlt. iIntros "HK".
  ZesuSsz.Automation2.ExistsPure.zesu_exists_pure_close ltac:(
    solve [ZesuSsz.Automation2.Finish.zesu_exists_pure_from_context]).
Qed.

(* Without the edge's new fact in the context the history does not follow. *)
Lemma exists_pure_history_refused (a : Z) :
  zesu_hist (exists_pure_hist_pre a) -> True.
Proof.
  intros Hpre.
  Fail assert (exists x : Z, x = a /\ zesu_hist (exists_pure_hist_succ x)) by
    solve [ZesuSsz.Automation2.Finish.zesu_exists_pure_from_context].
  exact I.
Qed.
End exists_pure.
