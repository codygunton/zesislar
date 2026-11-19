(** Hidden block history (generic rule library).

   A generated entry of `entry_hist: wrap` shape states the facts it does not
   need visibly under one sealed fact `⌜zesu_hist (<entry>_Hist …)⌝`. The seal
   keeps `simpl`, `cbn`, `vm_compute` and the search from opening it. A block
   reaches its successor's history through one `ZesuHistEdge` instance per
   edge and reads a fact its successor states visibly through one
   `ZesuHistReveal` instance (a loop exit). Generated entries contain no proof;
   the instances and their proofs are rendered by `tools/block/render_edges.py`
   in `Edges*.v` (proof sentences limited to its `EDGE_SENTENCES`). *)

From iris.proofmode Require Import proofmode environments.
From iris.base_logic Require Import iprop.
From stdpp Require Import base bitvector.definitions bitvector.tactics.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.LiaHook.

Definition zesu_hist_def (P : Prop) : Prop := P.
Definition zesu_hist_aux : seal (@zesu_hist_def). Proof. by eexists. Qed.
Definition zesu_hist : Prop → Prop := zesu_hist_aux.(unseal).
Lemma zesu_hist_eq : zesu_hist = zesu_hist_def.
Proof. exact (seal_eq zesu_hist_aux). Qed.
Lemma zesu_hist_intro (P : Prop) : P → zesu_hist P.
Proof. by rewrite zesu_hist_eq. Qed.
Lemma zesu_hist_elim (P : Prop) : zesu_hist P → P.
Proof. by rewrite zesu_hist_eq. Qed.
#[global] Typeclasses Opaque zesu_hist.
#[global] Opaque zesu_hist.

(* A join's history: the dropped ghost binders and their facts under one
   existential. A fact with this head is hidden by the generator. *)
Definition zesu_join_history (P : Prop) : Prop := P.

(* One instance per successor edge: from the block entry's history and the new
   facts [N] (stated over the entry's ghost binders) follows the successor's
   history. *)
Class ZesuHistEdge {PROP : bi} (pre succ : Prop) (N : PROP) : Prop :=
  zesu_hist_edge : zesu_hist pre → N ⊢ ⌜zesu_hist succ⌝.
#[global] Hint Mode ZesuHistEdge + + + - : typeclass_instances.

(* Identity edge: the successor history is the block entry's history (a loop
   back edge on the class history, or an unchanged forward history). *)
Global Instance zesu_hist_edge_refl {PROP : bi} (P : Prop) :
  ZesuHistEdge (PROP := PROP) P P True | 0.
Proof. rewrite /ZesuHistEdge => Hh. iIntros "_". by iPureIntro. Qed.

Lemma tac_zesu_hist_edge {PROP : bi} Δ (pre succ : Prop) (N Q : PROP) :
  ZesuHistEdge pre succ N → zesu_hist pre →
  envs_entails Δ (N ∧ Q) → envs_entails Δ (⌜zesu_hist succ⌝ ∗ Q).
Proof.
  rewrite envs_entails_unseal => Hedge Hpre ->. iIntros "H".
  iAssert ⌜zesu_hist succ⌝%I as %Hs.
  { iApply (Hedge Hpre). by iDestruct "H" as "[H _]". }
  iSplit; first done. by iDestruct "H" as "[_ H]".
Qed.

(* A fact visible at a successor that the block's history holds (a loop exit
   reads it from the loop class history). *)
Class ZesuHistReveal (pre : Prop) (fact : Prop) :=
  zesu_hist_reveal : zesu_hist pre → fact.
#[global] Hint Mode ZesuHistReveal + + : typeclass_instances.

Lemma tac_zesu_hist_reveal {PROP : bi} Δ (pre F : Prop) (Q : PROP) :
  ZesuHistReveal pre F → zesu_hist pre →
  envs_entails Δ Q → envs_entails Δ (⌜F⌝ ∗ Q).
Proof.
  rewrite envs_entails_unseal => Hr Hpre ->. iIntros "H".
  iSplit; [iPureIntro; exact (Hr Hpre)|done].
Qed.

(* Guards of the two search steps: the goal is a history conjunct; some
   history is in the context. *)
Ltac zesu_hist_goal :=
  lazymatch goal with
  | |- envs_entails _ (bi_sep (bi_pure (zesu_hist _)) _) => idtac
  end.
Ltac zesu_hist_in_context :=
  match goal with
  | _ : zesu_hist _ |- _ => idtac
  end.

(* `⌜zesu_hist S⌝ ∗ Q`: the edge instance from a context history to [S]
   leaves its new facts [N] beside [Q]. *)
Ltac zesu_hist_step :=
  lazymatch goal with
  | |- envs_entails ?Δ (bi_sep (bi_pure (zesu_hist ?S)) ?Q) =>
      match goal with
      | Hh : zesu_hist ?P |- _ =>
          notypeclasses refine (tac_zesu_hist_edge Δ P S _ Q _ Hh _);
          [ solve [typeclasses eauto] | idtac ]
      end
  end.

(* `⌜F⌝ ∗ Q`: the reveal instance from a context history proves [F]. *)
Ltac zesu_hist_reveal_step :=
  lazymatch goal with
  | |- envs_entails ?Δ (bi_sep (bi_pure ?F) ?Q) =>
      match goal with
      | Hh : zesu_hist ?P |- _ =>
          notypeclasses refine (tac_zesu_hist_reveal Δ P F Q _ Hh _);
          [ solve [typeclasses eauto] | idtac ]
      end
  end.

(* A successor fact that elaborates a block-entry fact [H] (the guard, then its
   unsigned views): prove the guard by [H], the views from the decided guard.
   Used by generated edge proofs. *)
Ltac zesu_hist_view_fact H :=
  repeat match type of H with
  | bool_decide _ = true => apply bool_decide_eq_true_1 in H
  | negb (bool_decide _) = true => apply negb_true_iff, bool_decide_eq_false_1 in H
  end;
  rewrite ?zesu_signed_zero_extend_64_128 ?bv_signed_BV in H;
  repeat match type of H with
  | context [bv_swrap ?n ?z] =>
      (rewrite (bv_swrap_small n z) in H; [|unfold bv_half_modulus, bv_modulus; simpl; zesu_lia])
  end;
  try (lazymatch type of H with
       | @eq (bv _) _ _ => apply (f_equal bv_unsigned) in H;
                          repeat (rewrite bv_zero_extend_unsigned in H; [|zesu_lia]); rewrite ?bv_unsigned_BV in H
       end).

Ltac zesu_hist_view H :=
  let Hv := fresh "Hv" in
  pose proof H as Hv;
  first [ exact Hv
        | split; [exact Hv|];
          zesu_hist_view_fact Hv;
          repeat split;
          first [ assumption | zesu_lia
                | match goal with |- context [bv_unsigned ?x] =>
                    pose proof (bv_unsigned_in_range _ x); unfold bv_modulus in *; simpl in *; zesu_lia end ] ].

(* Block tail at a loop exit: a visible fact `guard /\ views` whose guard is a
   context fact; the views follow from the decided guard. *)
Ltac zesu_hist_exit_view :=
  lazymatch goal with
  | |- ?A /\ ?B =>
      let HA := fresh "HA" in
      assert A as HA by assumption; split; [exact HA|];
      zesu_hist_view_fact HA; repeat split; first [assumption | zesu_lia]
  end.

(* First-pass registration of a sealed loop class: the invariant split into the
   visible part [V] and the history part [H] (the class body is
   `resources ∗ ⌜V⌝ ∗ ⌜H⌝`). *)
Lemma zesu_loop_first_pass_intro_sealed {Sigma} {A B C D E : Type}
    (resources : A -> B -> C -> D -> E -> iProp Sigma)
    (V H : A -> B -> C -> D -> E -> Prop)
    (initial : Prop) (a : A) (b : B) (c : C) (d : D) (e : E)
    (derive : initial -> V a b c d e /\ H a b c d e) :
  resources a b c d e ∗ ⌜initial⌝ ⊢
  ∃ a' b' c' d' e', resources a' b' c' d' e' ∗ ⌜V a' b' c' d' e'⌝ ∗ ⌜H a' b' c' d' e'⌝.
Proof.
  iIntros "[Hresources %Hinitial]". destruct (derive Hinitial) as [HV HH].
  iExists a, b, c, d, e. iFrame. by iPureIntro.
Qed.
