From iris.proofmode Require Import proofmode environments reduction.
From iris.base_logic Require Import iprop.
Set Default Proof Mode "Classic".

(* Pure facts of an opaque resource as plain facts.

   A sealed resource (an allocator's block token, say) may carry a pure
   conjunct in its definition. Lithium keeps the resource folded, so the
   solvers and the residual exporter never see that fact. A module that
   seals such a resource registers its fact once, as a
   `ZesuFactView R P` instance (`R ⊢ R ∗ ⌜P⌝`). The fact is posed as a
   hypothesis whenever an instance's resource enters the spatial context:
   at the block entry (`zesu_pose_fact_views`) and when Lithium introduces
   it (`liWand` in `Hooks.v`, through `tac_zesu_fact_view_intro`). The resource
   stays in the context unchanged. *)

Class ZesuFactView {PROP : bi} (resource : PROP) (fact : Prop) : Prop :=
  zesu_fact_view : resource ⊢ resource ∗ ⌜fact⌝.

(* The lookup is indexed by the resource: a resource whose head has no
   instance fails at once. *)
Global Hint Mode ZesuFactView - ! - : typeclass_instances.

(* Stated for `iProp`, whose affinity the pose lemma uses: Lithium's goals
   are `iProp`, and the tactics below apply these lemmas without a type
   class search. *)
Section fact_views.
  Context {Σ : gFunctors}.

  (* A held resource with a view: its fact is a hypothesis. *)
  Lemma tac_zesu_fact_view_pose Δ i p (resource : iProp Σ) (fact : Prop) Q :
    envs_lookup i Δ = Some (p, resource) →
    ZesuFactView resource fact →
    (fact → envs_entails Δ Q) →
    envs_entails Δ Q.
  Proof.
    rewrite envs_entails_unseal => Hlookup view HQ.
    apply (bi.pure_elim fact); [|exact HQ].
    rewrite envs_lookup_sound // bi.intuitionistically_if_elim view.
    iIntros "[[_ %Hfact] _]". done.
  Qed.

  (* Lithium's introduction of a resource with a view: the resource enters
     the context and its fact follows as a pure premise. *)
  Lemma tac_zesu_fact_view_intro (resource : iProp Σ) (fact : Prop) Δ T :
    ZesuFactView resource fact →
    envs_entails Δ (resource -∗ ⌜fact⌝ -∗ T) →
    envs_entails Δ (resource -∗ T).
  Proof.
    rewrite envs_entails_unseal => view ->.
    iIntros "HT Hresource".
    iDestruct (@zesu_fact_view _ _ _ view with "Hresource") as "[Hresource %Hfact]".
    iApply ("HT" with "Hresource"). done.
  Qed.
End fact_views.

Ltac zesu_fact_view_head term :=
  lazymatch term with
  | ?f _ => zesu_fact_view_head f
  | _ => term
  end.

(* Runs `k view fact` with the registered fact of `resource`, or fails. Only
   a resource whose head is a constant is looked up. *)
Ltac zesu_fact_view_with resource k :=
  let head := zesu_fact_view_head resource in
  is_const head;
  let view := constr:(_ : ZesuFactView resource _) in
  lazymatch type of view with
  | ZesuFactView _ ?fact => k view fact
  end.

(* Fails when `fact` is already a hypothesis. *)
Ltac zesu_fact_view_new fact :=
  assert_fails (has_evar fact);
  lazymatch goal with
  | _ : fact |- _ => fail
  | _ => idtac
  end.

(* Every held resource with a view whose fact is not a hypothesis yet:
   pose the fact. Idempotent. *)
Ltac zesu_pose_fact_views :=
  repeat (
    iMatchHyp ltac:(fun H resource =>
      zesu_fact_view_with resource ltac:(fun view fact =>
        zesu_fact_view_new fact;
        notypeclasses refine (tac_zesu_fact_view_pose _ H _ resource fact _ _ view _);
        [pm_reflexivity | intros ?]))).

(* Guarded pure facts as plain facts.

   A context fact may be guarded, `A -> B`, when it holds only on one
   outcome of a call (a window of a returned payload, say, that holds when
   the outcome's success test passed). Once the guard `A` is itself a
   hypothesis (the block's path took that branch), `B` is posed, and the
   components of a conjunction `B` as well, so a step that looks for one of
   them by its shape finds it. The guard is matched against the hypotheses
   syntactically: no search and no solver. A chain `A1 -> A2 -> B` is
   specialised one premise per round. Idempotent: a conclusion already a
   hypothesis is not posed again. *)
Ltac zesu_guarded_fact_components H :=
  lazymatch type of H with
  | ?P /\ ?Q =>
      let H1 := fresh "HguardedFact" in
      let H2 := fresh "HguardedFact" in
      pose proof (proj1 H) as H1; pose proof (proj2 H) as H2;
      zesu_guarded_fact_components H1; zesu_guarded_fact_components H2
  | _ => idtac
  end.

Ltac zesu_specialise_guarded_facts :=
  repeat match goal with
  | H : ?A -> ?B, Ha : ?A |- _ =>
      lazymatch type of B with Prop => idtac end;
      zesu_fact_view_new B;
      let Hb := fresh "HguardedFact" in
      pose proof (H Ha) as Hb;
      zesu_guarded_fact_components Hb
  end.
