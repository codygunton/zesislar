From stdpp Require Import bitvector.definitions bitvector.tactics.
Require Import ZesuSsz.Automation2.PureFacts.
Require Import ZesuSsz.Automation2.Rewrites.
From Coq Require Import ZArith Lia.
Require Import ZesuSsz.Automation2.LiaHook.
Require ZesuSsz.Automation2.Hooks.

(* A pure goal whose head a contract registers in `zesu_goal_domain`: a
   callee's call-site domain that is a conjunction of address arithmetic
   (lengths, ranges, separations) over the caller's own domain. The step
   unfolds the registered heads in the goal and in the context, splits the
   conjunctions, and closes every part with `lia` or `bv_solve` over the
   bitvector images. `solve` keeps it all-or-nothing: a goal it cannot close
   stays exactly as it was. A goal with no registered head costs one failed
   `progress`.

   A proved callee's call-site domain is sealed (ZesuSsz/Interfaces/<F>.v):
   the step never unfolds it. Its interface registers the lemma that
   introduces it from the callee's stated precondition as a
   `ZesuGoalDomainIntro` instance, and the precondition's public names in
   `zesu_goal_domain`; the step applies the lemma, then unfolds the
   precondition. *)
Create HintDb zesu_goal_domain.

Class ZesuStepGoalDomain : Prop := zesu_step_goal_domain : True.

Class ZesuGoalDomainIntro (goal premise : Prop) : Prop :=
  zesu_goal_domain_intro : premise -> goal.
#[global] Hint Mode ZesuGoalDomainIntro ! - : typeclass_instances.

(* Apply the registered introduction of a sealed domain and unfold the
   precondition it leaves; or unfold a registered head. The introduction
   comes first: unfolding the arguments of a sealed domain is progress that
   leaves the domain sealed. *)
Ltac zesu_goal_domain_open :=
  first
    [lazymatch goal with
     | |- ?goal =>
         let premise := fresh "premise" in
         evar (premise : Prop);
         let intro := fresh "intro" in
         assert (intro : ZesuGoalDomainIntro goal premise) by (unfold premise; typeclasses eauto);
         unfold premise in intro; clear premise;
         apply intro; clear intro;
         progress (autounfold with zesu_goal_domain)
     end
    |progress (autounfold with zesu_goal_domain)].

(* The goal is a sealed callee domain: it has a registered introduction.
   Such a goal is opaque to every solver; `lia` or `bv_solve` on it only
   search the context for a contradiction, which on a large context does not
   end (Finish.v runs the introduction instead). *)
Ltac zesu_goal_domain_sealed :=
  lazymatch goal with
  | |- ?goal =>
      assert_succeeds (
        let premise := fresh "premise" in
        evar (premise : Prop);
        let intro := fresh "intro" in
        assert (intro : ZesuGoalDomainIntro goal premise)
          by (unfold premise; typeclasses eauto))
  end.

(* lia and bv_solve never close an existential, nor a witness that `split`
   leaves as a goal of a type such as `bv 64`: on a large context they only
   search the whole context for a contradiction (a call's precondition
   restated over fresh names, 274 hypotheses: lia on its first witness grew
   past 8 GiB). *)
Ltac zesu_final_solver_goal :=
  lazymatch goal with
  | |- ex _ => fail 0
  | |- ?target => lazymatch type of target with Prop => idtac end
  end.

(* bv_solve only on a conjunct that reads a bit-vector: on one without (a
   list length) it can only refute the whole context. *)
Ltac zesu_goal_domain_part :=
  zesu_final_solver_goal;
  first
    [zesu_lia
    |lazymatch goal with |- context [bv_unsigned _] => bv_solve end
    |match goal with
     | |- context [bv_unsigned ?word] =>
         pose proof (bv_unsigned_in_range _ word);
         unfold bv_modulus in *; cbn [Z.of_N] in *; zesu_lia
     end].

(* An existential goal is refused before anything is unfolded: every part
   of it would be a witness or an existential. *)
Ltac zesu_finish_goal_domain :=
  let _ := constr:(_ : ZesuStepGoalDomain) in
  zesu_final_solver_goal;
  solve [
    zesu_goal_domain_open; cbn;
    zesu_witness_facts;
    autounfold with zesu_contract_constants zesu_goal_domain in *;
    (* one normal form of the machine map in the goal and the hypotheses:
       `cbn` above reduced the goal's `mapRamBase defaultMap` to its value,
       a hypothesis that states the same bound keeps the projection, and
       lia would see two atoms *)
    ZesuSsz.Automation2.Hooks.zesu_normalize_machine_map;
    rewrite ?bv_add_unsigned;
    unfold bv_wrap, bv_modulus in *; cbn [Z.of_N] in *;
    repeat split; zesu_goal_domain_part].
