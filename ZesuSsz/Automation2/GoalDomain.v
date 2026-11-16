From stdpp Require Import bitvector.definitions bitvector.tactics.
Require Import ZesuSsz.Automation2.PureFacts.
Require Import ZesuSsz.Automation2.Rewrites.
From Coq Require Import ZArith Lia.

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

Ltac zesu_goal_domain_part :=
  first
    [lia
    |bv_solve
    |match goal with
     | |- context [bv_unsigned ?word] =>
         pose proof (bv_unsigned_in_range _ word);
         unfold bv_modulus in *; cbn [Z.of_N] in *; lia
     end].

(* An existential is refused before anything unfolds: its witnesses are not
   chosen here, so `split` cannot open it; only a contradictory context could
   close it, which `zesu_finish_lia` already tries just before. In 032c a callee
   precondition `∃ x13 … before, decodeItemCallDomain … ∧ decodeItemCallMeaning …`
   reached this step; opening and `cbn` on it reached 32 GiB. *)
Ltac zesu_finish_goal_domain :=
  let _ := constr:(_ : ZesuStepGoalDomain) in
  lazymatch goal with
  | |- @ex _ _ => fail 0 "The goal domain step does not choose witnesses."
  | |- _ => idtac
  end;
  solve [
    zesu_goal_domain_open; cbn;
    zesu_witness_facts;
    autounfold with zesu_contract_constants zesu_goal_domain in *;
    rewrite ?bv_add_unsigned;
    unfold bv_wrap, bv_modulus in *; cbn [Z.of_N] in *;
    repeat split; zesu_goal_domain_part].
