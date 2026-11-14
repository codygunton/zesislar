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
   `progress`. *)
Create HintDb zesu_goal_domain.

Class ZesuStepGoalDomain : Prop := zesu_step_goal_domain : True.

Ltac zesu_goal_domain_part :=
  first
    [lia
    |bv_solve
    |match goal with
     | |- context [bv_unsigned ?word] =>
         pose proof (bv_unsigned_in_range _ word);
         unfold bv_modulus in *; cbn [Z.of_N] in *; lia
     end].

Ltac zesu_finish_goal_domain :=
  let _ := constr:(_ : ZesuStepGoalDomain) in
  solve [
    progress (autounfold with zesu_goal_domain); cbn;
    zesu_witness_facts;
    autounfold with zesu_contract_constants zesu_goal_domain in *;
    rewrite ?bv_add_unsigned;
    unfold bv_wrap, bv_modulus in *; cbn [Z.of_N] in *;
    repeat split; zesu_goal_domain_part].
