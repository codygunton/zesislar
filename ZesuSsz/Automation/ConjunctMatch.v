(* Match one owned conjunct. This step does not open a spatial resource. *)
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.ResourceGroups.
From iris.proofmode Require Import environments base coq_tactics reduction ltac_tactics.

Class ZesuStepConjunctMatch : Prop := zesu_step_conjunct_match : True.

Ltac zesu_match_owned_conjunct_in spatial left :=
  lazymatch spatial with
  | Esnoc ?rest ?H ?body =>
      first
        [unify body left;
         eapply tac_sep_split with Left [H] _ _;
           [tc_solve | pm_reduce; split; [iExact H |]]
        | zesu_match_owned_conjunct_in rest left]
  | _ => fail 0 "The matcher found no spatial resource."
  end.

Ltac zesu_match_owned_conjunct :=
  lazymatch goal with
  | |- envs_entails ?Delta (?left ∗ _)%I =>
      assert_fails (has_evar left);
      let spatial := eval cbn [env_spatial] in (env_spatial Delta) in
      zesu_match_owned_conjunct_in spatial left
  end.

Ltac zesu_conjunct_match_if_enabled :=
  lazymatch goal with
  | |- envs_entails _ (_ ∗ _)%I =>
      let _ := constr:(_ : ZesuRuleSetV2) in
      let _ := constr:(_ : ZesuStepConjunctMatch) in
      zesu_expose_environment_alias;
      cbn beta zeta;
      first
        [zesu_match_owned_conjunct
        | lazymatch goal with
          | |- envs_entails _ ((_ ∗ _) ∗ _)%I =>
              iEval (rewrite -bi.sep_assoc)
          end]
  end.
