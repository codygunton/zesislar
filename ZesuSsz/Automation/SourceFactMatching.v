Require Import ZesuSsz.Automation.All.
From iris.proofmode Require Import tactics environments.
From Coq Require Import Bool.Bool.
From stdpp Require Import decidable.

(* Select constrained values through source propositions, with correlated
   alternatives. Pure completion introduces no new arithmetic premise. *)
Ltac zesu_source_fact := first [solve [assumption] | solve [reflexivity] | lazymatch goal with | |- bool_decide ?fact = true => apply bool_decide_eq_true_2; zesu_source_fact | |- bool_decide ?fact = false => apply bool_decide_eq_false_2; zesu_source_fact | |- negb ?b = true => apply Bool.negb_true_iff; zesu_source_fact | |- ?a /\ ?b => split; zesu_source_fact end].

Ltac zesu_source_finish_package := lazymatch goal with | |- environments.envs_entails _ (@bi_pure _ _) => iPureIntro; zesu_source_fact | |- environments.envs_entails _ (@bi_sep _ _ _) => iSplit; zesu_source_finish_package end.

Ltac zesu_source_match_fact requested finish :=
  lazymatch requested with
  | bool_decide ?fact = true => zesu_source_match_fact fact finish
  | bool_decide ?fact = false => zesu_source_match_fact (~ fact) finish
  | negb (bool_decide ?fact) = true => zesu_source_match_fact (~ fact) finish
  | negb (bool_decide ?fact) = false => zesu_source_match_fact fact finish
  | ?left /\ ?right =>
      zesu_source_match_fact left
        ltac:(zesu_source_match_fact right finish)
  | _ =>
      tryif has_evar requested then
        multimatch goal with
        | source_fact : ?available |- _ =>
            assert_fails (has_evar available);
            unify requested available;
            finish
        end
      else
        let checked := fresh "HspatialConstraint" in
        assert (checked : requested) by
          (zesu_source_fact);
        clear checked; finish
  end.

Ltac zesu_source_match_tree requested finish :=
  lazymatch requested with
  | @bi_pure _ ?fact => zesu_source_match_fact fact finish
  | @bi_sep _ ?left ?right =>
      zesu_source_match_tree left
        ltac:(zesu_source_match_tree right finish)
  | _ => finish
  end.
