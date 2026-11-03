From iris.proofmode Require Import tactics environments.
From Coq Require Import Bool.Bool.
From stdpp Require Import decidable.
From stdpp.bitvector Require Import definitions.

(* Select constrained values through source propositions, with correlated
   alternatives. Pure completion introduces no new arithmetic premise. *)
Ltac zesu_source_fact := first [solve [assumption] | solve [reflexivity] | lazymatch goal with | |- bool_decide ?fact = true => apply bool_decide_eq_true_2; zesu_source_fact | |- bool_decide ?fact = false => apply bool_decide_eq_false_2; zesu_source_fact | |- negb ?b = true => apply Bool.negb_true_iff; zesu_source_fact | |- ?a /\ ?b => split; zesu_source_fact | |- Z.le Z0 (@bv_unsigned ?width ?value) => assert_fails (has_evar value); exact (proj1 (bv_unsigned_in_range width value)) | |- Z.lt (@bv_unsigned ?width ?value) ?bound => assert_fails (has_evar value); assert_fails (has_evar bound); exact (proj2 (bv_unsigned_in_range width value)) | |- ?fact => let exposed := eval hnf in fact in lazymatch exposed with | ?left /\ ?right => change exposed; split; zesu_source_fact end end].

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

(* Check fixed facts before any source-value alternatives can branch. *)
Ltac zesu_source_check_fixed_fact requested :=
  lazymatch requested with
  | bool_decide ?fact = true => zesu_source_check_fixed_fact fact
  | bool_decide ?fact = false => zesu_source_check_fixed_fact (~ fact)
  | negb (bool_decide ?fact) = true => zesu_source_check_fixed_fact (~ fact)
  | negb (bool_decide ?fact) = false => zesu_source_check_fixed_fact fact
  | ?left /\ ?right =>
      zesu_source_check_fixed_fact left; zesu_source_check_fixed_fact right
  | _ =>
      tryif has_evar requested then idtac
      else
        let checked := fresh "HsourceFixedConstraint" in
        tryif (assert (checked : requested) by zesu_source_fact)
        then clear checked
        else fail 0 "Unsupported fixed source fact:" requested
  end.

Ltac zesu_source_check_fixed_tree requested :=
  lazymatch requested with
  | @bi_pure _ ?fact => zesu_source_check_fixed_fact fact
  | @bi_sep _ ?left ?right =>
      zesu_source_check_fixed_tree left; zesu_source_check_fixed_tree right
  | _ => idtac
  end.
