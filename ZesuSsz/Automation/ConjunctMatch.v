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


Require Import ZesuSsz.Automation.EntryIntro.

Ltac zesu_qualify_context_fact_head premise_solver head available :=
  zesu_cached_entry_fact_head head.

(* Read closed context facts without assigning a requested root. *)
Ltac zesu_pure_head head_term :=
  lazymatch head_term with
  | ?function ?argument => zesu_pure_head function
  | _ => head_term
  end.

(* An implication is eligible only after its conclusion has a cached head. *)
Ltac zesu_cached_conclusion_head requested available :=
  first
    [let wanted := zesu_pure_head requested in
     let found := zesu_pure_head available in
     constr_eq wanted found;
     zesu_cached_entry_fact_head wanted
    | lazymatch available with
      | ?left /\ ?right => first
          [zesu_cached_conclusion_head requested left
          |zesu_cached_conclusion_head requested right]
      | _ -> ?tail => zesu_cached_conclusion_head requested tail
      end].

(* The marker retains the actual proof returned by the registered bridge. *)
Inductive ZesuConjunctPremiseApplied (premise : Prop) (evidence : premise) : Prop :=
  ZesuConjunctPremiseWasProved.

Ltac zesu_with_conjunct_premise premise_solver premise continuation :=
  lazymatch goal with
  | _ : @ZesuConjunctPremiseApplied premise ?proof |- _ =>
      assert_fails (has_evar proof);
      continuation proof
  | _ =>
      let proof := premise_solver premise in
      let proof_type := type of proof in
      assert_fails (has_evar proof);
      assert_fails (has_evar proof_type);
      let marker := fresh "HconjunctPremiseApplied" in
      pose proof (@ZesuConjunctPremiseWasProved premise proof) as marker;
      continuation proof
  end.

Ltac zesu_context_pure_leaf premise_solver requested evidence continuation :=
  let available := type of evidence in
  first [
    assert_fails (has_evar available);
    let wanted_head := zesu_pure_head requested in
    let available_head := zesu_pure_head available in
    assert_fails (is_var wanted_head);
    assert_fails (is_var available_head);
    constr_eq wanted_head available_head;
    zesu_qualify_context_fact_head premise_solver wanted_head available;
    assert_fails (assert_fails (unify requested available));
    continuation available evidence
  | lazymatch available with
    | ?left /\ ?right =>
        first [
          let proof := constr:(proj1 evidence) in
          zesu_context_pure_leaf premise_solver requested proof continuation
        | let proof := constr:(proj2 evidence) in
          zesu_context_pure_leaf premise_solver requested proof continuation]
    | ?premise -> ?conclusion =>
        zesu_cached_conclusion_head requested conclusion;
        assert_fails (has_evar premise);
        zesu_with_conjunct_premise premise_solver premise
          ltac:(fun premise_proof =>
            let proof := constr:(evidence premise_proof) in
            zesu_context_pure_leaf premise_solver requested proof continuation)
    end].

(* Reject different concrete arguments before assigning any requested root. *)
Ltac zesu_match_context_pure_head premise_solver requested :=
  has_evar requested;
  multimatch goal with
  | H : _ |- _ =>
      zesu_context_pure_leaf premise_solver requested H
        ltac:(fun available evidence =>
          tryif (multimatch goal with
            | Hother : _ |- _ =>
                zesu_context_pure_leaf premise_solver requested Hother
                  ltac:(fun other _ => assert_fails (constr_eq available other))
            end)
          then fail 100 "Different context facts match the requested head."
          else unify requested available)
  end.

Ltac zesu_match_pure_conjunct_heads premise_solver requested :=
  lazymatch requested with
  | ?left /\ ?right =>
      try zesu_match_pure_conjunct_heads premise_solver left;
      try zesu_match_pure_conjunct_heads premise_solver right
  | _ => try zesu_match_context_pure_head premise_solver requested
  end.

Ltac zesu_match_resource_pure_heads premise_solver fuel requested :=
  lazymatch requested with
  | @bi_pure _ ?fact => zesu_match_pure_conjunct_heads premise_solver fact
  | @bi_sep _ ?left ?right =>
      zesu_match_resource_pure_heads premise_solver fuel left;
      zesu_match_resource_pure_heads premise_solver fuel right
  | _ =>
      lazymatch fuel with
      | S ?remaining =>
          try (let head := zesu_pure_head requested in
            assert_fails (is_var head);
            assert_fails (has_evar head);
            let expanded := eval cbv beta iota delta [head] in requested in
            assert_fails (constr_eq requested expanded);
            zesu_match_resource_pure_heads premise_solver remaining expanded)
      | O => idtac
      end
  end.
