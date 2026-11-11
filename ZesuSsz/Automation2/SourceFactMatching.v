Require ZesuSsz.Automation.Hooks.
Require isla.automation.
Require Import ZesuSsz.Automation2.ResourceGroups.
From iris.proofmode Require Import intro_patterns.
Require Import ZesuSsz.Automation2.ContextRange.
Require Import ZesuSsz.Automation2.ArrayByteValues.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.VmClosed.
Require ZesuSsz.Automation2.ResidualLemmas.
From Coq Require Import Lia.
Require Coq.ZArith.Zbitwise.
From iris.proofmode Require Import tactics environments.
From Coq Require Import Bool.Bool.
From stdpp Require Import decidable.
From stdpp.bitvector Require Import definitions.

(* Select constrained values through source propositions, with correlated
   alternatives. Pure completion introduces no new arithmetic premise. *)

Ltac zesu_source_signed_lookup :=
  lazymatch goal with
  | |- (bv_signed (bv_sign_extend ?wide (bv_sign_extend ?middle ?byte)) < bv_signed ?zero)%Z =>
    assert_fails (has_evar byte);
    is_closed_term wide; is_closed_term middle;
    multimatch goal with
    | Hsource : (bv_signed (bv_sign_extend wide (bv_sign_extend middle ?loaded)) < bv_signed zero)%Z |- _ =>
      let equality := fresh "HsourceLoadedByte" in
      assert (equality : loaded = byte) by
        ArrayByteValues.zesu_finish_array_byte_lookup_if_closed;
      let transported := fresh "HsourceSignedByte" in
      pose proof Hsource as transported;
      rewrite equality in transported;
      exact transported
    end
  end.





Ltac zesu_source_signed_lookup_lower :=
 lazymatch goal with
 | |- (?threshold <= bv_unsigned ?byte)%Z =>
   assert_fails (has_evar byte);
   multimatch goal with
   | Hsource : (bv_signed (bv_sign_extend ?wide (bv_sign_extend ?middle ?loaded)) < bv_signed ?zero)%Z |- _ =>
     let transported := fresh "HsignedLookupLower" in
     assert (transported : (bv_signed (bv_sign_extend wide (bv_sign_extend middle byte)) < bv_signed zero)%Z) by
       zesu_source_signed_lookup;
     BitvectorFacts.zesu_source_signed_lower
   end
 end.





(* Retained order facts can use either standard integer presentation. *)
Ltac zesu_source_retained_order :=
  first [
    lazymatch goal with
    | |- Z.ge (bv_unsigned ?left) (bv_unsigned ?right) =>
        assert_fails (has_evar left);
        assert_fails (has_evar right);
        multimatch goal with
        | retained : not (Z.lt (bv_signed (bv_zero_extend 128 left))
                         (bv_signed (bv_zero_extend 128 right))) |- _ =>
            let view := fresh "HretainedUnsignedOrder" in
            pose proof retained as view;
            rewrite !BitvectorFacts.zesu_signed_zero_extend_64_128 in view;
            apply Z.nlt_ge in view;
            apply Z.le_ge; exact view
        | retained : Z.ge (bv_signed (bv_zero_extend 128 left))
                          (bv_signed (bv_zero_extend 128 right)) |- _ =>
            let view := fresh "HretainedUnsignedOrder" in
            pose proof retained as view;
            rewrite !BitvectorFacts.zesu_signed_zero_extend_64_128 in view;
            exact view
        end
    | |- Z.le (bv_unsigned ?right) (bv_unsigned ?left) =>
        assert_fails (has_evar left);
        assert_fails (has_evar right);
        multimatch goal with
        | retained : not (Z.lt (bv_signed (bv_zero_extend 128 left))
                         (bv_signed (bv_zero_extend 128 right))) |- _ =>
            let view := fresh "HretainedUnsignedOrder" in
            pose proof retained as view;
            rewrite !BitvectorFacts.zesu_signed_zero_extend_64_128 in view;
            apply Z.nlt_ge in view; exact view
        | retained : Z.ge (bv_signed (bv_zero_extend 128 left))
                          (bv_signed (bv_zero_extend 128 right)) |- _ =>
            let view := fresh "HretainedUnsignedOrder" in
            pose proof retained as view;
            rewrite !BitvectorFacts.zesu_signed_zero_extend_64_128 in view;
            apply Z.ge_le; exact view
        end
    end |
    lazymatch goal with
    | |- Z.ge ?left ?right =>
        assert_fails (has_evar left);
        assert_fails (has_evar right);
        apply Z.le_ge; assumption
    | |- Z.le ?left ?right =>
        assert_fails (has_evar left);
        assert_fails (has_evar right);
        apply Z.ge_le; assumption
    end ].

(* A fact that reads a byte through `nth`, with the lookup of the same list
   and index in the context, is a fact about the lookup value. A strict upper
   bound `bound > value` becomes `value <= bound - 1` for the bound closers. *)
Ltac zesu_source_array_byte_nth close :=
  ArrayByteValues.zesu_rewrite_array_byte_nth_if_closed;
  first [close tt |
    lazymatch goal with
    | |- Z.gt ?bound ?value =>
        VmClosed.zesu_vm_closed bound;
        let ceiling := VmClosed.zesu_vm_eval_closed (Z.pred bound) in
        apply Z.lt_gt; apply (Z.le_lt_trans value ceiling bound);
        [close tt | VmClosed.zesu_vm_closed_decide]
    end].

Ltac zesu_source_fact := first [solve [assumption] | solve [reflexivity] |
 solve [zesu_source_retained_order] |
  lazymatch goal with
  | |- context [bv_unsigned (Z_to_bv ?width ?value)] =>
      assert_fails (has_evar value);
      let range := fresh "HsourceCastRange" in
      assert (range : (0 <= value < bv_modulus width)%Z) by
        ContextRange.zesu_hypothesis_cast_range_fact width value;
      rewrite (Z_to_bv_small width value range); clear range;
      zesu_source_fact
  end |
  solve [BitvectorFacts.zesu_source_unsigned_bound] |
  solve [BitvectorFacts.zesu_source_signed_lower] |
  solve [zesu_source_signed_lookup_lower] |
  solve [zesu_source_signed_lookup] |
  solve [zesu_source_array_byte_nth ltac:(fun _ => zesu_source_fact)] |
  solve [BitvectorFacts.zesu_source_signed_upper] | lazymatch goal with
| |- Z.ge (@bv_unsigned ?width ?value) Z0 =>
    apply Z.le_ge; exact (proj1 (bv_unsigned_in_range width value))
| |- Z.ge (@bv_unsigned ?width ?value) (@bv_unsigned ?closedWidth ?closedValue) =>
    assert_fails (has_evar closedValue);
    VmClosed.zesu_vm_closed closedValue;
    let reduced := eval cbv in (@bv_unsigned closedWidth closedValue) in
    constr_eq reduced Z0;
    apply Z.le_ge; change (Z.le reduced (@bv_unsigned width value));
    zesu_source_fact
| |- Z.le (@bv_unsigned ?closedWidth ?closedValue) (@bv_unsigned ?width ?value) =>
    assert_fails (has_evar closedValue);
    VmClosed.zesu_vm_closed closedValue;
    let reduced := eval cbv in (@bv_unsigned closedWidth closedValue) in
    constr_eq reduced Z0;
    change (Z.le reduced (@bv_unsigned width value));
    zesu_source_fact
end
 | lazymatch goal with
| |- Z.le ?value ?bound =>
    assert_fails (has_evar bound);
    VmClosed.zesu_vm_closed bound;
    let normalized := eval cbv in bound in
    assert_fails (constr_eq bound normalized);
    change (Z.le value normalized); zesu_source_fact
| |- Z.lt ?value ?bound =>
    assert_fails (has_evar bound);
    VmClosed.zesu_vm_closed bound;
    let normalized := eval cbv in bound in
    assert_fails (constr_eq bound normalized);
    change (Z.lt value normalized); zesu_source_fact
end
 | lazymatch goal with
| |- Z.le (bv_unsigned (bv_and ?value ?mask)) ?bound =>
    assert_fails (has_evar mask);
    assert_fails (has_evar bound);
    VmClosed.zesu_vm_closed mask;
    VmClosed.zesu_vm_closed bound;
    let Hbound := fresh "HclosedMaskBound" in
    assert (Hbound : (bv_unsigned mask <= bound)%Z) by
      (vm_compute; congruence);
    rewrite bv_and_unsigned; rewrite Z.land_comm;
    let Hremaining := fresh "HmaskRemainder" in
    assert (Hremaining :
      (0 <= bv_unsigned mask - Z.land (bv_unsigned mask) (bv_unsigned value))%Z) by
      (rewrite Coq.ZArith.Zbitwise.Z.sub_land_same_l; apply Z.land_nonneg;
       left; exact (proj1 (bv_unsigned_in_range _ mask)));
    clear -Hbound Hremaining; lia
| |- Z.lt (bv_unsigned (bv_and ?value ?mask)) ?bound =>
    assert_fails (has_evar mask);
    assert_fails (has_evar bound);
    VmClosed.zesu_vm_closed mask;
    VmClosed.zesu_vm_closed bound;
    let Hbound := fresh "HclosedMaskBound" in
    assert (Hbound : (bv_unsigned mask < bound)%Z) by
      (vm_compute; congruence);
    rewrite bv_and_unsigned; rewrite Z.land_comm;
    let Hremaining := fresh "HmaskRemainder" in
    assert (Hremaining :
      (0 <= bv_unsigned mask - Z.land (bv_unsigned mask) (bv_unsigned value))%Z) by
      (rewrite Coq.ZArith.Zbitwise.Z.sub_land_same_l; apply Z.land_nonneg;
       left; exact (proj1 (bv_unsigned_in_range _ mask)));
    clear -Hbound Hremaining; lia
end
 | lazymatch goal with | |- bool_decide ?fact = true => apply bool_decide_eq_true_2; zesu_source_fact | |- bool_decide ?fact = false => apply bool_decide_eq_false_2; zesu_source_fact | |- negb ?b = true => apply Bool.negb_true_iff; zesu_source_fact | |- ?a /\ ?b => split; zesu_source_fact | |- Z.le Z0 (@bv_unsigned ?width ?value) => assert_fails (has_evar value); exact (proj1 (bv_unsigned_in_range width value)) | |- Z.lt (@bv_unsigned ?width ?value) ?bound => assert_fails (has_evar value); assert_fails (has_evar bound); exact (proj2 (bv_unsigned_in_range width value)) | |- ?fact => let exposed := eval hnf in fact in lazymatch exposed with | ?left /\ ?right => change exposed; split; zesu_source_fact end end |
  (* A fact that no source closer proves, such as a merge-point meaning fact,
     gets the block's residual lemmas before the package fails. Without this,
     a failed fixed-fact check saturates the whole context and retries. *)
  ZesuSsz.Automation2.ResidualLemmas.zesu_residual_lemma].

Ltac zesu_source_finish_package :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_pure _ _) =>
      iPureIntro; zesu_source_fact
  | |- environments.envs_entails _ (@bi_sep _ _ _) =>
      iSplit; zesu_source_finish_package
  | |- environments.envs_entails _ (@big_opL _ (@bi_sep _) _ _ _ nil) =>
      rewrite big_sepL_nil; iEmpIntro
  | |- environments.envs_entails _ (@bi_emp _) => iEmpIntro
  end.

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
            let available_sort := type of available in
            lazymatch available_sort with Prop => idtac
            | _ => fail 0 "The source candidate is not a proposition." end;
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

(* The same walk, but a fixed fact that the source closers cannot prove does
   not stop the package. The residual tier gets one attempt. If it fails, the
   fact becomes its own goal on the shelf, and the package continues with the
   fact as a hypothesis. A fact with an evar is left to the matching step, so
   the witnesses are chosen as before. The caller must unshelve. *)
Ltac zesu_source_defer_fixed_fact requested :=
  lazymatch requested with
  | bool_decide ?fact = true => zesu_source_defer_fixed_fact fact
  | bool_decide ?fact = false => zesu_source_defer_fixed_fact (~ fact)
  | negb (bool_decide ?fact) = true => zesu_source_defer_fixed_fact (~ fact)
  | negb (bool_decide ?fact) = false => zesu_source_defer_fixed_fact fact
  | ?left /\ ?right =>
      zesu_source_defer_fixed_fact left; zesu_source_defer_fixed_fact right
  | _ =>
      tryif has_evar requested then idtac
      else
        let checked := fresh "HsourceFixedConstraint" in
        tryif (assert (checked : requested) by zesu_source_fact)
        then clear checked
        else
          let deferred := fresh "HdeferredFact" in
          first [assert (deferred : requested) by
                   ZesuSsz.Automation2.ResidualLemmas.zesu_residual_lemma
                | assert (deferred : requested); [shelve | ]]
  end.

Ltac zesu_source_defer_fixed_tree requested :=
  lazymatch requested with
  | @bi_pure _ ?fact => zesu_source_defer_fixed_fact fact
  | @bi_sep _ ?left ?right =>
      zesu_source_defer_fixed_tree left; zesu_source_defer_fixed_tree right
  | _ => idtac
  end.

(* Traverse only the requested disjunction. Each registered leaf must close. *)
Ltac zesu_source_registered_disjunction_tree close :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_or _ _ _) =>
      first
        [ solve [iLeft; zesu_source_registered_disjunction_tree close]
        | solve [iRight; zesu_source_registered_disjunction_tree close] ]
  | |- environments.envs_entails _ (@bi_sep _ (@bi_or _ _ _) _) =>
      rewrite bi.sep_or_r;
      zesu_source_registered_disjunction_tree close
  | |- environments.envs_entails _ (@bi_sep _ ?target ?frame) =>
      let evidence := constr:(_ : ZesuSsz.Automation.Hooks.ZesuPureFactIntro target _) in
      assert_fails (has_evar evidence);
      lazymatch type of evidence with
      | ZesuSsz.Automation.Hooks.ZesuPureFactIntro _ ?source =>
          iApply (bi.sep_mono_l source frame target
            (@ZesuSsz.Automation.Hooks.zesu_pure_fact_intro _ target source evidence));
          try rewrite bi.sep_exist_r;
          solve [close]
      end
  | |- environments.envs_entails _ ?target =>
      let evidence := constr:(_ : ZesuSsz.Automation.Hooks.ZesuPureFactIntro target _) in
      assert_fails (has_evar evidence);
      lazymatch type of evidence with
      | ZesuSsz.Automation.Hooks.ZesuPureFactIntro _ ?source =>
          iApply (@ZesuSsz.Automation.Hooks.zesu_pure_fact_intro _ target source evidence);
          solve [close]
      end
  end.

(* A heterogeneous tuple retains the first path for each exact registered source. *)
Ltac zesu_source_candidate_contains candidates key :=
  lazymatch candidates with
  | tt => fail 0
  | ((?path, ?previous), ?rest) =>
      first [constr_eq_strict key previous | zesu_source_candidate_contains rest key]
  end.

Ltac zesu_source_candidate_append candidates candidate :=
  lazymatch candidates with
  | tt => constr:((candidate, tt))
  | (?head, ?rest) =>
      let tail := zesu_source_candidate_append rest candidate in
      constr:((head, tail))
  end.

Ltac zesu_source_candidate_key requested :=
  lazymatch requested with
  | @bi_sep _ ?target ?frame =>
      let evidence := constr:(_ : ZesuSsz.Automation.Hooks.ZesuPureFactIntro target _) in
      lazymatch type of evidence with
      | ZesuSsz.Automation.Hooks.ZesuPureFactIntro _ ?source => constr:((source ∗ frame)%I)
      end
  | ?target =>
      let evidence := constr:(_ : ZesuSsz.Automation.Hooks.ZesuPureFactIntro target _) in
      lazymatch type of evidence with
      | ZesuSsz.Automation.Hooks.ZesuPureFactIntro _ ?source => source
      end
  end.

Ltac zesu_source_collect_candidates requested path candidates continuation :=
  lazymatch requested with
  | @bi_or _ ?left ?right =>
      let left_path := eval cbv in (@List.app bool path (cons false nil)) in
      let right_path := eval cbv in (@List.app bool path (cons true nil)) in
      zesu_source_collect_candidates left left_path candidates
        ltac:(fun previous => zesu_source_collect_candidates right right_path previous continuation)
  | @bi_sep _ (@bi_or _ ?left ?right) ?frame =>
      let left_path := eval cbv in (@List.app bool path (cons false nil)) in
      let right_path := eval cbv in (@List.app bool path (cons true nil)) in
      let left_goal := constr:((left ∗ frame)%I) in
      let right_goal := constr:((right ∗ frame)%I) in
      zesu_source_collect_candidates left_goal left_path candidates
        ltac:(fun previous => zesu_source_collect_candidates right_goal right_path previous continuation)
  | _ =>
      tryif (let key := zesu_source_candidate_key requested in assert_fails (has_evar key))
      then
        let key := zesu_source_candidate_key requested in
        tryif zesu_source_candidate_contains candidates key
        then continuation candidates
        else let updated := zesu_source_candidate_append candidates constr:((path, key)) in
          continuation updated
      else continuation candidates
  end.

Ltac zesu_source_select_candidate_path path :=
  lazymatch path with
  | nil => idtac
  | cons ?direction ?rest =>
      lazymatch goal with
      | |- environments.envs_entails _ (@bi_sep _ (@bi_or _ _ _) _) => rewrite bi.sep_or_r
      | _ => idtac
      end;
      lazymatch direction with false => iLeft | true => iRight end;
      zesu_source_select_candidate_path rest
  end.

Ltac zesu_source_try_candidates candidates close :=
  lazymatch candidates with
  | tt => fail 0
  | ((?path, ?key), ?rest) =>
      first [solve [zesu_source_select_candidate_path path;
                    zesu_source_registered_disjunction_tree close]
            | zesu_source_try_candidates rest close]
  end.

Ltac zesu_source_registered_disjunction close :=
  lazymatch goal with
  | |- environments.envs_entails _ ?requested =>
      lazymatch requested with
      | @bi_or _ _ _ => idtac
      | @bi_sep _ (@bi_or _ _ _) _ => idtac
      end;
      zesu_source_collect_candidates requested constr:(@nil bool) constr:(tt)
        ltac:(fun candidates => once (zesu_source_try_candidates candidates close))
  end.

Ltac zesu_source_registered_tree target :=
  lazymatch target with
  | @bi_or _ ?left ?right =>
      zesu_source_registered_tree left;
      zesu_source_registered_tree right
  | _ =>
      let evidence := constr:(_ : ZesuSsz.Automation.Hooks.ZesuPureFactIntro target _) in
      assert_fails (has_evar evidence)
  end.

Ltac zesu_source_open_registered_tree name body :=
  lazymatch body with
  | @bi_or _ ?left ?right =>
      let branch := iFresh in
      let pattern := constr:(IList (cons (cons (IIdent branch) nil)
        (cons (cons (IIdent branch) nil) nil))) in
      iDestruct name as pattern;
      [ zesu_source_open_registered_tree branch left
      | zesu_source_open_registered_tree branch right ]
  | _ =>
      let head := get_head body in
      let registration := constr:(_ : isla.automation.LithiumUnfold head) in
      iEval (unfold head) in name;
      repeat iDestruct name as (?) name;
      ResourceGroups.zesu_open_resource_groups
  end.

Ltac zesu_source_destruct_registered_disjunction :=
  iMatchHyp ltac:(fun name body =>
    let head := get_head body in
    constr_eq_strict head constr:(@bi_or);
    zesu_source_registered_tree body;
    zesu_source_open_registered_tree name body).
