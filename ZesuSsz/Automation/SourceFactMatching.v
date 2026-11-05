Require Import ZesuSsz.Automation.ContextRange.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.VmClosed.
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
  | |- bv_signed (bv_sign_extend ?wide (bv_sign_extend ?middle ?byte)) < bv_signed ?zero =>
    assert_fails (has_evar byte);
    is_closed_term wide; is_closed_term middle;
    multimatch goal with
    | Hsource : bv_signed (bv_sign_extend wide (bv_sign_extend middle ?loaded)) < bv_signed zero |- _ =>
      let equality := fresh "HsourceLoadedByte" in
      assert (equality : loaded = byte) by
        ArrayByteValues.zesu_finish_array_byte_lookup_if_closed;
      let transported := fresh "HsourceSignedByte" in
      pose proof Hsource as transported;
      rewrite equality in transported;
      exact transported
    end
  end.





Ltac zesu_source_fact := first [solve [assumption] | solve [reflexivity] |
  solve [BitvectorFacts.zesu_source_unsigned_bound] |
  solve [zesu_source_signed_lookup] | lazymatch goal with
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
 | lazymatch goal with | |- bool_decide ?fact = true => apply bool_decide_eq_true_2; zesu_source_fact | |- bool_decide ?fact = false => apply bool_decide_eq_false_2; zesu_source_fact | |- negb ?b = true => apply Bool.negb_true_iff; zesu_source_fact | |- ?a /\ ?b => split; zesu_source_fact | |- Z.le Z0 (@bv_unsigned ?width ?value) => assert_fails (has_evar value); exact (proj1 (bv_unsigned_in_range width value)) | |- Z.lt (@bv_unsigned ?width ?value) ?bound => assert_fails (has_evar value); assert_fails (has_evar bound); exact (proj2 (bv_unsigned_in_range width value)) | |- ?fact => let exposed := eval hnf in fact in lazymatch exposed with | ?left /\ ?right => change exposed; split; zesu_source_fact end end].

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
