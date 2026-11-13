Require Import ZesuSsz.Automation2.ContextRange.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.MaskWrapPresentation.
From stdpp Require Import bitvector.tactics.
From Coq Require Import ZArith Lia.
Require ZesuSsz.Automation2.VmClosed.
Local Open Scope Z_scope.

Class ZesuStepHypothesisCast : Prop := {}.

Ltac zesu_hypothesis_cast_range width value :=
  first [solve [unfold bv_modulus; cbn; lia] |
    lazymatch value with
    | bv_unsigned ?word =>
        let kind := type of word in
        lazymatch kind with bv ?source =>
          ZesuSsz.Automation2.VmClosed.zesu_closed_term source;
          let Hwidth := fresh "HcastWidth" in
          assert (Hwidth : (source <= width)%N) by (vm_compute; congruence);
          pose proof (bv_unsigned_in_range source word);
          pose proof (bv_modulus_le_mono source width Hwidth);
          lia
        end
    end].

Ltac zesu_hypothesis_casts :=
  repeat match goal with
  | H : context [bv_unsigned (Z_to_bv ?width ?value)] |- _ =>
      ZesuSsz.Automation2.VmClosed.zesu_closed_term width; assert_fails (has_evar value);
      let Hrange := fresh "HcastRange" in
      let Hequal := fresh "HcastEqual" in
      assert (Hrange : 0 <= value < bv_modulus width) by
        zesu_hypothesis_cast_range width value;
      assert (Hequal : bv_unsigned (Z_to_bv width value) = value) by
        exact (Z_to_bv_small width value Hrange);
      progress rewrite Hequal in H;
      clear Hequal Hrange
  end.

Ltac zesu_hypothesis_mask_wraps :=
  repeat match goal with
  | H : context [bv_unsigned (bv_and ?value ?mask)] |- _ =>
      ZesuSsz.Automation2.VmClosed.zesu_closed_term mask; assert_fails (has_evar value);
      let kind := type of value in
      lazymatch kind with bv ?width =>
        ZesuSsz.Automation2.VmClosed.zesu_closed_term width;
        let modulus := eval vm_compute in (bv_unsigned mask + 1) in
        let requested := constr:(bv_unsigned value - modulus) in
        let Hequal := fresh "HmaskEqual" in
        assert (Hequal : bv_and value mask = Z_to_bv width requested) by
          (try ZesuSsz.Automation2.MaskWrapPresentation.zesu_mask_wide_cast_fact;
           ZesuSsz.Automation2.MaskWrapPresentation.zesu_mask_plain_wrap_goal);
        progress rewrite Hequal in H;
        clear Hequal
      end
  end.

Ltac zesu_hypothesis_cast_finish :=
  zesu_switch_enabled constr:(ZesuStepHypothesisCast);
  lazymatch goal with
  | |- Z.lt _ _ => idtac
  | |- Z.le _ _ => idtac
  end;
  match goal with
  | _ : context [bv_unsigned (Z_to_bv _ _)] |- _ => idtac
  end;
  solve [zesu_hypothesis_casts;
    try zesu_hypothesis_mask_wraps;
    zesu_hypothesis_casts;
    lia].

Ltac zesu_cast_nonzero_derived :=
  lazymatch goal with
  | |- ZesuSsz.Automation.PureFacts.ZesuDerivedFacts ?premise ?derived =>
    lazymatch premise with
    | Z_to_bv ?width ?value <> ?zero =>
      ZesuSsz.Automation2.VmClosed.zesu_closed_term width; assert_fails (has_evar value);
      first [constr_eq zero constr:((0%bv : bv width)) |
        constr_eq zero constr:(Z_to_bv width 0)];
      let wanted := constr:((value <> 0)%Z) in
      unify derived wanted;
      let range := fresh "HcastNonzeroRange" in
      assert (range : (0 <= value < bv_modulus width)%Z) by
        ContextRange.zesu_hypothesis_cast_range_fact width value;
      unfold ZesuSsz.Automation.PureFacts.ZesuDerivedFacts;
      let nonzero := fresh "HcastNonzero" in
      let zeroValue := fresh "HzeroValue" in
      intros nonzero zeroValue;
      apply nonzero; rewrite zeroValue;
      first [reflexivity |
        change (Z_to_bv width (bv_unsigned (0%bv : bv width)) = (0%bv : bv width));
        apply Z_to_bv_bv_unsigned]
    end
  end.
#[export] Hint Extern 4
  (ZesuSsz.Automation.PureFacts.ZesuDerivedFacts
    (Z_to_bv ?width ?value <> ?zero) _) =>
  zesu_cast_nonzero_derived : typeclass_instances.
