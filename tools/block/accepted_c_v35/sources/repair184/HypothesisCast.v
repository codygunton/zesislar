Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.MaskWrapPresentation.
From stdpp Require Import bitvector.tactics.
From Coq Require Import ZArith Lia.
Local Open Scope Z_scope.

Class ZesuStepHypothesisCast : Prop := {}.

Ltac zesu_hypothesis_cast_range width value :=
  first [solve [unfold bv_modulus; cbn; lia] |
    lazymatch value with
    | bv_unsigned ?word =>
        let kind := type of word in
        lazymatch kind with bv ?source =>
          is_closed_term source;
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
      is_closed_term width; assert_fails (has_evar value);
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
      is_closed_term mask; assert_fails (has_evar value);
      let kind := type of value in
      lazymatch kind with bv ?width =>
        is_closed_term width;
        let modulus := eval vm_compute in (bv_unsigned mask + 1) in
        let requested := constr:(bv_unsigned value - modulus) in
        let Hequal := fresh "HmaskEqual" in
        assert (Hequal : bv_and value mask = Z_to_bv width requested) by
          (try ZesuSsz.Automation.MaskWrapPresentation.zesu_mask_wide_cast_fact;
           ZesuSsz.Automation.MaskWrapPresentation.zesu_mask_plain_wrap_goal);
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
