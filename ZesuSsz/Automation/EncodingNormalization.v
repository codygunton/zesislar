Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Rewrites.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.SwitchDispatch.

Class ZesuStepEncodingNormalization : Prop := {}.

Lemma zesu_bv_signed_zero_extend_wide (n width : N) (value : bv n) :
  (n < width)%N ->
  bv_signed (bv_zero_extend width value) = bv_unsigned value.
Proof.
  intros Hwidth. rewrite bv_zero_extend_signed. apply bv_swrap_small.
  pose proof (bv_unsigned_in_range n value) as Hrange.
  assert (Hsuccessor : bv_half_modulus (N.succ n) = bv_modulus n).
  { unfold bv_half_modulus, bv_modulus.
    rewrite N2Z.inj_succ Z.pow_succ_r; last lia.
    rewrite Z.mul_comm Z.div_mul; lia. }
  pose proof (bv_half_modulus_le_mono (N.succ n) width ltac:(lia)) as Hmono.
  pose proof (bv_half_modulus_nonneg width).
  rewrite Hsuccessor in Hmono. lia.
Qed.
Print Assumptions zesu_bv_signed_zero_extend_wide.

Ltac zesu_encoding_rewrite equality location :=
  tryif constr_eq location tt then rewrite equality
  else rewrite equality in location.

Ltac zesu_encoding_change term reduced location :=
  tryif constr_eq location tt then change_no_check term with reduced
  else change_no_check term with reduced in location.

(* Only the selected closed term enters the virtual machine. *)
Ltac zesu_encoding_width_literal width :=
  tryif is_var width then fail 0 else
  lazymatch width with
  | N0 => idtac
  | Npos ?positive => zesu_region_positive_literal positive
  end.

Ltac zesu_encoding_bv_literal value :=
  lazymatch value with
  | @BV ?width ?integer _ =>
      zesu_encoding_width_literal width; zesu_region_integer_literal integer
  | Z_to_bv ?width ?integer =>
      zesu_encoding_width_literal width; zesu_region_integer_literal integer
  end.

Ltac zesu_encoding_compute term location :=
  zesu_stack_closed_term term;
  let reduced := eval vm_compute in term in
  tryif constr_eq term reduced then fail 0
  else zesu_encoding_change term reduced location.

Ltac zesu_encoding_wide_term term location :=
  lazymatch term with
  | @bv_signed ?width (@bv_zero_extend ?n ?width ?value) =>
      let Hwidth := fresh "HencodingWidth" in
      assert (Hwidth : (n < width)%N) by lia;
      zesu_encoding_rewrite constr:(zesu_bv_signed_zero_extend_wide n width value Hwidth) location;
      clear Hwidth
  end.

Ltac zesu_encoding_cast_term term location :=
  lazymatch term with
  | @bv_unsigned ?width (Z_to_bv ?width ?value) =>
      assert_fails (zesu_condition_has_unresolved_evar width);
      assert_fails (zesu_condition_has_unresolved_evar value);
      zesu_encoding_width_literal width;
      let modulus := eval vm_compute in (bv_modulus width) in
      let Hbound := fresh "HencodingBound" in
      assert (Hbound : (0 <= value < modulus)%Z) by lia;
      zesu_encoding_rewrite constr:(zesu_bv_unsigned_Z_to_bv_small width value Hbound) location;
      clear Hbound
  end.

Ltac zesu_encoding_literal_term term location :=
  lazymatch term with
  | @bv_xor _ ?left ?right =>
      zesu_encoding_bv_literal left; zesu_encoding_bv_literal right;
      zesu_encoding_compute term location
  | @bv_sub _ ?left ?right =>
      zesu_encoding_bv_literal left; zesu_encoding_bv_literal right;
      zesu_encoding_compute term location
  | @bv_unsigned _ ?value =>
      zesu_encoding_bv_literal value; zesu_encoding_compute term location
  | @bool_decide ?condition _ =>
      lazymatch condition with
      | Z.le ?left ?right =>
          zesu_region_integer_literal left; zesu_region_integer_literal right;
          zesu_encoding_compute term location
      | Z.lt ?left ?right =>
          zesu_region_integer_literal left; zesu_region_integer_literal right;
          zesu_encoding_compute term location
      | @eq Z ?left ?right =>
          zesu_region_integer_literal left; zesu_region_integer_literal right;
          zesu_encoding_compute term location
      end
  | @ite _ true ?left _ => zesu_encoding_change term left location
  | @ite _ false _ ?right => zesu_encoding_change term right location
  end.

Ltac zesu_encoding_normalize_term term location :=
  first [zesu_encoding_wide_term term location |
         zesu_encoding_cast_term term location |
         zesu_encoding_literal_term term location].

Ltac zesu_encoding_matching_term statement location :=
  first
    [multimatch statement with
     | context[bv_signed (bv_zero_extend ?width ?value)] =>
         zesu_encoding_normalize_term constr:(bv_signed (bv_zero_extend width value)) location
     end
    |multimatch statement with
     | context[@bv_unsigned ?width ?value] =>
         zesu_encoding_normalize_term constr:(@bv_unsigned width value) location
     end
    |multimatch statement with
     | context[@bv_xor ?width ?left ?right] =>
         zesu_encoding_normalize_term constr:(@bv_xor width left right) location
     | context[@bv_sub ?width ?left ?right] =>
         zesu_encoding_normalize_term constr:(@bv_sub width left right) location
     | context[@bool_decide ?condition ?decision] =>
         zesu_encoding_normalize_term constr:(@bool_decide condition decision) location
     | context[@ite ?type ?condition ?left ?right] =>
         zesu_encoding_normalize_term constr:(@ite type condition left right) location
     end].

Ltac zesu_encoding_normalization_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepEncodingNormalization);
  progress (repeat first
    [match goal with
     | H : ?statement |- _ => zesu_encoding_matching_term statement H
     end
    |lazymatch goal with
     | |- ?statement => zesu_encoding_matching_term statement constr:(tt)
     end]).
