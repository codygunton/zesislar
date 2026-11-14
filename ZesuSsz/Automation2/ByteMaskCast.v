Require Import ZesuSsz.Automation2.SwitchDispatch.
From stdpp Require Import bitvector.tactics.
From Coq Require Import ZArith Lia.
Require ZesuSsz.Automation2.VmClosed.
Local Open Scope Z_scope.

Class ZesuStepByteMaskCast : Prop := {}.

Lemma zesu_sign_extended_byte_mask (width : N) (word : bv 8) :
  (8 <= width)%N ->
  bv_and (bv_sign_extend width word) (Z_to_bv width (2 ^ 8 - 1)) =
    Z_to_bv width (bv_unsigned word).
Proof.
  intros Hwidth.
  pose proof (bv_modulus_le_mono 8 width Hwidth) as Hmodulus.
  pose proof (bv_unsigned_in_range 8 word) as Hword.
  assert (Hmask : 0 <= 2 ^ 8 - 1 < bv_modulus width).
  { change (256 <= bv_modulus width) in Hmodulus. lia. }
  apply bv_eq.
  rewrite bv_and_unsigned.
  rewrite bv_sign_extend_unsigned.
  rewrite (Z_to_bv_small width (2 ^ 8 - 1) Hmask).
  rewrite Z_to_bv_unsigned.
  change (Z.land (bv_wrap width (bv_signed word)) (Z.ones (Z.of_N 8)) =
    bv_wrap width (bv_unsigned word)).
  rewrite <-bv_wrap_land.
  rewrite (bv_wrap_bv_wrap 8 width _ Hwidth).
  unfold bv_signed, bv_swrap.
  rewrite bv_wrap_sub_idemp_l.
  replace (bv_unsigned word + bv_half_modulus 8 - bv_half_modulus 8)
    with (bv_unsigned word) by lia.
  rewrite bv_wrap_bv_unsigned.
  rewrite bv_wrap_small; [reflexivity |].
  change (256 <= bv_modulus width) in Hmodulus.
  change (0 <= bv_unsigned word < 256) in Hword. lia.
Qed.

Ltac zesu_byte_mask_cast :=
  zesu_switch_enabled constr:(ZesuStepByteMaskCast);
  progress (repeat match goal with
  | |- context [bv_and (bv_sign_extend ?width ?word) ?mask] =>
      ZesuSsz.Automation2.VmClosed.zesu_closed_term width; ZesuSsz.Automation2.VmClosed.zesu_closed_term mask;
      assert_fails (has_evar word);
      let expected := eval vm_compute in (2 ^ 8 - 1) in
      let actual := eval vm_compute in (bv_unsigned mask) in
      constr_eq actual expected;
      let Hmask := fresh "HbyteMaskValue" in
      assert (Hmask : mask = Z_to_bv width (2 ^ 8 - 1)) by
        (apply bv_eq; vm_compute; reflexivity);
      try rewrite Hmask;
      let Hwidth := fresh "HbyteMaskWidth" in
      assert (Hwidth : (8 <= width)%N) by (vm_compute; congruence);
      rewrite (zesu_sign_extended_byte_mask width word Hwidth);
      clear Hwidth Hmask
  end);
  assumption.
