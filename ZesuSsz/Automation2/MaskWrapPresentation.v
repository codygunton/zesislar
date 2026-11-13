Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.Hooks.
From stdpp Require Import bitvector.definitions bitvector.tactics list.
From Coq Require Import ZArith.ZArith NArith.NArith Lia Lists.List.
Require ZesuSsz.Automation2.VmClosed.
Local Open Scope Z_scope.

Ltac zesu_mask_wide_cast_fact :=
  match goal with
  | |- context [Z_to_bv ?width (bv_unsigned ?word)] =>
      assert_fails (has_evar word);
      ZesuSsz.Automation2.VmClosed.zesu_closed_term width;
      let kind := type of word in
      lazymatch kind with bv ?source =>
        ZesuSsz.Automation2.VmClosed.zesu_closed_term source;
        let Hwidth := fresh "HcastWidth" in
        let Hrange := fresh "HcastRange" in
        let Hbridge := fresh "HunsignedCast" in
        assert (Hwidth : (source <= width)%N) by (vm_compute; congruence);
        assert (Hrange : 0 <= bv_unsigned word < bv_modulus width) by
          (pose proof (bv_unsigned_in_range source word);
           pose proof (bv_modulus_le_mono source width Hwidth); lia);
        assert (Hbridge : bv_unsigned (Z_to_bv width (bv_unsigned word)) =
                          bv_unsigned word) by
          exact (Z_to_bv_small width (bv_unsigned word) Hrange);
        clear Hrange Hwidth
      end
  end.

Ltac zesu_mask_plain_wrap_goal :=
  lazymatch goal with
  | |- bv_and ?value ?mask = Z_to_bv ?width ?requested =>
      assert_fails (has_evar value);
      assert_fails (has_evar requested);
      ZesuSsz.Automation2.VmClosed.zesu_closed_term width;
      ZesuSsz.Automation2.VmClosed.zesu_closed_term mask;
      let low := eval vm_compute in
        (N.log2 (Z.to_N (bv_unsigned mask + 1))) in
      let modulus := eval vm_compute in (bv_modulus low) in
      let Hwidth := fresh "HmaskWidth" in
      let Hmask := fresh "HmaskBits" in
      let Hrange := fresh "HmaskWindow" in
      let Hresult := fresh "HmaskResult" in
      let Hsmall := fresh "HmaskResultRange" in
      assert (Hwidth : (low <= width)%N) by (vm_compute; congruence);
      assert (Hmask : bv_unsigned mask = Z.ones (Z.of_N low)) by
        (vm_compute; reflexivity);
      assert (Hrange : modulus <= bv_unsigned value < 2 * modulus) by lia;
      assert (Hresult : requested = bv_unsigned value - modulus) by lia;
      assert (Hsmall : 0 <= requested < bv_modulus width) by
        (let Hmono := fresh "HmaskModulusOrder" in
         pose proof (bv_modulus_le_mono low width Hwidth) as Hmono;
         change (modulus <= bv_modulus width)%Z in Hmono;
         lia);
      apply bv_eq;
      rewrite (ZesuSsz.Automation2.BitvectorFacts.zesu_guard_low_mask_one_wrap
        width low value mask Hwidth Hmask Hrange);
      rewrite (Z_to_bv_small width requested Hsmall);
      change (bv_unsigned value - modulus = requested);
      lia
  end.

Ltac zesu_mask_wrap_presentation :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuSsz.Automation2.BitvectorFacts.ZesuStepMaskNormalizer);
  try zesu_mask_wide_cast_fact;
  first [solve [ZesuSsz.Automation2.Hooks.zesu_low_mask_sub_modulus_if_enabled]
        | solve [zesu_mask_plain_wrap_goal]].
