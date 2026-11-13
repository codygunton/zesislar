Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.Hooks.
From stdpp Require Import bitvector.definitions bitvector.tactics list.
From Coq Require Import ZArith.ZArith NArith.NArith Lia Lists.List.
Require ZesuSsz.Automation2.VmClosed.
Local Open Scope Z_scope.

(* Replace a sign-extended word's exact low-bit mask with its unsigned cast. *)
Ltac zesu_mask_sign_extend_presentation :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuSsz.Automation2.BitvectorFacts.ZesuStepMaskNormalizer);
  repeat match goal with
  | |- context [bv_and (bv_sign_extend ?width ?value) ?mask] =>
      assert_fails (has_evar value);
      ZesuSsz.Automation2.VmClosed.zesu_closed_term width;
      ZesuSsz.Automation2.VmClosed.zesu_closed_term mask;
      let kind := type of value in
      lazymatch kind with bv ?low =>
        ZesuSsz.Automation2.VmClosed.zesu_closed_term low;
        let Hwidth := fresh "HmaskWidth" in
        let Hmask := fresh "HmaskValue" in
        let Hrange := fresh "HmaskCastRange" in
        let Hnormalized := fresh "HmaskUnsigned" in
        let Hequal := fresh "HmaskPresentation" in
        assert (Hwidth : (low <= width)%N) by (vm_compute; congruence);
        assert (Hmask : bv_unsigned mask = Z.ones (Z.of_N low)) by
          (vm_compute; reflexivity);
        assert (Hrange : 0 <= bv_unsigned value < bv_modulus width) by
          (pose proof (bv_unsigned_in_range low value);
           pose proof (bv_modulus_le_mono low width Hwidth); lia);
        pose proof (ZesuSsz.Automation2.BitvectorFacts.zesu_guard_mask_signed_value
          width low value mask Hwidth Hmask) as Hnormalized;
        rewrite bv_and_unsigned in Hnormalized;
        rewrite Z_to_bv_unsigned in Hnormalized;
        assert (Hequal : bv_and (bv_sign_extend width value) mask =
                        Z_to_bv width (bv_unsigned value)) by
          (apply bv_eq;
           rewrite bv_and_unsigned;
           rewrite bv_sign_extend_unsigned;
           rewrite Hnormalized;
           rewrite (Z_to_bv_small width (bv_unsigned value) Hrange);
           reflexivity);
        rewrite Hequal;
        clear Hequal Hnormalized Hrange Hmask Hwidth
      end
  end;
  first [reflexivity | lia].
