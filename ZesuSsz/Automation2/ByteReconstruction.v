Require Import ZesuSsz.Automation2.SwitchDispatch.
From stdpp Require Import bitvector.tactics.
From Coq Require Import ZArith Lia.
Require ZesuSsz.Automation2.VmClosed.
Local Open Scope Z_scope.

Class ZesuStepByteReconstruction : Prop := {}.

Ltac zesu_goal_word_bounds :=
  repeat match goal with
  | |- context [bv_unsigned ?word] =>
      tryif has_evar word then fail 0 else
      let kind := type of word in
      lazymatch kind with bv ?width =>
        let bound := constr:(0 <= bv_unsigned word < bv_modulus width) in
        tryif match goal with _ : bound |- _ => idtac end
        then fail 0 else
        let Hbound := fresh "HwordRange" in
        pose proof (bv_unsigned_in_range width word) as Hbound
      end
  end.

Ltac zesu_byte_reconstruction finish :=
  zesu_switch_enabled constr:(ZesuStepByteReconstruction);
  lazymatch goal with |- @eq Z _ _ => idtac end;
  lazymatch goal with |- context [Z.land _ (Z.ones _)] => idtac end;
  lazymatch goal with |- context [Z.shiftr _ _] => idtac end;
  zesu_goal_word_bounds;
  repeat match goal with
  | Hbound : 0 <= bv_unsigned _ < bv_modulus ?width |- _ =>
      ZesuSsz.Automation2.VmClosed.zesu_closed_term width;
      unfold bv_modulus in Hbound; cbn in Hbound
  end;
  repeat match goal with
  | |- context [Z.land ?value (Z.ones ?bits)] =>
      ZesuSsz.Automation2.VmClosed.zesu_closed_term bits;
      let Hbits := fresh "HdigitWidth" in
      assert (Hbits : 0 <= bits) by (vm_compute; congruence);
      rewrite (Z.land_ones value bits Hbits);
      clear Hbits
  end;
  repeat match goal with
  | |- context [Z.shiftr ?value ?bits] =>
      ZesuSsz.Automation2.VmClosed.zesu_closed_term bits;
      let Hbits := fresh "HdigitShift" in
      assert (Hbits : 0 <= bits) by (vm_compute; congruence);
      rewrite (Z.shiftr_div_pow2 value bits Hbits);
      clear Hbits
  end;
  cbn;
  finish.
