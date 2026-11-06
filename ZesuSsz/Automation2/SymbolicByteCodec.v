Require Import Coq.ssr.ssreflect.
Require Import ZesuSsz.Automation2.SwitchDispatch.
From stdpp Require Import bitvector.tactics list list_numbers.
From Coq Require Import Lists.List ZArith.ZArith Lia.
Import ListNotations.
Local Open Scope Z_scope.

Class ZesuStepSymbolicByteCodec : Prop := {}.

Lemma zesu_extract_as_cast {width : N} (offset count : N) (word : bv width) :
  bv_extract offset count word =
  Z_to_bv count (Z.shiftr (bv_unsigned word) (Z.of_N offset)).
Proof.
  apply bv_eq.
  rewrite bv_extract_unsigned.
  reflexivity.
Qed.

Lemma zesu_low_mask_cast (width : N) (value : Z) :
  Z_to_bv width (Z.land value (Z.ones (Z.of_N width))) =
  Z_to_bv width value.
Proof.
  rewrite <- bv_wrap_land.
  apply bv_eq.
  rewrite !Z_to_bv_unsigned.
  rewrite bv_wrap_idemp.
  reflexivity.
Qed.

(* Normalize only an explicit extraction list. An unconstrained list stays opaque. *)
Ltac zesu_symbolic_byte_codec :=
  zesu_switch_enabled constr:(ZesuStepSymbolicByteCodec);
  lazymatch goal with
  | |- @eq (list (bv _)) (_ :: _) _ => idtac
  end;
  solve [
    repeat rewrite zesu_extract_as_cast;
    try unfold bv_to_little_endian;
    rewrite /Z_to_little_endian /=;
    repeat rewrite zesu_low_mask_cast;
    try (rewrite !Z_to_bv_small;
      [| unfold bv_modulus; cbn; lia]);
    repeat (rewrite Z.shiftr_shiftr; [| lia]);
    rewrite ?Z.shiftr_0_r;
    cbn;
    reflexivity
  ].
