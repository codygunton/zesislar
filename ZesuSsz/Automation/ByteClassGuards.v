Require Import ZesuSsz.Automation.ByteMaskCast.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.ListSliceWindows.
From Coq Require Import Bool.Bool ZArith.ZArith Lia.
From stdpp Require Import bitvector.tactics list decidable.
Local Open Scope Z_scope.

Lemma zesu_masked_byte_class (byte : bv 8) (lengthWord : bv 64) (upper : Z) :
  0 <= upper < bv_half_modulus 128 ->
  bool_decide (bv_signed (bv_sign_extend 128 (bv_sign_extend 64 byte)) < bv_signed (BV 128 0)) = true ->
  negb (bool_decide (bv_and (bv_sign_extend 64 byte) (BV 64 255) = BV 64 128)) = true ->
  negb (bool_decide (bv_signed (Z_to_bv 128 upper) < bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 byte) (BV 64 255))))) = true ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 127))) >= bv_signed (bv_zero_extend 128 lengthWord))) = true ->
  129 <= bv_unsigned byte <= upper /\
  bv_unsigned (bv_and (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 127)) = bv_unsigned byte - 128 /\
  1 + (bv_unsigned byte - 128) <= bv_unsigned lengthWord.
Proof.
  intros HupperRange Hnegative Hnot128 HupperGuard HlengthGuard.
  set (payloadWord := bv_and (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 127)) in *.
  pose proof (bv_unsigned_in_range 8 byte) as Hrange.
  change (0 <= bv_unsigned byte < 256) in Hrange.
  pose proof (zesu_sign_extended_byte_mask 64 byte ltac:(lia)) as Hmask.
  assert (HmaskLiteral : Z_to_bv 64 (2 ^ 8 - 1) = BV 64 255).
  { apply bv_eq. vm_compute. reflexivity. }
  rewrite HmaskLiteral in Hmask.
  assert (HcastByte : bv_unsigned (Z_to_bv 64 (bv_unsigned byte)) = bv_unsigned byte).
  { apply Z_to_bv_small. change (0 <= bv_unsigned byte < 18446744073709551616). lia. }
  apply bool_decide_eq_true_1 in Hnegative.
  rewrite (bv_sign_extend_signed 128 (bv_sign_extend 64 byte) ltac:(lia)) in Hnegative.
  rewrite (bv_sign_extend_signed 64 byte ltac:(lia)) in Hnegative.
  rewrite bv_signed_BV in Hnegative.
  rewrite bv_swrap_0 in Hnegative.
  assert (Hlower : 128 <= bv_unsigned byte).
  { destruct (Z_lt_ge_dec (bv_unsigned byte) 128); [|lia].
    assert (Hsmall : - bv_half_modulus 8 <= bv_unsigned byte < bv_half_modulus 8).
    { change (-128 <= bv_unsigned byte < 128). lia. }
    unfold bv_signed in Hnegative.
    rewrite (bv_swrap_small 8 (bv_unsigned byte) Hsmall) in Hnegative. lia. }
  apply Bool.negb_true_iff in HupperGuard.
  apply bool_decide_eq_false_1 in HupperGuard.
  rewrite Hmask in HupperGuard.
  rewrite (BitvectorFacts.zesu_signed_zero_extend_64_128 (Z_to_bv 64 (bv_unsigned byte))) in HupperGuard.
  rewrite HcastByte in HupperGuard.
  assert (HupperSigned : bv_signed (Z_to_bv 128 upper) = upper).
  { rewrite Z_to_bv_signed. apply bv_swrap_small.
    pose proof (bv_half_modulus_nonneg 128). lia. }
  rewrite HupperSigned in HupperGuard.
  apply Bool.negb_true_iff in Hnot128.
  apply bool_decide_eq_false_1 in Hnot128.
  rewrite Hmask in Hnot128.
  assert (HnotEqual : bv_unsigned byte <> 128).
  { intro Heq. rewrite Heq in Hnot128. apply Hnot128. apply bv_eq. vm_compute. reflexivity. }
  assert (Hpayload : bv_unsigned payloadWord = bv_unsigned byte - 128).
  { unfold payloadWord. rewrite Hmask. rewrite bv_and_unsigned. rewrite HcastByte. rewrite bv_unsigned_BV.
    change (Z.land (bv_unsigned byte) (Z.ones 7) = bv_unsigned byte - 128).
    rewrite (Z.land_ones (bv_unsigned byte) 7 ltac:(lia)).
    change (bv_unsigned byte mod 128 = bv_unsigned byte - 128).
    replace (bv_unsigned byte) with (bv_unsigned byte - 128 + 1 * 128) at 1 by lia.
    rewrite (Z.mod_add (bv_unsigned byte - 128) 1 128 ltac:(lia)).
    apply Z.mod_small. lia. }
  apply Bool.negb_true_iff in HlengthGuard.
  apply bool_decide_eq_false_1 in HlengthGuard.
  rewrite (BitvectorFacts.zesu_signed_zero_extend_64_128 payloadWord) in HlengthGuard.
  rewrite (BitvectorFacts.zesu_signed_zero_extend_64_128 lengthWord) in HlengthGuard.
  rewrite Hpayload in HlengthGuard.
  repeat split; try exact Hpayload; lia.
Qed.

(* Normalize a byte-list image without selecting machine resources. *)
Ltac zesu_byte_class_image :=
  lazymatch goal with |- @eq (list (bv 8)) _ _ => idtac end;
  list_simplifier;
  repeat lazymatch goal with |- ?head :: ?left = ?head :: ?right =>
    apply (f_equal (cons head)) end;
  repeat rewrite bv_unsigned_BV;
  cbn [Z.land Z.ones Z.shiftr];
  repeat rewrite drop_drop;
  cbn [Nat.add];
  list_simplifier;
  repeat lazymatch goal with |- ?head :: ?left = ?head :: ?right =>
    apply (f_equal (cons head)) end;
  repeat rewrite Z.shiftr_0_l;
  repeat rewrite Z.land_0_l;
  repeat zesu_list_slice_windows;
  list_simplifier;
  reflexivity.

Ltac zesu_byte_class_guards :=
  multimatch goal with
  | Hnegative : bool_decide (bv_signed (bv_sign_extend 128 (bv_sign_extend 64 ?byte)) < bv_signed (BV 128 0)) = true,
    Hnot128 : negb (bool_decide (bv_and (bv_sign_extend 64 ?byte) (BV 64 255) = BV 64 128)) = true,
    Hupper : negb (bool_decide (bv_signed ?upperWord < bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 ?byte) (BV 64 255))))) = true,
    Hlength : negb (bool_decide (bv_signed (bv_zero_extend 128 ?actualPayload) >= bv_signed (bv_zero_extend 128 ?lengthWord))) = true |- _ =>
      is_closed_term upperWord;
      let upper := eval vm_compute in (bv_signed upperWord) in
      let Hrange := fresh "HbyteClassUpperRange" in
      assert (Hrange : 0 <= upper < bv_half_modulus 128) by
        (vm_compute; split; congruence);
      let Hpresentation := fresh "HbyteClassUpperPresentation" in
      assert (Hpresentation : upperWord = Z_to_bv 128 upper) by
        (apply bv_eq; vm_compute; reflexivity);
      let Hguard := fresh "HbyteClassUpperGuard" in
      pose proof Hupper as Hguard;
      rewrite Hpresentation in Hguard;
      let HlengthView := fresh "HbyteClassLengthGuard" in
      pose proof Hlength as HlengthView;
      change (negb (bool_decide (bv_signed (bv_zero_extend 128
        (bv_and (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 127))) >=
        bv_signed (bv_zero_extend 128 lengthWord))) = true) in HlengthView;
      let Hfacts := fresh "HbyteClassFacts" in
      pose proof (zesu_masked_byte_class byte lengthWord upper Hrange Hnegative Hnot128 Hguard HlengthView) as Hfacts;
      clear Hrange Hpresentation Hguard HlengthView
  end.
