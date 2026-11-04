Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.AdditiveDecoder.
From Coq Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions list_numbers.
Local Open Scope Z_scope.

Class ZesuStepCodecRoundtrip : Prop := {}.

Definition zesu_integer_additive_decoder (width : N) (digits : list Z) : Z :=
  fold_right (fun digit tail => digit + 2 ^ Z.of_N width * tail) 0 digits.

Lemma zesu_integer_additive_decoder_view (width : N) (digits : list Z) :
  Forall (fun digit => 0 <= digit < 2 ^ Z.of_N width) digits ->
  zesu_integer_additive_decoder width digits =
    little_endian_to_Z (Z.of_N width) digits.
Proof.
  intros Hdigits. induction Hdigits as [|digit digits Hdigit Hdigits IH].
  - reflexivity.
  - change (digit + 2 ^ Z.of_N width *
      zesu_integer_additive_decoder width digits =
      Z.lor digit (Z.shiftl (little_endian_to_Z (Z.of_N width) digits)
        (Z.of_N width))).
    rewrite IH.
    pose proof (zesu_digit_add_shift width (Z_to_bv width digit)
      (little_endian_to_Z (Z.of_N width) digits)) as Hshift.
    rewrite (Z_to_bv_small width digit Hdigit) in Hshift.
    exact Hshift.
Qed.

Lemma zesu_integer_codec_roundtrip (count : Z) (width : N) (value : Z) :
  0 <= count ->
  zesu_integer_additive_decoder width
    (Z_to_little_endian count (Z.of_N width) value) =
    value mod 2 ^ (count * Z.of_N width).
Proof.
  intros Hcount. rewrite zesu_integer_additive_decoder_view.
  - apply little_endian_to_Z_to_little_endian; lia.
  - apply Z_to_little_endian_bound; lia.
Qed.

(* A mask exposes the digit width. Closed widths determine the complete image.
   The bitvector type supplies its range; no machine fact enters this rule. *)
Ltac zesu_codec_roundtrip :=
  zesu_switch_enabled constr:(ZesuStepCodecRoundtrip);
  lazymatch goal with
  | |- ?image = bv_unsigned ?word =>
      lazymatch image with context [Z.land _ (Z.ones ?digit_width)] =>
      lazymatch type of word with bv ?source_width =>
        is_closed_term source_width; is_closed_term digit_width;
        let positive := eval vm_compute in (0 <? digit_width)%Z in
        constr_eq positive true;
        let width := eval vm_compute in (Z.to_N digit_width) in
        let count := eval vm_compute in (Z.of_N source_width / digit_width)%Z in
        change (zesu_integer_additive_decoder width
          (Z_to_little_endian count (Z.of_N width) (bv_unsigned word)) =
          bv_unsigned word);
        rewrite (zesu_integer_codec_roundtrip count width (bv_unsigned word) ltac:(lia));
        apply Z.mod_small;
        let Hrange := fresh "HcodecWordRange" in
        pose proof (bv_unsigned_in_range source_width word) as Hrange;
        change (0 <= bv_unsigned word < bv_modulus source_width)%Z;
        exact Hrange
      end end
  end.
