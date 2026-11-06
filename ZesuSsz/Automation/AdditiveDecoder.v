From Coq Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions list_numbers.
Local Open Scope Z_scope.

Definition zesu_additive_decoder (width : N) (bytes : list (bv width)) : Z :=
  fold_right (fun word tail => bv_unsigned word + 2 ^ Z.of_N width * tail)
    0 bytes.

Lemma zesu_digit_add_shift (width : N) (word : bv width) (tail : Z) :
  bv_unsigned word + 2 ^ Z.of_N width * tail =
    Z.lor (bv_unsigned word) (Z.shiftl tail (Z.of_N width)).
Proof.
  pose proof (bv_unsigned_in_range width word) as Hbound.
  unfold bv_modulus in Hbound.
  assert (Hmask : Z.land (bv_unsigned word) (Z.ones (Z.of_N width)) =
      bv_unsigned word).
  { rewrite Z.land_ones; [apply Z.mod_small; exact Hbound|lia]. }
  rewrite Z.shiftl_mul_pow2; [|lia].
  rewrite (Z.mul_comm (2 ^ Z.of_N width) tail).
  apply Z.add_nocarry_lor.
  assert (Htail : Z.land (tail * 2 ^ Z.of_N width)
      (Z.ones (Z.of_N width)) = 0).
  { rewrite Z.land_ones; [apply Z.mod_mul; apply Z.pow_nonzero; lia|lia]. }
  rewrite <- Hmask at 1.
  rewrite <- Z.land_assoc.
  rewrite (Z.land_comm (Z.ones (Z.of_N width))
    (tail * 2 ^ Z.of_N width)), Htail.
  apply Z.land_0_r.
Qed.

Lemma zesu_additive_decoder_view (width : N) (bytes : list (bv width)) :
  zesu_additive_decoder width bytes = little_endian_to_bv width bytes.
Proof.
  induction bytes as [|word bytes IH]; [reflexivity|].
  change (bv_unsigned word + 2 ^ Z.of_N width *
    zesu_additive_decoder width bytes =
    Z.lor (bv_unsigned word)
      (Z.shiftl (little_endian_to_bv width bytes) (Z.of_N width))).
  rewrite IH. apply zesu_digit_add_shift.
Qed.

(* Conversion, not a name whitelist, identifies supported additive decoders. *)
Ltac zesu_additive_decoder_views :=
  progress (repeat match goal with
  | Hdecoder : ?decoder ?bytes = ?value |- _ =>
      lazymatch decoder with
      | little_endian_to_bv _ => fail 0
      | _ => idtac
      end;
      let bytes_type := type of bytes in
      lazymatch bytes_type with
      | list (bv ?width) =>
          progress (change (zesu_additive_decoder width bytes = value) in Hdecoder;
            rewrite zesu_additive_decoder_view in Hdecoder)
      end
  end).
