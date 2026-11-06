Require Export ZesuSsz.Automation2.AdjacentWordSubsumption278.
Require Import ZesuSsz.Automation2.ByteExtractCodec281.
Require Import isla.riscv64.riscv64.
Require Import stdpp.bitvector.definitions.
From Coq Require Import List NArith ZArith.
Import ListNotations.
Set Default Proof Mode "Classic".

Ltac adjacent_codec_equation282 :=
  lazymatch goal with
  | |- @eq (list (bv 8)) ?lhs ?rhs =>
      tryif has_evar lhs then fail 1 "The byte target contains an evar." else idtac;
      tryif has_evar rhs then fail 1 "The codec target contains an evar." else idtac;
      lazymatch lhs with
      | bv_extract 0 8 ?low :: _ =>
          adjacent_word_counts low lhs ltac:(fun n m =>
            let high_byte := eval cbn [List.nth_error] in (List.nth_error lhs n) in
            lazymatch high_byte with
            | Some (bv_extract 0 8 ?high) =>
                change (byte_extracts281 n low ++ byte_extracts281 m high =
                  bv_to_little_endian (Z.of_nat n) 8 (bv_unsigned low) ++
                  bv_to_little_endian (Z.of_nat m) 8 (bv_unsigned high));
                rewrite byte_extracts_codec281;
                rewrite byte_extracts_codec281;
                reflexivity
            end)
      end
  end.

#[export] Hint Extern 20
  (SimplAnd (@eq (list (bv 8)) ?lhs ?rhs) ?reduced) =>
    unify reduced True;
    unfold SimplAnd; split;
    [intros _; adjacent_codec_equation282 | intros _; exact I]
  : typeclass_instances.
