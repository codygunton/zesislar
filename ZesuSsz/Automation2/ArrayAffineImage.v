From Coq Require Import List ZArith.
Require Import ZesuSsz.Automation2.ArrayPayloadPresentation.
Require Import ZesuSsz.Automation2.ByteClassGuards.
Require Import ZesuSsz.Automation2.JoinEntailment.

(* Keep only the existing length view inside the equality proof. *)
Ltac zesu_array_affine_image :=
  repeat rewrite JoinEntailment.zesu_join_cancel_right;
  repeat rewrite JoinEntailment.zesu_join_cancel_shared;
  repeat rewrite Z.add_simpl_l;
  first [solve [
    cbv beta iota zeta delta [firstn skipn List.app Z.to_nat Pos.to_nat
      Pos.iter_op N.to_nat Nat.add]; reflexivity] |
  multimatch goal with
  | Hlength : List.length ?bytes = ?count |- ?target =>
      lazymatch target with context [bytes] =>
        clear - Hlength;
        ByteClassGuards.zesu_byte_class_image
      end
  end].

Ltac zesu_array_affine_presentation :=
  ArrayPayloadPresentation.zesu_array_payload_presentation ltac:(zesu_array_affine_image).
