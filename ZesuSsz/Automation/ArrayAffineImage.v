From Coq Require Import List ZArith.
Require Import ZesuSsz.Automation.ArrayPayloadPresentation.
Require Import ZesuSsz.Automation.ByteClassGuards.
Require Import ZesuSsz.Automation.JoinEntailment.

(* Keep only the existing length view inside the equality proof. *)
Ltac zesu_array_affine_image :=
  repeat rewrite JoinEntailment.zesu_join_cancel_right;
  repeat rewrite Z.add_simpl_l;
  multimatch goal with
  | Hlength : List.length ?bytes = ?count |- ?target =>
      lazymatch target with context [bytes] =>
        clear - Hlength;
        ByteClassGuards.zesu_byte_class_image
      end
  end.

Ltac zesu_array_affine_presentation :=
  ArrayPayloadPresentation.zesu_array_payload_presentation ltac:(zesu_array_affine_image).
