From Coq Require Import List ZArith.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.ByteClassGuards.

(* Keep only the existing length view inside the equality proof. *)
Ltac zesu_array_affine_image :=
  repeat rewrite Z.add_simpl_l;
  multimatch goal with
  | Hlength : List.length ?bytes = ?count |- ?target =>
      lazymatch target with context [bytes] =>
        clear - Hlength;
        ByteClassGuards.zesu_byte_class_image
      end
  end.

Ltac zesu_array_affine_presentation :=
  Hooks.zesu_array_payload_presentation ltac:(zesu_array_affine_image).
