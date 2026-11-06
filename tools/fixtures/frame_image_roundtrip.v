Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.FrameImageRoundtrip.
From Coq Require Import Lia.
From stdpp Require Import bitvector.definitions list.
Require Import ZesuSsz.Automation.All.
Local Open Scope Z_scope.

(* The existing switch still controls this rule. *)


#[local] Instance frame_roundtrip_enabled : ZesuStepCodecArrayRead := {}.

Lemma frame_roundtrip_canonical (word : bv 64) :
  Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat (3 - 3))
      (bv_to_little_endian 8 8 (bv_unsigned word))))) = word.
Proof. zesu_frame_image_to_word. Qed.

Lemma frame_roundtrip_raw_word (word : bv 64) :
  Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat 0)
      (Z_to_bv 8 (Z.land (bv_unsigned word) (Z.ones 8)) ::
       bv_to_little_endian 7 8 (Z.shiftr (bv_unsigned word) 8))))) = word.
Proof. zesu_frame_image_to_word. Qed.

(* A different symbolic word cannot pass the definitional image check. *)

(* A nonzero drop does not receive the zero-offset rewrite. *)
