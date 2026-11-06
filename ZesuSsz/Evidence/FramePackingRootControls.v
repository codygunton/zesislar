Require Import ZesuSsz.Automation.FramePackingFinish.
Require Import ZesuSsz.Automation.FramePacking.
Require Import ZesuSsz.Automation.AdditiveDecoder.
Require Import ZesuSsz.Automation.SymbolicByteCodec.
Require Import ZesuSsz.Automation.SwitchDispatch.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
From stdpp Require Import bitvector.definitions list tactics.
Import ListNotations.
Require Import ZesuSsz.Automation.All.
Local Open Scope Z_scope.

Section enabled.
Context (enabled : ZesuStepFramePacking).

Lemma frame_zero_drop_symbolic (width : N) (bytes : list (bv width)) (left right : Z)
    (Hlength : length bytes = 2%nat)
    (Hleft : zesu_additive_decoder width (take 1 (drop 0 bytes)) = left)
    (Hright : zesu_additive_decoder width (take 1 (drop 1 bytes)) = right) :
  bytes = bv_to_little_endian (Z.of_nat 1) width left ++
    bv_to_little_endian (Z.of_nat 1) width right.
Proof. zesu_frame_packing_finish. Qed.

Lemma frame_nested_zero_drop (width : N) (bytes : list (bv width)) (left right : Z)
    (Hlength : length bytes = 2%nat)
    (Hleft : little_endian_to_bv width (take 1 (drop 0 (drop 0 bytes))) = left)
    (Hright : little_endian_to_bv width (take 1 (drop 1 bytes)) = right) :
  bytes = bv_to_little_endian (Z.of_nat 1) width left ++
    bv_to_little_endian (Z.of_nat 1) width right.
Proof. zesu_frame_packing_finish. Qed.

Lemma frame_changed_left_root (width : N) (bytes other : list (bv width)) (left right : Z)
    (Hlength : length bytes = 2%nat)
    (Hleft : little_endian_to_bv width (take 1 (drop 0 other)) = left)
    (Hright : little_endian_to_bv width (take 1 (drop 1 bytes)) = right) : True.
Proof.
  Fail assert (Himage : bytes = bv_to_little_endian (Z.of_nat 1) width left ++
    bv_to_little_endian (Z.of_nat 1) width right) by zesu_frame_packing_finish.
  exact I.
Qed.

Lemma frame_changed_right_root (width : N) (bytes other : list (bv width)) (left right : Z)
    (Hlength : length bytes = 2%nat)
    (Hleft : little_endian_to_bv width (take 1 (drop 0 bytes)) = left)
    (Hright : little_endian_to_bv width (take 1 (drop 1 other)) = right) : True.
Proof.
  Fail assert (Himage : bytes = bv_to_little_endian (Z.of_nat 1) width left ++
    bv_to_little_endian (Z.of_nat 1) width right) by zesu_frame_packing_finish.
  exact I.
Qed.

Lemma frame_nonadjacent (width : N) (bytes : list (bv width)) (left right : Z)
    (Hlength : length bytes = 2%nat)
    (Hleft : little_endian_to_bv width (take 1 (drop 0 bytes)) = left)
    (Hright : little_endian_to_bv width (take 1 (drop 2 bytes)) = right) : True.
Proof.
  Fail assert (Himage : bytes = bv_to_little_endian (Z.of_nat 1) width left ++
    bv_to_little_endian (Z.of_nat 1) width right) by zesu_frame_packing_finish.
  exact I.
Qed.

Lemma frame_missing_extent (width : N) (bytes : list (bv width)) (left right : Z)
    (Hleft : little_endian_to_bv width (take 1 (drop 0 bytes)) = left)
    (Hright : little_endian_to_bv width (take 1 (drop 1 bytes)) = right) : True.
Proof.
  Fail assert (Himage : bytes = bv_to_little_endian (Z.of_nat 1) width left ++
    bv_to_little_endian (Z.of_nat 1) width right) by zesu_frame_packing_finish.
  exact I.
Qed.

Lemma frame_unknown_decoder (width : N) (decoder : list (bv width) -> Z)
    (bytes : list (bv width)) (left right : Z)
    (Hlength : length bytes = 2%nat)
    (Hleft : decoder (take 1 (drop 0 bytes)) = left)
    (Hright : decoder (take 1 (drop 1 bytes)) = right) : True.
Proof.
  Fail assert (Himage : bytes = bv_to_little_endian (Z.of_nat 1) width left ++
    bv_to_little_endian (Z.of_nat 1) width right) by zesu_frame_packing_finish.
  exact I.
Qed.
End enabled.

Lemma frame_swapped_image (enabled : ZesuStepFramePacking)
    (width : N) (bytes : list (bv width)) (left right : Z)
    (Hlength : length bytes = 2%nat)
    (Hleft : little_endian_to_bv width (take 1 (drop 0 bytes)) = left)
    (Hright : little_endian_to_bv width (take 1 (drop 1 bytes)) = right) : True.
Proof.
  Fail assert (Himage : bytes = bv_to_little_endian (Z.of_nat 1) width right ++
    bv_to_little_endian (Z.of_nat 1) width left) by zesu_frame_packing_finish.
  exact I.
Qed.

Lemma frame_wrong_goal (enabled : ZesuStepFramePacking) : True.
Proof. Fail zesu_frame_packing_finish. exact I. Qed.

Lemma frame_disabled (width : N) (bytes : list (bv width)) (left right : Z)
    (Hlength : length bytes = 2%nat)
    (Hleft : little_endian_to_bv width (take 1 (drop 0 bytes)) = left)
    (Hright : little_endian_to_bv width (take 1 (drop 1 bytes)) = right) : True.
Proof.
  assert (off : ZesuSsz.Automation.SwitchDispatch.ZesuSwitchDispatchCache
    [(ZesuStepFramePacking, false)]) by constructor.
  Fail assert (Himage : bytes = bv_to_little_endian (Z.of_nat 1) width left ++
    bv_to_little_endian (Z.of_nat 1) width right) by zesu_frame_packing_finish.
  exact I.
Qed.
