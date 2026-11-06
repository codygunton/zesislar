Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.FramePacking.
Require Import ZesuSsz.Automation2.AdditiveDecoder.
Require Import ZesuSsz.Automation2.SymbolicByteCodec.
From stdpp Require Import bitvector.definitions tactics.
From Coq Require Import Lists.List ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

(* A proved canonical image connects an opaque list to the existing codec. *)
Ltac zesu_frame_packing_finish :=
  zesu_switch_enabled constr:(ZesuStepFramePacking);
  lazymatch goal with
  | |- @eq (list (bv ?width)) ?bytes ?expected =>
      assert_fails ltac:(idtac; zesu_vm_has_unresolved bytes);
      assert_fails ltac:(idtac; zesu_vm_has_unresolved expected);
      match goal with
      | Hleft : ?decoder_left (firstn ?left_count ?left_bytes) = ?left_value,
        Hright : ?decoder_right
          (firstn ?right_count (skipn ?right_start ?right_bytes)) = ?right_value |- _ =>
          let left_root := eval cbv beta iota zeta delta [skipn] in left_bytes in
          let right_root := eval cbv beta iota zeta delta [skipn] in right_bytes in
          constr_eq left_root bytes;
          constr_eq right_root bytes;
          constr_eq left_count right_start;
          let canonical := constr:(bv_to_little_endian (Z.of_nat left_count) width left_value ++
            bv_to_little_endian (Z.of_nat right_count) width right_value) in
          let image := fresh "HframePackingImage" in
          solve [
            assert (image : bytes = canonical) by
              first [solve [zesu_frame_packing ltac:(zesu_additive_decoder_views)] |
                     solve [zesu_frame_packing ltac:(idtac)]];
            transitivity canonical;
            [exact image | first [reflexivity | symmetry; zesu_symbolic_byte_codec]]]
      end
  end.
