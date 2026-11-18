Require Import ZesuSsz.Automation2.ContextCollection.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.Hooks.
Require Import ZesuSsz.Automation2.CodecArrayRead.
From Coq Require Import Lia.
From stdpp Require Import bitvector.definitions list.

(* Close only the definitionally exact image of the target word. *)
Ltac zesu_frame_image_to_word :=
  zesu_switch_enabled constr:(ZesuStepCodecArrayRead);
  lazymatch goal with
  | |- Z_to_bv ?bits (little_endian_to_bv ?width
         (take ?count (drop (Z.to_nat ?offset) ?values))) = ?word =>
      is_closed_term bits; is_closed_term width; is_closed_term count;
      assert_fails (has_evar values); assert_fails (has_evar word);
      let index := fresh "HframeImageIndex" in
      assert (index : Z.to_nat offset = 0%nat) by
        (MemoryAddress.zesu_handoff_closed_Z offset ltac:(fun reduced =>
          change (Z.to_nat reduced = 0%nat); (ZesuSsz.Automation2.ContextCollection.zesu_solve_solver ("FrameImageRoundtrip.solver.18.46"%string) ltac:(lia))));
      rewrite index; clear index;
      cbn [drop N.to_nat]; rewrite ?drop_0;
      let digits := eval vm_compute in (Z.of_nat count) in
      change (Z_to_bv bits (little_endian_to_bv width
        (bv_to_little_endian digits width (bv_unsigned word))) = word);
      apply (Z_to_bv_little_endian_to_bv_to_little_endian bits digits width word);
        [(ZesuSsz.Automation2.ContextCollection.zesu_solve_solver ("FrameImageRoundtrip.solver.25.10"%string) ltac:(lia)) | reflexivity]
  end.
