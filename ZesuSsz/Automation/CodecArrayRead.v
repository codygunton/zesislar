Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.ByteArrayLengths.
Require Import ZesuSsz.Automation.CodecArrayRange.
From Coq Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions list.
From iris.proofmode Require Import environments.
Local Open Scope Z_scope.

Class ZesuStepCodecArrayRead : Prop := {}.
#[export] Instance codec_read_range `{ZesuStepCodecArrayRead} :
  ZesuStepCodecArrayRange := {}.
#[export] Instance codec_read_regions `{ZesuStepCodecArrayRead} :
  ZesuSsz.Automation.ByteArrayLengths.ZesuStepArrayRegionBounds := I.
#[export] Instance codec_read_bounds `{ZesuStepCodecArrayRead} :
  ZesuSsz.Automation.Hooks.ZesuStepArrayBounds := I.

(* Match the existing owned byte image. The public range proof runs after
   cast normalization, so it never uses a stale payload argument. *)
Ltac zesu_codec_array_find :=
  zesu_switch_enabled constr:(ZesuStepCodecArrayRead);
  ZesuSsz.Automation.ResourceGroups.zesu_expose_environment_alias;
  lazymatch goal with
  | |- environments.envs_entails _
      (find_in_context (FindMemMapsTo (bv_unsigned ?pointer)) _) =>
      let expanded := eval cbv beta zeta in pointer in
      ZesuSsz.Automation.Hooks.zesu_integer_pointer_root expanded ltac:(fun _ =>
      let integer := ZesuSsz.Automation.Hooks.zesu_stack_integer_address expanded in
      iMatchHyp ltac:(fun H body =>
        lazymatch body with
        | @mem_mapsto_array _ _ 8%N ?lower ?fraction ?values =>
            lazymatch values with context [bv_to_little_endian _ _ _] => idtac end;
            assert_fails (has_evar lower);
            assert_fails (has_evar fraction);
            assert_fails (has_evar values);
            let Haddress := fresh "HcodecArrayAddress" in
            assert (Haddress : bv_unsigned pointer = integer) by
              ZesuSsz.Automation.Hooks.zesu_stack_arithmetic;
            let Hrange := fresh "HcodecArrayRange" in
            assert (Hrange : (lower <= integer < lower +
              Z.of_nat (length values) * Z.of_N (8 `div` 8))%Z) by (
              ZesuSsz.Automation.Hooks.zesu_array_bound_integer_casts;
              ZesuSsz.Automation.ByteArrayLengths.zesu_byte_array_lengths_extended;
              zesu_codec_array_range);
            ZesuSsz.Automation.Hooks.zesu_integer_array_facts;
            rewrite Haddress; clear Haddress;
            liEnsureInvariant;
            liStep
        end))
  end.

(* Keep the public codec length available after the array rule shelves its
   index constraints. Normalize only closed parts of the existing offset. *)
Ltac zesu_codec_array_read_sidecond :=
  zesu_switch_enabled constr:(ZesuStepCodecArrayRead);
  lazymatch goal with |- SHELVED_SIDECOND ?condition => change condition end;
  lazymatch goal with
  | |- (0 <= ?offset)%Z =>
      Hooks.zesu_handoff_closed_Z offset ltac:(fun reduced =>
        change (0 <= reduced)%Z; lia)
  | |- (Z.to_nat ?offset + ?width <= ?extent)%nat =>
      Hooks.zesu_handoff_closed_Z offset ltac:(fun reduced =>
        change (Z.to_nat reduced + width <= extent)%nat;
        cbn [length];
        zesu_codec_range_lengths;
        cbn; lia)
  end.

(* Normalize the pure image before Lithium substitutes the decoded term into
   the remaining context. The complete codec must follow a literal prefix.
   The offset equality and the full take bound are proved, never assumed. *)
Ltac zesu_codec_array_read_image image :=
  zesu_switch_enabled constr:(ZesuStepCodecArrayRead);
  lazymatch type of image with
  | context [drop (Z.to_nat ?offset) ?values] =>
      let rec prefix_length values count :=
        lazymatch values with
        | _ :: ?tail => prefix_length tail constr:(S count)
        | bv_to_little_endian _ _ _ => count
        end in
      let count := prefix_length values constr:(O) in
      let rec check_extent values :=
        lazymatch values with
        | _ :: ?tail => check_extent tail
        | bv_to_little_endian ?digits ?width _ =>
            is_closed_term digits; is_closed_term width
        end in
      check_extent values;
      let index := fresh "HcodecIndex" in
      assert (index : Z.to_nat offset = count) by
        (Hooks.zesu_handoff_closed_Z offset ltac:(fun reduced =>
          change (Z.to_nat reduced = count); lia));
      rewrite index in image; clear index
  end;
  cbn [drop N.to_nat] in image;
  rewrite drop_0 in image;
  lazymatch type of image with
  | context [take ?count (bv_to_little_endian ?digits ?width ?value)] =>
      let bound := fresh "HcodecTake" in
      assert (bound :
        (length (bv_to_little_endian digits width value) <= count)%nat) by
        (rewrite (length_bv_to_little_endian digits width value ltac:(lia));
         lia);
      rewrite (take_ge (bv_to_little_endian digits width value) count bound)
        in image;
      clear bound
  end;
  lazymatch type of image with
  | context [Z_to_bv ?bits (little_endian_to_bv ?width
      (bv_to_little_endian ?digits ?width (bv_unsigned ?word)))] =>
      rewrite (Z_to_bv_little_endian_to_bv_to_little_endian
        bits digits width word ltac:(lia) ltac:(reflexivity)) in image
  end.

(* This rule introduces the existing full-array wand. It does not execute the
   next trace, discard an owner, or change the surrounding continuation. *)
Ltac zesu_codec_array_read_consumer :=
  zesu_switch_enabled constr:(ZesuStepCodecArrayRead);
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_forall _ (bv _) _) => idtac
  end;
  let value := fresh "codecValue" in
  let image := fresh "HcodecImage" in
  let loaded := fresh "HcodecLoaded" in
  let image_name := iFresh in
  iIntros (value) image_name;
  iDestruct image_name as %image;
  zesu_codec_array_read_image image;
  let loaded_name := iFresh in
  iIntros loaded_name;
  iDestruct loaded_name as %loaded;
  let owner := iFresh in
  iIntros owner;
  subst value;
  lazymatch type of loaded with
  | ?source = _ => is_var source; subst source
  end.

Ltac zesu_codec_array_read :=
  first [zesu_codec_array_find |
    zesu_codec_array_read_consumer |
    zesu_codec_array_read_sidecond].
