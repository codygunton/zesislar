Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.MachinePilot180Entries.
Require Import ZesuSsz.Generated.DecodeItem.MachinePilot180Structural.
Require Import ZesuSsz.Generated.DecodeItem.PilotRejectJoin200.
Require Import ZesuSsz.Automation.EffectiveOverrides.
Open Scope Z_scope.

From iris.proofmode Require Import environments.
Import ZesuSsz.Automation.SwitchDispatch ZesuSsz.Automation.Hooks.
#[local] Instance diagnostic_approved_register_collection :
  Hooks.ZesuStepRegisterCollectionSelection := {}.
Ltac zesu_contains_existential_resource body :=
  lazymatch body with
  | @bi_exist _ _ _ => idtac
  | (?left ∗ ?right)%I =>
      first [zesu_contains_existential_resource left |
             zesu_contains_existential_resource right]
  | _ =>
      let head := get_head body in
      let registered := constr:(_ : LithiumUnfold head) in
      let expanded := eval cbv beta zeta delta [head] in body in
      tryif constr_eq expanded body then fail else
        zesu_contains_existential_resource expanded
  end.

Ltac zesu_open_existential_package_step :=
  first [
    progress iMatchHyp ltac:(fun H body =>
      lazymatch body with
      | @bi_exist _ _ _ => iDestruct H as (?) H
      end)
  | progress iMatchHyp ltac:(fun H body =>
      lazymatch body with
      | (_ ∗ _)%I => zesu_contains_existential_resource body;
          iDestruct H as "[? ?]"
      end)
  | progress iMatchHyp ltac:(fun H body =>
      let head := get_head body in
      tryif first [constr_eq head constr:(@bi_sep) |
                   constr_eq head constr:(@bi_pure) |
                   constr_eq head constr:(@bi_exist)] then fail else idtac;
      let expanded := eval cbv beta zeta delta [head] in body in
      zesu_contains_existential_resource expanded;
      progress iEval (unfold head) in H;
      ResourceGroups.zesu_open_resource_groups)
  ].

Ltac zesu_open_nested_existential_packages :=
  zesu_open_existential_package_step;
  repeat zesu_open_existential_package_step;
  ResourceGroups.zesu_open_resource_groups.

(* Preserve every package component before selecting the requested field. *)
Ltac ResourceGroups.zesu_open_requested_struct_sys_package ::=
  ResourceGroups.zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindStructRegMapsTo _ _) _) =>
      progress zesu_open_nested_existential_packages
  end.


#[local] Instance diagnostic_decode_item_sys_regs_unfold :
 LithiumUnfold (@ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemSysRegs) := I.

Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Lemma zesu_bv64_clear_low_bit_even (value : bv 64) :
  (bv_unsigned value mod 2 = 0)%Z ->
  bv_and value (BV 64 18446744073709551614) = value.
Proof.
 intro Heven.
 assert (Hlow : bv_extract 0 1 value = BV 1 0).
 { apply bv_eq. rewrite bv_extract_0_unsigned.
   change (bv_unsigned value mod 2 = 0)%Z. exact Heven. }
 apply bv_eq.
 pose proof (normalize_instr_addr_riscv64_ret_tac value _ Hlow eq_refl) as Hnormalized.
 rewrite !bv_wrap_bv_unsigned in Hnormalized.
 rewrite (bv_add_0_r value (BV 64 0) eq_refl) in Hnormalized.
 rewrite (bv_or_0_r (bv_and value (BV 64 18446744073709551614)) (BV 64 0) eq_refl) in Hnormalized.
 exact Hnormalized.
Qed.
Print Assumptions zesu_bv64_clear_low_bit_even.

(* Inspect the requested low-bit mask before using existing integer bounds. *)
Ltac zesu_return_integer_even_mask :=
  repeat match goal with
  | |- context [bv_add ?word (BV 64 0)] =>
      rewrite (bv_add_0_r word (BV 64 0) eq_refl)
  end;
  lazymatch goal with
  | |- context [bv_and ?value (BV 64 18446744073709551614)] =>
      assert_fails (has_evar value);
      let Heven := fresh "HreturnWordEven" in
      assert (Heven : (bv_unsigned value mod 2 = 0)%Z) by (
        first [assumption |
          lazymatch value with
          | Z_to_bv 64 ?integer =>
              let Hrange := fresh "HreturnIntegerRange" in
              assert (Hrange : (0 <= integer < 2 ^ 64)%Z) by lia;
              rewrite Z_to_bv_unsigned;
              rewrite (bv_wrap_small 64 integer Hrange);
              match goal with
              | Haligned : (integer mod 4 = 0)%Z |- _ => lia
              end
          end]);
      rewrite (zesu_bv64_clear_low_bit_even value Heven);
      clear Heven;
      repeat match goal with
      | |- context [bv_or ?word (BV 64 0)] =>
          rewrite (bv_or_0_r word (BV 64 0) eq_refl)
      end;
      try (lazymatch value with
      | Z_to_bv 64 ?integer =>
          let Hrange := fresh "HreturnIntegerRange" in
          assert (Hrange : (0 <= integer < 2 ^ 64)%Z) by lia;
          rewrite (Z_to_bv_unsigned 64 integer);
          rewrite (bv_wrap_small 64 integer Hrange);
          clear Hrange
      end)
  end.

From Coq Require Import Lia.
From stdpp Require Import list.
From iris.proofmode Require Import environments.
Import ZesuSsz.Automation.SwitchDispatch ZesuSsz.Automation.Hooks.
Class ZesuStepCodecArrayRange : Prop := {}.

(* Length does not depend on the symbolic payload. Only closed counts and
   widths enter this presentation rule. Unsupported codecs must remain refused. *)
Ltac zesu_codec_range_lengths :=
  lazymatch goal with
  | |- context [length (bv_to_little_endian _ _ _)] => idtac
  end;
  repeat match goal with
  | |- context [length (bv_to_little_endian ?count ?width ?value)] =>
      is_closed_term count; is_closed_term width;
      let nonnegative := fresh "HcodecCount" in
      assert (nonnegative : (0 <= count)%Z) by lia;
      rewrite (length_bv_to_little_endian count width value nonnegative);
      clear nonnegative
  end;
  lazymatch goal with
  | |- context [length (bv_to_little_endian _ _ _)] => fail 1
  | _ => idtac
  end.

(* The existing closed-term adapter computes only closed integer terms.
   It preserves symbolic bases. No resource or entry assumption is changed. *)
Ltac zesu_codec_array_range :=
  zesu_switch_enabled constr:(ZesuStepCodecArrayRange);
  solve [
    zesu_codec_range_lengths;
    lazymatch goal with
    | |- (?lower <= ?pointer < ?upper)%Z =>
        ZesuSsz.Automation.Hooks.zesu_handoff_closed_Z lower ltac:(fun low =>
        ZesuSsz.Automation.Hooks.zesu_handoff_closed_Z pointer ltac:(fun point =>
        ZesuSsz.Automation.Hooks.zesu_handoff_closed_Z upper ltac:(fun high =>
          change (low <= point < high)%Z;
          lia)))
    end
  ].
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
  try (lazymatch goal with |- SHELVED_SIDECOND ?condition => change condition end);
  lazymatch goal with
  | |- (0 <= ?offset)%Z =>
      Hooks.zesu_handoff_closed_Z offset ltac:(fun reduced =>
        change (0 <= reduced)%Z; lia)
  | |- (Z.to_nat ?offset + ?width <= ?extent)%nat =>
      Hooks.zesu_handoff_closed_Z offset ltac:(fun reduced =>
        change (Z.to_nat reduced + width <= extent)%nat;
        cbn [length];
        first [
          let rec literal_extent n :=
            lazymatch n with
            | O => idtac
            | S ?tail => literal_extent tail
            end in
          literal_extent extent
        | zesu_codec_range_lengths];
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
  first [
    lazymatch type of image with
    | context [Z_to_bv ?bits (little_endian_to_bv ?width
        (bv_to_little_endian ?digits ?width (bv_unsigned ?word)))] =>
        rewrite (Z_to_bv_little_endian_to_bv_to_little_endian
          bits digits width word ltac:(lia) ltac:(reflexivity)) in image
    end
  | lazymatch type of image with
    | context [Z_to_bv ?bits (little_endian_to_bv ?width
        (bv_to_little_endian ?digits ?width ?value))] =>
        is_closed_term bits; is_closed_term digits; is_closed_term width;
        let roundtrip := fresh "HcodecRoundtrip" in
        assert (roundtrip :
          Z_to_bv bits (little_endian_to_bv width
            (bv_to_little_endian digits width value)) = Z_to_bv bits value) by (
          apply bv_eq; rewrite !Z_to_bv_unsigned;
          rewrite (little_endian_to_bv_to_little_endian digits width value ltac:(lia));
          change (bv_wrap bits (bv_wrap bits value) = bv_wrap bits value);
          apply bv_wrap_bv_wrap; lia);
        rewrite roundtrip in image; clear roundtrip
    end].

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

(* Normalize only a codec value requested by the current goal. *)
Ltac zesu_codec_array_direct_prepare continuation :=
  zesu_switch_enabled constr:(ZesuStepCodecArrayRead);
  let inspect target :=
    lazymatch target with
    | context [Z_to_bv ?bits (little_endian_to_bv ?width
        (take ?count (drop (Z.to_nat ?offset) ?values)))] =>
        let expression := constr:(Z_to_bv bits (little_endian_to_bv width
          (take count (drop (Z.to_nat offset) values)))) in
        assert_fails (has_evar expression);
        let loaded := fresh "codecDirectValue" in
        let image := fresh "HcodecDirectImage" in
        remember expression as loaded eqn:image in *;
        continuation loaded image
    end in
  lazymatch goal with
  | |- environments.envs_entails _ ?target => inspect target
  | |- ?target => inspect target
  end.

Ltac zesu_codec_array_direct_value :=
  zesu_codec_array_direct_prepare ltac:(fun loaded image =>
    zesu_codec_array_read_image image;
    subst loaded;
    try zesu_return_integer_even_mask).

Ltac zesu_codec_array_read :=
  first [zesu_codec_array_find |
    zesu_codec_array_read_consumer |
    zesu_codec_array_direct_value |
    zesu_codec_array_read_sidecond].
#[local] Instance exact_codec_read_enabled : ZesuStepCodecArrayRead := {}.
#[local] Instance exact_register_selector_enabled : Hooks.ZesuStepRegisterCollectionSelection := {}.


Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.ResourceGroups.
Ltac zesu_prefer_owned_instr_pre :=
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindInstrKind _ _) _) =>
      try zesu_return_integer_even_mask;
      zesu_expose_environment_alias;
      lazymatch goal with
      | |- envs_entails _ (find_in_context (FindInstrKind ?requested ?later) ?T) =>
          assert_fails (has_evar requested);
          iMatchHyp ltac:(fun name body =>
            lazymatch body with
            | instr_pre' ?available_later ?available ?P =>
                assert_fails (has_evar available);
                constr_eq available requested;
                lazymatch later with
                | true =>
                    iApply (find_in_context_instr_kind_pre_true requested T);
                    iExists available_later, P; iFrame name
                | false =>
                    constr_eq available_later false;
                    iApply (find_in_context_instr_kind_pre_false requested T);
                    iExists P; iFrame name
                end
            end)
      end
  end.

Ltac zesu_liAStep ::=
 liEnsureInvariant;
 try progress (unfold TRACE_LET);
 try liAIntroduceLetInGoal;
 first [
    progress zesu_open_nested_existential_packages
  | zesu_codec_array_read
  | zesu_prefer_owned_instr_pre
  | zesu_expose_instruction_lookup
  | zesu_region_fault_if_enabled
  | zesu_ram_fault_if_enabled
  | zesu_signed_address_if_enabled
  | zesu_stack_write_if_enabled
  | zesu_handoff_goal_address_if_enabled
  | zesu_handoff_memory_if_enabled
  | zesu_handoff_adjacent_words_if_enabled
  | zesu_handoff_facts_if_enabled
  | zesu_handoff_integer_equality_if_enabled
  | zesu_integer_array_address_if_enabled
  | zesu_normalize_find_mem_address
  | zesu_liAWriteMem
  | zesu_liAReadMem
  | liAAsm
  | liAExp
  | liAOther
  | zesu_pure_fact_hints_if_enabled
  | zesu_known_pair_conjunct_witness_if_enabled
  | liUnfoldEarly
  | zesu_conjunct_head_if_enabled
  | zesu_known_pair_witness_if_enabled
  | zesu_pure_witness_constraints_if_enabled
  | zesu_record_witness_if_enabled
  | zesu_primitive_tuple_if_enabled
  | zesu_liInstrPreMatch
  | zesu_preserve_current_unsigned
  | zesu_register_collection_selection_if_enabled
  | liStep
  | liLetBindHint
  | liUnfoldLate
 ]; liSimpl.

Ltac liAStep ::= zesu_liAStep.


Ltac zesu_array_bounds_if_enabled ::=
 first [zesu_codec_array_read_sidecond | zesu_array_bounds_base | zesu_array_bounds_extended].

Require Import ZesuSsz.Automation.FramePackingFinish167.
Require Import ZesuSsz.Automation.ArrayContinuation167.
Require Import ZesuSsz.Automation.EffectiveOverrides.
(* Normalize only a closed low-mask addition with an existing one-wrap range. *)
Ltac zesu_masked_add_branch_finish :=
  solve [
    match goal with
    | branch : ~ (?masked_expression >= ?bound_expression)%Z |- _ =>
      lazymatch masked_expression with
      | bv_unsigned (bv_and (bv_add (Z_to_bv ?width ?value) ?offset) ?mask) =>
        is_closed_term width; is_closed_term offset; is_closed_term mask;
        assert_fails (has_evar value);
        let delta := eval vm_compute in (bv_unsigned offset) in
        let low := eval vm_compute in (N.log2 (Z.to_N (bv_unsigned mask + 1)%Z)) in
        let modulus := eval vm_compute in (bv_modulus low) in
        let base := constr:(Z_to_bv width value) in
        let cast := fresh "HmaskedBaseCast" in
        assert (cast : bv_unsigned base = value) by
          (apply Z_to_bv_small;
           ZesuSsz.Automation.HypothesisCast.zesu_hypothesis_cast_range width value);
        let widths := fresh "HmaskedWidths" in
        assert (widths : (low <= width)%N) by (vm_compute; congruence);
        let bits := fresh "HmaskedBits" in
        assert (bits : bv_unsigned mask = Z.ones (Z.of_N low)) by
          (vm_compute; reflexivity);
        let range := fresh "HmaskedOneWrap" in
        assert (range : (bv_modulus low <= bv_unsigned base + delta < 2 * bv_modulus low)%Z) by
          (rewrite cast; change (modulus <= value + delta < 2 * modulus)%Z; lia);
        let image := fresh "HmaskedAddImage" in
        assert (image : masked_expression = (value + delta - modulus)%Z) by
          (change (bv_unsigned (bv_and (bv_add base (Z_to_bv width delta)) mask) = (value + delta - modulus)%Z);
           rewrite (ZesuSsz.Automation.BitvectorFacts.zesu_unsigned_low_mask_add_sub_modulus
             width low base mask delta widths bits range) cast;
           reflexivity);
        rewrite image in branch;
        lazymatch bound_expression with
        | bv_unsigned (Z_to_bv ?bound_width ?bound) =>
          let bound_cast := fresh "HmaskedBoundCast" in
          assert (bound_cast : bv_unsigned (Z_to_bv bound_width bound) = bound) by
            (apply Z_to_bv_small;
             ZesuSsz.Automation.HypothesisCast.zesu_hypothesis_cast_range bound_width bound);
          rewrite bound_cast in branch
        | _ => idtac
        end;
        lia
      end
    end].

Ltac ZesuSsz.Automation.Finish.zesu_finish_residual_cascade ::=
  first [solve [zesu_masked_add_branch_finish]
  | solve [zesu_finish_residual_switches;
      let frame := fresh "HregisteredFramePacking" in
      assert (frame : ZesuSsz.Automation.FramePacking.ZesuStepFramePacking) by constructor;
      ZesuSsz.Automation.FramePackingFinish167.zesu_frame_packing_finish]
  | solve [zesu_finish_residual_switches;
      let frame := fresh "HregisteredFramePacking" in
      let array := fresh "HregisteredArrayContinuation" in
      assert (frame : ZesuSsz.Automation.FramePacking.ZesuStepFramePacking) by constructor;
      assert (array : ZesuSsz.Automation.ArrayContinuation167.ZesuStepArrayContinuation) by constructor;
      ZesuSsz.Automation.ArrayContinuation167.zesu_array_continuation
        ltac:(ZesuSsz.Automation.FramePackingFinish167.zesu_frame_packing_finish)]
  | solve [
    zesu_finish_residual_switches;
    first [ solve [ZesuSsz.Automation.HypothesisCast.zesu_hypothesis_cast_finish]
          | solve [ZesuSsz.Automation.ByteMaskCast.zesu_byte_mask_cast]
          | solve [ZesuSsz.Automation.ByteReconstruction.zesu_byte_reconstruction ltac:(lia)]
          | solve [ZesuSsz.Automation.SymbolicByteCodec.zesu_symbolic_byte_codec]
          | solve [ZesuSsz.Automation.MaskPresentation.zesu_mask_sign_extend_presentation]
          | solve [ZesuSsz.Automation.MaskWrapPresentation.zesu_mask_wrap_presentation]
          | solve [ZesuSsz.Automation.BranchCastUnsigned.zesu_unsigned_branch_cast_evidence]
          | solve [ZesuSsz.Automation.BranchUnsigned.zesu_unsigned_branch_evidence]
          | solve [ZesuSsz.Automation.FramePackingFinish.zesu_frame_packing_finish]
          | solve [ZesuSsz.Automation.ArrayPayloadPresentation.zesu_array_payload_presentation
              ltac:(first [ZesuSsz.Automation.SymbolicByteCodec.zesu_symbolic_byte_codec |
      ZesuSsz.Automation.FramePackingFinish.zesu_frame_packing_finish])] ]
  ]].

Lemma DesignedBoundary_800d6aa8 `{!islaG Sigma} `{!threadG}
  (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) (entry_fact_0 : (decodeItemReturnAddress ( args ) = ( returnAddress ))%Z) (entry_fact_1 : (( decodeItemInputLength ( args ) ) = Z.of_nat ( List.length ( decodeItemInputBytes ( args ) ) ))%Z) (entry_fact_2 : (List.length ( decodeItemBeforeStorage ( args ) ) = 40)%nat) (entry_fact_3 : (0 <= ( decodeItemInputPointer ( args ) ))%Z) (entry_fact_4 : (0 <= ( decodeItemInputLength ( args ) ))%Z) (entry_fact_5 : (0 <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_6 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_7 : (( decodeItemOutputPointer ( args ) ) + 40 < ( 18446744073709551616 ))%Z) (entry_fact_8 : (( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_9 : (( decodeItemStackPointer ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_10 : (( 2684354560 ) + ( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_11 : (( decodeItemStackPointer ( args ) ) <= ( 3221225472 ))%Z) (entry_fact_12 : (0 <= ( decodeItemReturnAddress ( args ) ))%Z) (entry_fact_13 : (( decodeItemReturnAddress ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_14 : (( decodeItemReturnAddress ( args ) ) mod 4 = 0)%Z) (entry_fact_15 : (( 2684354560 ) <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_16 : (( decodeItemOutputPointer ( args ) ) + 40 <= ( 3221225472 ))%Z) (entry_fact_17 : (0 <= ( decodeItemInputEnd ( args ) ))%Z) (entry_fact_18 : (( decodeItemInputEnd ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_19 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) <= ( decodeItemInputEnd ( args ) ))%Z) :
  instr_pre 0x800d6ae0 (machineRejectJoin200 (args) (returnAddress) (K) (entry_fact_0) (entry_fact_1) (entry_fact_2) (entry_fact_3) (entry_fact_4) (entry_fact_5) (entry_fact_6) (entry_fact_7) (entry_fact_8) (entry_fact_9) (entry_fact_10) (entry_fact_11) (entry_fact_12) (entry_fact_13) (entry_fact_14) (entry_fact_15) (entry_fact_16) (entry_fact_17) (entry_fact_18) (entry_fact_19)) -∗
  instr_pre 0x800d6ab4 (machineAt6ab4_180 (args) (returnAddress) (K) (entry_fact_0) (entry_fact_1) (entry_fact_2) (entry_fact_3) (entry_fact_4) (entry_fact_5) (entry_fact_6) (entry_fact_7) (entry_fact_8) (entry_fact_9) (entry_fact_10) (entry_fact_11) (entry_fact_12) (entry_fact_13) (entry_fact_14) (entry_fact_15) (entry_fact_16) (entry_fact_17) (entry_fact_18) (entry_fact_19)) -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6aa8 (machineAt6aa8_180 (args) (returnAddress) (K) (entry_fact_0) (entry_fact_1) (entry_fact_2) (entry_fact_3) (entry_fact_4) (entry_fact_5) (entry_fact_6) (entry_fact_7) (entry_fact_8) (entry_fact_9) (entry_fact_10) (entry_fact_11) (entry_fact_12) (entry_fact_13) (entry_fact_14) (entry_fact_15) (entry_fact_16) (entry_fact_17) (entry_fact_18) (entry_fact_19)).

Proof.
zesu_block.
Qed.
Print Assumptions DesignedBoundary_800d6aa8.
