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

Require Import ZesuSsz.Automation.EffectiveOverrides.

Require Import ZesuSsz.Automation.AdditiveDecoder.
Lemma exact6aa8_frame157
(Sigma : gFunctors)
(islaG0 : islaG Sigma)
(H : threadG)
(args : DecodeItemArgs)
(K : uPred (iResUR Sigma))
(entry_fact_1 : @eq Z (decodeItemInputLength args)
  (Z.of_nat
     (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
        (decodeItemInputBytes args))))
(entry_fact_2 : @eq nat
  (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
     (decodeItemBeforeStorage args))
  (S
     (S
        (S
           (S
              (S
                 (S
                    (S
                       (S
                          (S
                             (S
                                (S
                                   (S
                                      (S
                                         (S
                                            (S
                                               (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))
(entry_fact_3 : Z.le Z0 (decodeItemInputPointer args))
(entry_fact_4 : Z.le Z0 (decodeItemInputLength args))
(entry_fact_5 : Z.le Z0 (decodeItemOutputPointer args))
(entry_fact_6 : Z.lt (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_7 : Z.lt
  (Z.add (decodeItemOutputPointer args) (Zpos (xO (xO (xO (xI (xO xH)))))))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_8 : Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
(entry_fact_9 : Z.lt (decodeItemStackPointer args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_10 : Z.le
  (Z.add
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
     (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
(entry_fact_11 : Z.le (decodeItemStackPointer args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
(entry_fact_12 : Z.le Z0 (decodeItemReturnAddress args))
(entry_fact_13 : Z.lt (decodeItemReturnAddress args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_14 : @eq Z (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0)
(entry_fact_15 : Z.le
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
  (decodeItemOutputPointer args))
(entry_fact_16 : Z.le
  (Z.add (decodeItemOutputPointer args) (Zpos (xO (xO (xO (xI (xO xH)))))))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
(entry_fact_17 : Z.le Z0 (decodeItemInputEnd args))
(entry_fact_18 : Z.lt (decodeItemInputEnd args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_19 : Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
  (decodeItemInputEnd args))
(frameBytes : list (bv (Npos (xO (xO (xO xH))))))
(H0 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))
(H1 : Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H2 : Z.le (Zpos (xO (xO (xO (xI (xI (xI (xI xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H3 : Z.le
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
  (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
(H4 : not
  (@eq (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xO (xO (xO (xO (xO (xO (xO xH)))))))) I)))
(H5 : not
  (@eq Z
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))))
(H6 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_sign_extend (Npos (xO (xO (xO xH))))
              (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
(H7 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H8 : Z.ge
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_sign_extend (Npos (xO (xO (xO xH))))
              (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I)))
(H9 : Z.ge
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
  (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))))
(H10 : Z.ge
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_sign_extend (Npos (xO (xO (xO xH))))
              (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Zpos (xO (xO (xO (xI (xI (xI (xI xH)))))))) I)))
(H11 : Z.ge
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
  (Zpos (xO (xO (xO (xI (xI (xI (xI xH)))))))))
(H12 : @eq Z
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H13 : Z.le (Zpos xH)
  (Z.sub
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xI (xI (xI (xO (xI (xI (xI xH))))))))))
(H14 : Z.le
  (Z.sub
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xI (xI (xI (xO (xI (xI (xI xH))))))))) 
  (Zpos (xO (xO (xO xH)))))
(H15 : @eq nat (@Datatypes.length (bv (Npos (xO (xO (xO xH))))) frameBytes)
  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))
(H16 : @eq nat
  (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
     (@firstn (bv (Npos (xO (xO (xO xH))))) (S (S (S (S (S (S (S (S O))))))))
        (@skipn (bv (Npos (xO (xO (xO xH))))) O frameBytes)))
  (S (S (S (S (S (S (S (S O)))))))))
(H17 : @eq nat
  (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
     (@firstn (bv (Npos (xO (xO (xO xH))))) (S (S (S (S (S (S (S (S O))))))))
        (@skipn (bv (Npos (xO (xO (xO xH)))))
           (S (S (S (S (S (S (S (S O)))))))) frameBytes)))
  (S (S (S (S (S (S (S (S O)))))))))
(H18 : Z.le (decodeItemInputLength args)
  (Zpos
     (xI
        (xI
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H19 : @eq Z
  (littleEndian
     (@firstn (bv (Npos (xO (xO (xO xH))))) (S (S (S (S (S (S (S (S O))))))))
        (@skipn (bv (Npos (xO (xO (xO xH))))) O frameBytes)))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (decodeItemSavedFramePointer args)))
(H20 : @eq Z
  (littleEndian
     (@firstn (bv (Npos (xO (xO (xO xH))))) (S (S (S (S (S (S (S (S O))))))))
        (@skipn (bv (Npos (xO (xO (xO xH)))))
           (S (S (S (S (S (S (S (S O)))))))) frameBytes)))
  (decodeItemReturnAddress args))
(b : bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
(H21 : @eq Z
  (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))))
  Z0)
(b0 : bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
(H22 : @eq Z
  (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))))
  Z0)
(b1 : bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
(H23 : @eq Z
  (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b1)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))))
  Z0)
(H24 : not
  (Z.ge
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_add (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@bv_unsigned (Npos (xO (xO (xO xH))))
                       (@nth (bv (Npos (xO (xO (xO xH))))) O
                          (decodeItemInputBytes args)
                          (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xO (xO xH)))) I))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (decodeItemInputLength args))))))
(zesuFinishAttempted : @zesu_context_finish_attempted Prop
  (@eq (list (bv (Npos (xO (xO (xO xH)))))) frameBytes
     (@cons (bv (Npos (xO (xO (xO xH)))))
        (Z_to_bv (Npos (xO (xO (xO xH))))
           (Z.land
              (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (decodeItemSavedFramePointer args))
              (Z.ones (Zpos (xO (xO (xO xH)))))))
        (@cons (bv (Npos (xO (xO (xO xH)))))
           (Z_to_bv (Npos (xO (xO (xO xH))))
              (Z.land
                 (Z.shiftr
                    (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                       (decodeItemSavedFramePointer args))
                    (Zpos (xO (xO (xO xH)))))
                 (Z.ones (Zpos (xO (xO (xO xH)))))))
           (@cons (bv (Npos (xO (xO (xO xH)))))
              (Z_to_bv (Npos (xO (xO (xO xH))))
                 (Z.land
                    (Z.shiftr
                       (Z.shiftr
                          (@bv_unsigned
                             (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                             (decodeItemSavedFramePointer args))
                          (Zpos (xO (xO (xO xH))))) 
                       (Zpos (xO (xO (xO xH)))))
                    (Z.ones (Zpos (xO (xO (xO xH)))))))
              (@cons (bv (Npos (xO (xO (xO xH)))))
                 (Z_to_bv (Npos (xO (xO (xO xH))))
                    (Z.land
                       (Z.shiftr
                          (Z.shiftr
                             (Z.shiftr
                                (@bv_unsigned
                                   (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                                   (decodeItemSavedFramePointer args))
                                (Zpos (xO (xO (xO xH)))))
                             (Zpos (xO (xO (xO xH)))))
                          (Zpos (xO (xO (xO xH)))))
                       (Z.ones (Zpos (xO (xO (xO xH)))))))
                 (@cons (bv (Npos (xO (xO (xO xH)))))
                    (Z_to_bv (Npos (xO (xO (xO xH))))
                       (Z.land
                          (Z.shiftr
                             (Z.shiftr
                                (Z.shiftr
                                   (Z.shiftr
                                      (@bv_unsigned
                                         (Npos
                                            (xO (xO (xO (xO (xO (xO xH)))))))
                                         (decodeItemSavedFramePointer args))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Zpos (xO (xO (xO xH)))))
                                (Zpos (xO (xO (xO xH)))))
                             (Zpos (xO (xO (xO xH)))))
                          (Z.ones (Zpos (xO (xO (xO xH)))))))
                    (@cons (bv (Npos (xO (xO (xO xH)))))
                       (Z_to_bv (Npos (xO (xO (xO xH))))
                          (Z.land
                             (Z.shiftr
                                (Z.shiftr
                                   (Z.shiftr
                                      (Z.shiftr
                                         (Z.shiftr
                                            (@bv_unsigned
                                               (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                               (decodeItemSavedFramePointer
                                                 args))
                                            (Zpos (xO (xO (xO xH)))))
                                         (Zpos (xO (xO (xO xH)))))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Zpos (xO (xO (xO xH)))))
                                (Zpos (xO (xO (xO xH)))))
                             (Z.ones (Zpos (xO (xO (xO xH)))))))
                       (@cons (bv (Npos (xO (xO (xO xH)))))
                          (Z_to_bv (Npos (xO (xO (xO xH))))
                             (Z.land
                                (Z.shiftr
                                   (Z.shiftr
                                      (Z.shiftr
                                         (Z.shiftr
                                            (Z.shiftr
                                               (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (decodeItemSavedFramePointer
                                                 args))
                                                 (Zpos (xO (xO (xO xH)))))
                                               (Zpos (xO (xO (xO xH)))))
                                            (Zpos (xO (xO (xO xH)))))
                                         (Zpos (xO (xO (xO xH)))))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Zpos (xO (xO (xO xH)))))
                                (Z.ones (Zpos (xO (xO (xO xH)))))))
                          (@cons (bv (Npos (xO (xO (xO xH)))))
                             (Z_to_bv (Npos (xO (xO (xO xH))))
                                (Z.land
                                   (Z.shiftr
                                      (Z.shiftr
                                         (Z.shiftr
                                            (Z.shiftr
                                               (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (decodeItemSavedFramePointer
                                                 args))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                               (Zpos (xO (xO (xO xH)))))
                                            (Zpos (xO (xO (xO xH)))))
                                         (Zpos (xO (xO (xO xH)))))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Z.ones (Zpos (xO (xO (xO xH)))))))
                             (bv_to_little_endian
                                (Z.of_nat (S (S (S (S (S (S (S (S O)))))))))
                                (Npos (xO (xO (xO xH))))
                                (@bv_unsigned
                                   (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                                   (Z_to_bv
                                      (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                                      (decodeItemReturnAddress args))))))))))))))
(H25 : and
  (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b1))
  (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b1)
     (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H26 : forall _ : not (@eq N (Npos (xO (xO (xO (xO (xO (xO xH))))))) N0),
and
  (Z.le (Z.opp (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b1))
  (Z.lt (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b1)
     (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H27 : and
  (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
  (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H28 : forall _ : not (@eq N (Npos (xO (xO (xO (xO (xO (xO xH))))))) N0),
and
  (Z.le (Z.opp (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
  (Z.lt (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H29 : and (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
  (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H30 : forall _ : not (@eq N (Npos (xO (xO (xO (xO (xO (xO xH))))))) N0),
and
  (Z.le (Z.opp (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
  (Z.lt (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H31 : Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
(H32 : @eq bool
  (@bool_decide
     (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
     (@decide_rel Z Z Z.lt Z.lt_dec (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))) true)
(H33 : Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
  (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
(H34 : @eq bool
  (@bool_decide
     (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))) true)
(H35 : Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
(H36 : @eq bool
  (@bool_decide
     (Z.lt (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
     (@decide_rel Z Z Z.lt Z.lt_dec (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))) true)
(H37 : Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
  (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
(H38 : @eq bool
  (@bool_decide
     (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))) true)
(H39 : Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b1))
(H40 : @eq bool
  (@bool_decide
     (Z.lt (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b1))
     (@decide_rel Z Z Z.lt Z.lt_dec (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b1))) true)
(H41 : Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b1)
  (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
(H42 : @eq bool
  (@bool_decide
     (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b1)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b1)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))) true)
(H43 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b1)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b1)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)) true)
(H44 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)) true)
(H45 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)) true)
(H46 : @eq bool
  (@bool_decide
     (@eq Z
        (littleEndian
           (@firstn (bv (Npos (xO (xO (xO xH)))))
              (S (S (S (S (S (S (S (S O))))))))
              (@skipn (bv (Npos (xO (xO (xO xH)))))
                 (S (S (S (S (S (S (S (S O)))))))) frameBytes)))
        (decodeItemReturnAddress args))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (littleEndian
           (@firstn (bv (Npos (xO (xO (xO xH)))))
              (S (S (S (S (S (S (S (S O))))))))
              (@skipn (bv (Npos (xO (xO (xO xH)))))
                 (S (S (S (S (S (S (S (S O)))))))) frameBytes)))
        (decodeItemReturnAddress args))) true)
(H47 : @eq bool
  (@bool_decide
     (@eq Z
        (littleEndian
           (@firstn (bv (Npos (xO (xO (xO xH)))))
              (S (S (S (S (S (S (S (S O))))))))
              (@skipn (bv (Npos (xO (xO (xO xH))))) O frameBytes)))
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (decodeItemSavedFramePointer args)))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (littleEndian
           (@firstn (bv (Npos (xO (xO (xO xH)))))
              (S (S (S (S (S (S (S (S O))))))))
              (@skipn (bv (Npos (xO (xO (xO xH))))) O frameBytes)))
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (decodeItemSavedFramePointer args)))) true)
(H48 : @eq bool
  (@bool_decide
     (Z.le (decodeItemInputLength args)
        (Zpos
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec (decodeItemInputLength args)
        (Zpos
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H49 : @eq Z
  (Z.of_nat
     (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
        (@firstn (bv (Npos (xO (xO (xO xH)))))
           (S (S (S (S (S (S (S (S O))))))))
           (@skipn (bv (Npos (xO (xO (xO xH)))))
              (S (S (S (S (S (S (S (S O)))))))) frameBytes))))
  (Z.of_nat (S (S (S (S (S (S (S (S O))))))))))
(H50 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (@firstn (bv (Npos (xO (xO (xO xH)))))
                 (S (S (S (S (S (S (S (S O))))))))
                 (@skipn (bv (Npos (xO (xO (xO xH)))))
                    (S (S (S (S (S (S (S (S O)))))))) frameBytes))))
        (Z.of_nat (S (S (S (S (S (S (S (S O))))))))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (@firstn (bv (Npos (xO (xO (xO xH)))))
                 (S (S (S (S (S (S (S (S O))))))))
                 (@skipn (bv (Npos (xO (xO (xO xH)))))
                    (S (S (S (S (S (S (S (S O)))))))) frameBytes))))
        (Z.of_nat (S (S (S (S (S (S (S (S O))))))))))) true)
(H51 : @eq Z
  (Z.of_nat
     (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
        (@firstn (bv (Npos (xO (xO (xO xH)))))
           (S (S (S (S (S (S (S (S O))))))))
           (@skipn (bv (Npos (xO (xO (xO xH))))) O frameBytes))))
  (Z.of_nat (S (S (S (S (S (S (S (S O))))))))))
(H52 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (@firstn (bv (Npos (xO (xO (xO xH)))))
                 (S (S (S (S (S (S (S (S O))))))))
                 (@skipn (bv (Npos (xO (xO (xO xH))))) O frameBytes))))
        (Z.of_nat (S (S (S (S (S (S (S (S O))))))))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (@firstn (bv (Npos (xO (xO (xO xH)))))
                 (S (S (S (S (S (S (S (S O))))))))
                 (@skipn (bv (Npos (xO (xO (xO xH))))) O frameBytes))))
        (Z.of_nat (S (S (S (S (S (S (S (S O))))))))))) true)
(H53 : @eq Z (Z.of_nat (@Datatypes.length (bv (Npos (xO (xO (xO xH))))) frameBytes))
  (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))
(H54 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH))))) frameBytes))
        (Z.of_nat
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH))))) frameBytes))
        (Z.of_nat
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))
  true)
(H55 : @eq bool
  (@bool_decide
     (Z.le
        (Z.sub
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xO (xI (xI (xI xH)))))))))
        (Zpos (xO (xO (xO xH)))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.sub
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xO (xI (xI (xI xH)))))))))
        (Zpos (xO (xO (xO xH)))))) true)
(H56 : @eq bool
  (@bool_decide
     (Z.le (Zpos xH)
        (Z.sub
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xO (xI (xI (xI xH))))))))))
     (@decide_rel Z Z Z.le Z.le_dec (Zpos xH)
        (Z.sub
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xO (xI (xI (xI xH))))))))))) true)
(H57 : @eq bool
  (@bool_decide
     (@eq Z
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H58 : @eq (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
  (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_sign_extend (Npos (xO (xO (xO xH))))
        (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))
  (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
(H59 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xI xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos (xO (xO (xO (xI (xI (xI (xI xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H60 : Z.le
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Zpos (xO (xO (xO (xI (xI (xI (xI xH)))))))) I))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_sign_extend (Npos (xO (xO (xO xH))))
              (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
(H61 : @eq bool
  (@bool_decide
     (Z.le
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xO (xO (xO (xI (xI (xI (xI xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
     (@decide_rel Z Z Z.le Z.le_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xO (xO (xO (xI (xI (xI (xI xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))) true)
(H62 : Z.le (Zpos (xO (xO (xO (xO (xO (xO (xI xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H63 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xI xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos (xO (xO (xO (xO (xO (xO (xI xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H64 : Z.le
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_sign_extend (Npos (xO (xO (xO xH))))
              (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
(H65 : @eq bool
  (@bool_decide
     (Z.le
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
     (@decide_rel Z Z Z.le Z.le_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))) true)
(H66 : @eq bool
  (@bool_decide
     (Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H67 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))) true)
(H68 : @eq bool
  (@bool_decide
     (Z.le
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
     (@decide_rel Z Z Z.le Z.le_dec
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))) true)
(H69 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H70 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))) true)
(H71 : @eq bool
  (@bool_decide
     (Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (decodeItemInputEnd args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (decodeItemInputEnd args))) true)
(H72 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemInputEnd args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemInputEnd args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H73 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputEnd args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputEnd args))) true)
(H74 : @eq bool
  (@bool_decide
     (Z.le
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
  true)
(H75 : @eq bool
  (@bool_decide
     (Z.le
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (decodeItemOutputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (decodeItemOutputPointer args))) true)
(H76 : @eq bool
  (@bool_decide
     (@eq Z (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0))
  true)
(H77 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemReturnAddress args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemReturnAddress args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H78 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemReturnAddress args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemReturnAddress args))) true)
(H79 : @eq bool
  (@bool_decide
     (Z.le (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
  true)
(H80 : @eq bool
  (@bool_decide
     (Z.le
        (Z.add
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
           (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
           (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args)))
  true)
(H81 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H82 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
     (@decide_rel Z Z Z.le Z.le_dec (Zpos (xO (xO (xO (xO xH)))))
        (decodeItemStackPointer args))) true)
(H83 : @eq bool
  (@bool_decide
     (Z.lt
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H84 : @eq bool
  (@bool_decide
     (Z.lt (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H85 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemOutputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemOutputPointer args))) true)
(H86 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputLength args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputLength args))) true)
(H87 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputPointer args))) true)
(H88 : @eq Z
  (Z.of_nat
     (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
        (decodeItemBeforeStorage args)))
  (Z.of_nat
     (S
        (S
           (S
              (S
                 (S
                    (S
                       (S
                          (S
                             (S
                                (S
                                   (S
                                      (S
                                         (S
                                            (S
                                               (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))
(H89 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemBeforeStorage args)))
        (Z.of_nat
           (S
              (S
                 (S
                    (S
                       (S
                          (S
                             (S
                                (S
                                   (S
                                      (S
                                         (S
                                            (S
                                               (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemBeforeStorage args)))
        (Z.of_nat
           (S
              (S
                 (S
                    (S
                       (S
                          (S
                             (S
                                (S
                                   (S
                                      (S
                                         (S
                                            (S
                                               (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))
  true)
(H90 : @eq bool
  (@bool_decide
     (@eq Z (decodeItemInputLength args)
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemInputBytes args))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec (decodeItemInputLength args)
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemInputBytes args))))) true)
(H91 : and
  (Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
     (decodeItemInputEnd args))
  (Z.lt (decodeItemInputEnd args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H92 : and (Z.le Z0 (decodeItemInputEnd args))
  (Z.lt (decodeItemInputEnd args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H93 : and (Z.le Z0 (decodeItemReturnAddress args))
  (Z.lt (decodeItemReturnAddress args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H94 : and
  (Z.le
     (Z.add
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
  (Z.lt (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H95 : and (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
  (Z.lt (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H96 : and (Z.le Z0 (decodeItemInputLength args))
  (Z.le (decodeItemInputLength args)
     (Zpos
        (xI
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H97 : @eq bool
  (andb
     (@bool_decide (Z.le Z0 (decodeItemInputLength args))
        (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputLength args)))
     (@bool_decide
        (Z.le (decodeItemInputLength args)
           (Zpos
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemInputLength args)
           (Zpos
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H98 : and
  (Z.le (Zpos xH)
     (Z.sub
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (Zpos (xI (xI (xI (xO (xI (xI (xI xH))))))))))
  (Z.le
     (Z.sub
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (Zpos (xI (xI (xI (xO (xI (xI (xI xH)))))))))
     (Zpos (xO (xO (xO xH))))))
(H99 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos xH)
           (Z.sub
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (Zpos (xI (xI (xI (xO (xI (xI (xI xH))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (Zpos xH)
           (Z.sub
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (Zpos (xI (xI (xI (xO (xI (xI (xI xH)))))))))))
     (@bool_decide
        (Z.le
           (Z.sub
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (Zpos (xI (xI (xI (xO (xI (xI (xI xH)))))))))
           (Zpos (xO (xO (xO xH)))))
        (@decide_rel Z Z Z.le Z.le_dec
           (Z.sub
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (Zpos (xI (xI (xI (xO (xI (xI (xI xH)))))))))
           (Zpos (xO (xO (xO xH))))))) true)
(H100 : and
  (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xI xH))))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
  (Z.le
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))
(H101 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xI xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
        (@decide_rel Z Z Z.le Z.le_dec
           (Zpos (xO (xO (xO (xO (xO (xO (xI xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
     (@bool_decide
        (Z.le
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
        (@decide_rel Z Z Z.le Z.le_dec
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))) true)
(H102 : and
  (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xI xH))))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
  (Z.le
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))
(H103 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xI xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
        (@decide_rel Z Z Z.le Z.le_dec
           (Zpos (xO (xO (xO (xI (xI (xI (xI xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
     (@bool_decide
        (Z.le
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
        (@decide_rel Z Z Z.le Z.le_dec
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))) true)
(H104 : and
  (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
  (Z.le
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))
(H105 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
        (@decide_rel Z Z Z.le Z.le_dec
           (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
     (@bool_decide
        (Z.le
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
        (@decide_rel Z Z Z.le Z.le_dec
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))) true)
(H106 : and
  (Z.le
     (Z.add
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
  (Z.le (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
(H107 : @eq bool
  (andb
     (@bool_decide
        (Z.le
           (Z.add
              (Zpos
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
              (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
        (@decide_rel Z Z Z.le Z.le_dec
           (Z.add
              (Zpos
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
              (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args)))
     (@bool_decide
        (Z.le (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))))
  true)
(H108 : and (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
  (Z.le (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
(H109 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
        (@decide_rel Z Z Z.le Z.le_dec (Zpos (xO (xO (xO (xO xH)))))
           (decodeItemStackPointer args)))
     (@bool_decide
        (Z.le (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))))
  true)
(zesuFinishAttempted0 : @zesu_context_finish_attempted Prop
  (@eq (list (bv (Npos (xO (xO (xO xH)))))) frameBytes
     (@cons (bv (Npos (xO (xO (xO xH)))))
        (Z_to_bv (Npos (xO (xO (xO xH))))
           (Z.land
              (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (decodeItemSavedFramePointer args))
              (Z.ones (Zpos (xO (xO (xO xH)))))))
        (@cons (bv (Npos (xO (xO (xO xH)))))
           (Z_to_bv (Npos (xO (xO (xO xH))))
              (Z.land
                 (Z.shiftr
                    (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                       (decodeItemSavedFramePointer args))
                    (Zpos (xO (xO (xO xH)))))
                 (Z.ones (Zpos (xO (xO (xO xH)))))))
           (@cons (bv (Npos (xO (xO (xO xH)))))
              (Z_to_bv (Npos (xO (xO (xO xH))))
                 (Z.land
                    (Z.shiftr
                       (Z.shiftr
                          (@bv_unsigned
                             (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                             (decodeItemSavedFramePointer args))
                          (Zpos (xO (xO (xO xH))))) 
                       (Zpos (xO (xO (xO xH)))))
                    (Z.ones (Zpos (xO (xO (xO xH)))))))
              (@cons (bv (Npos (xO (xO (xO xH)))))
                 (Z_to_bv (Npos (xO (xO (xO xH))))
                    (Z.land
                       (Z.shiftr
                          (Z.shiftr
                             (Z.shiftr
                                (@bv_unsigned
                                   (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                                   (decodeItemSavedFramePointer args))
                                (Zpos (xO (xO (xO xH)))))
                             (Zpos (xO (xO (xO xH)))))
                          (Zpos (xO (xO (xO xH)))))
                       (Z.ones (Zpos (xO (xO (xO xH)))))))
                 (@cons (bv (Npos (xO (xO (xO xH)))))
                    (Z_to_bv (Npos (xO (xO (xO xH))))
                       (Z.land
                          (Z.shiftr
                             (Z.shiftr
                                (Z.shiftr
                                   (Z.shiftr
                                      (@bv_unsigned
                                         (Npos
                                            (xO (xO (xO (xO (xO (xO xH)))))))
                                         (decodeItemSavedFramePointer args))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Zpos (xO (xO (xO xH)))))
                                (Zpos (xO (xO (xO xH)))))
                             (Zpos (xO (xO (xO xH)))))
                          (Z.ones (Zpos (xO (xO (xO xH)))))))
                    (@cons (bv (Npos (xO (xO (xO xH)))))
                       (Z_to_bv (Npos (xO (xO (xO xH))))
                          (Z.land
                             (Z.shiftr
                                (Z.shiftr
                                   (Z.shiftr
                                      (Z.shiftr
                                         (Z.shiftr
                                            (@bv_unsigned
                                               (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                               (decodeItemSavedFramePointer
                                                 args))
                                            (Zpos (xO (xO (xO xH)))))
                                         (Zpos (xO (xO (xO xH)))))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Zpos (xO (xO (xO xH)))))
                                (Zpos (xO (xO (xO xH)))))
                             (Z.ones (Zpos (xO (xO (xO xH)))))))
                       (@cons (bv (Npos (xO (xO (xO xH)))))
                          (Z_to_bv (Npos (xO (xO (xO xH))))
                             (Z.land
                                (Z.shiftr
                                   (Z.shiftr
                                      (Z.shiftr
                                         (Z.shiftr
                                            (Z.shiftr
                                               (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (decodeItemSavedFramePointer
                                                 args))
                                                 (Zpos (xO (xO (xO xH)))))
                                               (Zpos (xO (xO (xO xH)))))
                                            (Zpos (xO (xO (xO xH)))))
                                         (Zpos (xO (xO (xO xH)))))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Zpos (xO (xO (xO xH)))))
                                (Z.ones (Zpos (xO (xO (xO xH)))))))
                          (@cons (bv (Npos (xO (xO (xO xH)))))
                             (Z_to_bv (Npos (xO (xO (xO xH))))
                                (Z.land
                                   (Z.shiftr
                                      (Z.shiftr
                                         (Z.shiftr
                                            (Z.shiftr
                                               (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (decodeItemSavedFramePointer
                                                 args))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                               (Zpos (xO (xO (xO xH)))))
                                            (Zpos (xO (xO (xO xH)))))
                                         (Zpos (xO (xO (xO xH)))))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Z.ones (Zpos (xO (xO (xO xH)))))))
                             (bv_to_little_endian
                                (Z.of_nat (S (S (S (S (S (S (S (S O)))))))))
                                (Npos (xO (xO (xO xH))))
                                (decodeItemReturnAddress args))))))))))))
(H110 : Z.le (Zpos (xO (xO (xO (xO (xO (xO (xI xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))))
(H111 : Z.le (Zpos (xO (xO (xO (xI (xI (xI (xI xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))))
(H112 : not
  (Z.ge
     (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_add (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_unsigned (Npos (xO (xO (xO xH))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xO (xO xH)))) I))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
     (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (decodeItemInputLength args)))))
(H113 : Z.ge
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
  (Zpos (xO (xO (xO (xI (xI (xI (xI xH)))))))))
(H114 : Z.ge
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
  (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))))
(H115 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))))
 :
@eq (list (bv (Npos (xO (xO (xO xH)))))) frameBytes
  (@cons (bv (Npos (xO (xO (xO xH)))))
     (Z_to_bv (Npos (xO (xO (xO xH))))
        (Z.land
           (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (decodeItemSavedFramePointer args))
           (Z.ones (Zpos (xO (xO (xO xH)))))))
     (@cons (bv (Npos (xO (xO (xO xH)))))
        (Z_to_bv (Npos (xO (xO (xO xH))))
           (Z.land
              (Z.shiftr
                 (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (decodeItemSavedFramePointer args))
                 (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH)))))))
        (@cons (bv (Npos (xO (xO (xO xH)))))
           (Z_to_bv (Npos (xO (xO (xO xH))))
              (Z.land
                 (Z.shiftr
                    (Z.shiftr
                       (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                          (decodeItemSavedFramePointer args))
                       (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH)))))
                 (Z.ones (Zpos (xO (xO (xO xH)))))))
           (@cons (bv (Npos (xO (xO (xO xH)))))
              (Z_to_bv (Npos (xO (xO (xO xH))))
                 (Z.land
                    (Z.shiftr
                       (Z.shiftr
                          (Z.shiftr
                             (@bv_unsigned
                                (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                                (decodeItemSavedFramePointer args))
                             (Zpos (xO (xO (xO xH)))))
                          (Zpos (xO (xO (xO xH))))) 
                       (Zpos (xO (xO (xO xH)))))
                    (Z.ones (Zpos (xO (xO (xO xH)))))))
              (@cons (bv (Npos (xO (xO (xO xH)))))
                 (Z_to_bv (Npos (xO (xO (xO xH))))
                    (Z.land
                       (Z.shiftr
                          (Z.shiftr
                             (Z.shiftr
                                (Z.shiftr
                                   (@bv_unsigned
                                      (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                                      (decodeItemSavedFramePointer args))
                                   (Zpos (xO (xO (xO xH)))))
                                (Zpos (xO (xO (xO xH)))))
                             (Zpos (xO (xO (xO xH)))))
                          (Zpos (xO (xO (xO xH)))))
                       (Z.ones (Zpos (xO (xO (xO xH)))))))
                 (@cons (bv (Npos (xO (xO (xO xH)))))
                    (Z_to_bv (Npos (xO (xO (xO xH))))
                       (Z.land
                          (Z.shiftr
                             (Z.shiftr
                                (Z.shiftr
                                   (Z.shiftr
                                      (Z.shiftr
                                         (@bv_unsigned
                                            (Npos
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                            (decodeItemSavedFramePointer args))
                                         (Zpos (xO (xO (xO xH)))))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Zpos (xO (xO (xO xH)))))
                                (Zpos (xO (xO (xO xH)))))
                             (Zpos (xO (xO (xO xH)))))
                          (Z.ones (Zpos (xO (xO (xO xH)))))))
                    (@cons (bv (Npos (xO (xO (xO xH)))))
                       (Z_to_bv (Npos (xO (xO (xO xH))))
                          (Z.land
                             (Z.shiftr
                                (Z.shiftr
                                   (Z.shiftr
                                      (Z.shiftr
                                         (Z.shiftr
                                            (Z.shiftr
                                               (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (decodeItemSavedFramePointer
                                                 args))
                                               (Zpos (xO (xO (xO xH)))))
                                            (Zpos (xO (xO (xO xH)))))
                                         (Zpos (xO (xO (xO xH)))))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Zpos (xO (xO (xO xH)))))
                                (Zpos (xO (xO (xO xH)))))
                             (Z.ones (Zpos (xO (xO (xO xH)))))))
                       (@cons (bv (Npos (xO (xO (xO xH)))))
                          (Z_to_bv (Npos (xO (xO (xO xH))))
                             (Z.land
                                (Z.shiftr
                                   (Z.shiftr
                                      (Z.shiftr
                                         (Z.shiftr
                                            (Z.shiftr
                                               (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (decodeItemSavedFramePointer
                                                 args))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                               (Zpos (xO (xO (xO xH)))))
                                            (Zpos (xO (xO (xO xH)))))
                                         (Zpos (xO (xO (xO xH)))))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Zpos (xO (xO (xO xH)))))
                                (Z.ones (Zpos (xO (xO (xO xH)))))))
                          (bv_to_little_endian
                             (Z.of_nat (S (S (S (S (S (S (S (S O)))))))))
                             (Npos (xO (xO (xO xH))))
                             (decodeItemReturnAddress args)))))))))).
Proof.
assert (HsliceLen0 : (8 = Z.of_nat (length (take 8 (drop 0 frameBytes))))%Z) by (rewrite length_take length_drop H15; reflexivity).
assert (HsliceLen1 : (8 = Z.of_nat (length (take 8 (drop 8 frameBytes))))%Z) by (rewrite length_take length_drop H15; reflexivity).
change (zesu_additive_decoder 8%N (take 8 (drop 0 frameBytes)) = bv_unsigned (decodeItemSavedFramePointer args)) in H19.
change (zesu_additive_decoder 8%N (take 8 (drop 8 frameBytes)) = decodeItemReturnAddress args) in H20.
rewrite zesu_additive_decoder_view in H19.
rewrite zesu_additive_decoder_view in H20.
pose proof (bv_to_little_endian_to_bv 8 8%N (take 8 (drop 0 frameBytes)) HsliceLen0) as Himage0.
pose proof (bv_to_little_endian_to_bv 8 8%N (take 8 (drop 8 frameBytes)) HsliceLen1) as Himage1.
rewrite H19 in Himage0.
rewrite H20 in Himage1.
change (frameBytes = bv_to_little_endian 8 8%N (bv_unsigned (decodeItemSavedFramePointer args)) ++ bv_to_little_endian 8 8%N (decodeItemReturnAddress args)).
rewrite Himage0 Himage1 drop_0.
rewrite (take_ge (drop 8 frameBytes) 8 ltac:(rewrite length_drop H15; lia)).
symmetry. apply take_drop.
Qed.
