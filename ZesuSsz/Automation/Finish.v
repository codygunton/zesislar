Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.EntryIntro.
Require Import ZesuMachineMap.Machine.
Require Export ZesuSsz.Automation.ByteArrays.
Require Export ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.SwitchDispatch.
Require Export ZesuSsz.Automation.ArrayCursors.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import ZesuSsz.Automation.ArraySlices.
Require Import ZesuSsz.Automation.Rewrites.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation.PackedWordValues.
Require Export ZesuSsz.Automation.ResourceGroups.
Require Import ZesuSsz.Automation.NatBounds.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.BoundedArithmetic.
(* Names `zesu_rule_set_v2_steps` for `zesu_run_pass_v2` below. The
   module declares one tactic and installs no instance and no hint,
   so importing it changes nothing for a rule set v1 module. *)
Require Import ZesuSsz.Automation.V2Steps.
Require Import ZesuSsz.Automation.TracePrefixTail.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
Require Import ZesuSsz.Automation.ConjunctMatch.
Require Import ZesuSsz.Automation.ArrayLoadPreselect.
Require Import ZesuSsz.Automation.ReturnBundle.
Require Import ZesuSsz.Automation.ReturnWand.
From iris.proofmode Require Import environments.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Ltac zesu_saturate_alignment :=
  match goal with
  | H : bv_extract 0 _ _ = _ |- _ => bv_saturate
  | H : Z.land (bv_unsigned _) _ = _ |- _ => bv_saturate
  end.

Ltac zesu_finish_little_endian :=
  match goal with
  | |- context[Z_to_little_endian _ _ ?value] =>
      first
        [let reduced := eval vm_compute in value in
         lazymatch reduced with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
         solve [(vm_compute; reflexivity)]
        |rewrite /Z_to_little_endian /=;
         rewrite !Z.land_ones; [|lia..];
         rewrite !Z.shiftr_div_pow2; [|lia..];
         repeat eexists; repeat split; reflexivity]
  end.

Ltac zesu_finish_tag_bound :=
  solve [eapply zesu_aligned_tag_end;
    [eassumption | first [reflexivity | eassumption] | eassumption]].

Ltac zesu_finish_mask :=
  lazymatch goal with
  | |- bv_and _ _ = _ =>
      solve [apply bv_eq; rewrite bv_and_unsigned; simpl; assumption]
  end.

Ltac zesu_finish_extract_alias :=
  lazymatch goal with
  | |- context[bv_extract _ _ _] => cbv zeta
  end;
  match goal with
  | H : bv_extract ?start ?count ?value = ?bits
    |- bv_extract ?start ?count ?alias = ?bits =>
      change alias with value; exact H
  end.

Ltac zesu_finish_list_slice_length :=
  lazymatch goal with
  | |- context[length (take _ _)] => idtac
  | |- context[length (drop _ _)] => idtac
  end;
  solve [cbn; rewrite ?length_take ?length_drop; lia].

Ltac zesu_finish_constant :=
  lazymatch goal with
  | |- @eq (bv _) ?left ?right =>
      is_closed_term left; is_closed_term right;
      (solve [apply bv_eq; vm_compute; reflexivity])
  end.

Ltac zesu_normalize_memory_constants :=
  repeat match goal with
  | |- context[mem_mapsto _ _ (bv_add ?left ?right)] =>
      let value := constr:(bv_add left right) in
      is_closed_term value;
      let integer := eval vm_compute in (bv_unsigned value) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      let Hconstant := fresh "Hconstant" in
      assert (Hconstant : value = BV 64 integer) by
        (apply bv_eq; vm_compute; reflexivity);
      rewrite Hconstant; clear Hconstant
  end.

Ltac zesu_normalize_memory_addresses :=
  repeat match goal with
  | Hlower : (?minimum <= bv_unsigned ?pointer)%Z,
    Hupper : (bv_unsigned ?pointer2 + _ < ?maximum)%Z
    |- context[mem_mapsto (bv_unsigned (bv_add ?base ?offset)) _ _] =>
      constr_eq base pointer;
      constr_eq pointer pointer2;
      let low := eval vm_compute in minimum in
      let high := eval vm_compute in maximum in
      let ramLow := eval vm_compute in ((mapRamBase defaultMap)%Z) in
      let ramHigh := eval vm_compute in ((machineRamEnd defaultMap)%Z) in
      constr_eq low ramLow; constr_eq high ramHigh;
      let integer := eval vm_compute in (bv_unsigned offset) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      let Haddress := fresh "Haddress" in
      assert (Haddress : bv_unsigned (bv_add pointer offset) =
        (bv_unsigned pointer + integer)%Z) by
        (clear -Hlower Hupper; bv_solve);
      rewrite Haddress; clear Haddress
  end.

Ltac zesu_finish_ram_address :=
  match goal with
  | Hlower : ((mapRamBase defaultMap) <= bv_unsigned ?pointer)%Z,
    Hupper : (bv_unsigned ?pointer + _ < (machineRamEnd defaultMap))%Z |- _ =>
      lazymatch goal with
      | |- context[pointer] => solve [clear -Hlower Hupper; bv_solve]
      end
  end.

Ltac zesu_finish_pointer_alignment :=
  lazymatch goal with
  | |- bv_extract _ _ _ = _ => idtac
  | |- (bv_unsigned _ `mod` _ = 0)%Z => zesu_rule_set_v2_on
  end;
  match goal with
  | Halign : bv_unsigned ?pointer `mod` _ = 0 |- _ =>
      lazymatch goal with
      | |- context[pointer] => solve [clear -Halign; bv_solve]
      end
  | Halign : bv_extract 0 _ ?pointer = _ |- _ =>
      lazymatch goal with
      | |- context[pointer] =>
          solve [clear -Halign; bv_simplify_arith Halign; bv_solve]
      end
  end.

Ltac zesu_finish_ram_known :=
  lazymatch goal with
  | |- bv_unsigned ?pointer >= _ =>
      solve [change (bv_unsigned pointer >= (mapRamBase defaultMap))%Z;
        apply Z.le_ge; assumption]
  | |- bv_unsigned ?pointer < _ =>
      solve [change (bv_unsigned pointer < (machineRamEnd defaultMap))%Z; assumption]
  end.

Ltac zesu_finish_array_byte_lookup :=
  zesu_normalize_array_byte_lookups;
  repeat match goal with
  | Hlookup : ?bytes !! Z.to_nat (bv_unsigned ?offset `div` 1) = Some ?byte |- _ =>
      let integer := eval vm_compute in (bv_unsigned offset) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac end;
      let index := eval vm_compute in (Z.to_nat integer) in
      change (bytes !! index = Some byte) in Hlookup
  end;
  repeat match goal with
  | Hlookup : ?bytes !! ?index = Some ?byte
    |- context[default _ (?bytes !! ?index)] => rewrite Hlookup
  end;
  reflexivity.

Ltac zesu_normalize_equal_array_regions :=
  repeat match goal with
  | |- context[array_region_start 8 ?a ?b] =>
    let Hsame := fresh "HregionSame" in
    assert (Hsame : a = b) by bv_solve;
    rewrite (array_region_start_equal a b Hsame); clear Hsame
  end.
Ltac zesu_normalize_known_list_lengths :=
  repeat progress (rewrite ?length_take ?length_drop ?length_app);
  repeat match goal with
  | Hlen : length ?xs = ?n |- context[length ?xs] => rewrite Hlen
  end;
  cbn [Nat.min Nat.sub].
Ltac zesu_finish_known_list_shape :=
  lazymatch goal with
  | |- envs_entails _ _ => fail 0
  | |- context[array_region_start 8 _ _] => idtac
  | |- context[length _] => idtac
  | |- @eq (list _) _ _ => idtac
  | _ => fail 0
  end;
  zesu_normalize_equal_array_regions;
  cbn [drop];
  first [solve [zesu_normalize_known_list_lengths; reflexivity] |
    solve [repeat match goal with
      | |- context[take ?n ?xs] =>
        let Htake := fresh "Htake" in
        assert (Htake : (length xs <= n)%nat) by
          (zesu_normalize_known_list_lengths; lia);
        rewrite (take_ge xs n Htake); clear Htake
      end; reflexivity] |
    solve [zesu_normalize_known_list_lengths; lia] |
    solve [bv_solve]].

Ltac zesu_finish_selectors :=
  first [zesu_array_region_selection_if_enabled | lazymatch goal with
  | |- @eq _ _ _ =>
      (autounfold with zesu_selectors;
        zesu_normalize_stack_array_indices; reflexivity)
  end].

(* The finisher, dispatched on the head of the goal.

   It used to be a linear battery: about forty `try` entries that every
   goal ran through in order, whatever its head. WP1 measured what that
   costs. Over sixteen profiled block proofs `zesu_finish` was 62.6 percent
   of the automation's seconds, and `bv_solve` inside it was 36.9 percent
   at 5.9 seconds per call -- a solver that cannot close an Iris
   entailment, run on Iris entailments. The forty entries themselves were
   not the cost: the alternatives that fail cost 0 to 12 seconds per proof.

   So the structure is now one normalization pass, then a dispatch on the
   head, then a fallback chain for heads the dispatch does not know. Every
   entry stays reachable from every head it can close, and keeps its old
   relative order there, so the finisher closes no fewer goals than before.
   The two branches carry `time` labels in the WP1 probes, so the split can
   be measured. *)

(* The per-pass lia input has at most 64 term nodes and 16 hypotheses. *)
Ltac2 zesu_small_pure_context () :=
  if Int.le (List.length (Control.hyps ())) 16 then ()
  else Control.zero (Tactic_failure None).

Ltac zesu_pure_term_budget term budget continuation :=
  lazymatch budget with
  | S ?rest =>
      lazymatch term with
      | forall _, _ => fail 0
      | fun _ => _ => fail 0
      | ?function ?argument =>
          zesu_pure_term_budget function rest ltac:(fun remaining =>
            zesu_pure_term_budget argument remaining continuation)
      | _ => continuation rest
      end
  | O => fail 0
  end.

Ltac zesu_small_pure_lia :=
  ltac2:(zesu_small_pure_context ());
  lazymatch goal with
  | |- ?statement => zesu_pure_term_budget statement constr:(64%nat) ltac:(fun _ => lia)
  end.

Ltac zesu_finish_pure_resources_step :=
  lazymatch goal with
  | |- envs_entails _ ?body =>
      ZesuSsz.Automation.ResourceGroups.zesu_is_pure_resource body;
      solve [repeat first
        [solve [iPureIntro; assumption] | solve [iPureIntro; reflexivity] |
         iSplit | solve [iPureIntro; zesu_small_pure_lia]]]
  end.


Ltac zesu_finish_v1 :=
  try autorewrite with zesu_indices;
  try (zesu_normalize_memory_constants);
  try (zesu_normalize_memory_addresses);
  try iAssumption;
  lazymatch goal with
  | |- SHELVED_SIDECOND _ =>
      first [solve [zesu_array_bounds_if_enabled] |
        solve [unshelve_sidecond; unLET; zesu_array_eight_value] |
        prepare_sidecond]
  | _ => unLET
  end;
  try zesu_finish_selectors;
  try autorewrite with zesu_indices;
  try iAssumption;
  try (zesu_normalize_array_cursors);
  try (zesu_finish_known_list_shape);
  try (zesu_finish_pure_resources_step);
  try reflexivity;
  try (zesu_finish_integer_word_image);
  try (zesu_finish_packed_word_equality);
  try ((lazymatch goal with
    | |- @eq (bv 64) _ (Z_to_bv 64
        (little_endian_to_bv 8 (take 8 (drop _ _)))) =>
        solve [zesu_array_eight_value]
    end));
  try simpl;
  try done;
  try assumption;
  try (zesu_finish_extract_alias);
  try (zesu_finish_list_slice_length);
  zesu_normalize_nat_powers;
  try (zesu_finish_tag_bound);
  try (zesu_finish_mask);
  try (zesu_finish_array_byte_lookup);
  try zesu_finish_constant;
  try (apply Z.le_ge; assumption);
  try (zesu_finish_ram_known);
  try (zesu_finish_ram_address);
  try (zesu_finish_pointer_alignment);
  try (zesu_saturate_alignment);
  try zesu_finish_lia;
  try (bv_solve);
  try (zesu_finish_little_endian).

Ltac zesu_finish_normalize :=
  try autorewrite with zesu_indices;
  try (zesu_normalize_memory_constants);
  try (zesu_normalize_memory_addresses).

Ltac zesu_finish_shelved :=
  first [solve [zesu_array_bounds_if_enabled] |
        solve [unshelve_sidecond; unLET; zesu_array_eight_value] |
    prepare_sidecond].

(* An Iris entailment. The entries the dispatch leaves out here are the
   ones that cannot close one: `reflexivity`, the bitvector entries, `lia`
   and `bv_solve`. Everything that can act on an entailment keeps its old
   position relative to the others. *)
Ltac zesu_finish_entailment :=
  try autorewrite with zesu_indices;
  try iAssumption;
  try (zesu_normalize_array_cursors);
  try (zesu_finish_pure_resources_step);
  try simpl;
  try done;
  try assumption;
  (* Both of these work on the Coq context, not on the conclusion, so an
     entailment needs them as much as a pure goal does: they prepare the
     hypotheses that a later side condition is solved from, and leaving
     them out stops `repeat progress` one step early. *)
  zesu_normalize_nat_powers;
  try (zesu_saturate_alignment).

(* Anything else: the old chain, in the old order. *)
Ltac zesu_finish_pure_goal :=
  try zesu_finish_selectors;
  try autorewrite with zesu_indices;
  try iAssumption;
  try (zesu_normalize_array_cursors);
  try (zesu_finish_known_list_shape);
  try (zesu_finish_pure_resources_step);
  try reflexivity;
  try (zesu_finish_integer_word_image);
  try (zesu_finish_packed_word_equality);
  try ((lazymatch goal with
    | |- @eq (bv 64) _ (Z_to_bv 64
        (little_endian_to_bv 8 (take 8 (drop _ _)))) =>
        solve [zesu_array_eight_value]
    end));
  try simpl;
  try done;
  try assumption;
  try (zesu_finish_extract_alias);
  try (zesu_finish_list_slice_length);
  try zesu_finish_trace_tail;
  zesu_normalize_nat_powers;
  try (zesu_finish_tag_bound);
  try (zesu_finish_mask);
  try (zesu_finish_array_byte_lookup);
  try zesu_finish_constant;
  try (apply Z.le_ge; assumption);
  try (zesu_finish_ram_known);
  try (zesu_finish_ram_address);
  try (zesu_finish_pointer_alignment);
  try (zesu_saturate_alignment);
  try zesu_finish_lia;
  try (bv_solve);
  (* C6, last: the goal is arithmetic and everything above has refused it,
     so the facts it needs are still folded inside a hypothesis. Unfold
     them and ask once more. `solve` keeps the step honest: it either
     closes the goal or leaves it exactly as it was. *)
  try zesu_finish_witness_arithmetic;
  try (zesu_finish_little_endian).

Ltac zesu_finish_dispatch :=
  lazymatch goal with
  | |- envs_entails _ _ => zesu_finish_entailment
  | |- @bi_entails _ _ _ => zesu_finish_entailment
  | _ => zesu_finish_pure_goal
  end.

Ltac zesu_finish_v2 :=
  zesu_finish_normalize;
  lazymatch goal with
  | |- envs_entails _ _ => try iAssumption
  | _ => idtac
  end;
  lazymatch goal with
  | |- SHELVED_SIDECOND _ => zesu_finish_shelved
  | _ => unLET
  end;
  zesu_finish_dispatch.

Ltac zesu_finish :=
  try solve [zesu_array_region_selection_if_enabled];
  tryif zesu_defer_unresolved_sidecondition_if_enabled then idtac else (
  try solve [zesu_list_cons_witness_if_enabled |
    zesu_primitive_tuple_guard_if_enabled];
  tryif zesu_rule_set_v2_on
  then tryif let _ := constr:(_ : ZesuStepBoundedArithmetic) in idtac
       then try (zesu_finish_v2)
       else zesu_finish_v2
  else zesu_finish_v1).

Ltac zesu_finish_framed_wand :=
  lazymatch goal with
  | |- envs_entails _ ((?available -∗ ?requested) ∗ True)%I =>
      let Hpost := lazymatch goal with
        | |- envs_entails (Envs _ _ ?counter) _ => constr:(IAnon counter)
        end in
      iSplit;
      [iIntros "?"; rewrite ?Z_to_bv_bv_unsigned;
       (iFrame "∗");
       iEval (rewrite !bi.sep_True) in Hpost; iExact Hpost | done]
  end.

Ltac zesu_finish_closed_wand :=
  lazymatch goal with
  | |- envs_entails _ ((?available -∗ ?requested) ∗ ?rest)%I =>
      iSplitL "";
      [first [solve [iIntros "?"; iAssumption] |
        unshelve (repeat zesu_liAStep; liShow);
        lazymatch goal with
        | |- envs_entails _ _ => fail "closed wand needs external resources"
        | _ => zesu_finish
        end; done] |
       unshelve (repeat zesu_liAStep; liShow);
       first [zesu_finish_closed_wand | zesu_finish_framed_wand | zesu_finish]]
  end.

Ltac zesu_solve_instances :=
  lazymatch goal with
  | |- heapG _ => typeclasses eauto
  | |- islaG _ => typeclasses eauto
  | |- threadG => typeclasses eauto
  end.

Ltac zesu_pack_shaped_register_value register :=
  iSelect (register ↦ᵣ _)%I ltac:(fun H =>
    let entry := iTypeOf H in
    lazymatch entry with
    | Some (_, _ ↦ᵣ ?value)%I =>
        iExists (value, tt)ₗ; iFrame H;
        first [done | solve [iPureIntro; first [assumption | done]] |
          iSplit; [solve [iPureIntro; first [assumption | done]] |]]
    end).

Ltac zesu_pack_shaped_register_goal :=
  first
    [ lazymatch goal with
      | |- envs_entails _
          (∃ x : li_prod valu unit,
            ⌜valu_has_shape (li_fst x) (BitsShape 64)⌝ ∗
            ?register ↦ᵣ (li_fst x) ∗ _)%I =>
          zesu_pack_shaped_register_value register
      end
    | lazymatch goal with
      | |- envs_entails _
          (∃ x : li_prod valu unit,
            ⌜valu_has_shape (li_fst x) (BitsShape 64)⌝ ∗
            ?register ↦ᵣ (li_fst x))%I =>
          zesu_pack_shaped_register_value register
      end ].

Ltac zesu_pack_owned_word_goal :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod (bv ?width) unit) ?body) =>
    lazymatch body with
    | context[(?address ↦ₘ{?q} (li_fst _))%I] =>
      iSelect (address ↦ₘ{q} _)%I ltac:(fun H =>
        let entry := iTypeOf H in
        lazymatch entry with
        | Some (_, (_ ↦ₘ{_} ?value)%I) =>
            iExists (value, tt)ₗ; iFrame H; try done
        end)
    end
  end.

Ltac zesu_pack_owned_register_goal :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod valu unit) ?body) =>
    lazymatch body with
    | context[(@reg_mapsto _ _ _ ?register ?fraction (li_fst _))] =>
        zesu_pack_shaped_register_value register
    end
  end.

Ltac zesu_prepare_initialized_array_read :=
  lazymatch goal with
  | |- envs_entails _
      (⌜_⌝ ∗ ∃ i : nat,
        ⌜Z.of_nat i = ?offset⌝ ∗ ⌜(i < length ?values)%nat⌝ ∗
        ∃ Heq : ?width = ?width, _)%I =>
      constr_eq width 64%N;
      let valuesType := type of values in
      constr_eq valuesType (list (bv 64));
      let index := constr:(Z.to_nat offset) in
      iSplit; [iPureIntro; bv_solve |];
      iExists index; iSplit;
        [iPureIntro; rewrite Z2Nat.id; bv_solve |];
      iSplit;
        [iPureIntro; rewrite ?length_take;
         repeat match goal with
         | Hlength : length ?source = ?size |- context [length ?source] =>
             rewrite Hlength
         end;
         lia |];
      iExists eq_refl
  end.

Ltac zesu_finish_initialized_array_read :=
  lazymatch goal with
  | |- envs_entails _
      (∀ _ : bv _, ⌜_⌝ -∗ ⌜_⌝ -∗ (_ ↦ₘ∗ ?values) -∗ WPasm _)%I =>
      let valuesType := type of values in
      constr_eq valuesType (list (bv 64));
      do 2 zesu_liAStep;
      let Hlookup := fresh "Hlookup" in intro Hlookup;
      do 3 zesu_liAStep
  end.

(* The search list of rule set v1: the alternatives every merged proof in
   this repository was built against. A rule set v2 step does not belong
   in this list, and that is measured, not stylistic. With one v2 step
   added here, `check-iris` failed three times on
   `WriteSuccessExactByteListsPublicResources.v`, always at the same
   line, always with "Timeout!", and that file took 8 minutes 41 seconds
   to compile alone. With the step in `zesu_run_pass_v2` instead, the
   same file compiles in 24.3 seconds, against 30.0 seconds on
   `origin/islaris-native`; `make pass-cost` reproduces both, three
   interleaved runs each. An alternative in this list is tried on every
   step where all the others fail. The former automation wrapped several
   of its own tactics in `timeout`. *)
Ltac zesu_run_pass_steps :=
  first
    [zesu_target_registered_intro_if_enabled |
     zesu_open_requested_instr_bundle |
     zesu_open_requested_struct_sys_package |
     zesu_open_requested_saved_x9_package |
     zesu_open_matching_resource_package | zesu_finish_pure_resources |
     zesu_pack_owned_register_goal | zesu_pack_shaped_register_goal |
     zesu_pack_owned_word_goal | zesu_normalize_packed_word_subsume |
     zesu_prepare_initialized_array_read |
     zesu_finish_initialized_array_read |
     zesu_liAStep | zesu_open_matching_two_level_frame |
     zesu_extract_matching_descriptor_pure].

Ltac zesu_run_pass_v1 :=
  zesu_expose_environment_alias;
  try zesu_prepare_uninit_goal;
  try zesu_normalize_find_mem_address;
  unshelve (time "zesu_run" repeat first
    [zesu_target_registered_intro_if_enabled |
     zesu_open_requested_instr_bundle |
     zesu_open_requested_struct_sys_package |
     zesu_open_requested_saved_x9_package |
     zesu_open_matching_resource_package | zesu_finish_pure_resources |
     zesu_pack_owned_register_goal | zesu_pack_shaped_register_goal |
     zesu_pack_owned_word_goal | zesu_normalize_packed_word_subsume |
     zesu_prepare_initialized_array_read |
     zesu_finish_initialized_array_read |
     zesu_liAStep | zesu_open_matching_two_level_frame |
     zesu_extract_matching_descriptor_pure]; liShow;
    try zesu_finish_closed_wand;
    try zesu_finish_framed_wand;
    zesu_finish).

Ltac zesu_run_pass_v2 :=
  zesu_expose_environment_alias;
  try zesu_prepare_uninit_goal;
  try zesu_normalize_find_mem_address;
  unshelve (time "zesu_run" repeat first
    [zesu_target_registered_intro_if_enabled | zesu_array_load_preselect | zesu_array_load_priority | zesu_conjunct_match_if_enabled | zesu_run_pass_steps | zesu_close_matching_trace_tail | zesu_open_trace_exist | zesu_rule_set_v2_steps]; liShow;
    try zesu_finish_closed_wand;
    try zesu_finish_framed_wand;
    zesu_finish).

(* Which set a module runs is decided by what it imports, and it is
   decided once per pass rather than once per step. `Automation/Sets/v2.v`
   exports the one `ZesuRuleSetV2` instance; `All.v` and
   `Automation/Sets/v1.v` do not, so a module that imports either runs
   `zesu_run_pass_v1`, which is the tactic it ran before, and pays one
   failed class lookup per pass for the question.

   The selection is a `tryif` and not a redefinition of `zesu_run_pass`
   in `Sets/v2.v`: the hygiene checker refuses a tactic redefinition
   outside `Automation/Hooks.v`, and `Hooks.v` is imported by every
   module, so an override written there would not be opt-in. Ltac1
   cannot name `zesu_run_pass_v2` before it is defined, so the dispatch
   and the v2 body both live here. *)
Ltac zesu_run_pass :=
  tryif zesu_rule_set_v2_on then zesu_run_pass_v2 else zesu_run_pass_v1.

(* Resolve the approved switch set in the current search context. *)
Ltac zesu_search_switches := constr:([
  ZesuSsz.Automation.Hooks.ZesuStepRegionFaultNormalization; ZesuSsz.Automation.Hooks.ZesuStepInstructionLookup;
  ZesuSsz.Automation.Hooks.ZesuStepStackWrite; ZesuSsz.Automation.Hooks.ZesuStepRamFault; ZesuSsz.Automation.Hooks.ZesuStepRegionFault;
  ZesuSsz.Automation.BitvectorFacts.ZesuStepLowMask; ZesuSsz.Automation.EntryIntro.ZesuStepEntryIntro; ZesuSsz.Automation.Hooks.ZesuStepIntegerArrayAddress; ZesuSsz.Automation.Hooks.ZesuStepRecordWitness;
  ZesuSsz.Automation.Hooks.ZesuStepArrayBounds; ZesuSsz.Automation.ByteArrays.ZesuStepWordArrayHandoff; ZesuSsz.Automation.ReturnBundle.ZesuStepReturnBundle;
  ZesuSsz.Automation.ReturnWand.ZesuStepReturnWand; ZesuSsz.Automation.BitvectorFacts.ZesuStepStrictSigned; ZesuSsz.Automation.Hooks.ZesuStepListWitness;
  ZesuSsz.Automation.Hooks.ZesuStepTupleWitness; ZesuSsz.Automation.ByteArrayLengths.ZesuStepArrayRegionBounds; ZesuSsz.Automation.Hooks.ZesuStepPureFactHints;
  ZesuSsz.Automation.Hooks.ZesuStepKnownPairWitness; ZesuSsz.Automation.Hooks.ZesuStepPureWitnessConstraints;
  ZesuSsz.Automation.Hooks.ZesuStepRegisterCollectionSelection; ZesuSsz.Automation.Hooks.ZesuStepEvarSideconditionGuard;
  ZesuSsz.Automation.Hooks.ZesuStepEvarImplicationGuard;
  ZesuSsz.Automation.Hooks.ZesuStepCanonicalAnchor;
  ZesuSsz.Automation.Hooks.ZesuStepCanonicalPureConjunction;
  ZesuSsz.Automation.Hooks.ZesuStepByteListContainment;
  ZesuSsz.Automation.Hooks.ZesuStepRegionFaultCastHypotheses;
  ZesuSsz.Automation.BitvectorFacts.ZesuStepMaskNormalizer;
  ZesuSsz.Automation.Hooks.ZesuStepPureFactExistential;
  ZesuSsz.Automation.ConjunctMatch.ZesuStepConjunctMatch]).

Ltac zesu_run :=
  let switches := zesu_search_switches in
  zesu_dispatch_search switches ltac:(fun _ =>
    unshelve (repeat progress
      (zesu_run_pass; try zesu_solve_instances; zesu_finish));
    try zesu_solve_instances;
    try zesu_finish_pure_resources).

Ltac zesu_expose_code_list instructions :=
  lazymatch instructions with
  | take _ ?tail => zesu_expose_code_list tail
  | drop _ ?tail => zesu_expose_code_list tail
  | ?left ++ ?right =>
      first [zesu_expose_code_list left | zesu_expose_code_list right]
  | _ => progress (unfold instructions)
  end.

Ltac zesu_expose_code_lists :=
  repeat match goal with
  | |- context [big_opL _ _ ?instructions] =>
      zesu_expose_code_list instructions
  end;
  cbn [big_opL take drop fst snd].

Ltac zesu_reduce_introduced_code_lists :=
  repeat iMatchHyp ltac:(fun H body =>
    lazymatch body with
    | context [big_opL _ _ _] =>
        let reduced := eval cbn in body in
        tryif constr_eq reduced body then fail else
          iEval (cbn) in H
    end).

(* A pure goal is not a refusal any more.

   `iStartProof` fails on a goal that is not a bi assertion, and the corpus
   counted 443 hand lines written only because `zesu_block` stopped there:
   shelved side conditions and shapes like `bv_and b N = N`. The finisher
   handles those, so the block automation hands them to it instead of
   failing. *)
Ltac zesu_block_v1 :=
  tryif iStartProof then (
  zesu_expose_code_lists;
  repeat first [progress iIntros (?) | progress iIntros "#?" |
    progress iIntros "?"];
  zesu_reduce_introduced_code_lists;
  repeat iDestruct select (_ ∗ _)%I as "[? ?]";
  try zesu_entry_intro_if_enabled;
  zesu_run)
  else first [solve [zesu_finish] | idtac].

Ltac zesu_block_v2 :=
  tryif iStartProof then (
    zesu_expose_code_lists;
    repeat first [progress iIntros (?) | progress iIntros "#?" |
      progress iIntros "?"];
    zesu_reduce_introduced_code_lists;
    repeat iDestruct select (_ ∗ _)%I as "[? ?]";
    try zesu_entry_intro_if_enabled;
    zesu_run)
  else first [solve [zesu_finish] | idtac].

Ltac zesu_block :=
  try zesu_entry_intro_goal_if_enabled;
  tryif zesu_rule_set_v2_on then zesu_block_v2 else zesu_block_v1.

Ltac zesu_block_simpl :=
  iStartProof;
  simpl;
  repeat first [progress iIntros (?) | progress iIntros "#?" |
    progress iIntros "?"];
  repeat iDestruct select (_ ∗ _)%I as "[? ?]";
  zesu_run.

Ltac zesu_run_until_steps boundary :=
  first [boundary tt |
    first [liUnfoldLate | zesu_liAStep]; zesu_run_until_steps boundary | idtac].

Ltac zesu_run_until boundary :=
  let switches := zesu_search_switches in
  zesu_dispatch_search switches ltac:(fun _ => zesu_run_until_steps boundary).

Ltac zesu_known_array_values :=
  repeat match goal with
  | Hread : ?bytes !! ?index = Some ?value,
    Hknown : ?bytes !! ?known_index = Some ?known_value |- _ =>
      is_var value;
      tryif constr_eq value known_value then fail 1 else idtac;
      let Hindex := fresh "Hindex" in
      assert (Hindex : index = known_index) by
        (unLET; autorewrite with zesu_indices;
         rewrite ?Z.div_1_r; reflexivity);
      rewrite Hindex Hknown in Hread;
      injection Hread as Hread; subst value
  end.

Ltac zesu_finish_array_branch :=
  unLET; zesu_known_array_values; exfalso;
  first [bv_solve | match goal with
    | Hbranch : _ <> _ |- _ => bv_simplify Hbranch; congruence
    end | match goal with
    | Htag : ?tag <> _, Hbranch : bv_zero_extend _ ?tag = _ |- _ =>
        bv_simplify Htag; bv_simplify Hbranch; lia
    end].

Ltac zesu_instantiate_tuple :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T _) =>
      let witness := zesu_tuple_witness T in iExists witness
  end.

Ltac zesu_handoff := zesu_instantiate_tuple; zesu_run.

Ltac zesu_frame_handoff := (iFrame "∗"; zesu_run).

Tactic Notation "zesu_pack" constr(witness) :=
  iExists witness;
  iFrame;
  try done;
  try zesu_finish.
