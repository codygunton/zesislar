Require Import ZesuSsz.Automation2.MemoryAddress.
Require Import ZesuSsz.Automation2.MemoryTupleConsumer.
Require Import ZesuSsz.Automation2.SourceFactMatching.
Require Import ZesuSsz.Automation2.SourceFactByteViews.
Require Import ZesuSsz.Automation2.EntryWitnessFinish.
Require Import ZesuSsz.Automation2.WrappedWord.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.EntryIntro.
Require Import ZesuMachineMap.Machine.
Require Export ZesuSsz.Automation2.ByteArrays.
Require Export ZesuSsz.Automation2.Hooks.
Require Import ZesuSsz.Automation2.CodecArrayRead.
Require Import ZesuSsz.Automation2.WordIdentity.
Require Import ZesuSsz.Automation2.SignedMaskBranch.
Require Import ZesuSsz.Automation2.ArrayContinuation.
Require Import ZesuSsz.Automation2.CodecFrame.
Require Import ZesuSsz.Automation2.HypothesisCast.
Require Import ZesuSsz.Automation2.ByteMaskCast.
Require Import ZesuSsz.Automation2.ByteReconstruction.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.BranchUnsigned.
Require Import ZesuSsz.Automation2.BranchCastUnsigned.
Require Import ZesuSsz.Automation2.SymbolicByteCodec.
Require Import ZesuSsz.Automation2.MaskPresentation.
Require Import ZesuSsz.Automation2.MaskWrapPresentation.
Require Import ZesuSsz.Automation2.FramePackingFinish.
Require Import ZesuSsz.Automation2.ArrayPayloadPresentation.
Require Import ZesuSsz.Automation2.StoreMemoryLookup.
Require Import ZesuSsz.Automation2.ContextCollection.
Require Export ZesuSsz.Automation2.ArrayCursors.
Require Import ZesuSsz.Automation2.ArrayByteValues.
Require Import ZesuSsz.Automation2.ArraySlices.
Require Import ZesuSsz.Automation2.Rewrites.
Require Import ZesuSsz.Automation2.StackArrayIndices.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation2.PackedWordValues.
Require Import ZesuSsz.Automation2.RawWordArrayWitness.
Require Export ZesuSsz.Automation2.ResourceGroups.
Require Import ZesuSsz.Automation2.NatBounds.
Require Import ZesuSsz.Automation2.PureFacts.
Require Import ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.BoundedArithmetic.
(* Names `zesu_rule_set_v2_steps` for `zesu_run_pass_v2` below. The
   module declares one tactic and installs no instance and no hint,
   so importing it changes nothing for a rule set v1 module. *)
Require Import ZesuSsz.Automation2.V2Steps.
Require Import ZesuSsz.Automation2.TracePrefixTail.
Require Import ZesuSsz.Automation2.ArrayLoadPriority.
Require Import ZesuSsz.Automation2.ConjunctMatch.
Require Import ZesuSsz.Automation2.ArrayLoadPreselect.
Require Import ZesuSsz.Automation2.ReturnBundle.
Require Import ZesuSsz.Automation2.ReturnWand.
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
        [let reduced := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed value in
         lazymatch reduced with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
         solve [(first [ZesuSsz.Automation2.VmClosed.zesu_vm_closed_decide | reflexivity])]
        |rewrite /Z_to_little_endian /=;
         rewrite !Z.land_ones; [|lia..];
         rewrite !Z.shiftr_div_pow2; [|lia..];
         repeat eexists; repeat split; reflexivity]
  end.

(* The helper's VM branch evaluates the complete goal, not only its value. *)
Ltac zesu_finish_little_endian_if_closed :=
  lazymatch goal with
  | |- context[Z_to_little_endian _ _ _] =>
      let proposition := match goal with |- ?goal => constr:(goal) end in
      zesu_vm_closed proposition;
      zesu_finish_little_endian
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
      (solve [apply bv_eq; first [ZesuSsz.Automation2.VmClosed.zesu_vm_closed_decide | reflexivity]])
  end.

Ltac zesu_normalize_memory_constants :=
  repeat match goal with
  | |- context[mem_mapsto _ _ (bv_add ?left ?right)] =>
      let value := constr:(bv_add left right) in
      is_closed_term value;
      let integer := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_unsigned value) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      let Hconstant := fresh "Hconstant" in
      assert (Hconstant : value = BV 64 integer) by
        (apply bv_eq; first [ZesuSsz.Automation2.VmClosed.zesu_vm_closed_decide | reflexivity]);
      rewrite Hconstant; clear Hconstant
  end.

Ltac zesu_normalize_memory_addresses :=
  repeat match goal with
  | Hlower : (?minimum <= bv_unsigned ?pointer)%Z,
    Hupper : (bv_unsigned ?pointer2 + _ < ?maximum)%Z
    |- context[mem_mapsto (bv_unsigned (bv_add ?base ?offset)) _ _] =>
      constr_eq base pointer;
      constr_eq pointer pointer2;
      let low := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed minimum in
      let high := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed maximum in
      let ramLow := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed ((mapRamBase defaultMap)%Z) in
      let ramHigh := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed ((machineRamEnd defaultMap)%Z) in
      constr_eq low ramLow; constr_eq high ramHigh;
      let integer := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_unsigned offset) in
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
  ArrayByteValues.zesu_finish_array_byte_lookup.

Ltac zesu_finish_array_byte_lookup_if_closed :=
  ArrayByteValues.zesu_finish_array_byte_lookup_if_closed.

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
  (* A singleton codec count can retain a closed nat-to-Z conversion. *)
  repeat match goal with
  | |- context[bv_to_little_endian ?count 8 (bv_unsigned ?value)] =>
      is_closed_term count;
      let normalized := eval cbv beta iota zeta delta
        [Z.of_nat Pos.of_succ_nat Pos.succ] in count in
      constr_eq normalized constr:(1%Z);
      let Hsingleton := fresh "HsingletonCodec" in
      pose proof (bv_to_little_endian_to_bv 1 8 [value] eq_refl) as Hsingleton;
      cbn [little_endian_to_bv little_endian_to_Z fmap list_fmap List.map] in Hsingleton;
      rewrite ?Z.shiftl_0_l ?Z.lor_0_r in Hsingleton;
      rewrite Hsingleton; clear Hsingleton
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
      ZesuSsz.Automation2.ResourceGroups.zesu_is_pure_resource body;
      solve [repeat first
        [solve [iPureIntro; assumption] | solve [iPureIntro; reflexivity] |
         iSplit | solve [iPureIntro; zesu_small_pure_lia]]]
  end.


(* A proved zero displacement exposes the existing complete-word codec. *)
Ltac zesu_finish_zero_offset_u64_roundtrip :=
  lazymatch goal with
  | |- Z_to_bv 64 (little_endian_to_bv 8
      (take ?count (drop (Z.to_nat ?offset) ?bytes))) = ?word =>
      is_closed_term count;
      assert_fails (has_evar offset);
      assert_fails (has_evar bytes);
      assert_fails (has_evar word);
      let Hzero := fresh "HsliceOffsetZero" in
      assert (Hzero : offset = 0%Z) by lia;
      rewrite Hzero; clear Hzero;
      cbn [Z.to_nat drop];
      apply ByteArrays.zesu_u64_little_endian_roundtrip
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
  | _ => Hooks.zesu_unlet_preserving_witness_metadata
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
  try solve [zesu_finish_zero_offset_u64_roundtrip];
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
  try (zesu_finish_array_byte_lookup_if_closed);
  try zesu_finish_constant;
  try (apply Z.le_ge; assumption);
  try (zesu_finish_ram_known);
  try (zesu_finish_ram_address);
  try (zesu_finish_pointer_alignment);
  lazymatch goal with
  | |- environments.envs_entails _ _ => idtac
  | _ =>
      try (zesu_saturate_alignment);
      try zesu_finish_lia;
      try (ZesuSsz.Automation2.ContextCollection.zesu_solve_goal_selected
        ("finish.v1_tail"%string) ltac:(bv_solve))
  end;
  try (zesu_finish_little_endian_if_closed);
  try solve [SymbolicByteCodec.zesu_symbolic_byte_codec].

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
Ltac zesu_finish_entailment_base :=
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

(* Defer matching cancellation shapes to the later contract arithmetic. *)
Ltac zesu_finish_same_closed_Z left right :=
 stdpp.tactics.is_closed_term left;
 stdpp.tactics.is_closed_term right;
 let l := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed left in
 let r := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed right in
 constr_eq l r.
Ltac zesu_finish_defer_cancel_shape :=
 lazymatch goal with
 | |- @eq (bv _) _ _ => idtac
 | |- Z.le _ _ => idtac
 end;
 lazymatch goal with |- ?target => tryif has_evar target then fail 0 else idtac end;
 lazymatch goal with
 | |- @eq (bv ?n)
       (@bv_add ?n (Z_to_bv ?n (Z.sub ?base ?amount)) (@BV ?n ?increment ?wf))
       (Z_to_bv ?n ?base) => zesu_finish_same_closed_Z amount increment
 | |- Z.le (Z.add (Z.sub ?base ?amount) (Z.of_nat (length ?values))) ?limit =>
   multimatch goal with
   | Hlength : length values = ?count |- _ =>
     zesu_finish_same_closed_Z amount (Z.of_nat count);
     first [
       multimatch goal with Hupper : (base < ?bound)%Z |- _ =>
         zesu_finish_same_closed_Z bound limit end |
       multimatch goal with Hupper : (base <= ?bound)%Z |- _ =>
         zesu_finish_same_closed_Z bound limit end]
   end
 end.

(* Anything else: the old chain, in the old order. *)
Ltac zesu_finish_pure_goal_base :=
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
  try (zesu_finish_array_byte_lookup_if_closed);
  try zesu_finish_constant;
  try (apply Z.le_ge; assumption);
  try (zesu_finish_ram_known);
  try (zesu_finish_ram_address);
  try (zesu_finish_pointer_alignment);
  try (zesu_saturate_alignment);
  try zesu_finish_lia;
  try (tryif zesu_finish_defer_cancel_shape then idtac else bv_solve);
  (* C6, last: the goal is arithmetic and everything above has refused it,
     so the facts it needs are still folded inside a hypothesis. Unfold
     them and ask once more. `solve` keeps the step honest: it either
     closes the goal or leaves it exactly as it was. *)
  try zesu_finish_witness_arithmetic;
  try (zesu_finish_little_endian_if_closed).

(* Normalize only facts already retained by the contract. *)
Ltac zesu_finish_pure_shape :=
  try zesu_saturate_derived_facts;
  try autounfold with zesu_contract_constants in *;
  repeat match goal with
  | Hlength : Z.of_nat (length ?values) = ?count
      |- context [firstn (Z.to_nat ?count) ?values] =>
      rewrite (zesu_take_complete values count Hlength)
  end;
  repeat progress (rewrite ?zesu_Z_to_bv_add).

Ltac zesu_finish_negated_ge :=
  repeat match goal with
  | Hnot : ~ (?left >= ?right)%Z |- _ =>
      tryif has_evar left then fail 0 else idtac;
      tryif has_evar right then fail 0 else idtac;
      lazymatch goal with
      | _ : (left < right)%Z |- _ => fail 0
      | _ =>
          let Hlt := fresh "HstrictBound" in
          assert (Hlt : (left < right)%Z) by lia
      end
  end.

(* Apply one implication pair. Closed types prevent witness assignment. *)
Ltac zesu_finish_implication_pair :=
  match goal with
  | Houter : ?Middle -> ?Result, Hinner : ?Premise -> ?InnerResult |- _ =>
      tryif has_evar Premise then fail 0 else idtac;
      tryif has_evar Middle then fail 0 else idtac;
      tryif has_evar InnerResult then fail 0 else idtac;
      tryif has_evar Result then fail 0 else idtac;
      tryif constr_eq Result False then fail 0 else idtac;
      tryif (lazymatch goal with _ : Result |- _ => idtac end)
      then fail 0 else idtac;
      let Hp := fresh "HpairPremise" in
      assert (Hp : Premise) by assumption;
      let Hmiddle := fresh "HpairMiddle" in
      assert (Hmiddle : Middle) by exact (Hinner Hp);
      let Hresult := fresh "HpairResult" in
      pose proof (Houter Hmiddle) as Hresult;
      clear Hp Hmiddle;
      hnf in Hresult;
      zesu_integer_array_facts
  end.

(* Invoke only after the existing pure closers refuse the goal. *)
Ltac zesu_finish_contract_arithmetic :=
  lazymatch goal with
  | |- @eq Z _ _ => idtac
  | |- @eq nat _ _ => idtac
  | |- @eq (bv _) _ _ => idtac
  | |- Z.le _ _ => idtac
  | |- Z.lt _ _ => idtac
  | |- Z.ge _ _ => idtac
  | |- Z.gt _ _ => idtac
  | |- (_ <= _)%nat => idtac
  | |- (_ < _)%nat => idtac
  end;
  lazymatch goal with
  | |- ?target => tryif has_evar target then fail 0 else idtac
  end;
  solve [
    try autounfold with zesu_contract_constants in *;
    repeat progress (
      rewrite ?length_app ?length_take ?length_drop ?length_insert;
      rewrite ?length_bv_to_little_endian;
      cbn [length N.to_nat]);
    repeat progress (rewrite ?zesu_Z_to_bv_add);
    first [lia | bv_solve]].

Ltac zesu_finish_forall_leaf :=
  lazymatch goal with
  | |- ?target => tryif has_evar target then fail 0 else idtac
  end;
  match goal with
  | Hrule : forall x : ?A, _ |- _ =>
      solve [eapply Hrule; eassumption]
  end.

Ltac zesu_finish_simpl_and_leaf :=
  lazymatch goal with
  | |- ?target =>
      tryif has_evar target then fail 0 else idtac;
      let evidence := constr:(_ : SimplAnd target True) in
      exact (proj1 evidence I)
  end.

(* Select the list length atom before arithmetic expands unrelated facts. *)
Ltac zesu_finish_list_cons_atom :=
  lazymatch goal with
  | |- exists (head : ?A) (tail : list ?A),
      ?values = head :: tail /\ length tail = ?count =>
      tryif has_evar values then fail 0 else idtac;
      solve [
        apply zesu_list_cons_witness;
        multimatch goal with
        | Hlength : length ?root = ?size |- _ =>
            lazymatch goal with
            | |- context [root] =>
                is_closed_term size;
                clear - Hlength
            end
        end;
        zesu_finish_contract_arithmetic]
  end.

Ltac zesu_finish_list_cons_final :=
  solve [zesu_finish_list_cons_atom].

(* Restore only an already-enabled capability after the search scope ends. *)
Ltac zesu_finish_unsigned_branch :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuSsz.Automation2.BitvectorFacts.ZesuStepBranchGuards);
  let capability := constr:(_ : ZesuSsz.Automation2.BitvectorFacts.ZesuStepBranchGuards) in
  assert_fails ltac:(idtac; has_evar capability);
  let enabled := fresh "HbranchSwitch" in
  pose proof capability as enabled;
  first [ZesuSsz.Automation2.BranchUnsigned.zesu_unsigned_branch_evidence |
    ZesuSsz.Automation2.BranchCastUnsigned.zesu_unsigned_branch_cast_evidence].

(* Enable capabilities only while closing a residual after the search. *)
Ltac zesu_finish_residual_switches :=
  let branch := fresh "HlocalBranchSwitch" in
  let mask := fresh "HlocalMaskSwitch" in
  let codec := fresh "HlocalCodecSwitch" in
  assert (branch : ZesuSsz.Automation2.BitvectorFacts.ZesuStepBranchGuards) by exact I;
  assert (mask : ZesuSsz.Automation2.BitvectorFacts.ZesuStepMaskNormalizer) by exact I;
  assert (codec : ZesuSsz.Automation2.SymbolicByteCodec.ZesuStepSymbolicByteCodec) by constructor.

(* An unsuccessful cascade restores the goal and its original capabilities. *)
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
           ZesuSsz.Automation2.HypothesisCast.zesu_hypothesis_cast_range width value);
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
           rewrite (ZesuSsz.Automation2.BitvectorFacts.zesu_unsigned_low_mask_add_sub_modulus
             width low base mask delta widths bits range) cast;
           reflexivity);
        rewrite image in branch;
        lazymatch bound_expression with
        | bv_unsigned (Z_to_bv ?bound_width ?bound) =>
          let bound_cast := fresh "HmaskedBoundCast" in
          assert (bound_cast : bv_unsigned (Z_to_bv bound_width bound) = bound) by
            (apply Z_to_bv_small;
             ZesuSsz.Automation2.HypothesisCast.zesu_hypothesis_cast_range bound_width bound);
          rewrite bound_cast in branch
        | _ => idtac
        end;
        lia
      end
    end].

Ltac zesu_v34_array_continuation :=
  ZesuSsz.Automation2.ArrayContinuation.zesu_array_continuation
    ltac:(first [zesu_masked_add_branch_finish |
      ZesuSsz.Automation2.SymbolicByteCodec.zesu_symbolic_byte_codec |
      ZesuSsz.Automation2.FramePackingFinish.zesu_frame_packing_finish |
      assumption | reflexivity]).

(* Keep the shared route first. Assemble after matching only when it refuses. *)
Ltac zesu_finish_source_package :=
  first [solve [
  MemoryTupleConsumer.zesu_memory_tuple
    ltac:(fun requested =>
      once
        (SourceFactByteViews.zesu_source_byte_views;
         SourceFactByteViews.zesu_source_byte_order_tree requested;
         ZesuSsz.Automation2.BitvectorFacts.zesu_source_biased_mask_tree requested);
      (tryif SourceFactMatching.zesu_source_check_fixed_tree requested
       then idtac
       else (once (repeat JoinEntailment.zesu_join_project_once);
         PureFacts.zesu_saturate_derived_facts;
         SourceFactMatching.zesu_source_check_fixed_tree requested));
      once (SourceFactMatching.zesu_source_match_tree requested ltac:(idtac)))
    ltac:(fun _ => SourceFactMatching.zesu_source_finish_package)
  ] | solve [
let run := ltac:(fun consume_facts finish =>
once (try zesu_memory_registered_intro;
  ResourceGroups.zesu_open_resource_groups;
  ByteArrayAssemblyCodec.zesu_byte_array_normalize_stride;
  zesu_memory_open_tuple constr:(16%nat);
  repeat iMatchHyp ltac:(fun name body => is_var body; progress (iFrame name));
  repeat first [progress zesu_memory_frame_first |
    progress zesu_memory_join_arrays]);
  lazymatch goal with
  | |- environments.envs_entails _ ?requested => consume_facts requested
  end;
  try MemoryTupleConsumer.zesu_memory_assemble_leading;
  finish constr:(tt)) in
  run ltac:(fun requested =>
      once
        (SourceFactByteViews.zesu_source_byte_views;
         SourceFactByteViews.zesu_source_byte_order_tree requested;
         ZesuSsz.Automation2.BitvectorFacts.zesu_source_biased_mask_tree requested);
      (tryif SourceFactMatching.zesu_source_check_fixed_tree requested
       then idtac
       else (once (repeat JoinEntailment.zesu_join_project_once);
         PureFacts.zesu_saturate_derived_facts;
         SourceFactMatching.zesu_source_check_fixed_tree requested));
      SourceFactMatching.zesu_source_match_tree requested ltac:(idtac))
    ltac:(fun _ => SourceFactMatching.zesu_source_finish_package)
  ]].


(* Match the requested facts directly against the source facts. This adds no
   byte view and no residual switch. *)
Ltac zesu_finish_source_tail :=
  MemoryTupleConsumer.zesu_memory_tuple
    ltac:(fun requested =>
      SourceFactMatching.zesu_source_match_tree requested ltac:(idtac))
    ltac:(fun _ => SourceFactMatching.zesu_source_finish_package).

(* The direct source tail runs last, after the switched closers fail. *)
Ltac zesu_finish_residual_cascade :=
  first [solve [
    zesu_finish_residual_switches;
    first [ solve [ZesuSsz.Automation2.MaskWitness.zesu_mask_witness_telescope;
              unshelve (repeat liAStep); zesu_finish_v1]
          | solve [SourceFactMatching.zesu_source_registered_disjunction ltac:(zesu_finish_source_package)]
          | solve [zesu_finish_source_package]
          | solve [ZesuSsz.Automation2.WordIdentity.zesu_word_identity]
          | solve [zesu_masked_add_branch_finish]
          | solve [ZesuSsz.Automation2.HypothesisCast.zesu_hypothesis_cast_finish]
          | solve [ZesuSsz.Automation2.ByteMaskCast.zesu_byte_mask_cast]
          | solve [ZesuSsz.Automation2.ByteReconstruction.zesu_byte_reconstruction ltac:(lia)]
          | solve [ZesuSsz.Automation2.SymbolicByteCodec.zesu_symbolic_byte_codec]
          | solve [ZesuSsz.Automation2.MaskPresentation.zesu_mask_sign_extend_presentation]
          | solve [ZesuSsz.Automation2.MaskWrapPresentation.zesu_mask_wrap_presentation]
          | solve [ZesuSsz.Automation2.SignedMaskBranch.zesu_signed_mask_branch]
          | solve [ZesuSsz.Automation2.BranchCastUnsigned.zesu_unsigned_branch_cast_evidence]
          | solve [ZesuSsz.Automation2.BranchUnsigned.zesu_unsigned_branch_evidence]
          | solve [ZesuSsz.Automation2.FramePackingFinish.zesu_frame_packing_finish]
          | solve [zesu_v34_array_continuation]
          | solve [ZesuSsz.Automation2.CodecFrame.zesu_codec_frame]
          | solve [ZesuSsz.Automation2.ArrayPayloadPresentation.zesu_array_payload_presentation
              ltac:(first [ZesuSsz.Automation2.SymbolicByteCodec.zesu_symbolic_byte_codec |
      ZesuSsz.Automation2.FramePackingFinish.zesu_frame_packing_finish])] ]
  ] | solve [zesu_finish_source_tail]].

(* Fast generic evidence transport precedes broad arithmetic. *)
Ltac zesu_union_required_pure :=
  first [ZesuSsz.Automation2.WordIdentity.zesu_word_identity |
    ZesuSsz.Automation2.HypothesisCast.zesu_hypothesis_cast_finish |
    ZesuSsz.Automation2.ByteMaskCast.zesu_byte_mask_cast |
    ZesuSsz.Automation2.ByteReconstruction.zesu_byte_reconstruction ltac:(lia) |
    ZesuSsz.Automation2.MaskPresentation.zesu_mask_sign_extend_presentation |
    ZesuSsz.Automation2.MaskWrapPresentation.zesu_mask_wrap_presentation |
    ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_splice_bounds |
    ZesuSsz.Automation2.SymbolicByteCodec.zesu_symbolic_byte_codec |
    ZesuSsz.Automation2.SignedMaskBranch.zesu_signed_mask_branch |
    ZesuSsz.Automation2.BranchCastUnsigned.zesu_unsigned_branch_cast_evidence |
    ZesuSsz.Automation2.BranchUnsigned.zesu_unsigned_branch_evidence |
    ZesuSsz.Automation2.FramePackingFinish.zesu_frame_packing_finish].

Ltac zesu_union_pure_leaf :=
  first [ZesuSsz.Automation2.UnionRuleComponents.block2_signed_mask_solve |
    solve [zesu_finish_list_cons_atom] |
    ZesuSsz.Automation2.UnionRuleComponents.block2_f7_arithmetic |
    assumption | ZesuSsz.Automation2.UnionRuleComponents.range_interval].

Ltac zesu_union_pure_finish :=
  zesu_final_pure_head_gate;
  first [zesu_union_required_pure |
    ZesuSsz.Automation2.UnionRuleComponents.block2_signed_mask_solve |
    solve [zesu_finish_list_cons_atom] |
    ZesuSsz.Automation2.UnionRuleComponents.block2_f7_arithmetic |
    (try ZesuSsz.Automation2.UnionRuleComponents.block2_range_add_zero_goal;
     try ZesuSsz.Automation2.UnionRuleComponents.block2_range_boolean_goal;
     try ZesuSsz.Automation2.UnionRuleComponents.range_unsigned_facts;
     zesu_union_pure_leaf)].


(* The common pure path uses existing facts and bounded address rewrites. *)
Ltac zesu_finish_common_pure :=
  zesu_final_pure_head_gate;
  first [zesu_union_required_pure | solve [
    zesu_saturate_derived_facts;
    repeat first [progress zesu_split_folded_pure |
      match goal with Hpair : _ /\ _ |- _ => destruct Hpair end];
    zesu_normalize_machine_map;
    first [solve [apply andb_true_iff; split; apply bool_decide_eq_true_2;
      WrappedWord.zesu_wrapped_word_range ltac:(
        WrappedWord.zesu_reduce_closed_Z_aliases;
        cbv [bv_unsigned bv_modulus] in *; lia)]
    | autorewrite with isla_coq_rewrite; zesu_union_pure_finish]]].

(* The common pure path and final tail share the union helper. Baseline closers remain available. *)
Ltac zesu_finish_final_pure :=
  first [
  zesu_final_pure_head_gate;
  tryif progress zesu_saturate_derived_facts
  then try solve [zesu_array_bounds_if_enabled]
  else idtac;
  try solve [
    first [
      zesu_finish_negated_ge; zesu_finish_implication_pair; repeat split;
      first [reflexivity | assumption | eassumption | lia | bv_solve |
        zesu_finish_forall_leaf | zesu_finish_contract_arithmetic |
        zesu_finish_simpl_and_leaf]
    | repeat split; zesu_finish_forall_leaf
    | repeat split; first [zesu_finish_contract_arithmetic |
        zesu_finish_simpl_and_leaf]
    | let rec finish_leaf :=
        first [reflexivity | assumption | eassumption | lia | bv_solve |
          zesu_finish_forall_leaf | zesu_finish_contract_arithmetic |
          zesu_finish_simpl_and_leaf |
          lazymatch goal with |- and _ _ => split; finish_leaf end]
      in finish_leaf
    | zesu_finish_list_cons_final]] | zesu_finish_common_pure].



Ltac zesu_finish_pure_goal :=
  first [
zesu_finish_pure_goal_base;
  try solve [
    first [
      zesu_finish_negated_ge; zesu_finish_implication_pair; repeat split;
      first [reflexivity | assumption | eassumption | lia | bv_solve |
        zesu_finish_forall_leaf]
    | repeat split; zesu_finish_forall_leaf]] | zesu_finish_common_pure].

Ltac zesu_finish_entailment :=
  lazymatch goal with
  | |- envs_entails _ (@bi_pure _ _) =>
      iPureIntro; zesu_finish_pure_shape; zesu_finish_pure_goal
  | _ => zesu_finish_entailment_base
  end.

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
  | _ => Hooks.zesu_unlet_preserving_witness_metadata
  end;
  zesu_finish_dispatch.

Ltac zesu_union_array_payload_finish :=
  ZesuSsz.Automation2.Hooks.zesu_array_payload_presentation
    ltac:(first [ZesuSsz.Automation2.SymbolicByteCodec.zesu_symbolic_byte_codec |
      ZesuSsz.Automation2.FramePackingFinish.zesu_frame_packing_finish]).

Ltac zesu_finish_base :=
  first [solve [zesu_union_array_payload_finish] |
  try solve [zesu_array_region_selection_if_enabled];
  tryif zesu_defer_unresolved_sidecondition_if_enabled then idtac else (
  try solve [zesu_list_cons_witness_if_enabled |
    zesu_primitive_tuple_guard_if_enabled];
  tryif zesu_rule_set_v2_on
  then tryif let _ := constr:(_ : ZesuStepBoundedArithmetic) in idtac
       then try (zesu_finish_v2)
       else zesu_finish_v2
  else zesu_finish_v1) | zesu_finish_common_pure].


Ltac zesu_finish := zesu_finish_once_if_enabled ltac:(zesu_finish_base).

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
  first [zesu_raw_array_witness_if_enabled |
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
  end ].

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
    [SourceFactMatching.zesu_source_destruct_registered_disjunction |
     ZesuSsz.Automation2.CodecArrayRead.zesu_codec_array_read_consumer |
     zesu_v34_array_continuation |
     zesu_union_witness_step | zesu_target_registered_intro_if_enabled |
     zesu_open_requested_instr_bundle |
     zesu_open_requested_struct_sys_package |
     zesu_open_requested_saved_x9_package |
     zesu_open_matching_resource_package | zesu_finish_pure_resources_step |
     zesu_pack_owned_register_goal | zesu_pack_shaped_register_goal |
     zesu_pack_owned_word_goal | zesu_normalize_packed_word_subsume |
     ZesuSsz.Automation2.CodecArrayRead.zesu_codec_array_find |
     zesu_prepare_initialized_array_read |
     zesu_finish_initialized_array_read |
     ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup |
     zesu_liAStep |
     ZesuSsz.Automation2.CodecArrayRead.zesu_codec_array_read_sidecond |
     zesu_open_matching_two_level_frame |
     zesu_extract_matching_descriptor_pure].

Ltac zesu_run_pass_v1 :=
  zesu_expose_environment_alias;
  try zesu_prepare_uninit_goal;
  try zesu_normalize_find_mem_address;
  unshelve (time "zesu_run" repeat first
    [SourceFactMatching.zesu_source_destruct_registered_disjunction |
     ZesuSsz.Automation2.CodecArrayRead.zesu_codec_array_read_consumer |
     zesu_v34_array_continuation |
     zesu_union_witness_step | zesu_target_registered_intro_if_enabled |
     zesu_open_requested_instr_bundle |
     zesu_open_requested_struct_sys_package |
     zesu_open_requested_saved_x9_package |
     zesu_open_matching_resource_package | zesu_finish_pure_resources_step |
     zesu_pack_owned_register_goal | zesu_pack_shaped_register_goal |
     zesu_pack_owned_word_goal | zesu_normalize_packed_word_subsume |
     ZesuSsz.Automation2.CodecArrayRead.zesu_codec_array_find |
     zesu_prepare_initialized_array_read |
     zesu_finish_initialized_array_read |
     ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup |
     zesu_liAStep |
     ZesuSsz.Automation2.CodecArrayRead.zesu_codec_array_read_sidecond |
     zesu_open_matching_two_level_frame |
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

(* All and Sets/v1 explicitly select v1. Opt-in switches select v2.
   The v2 selector has priority. Missing selection is an error. *)
(* Select the rule set before running either continuation. A selected tactic's
   failure must not select the other rule set. *)
Ltac zesu_with_rule_set v1 v2 :=
  tryif zesu_rule_set_v2_on then v2
  else tryif zesu_rule_set_v1_on then v1
  else fail 1000 "No automation rule set is selected. Import All or an explicit Sets module.".

Ltac zesu_run_pass :=
  zesu_with_rule_set ltac:(zesu_run_pass_v1) ltac:(zesu_run_pass_v2).

(* Resolve the approved switch set in the current search context. *)
Ltac zesu_search_switches := constr:([
  ZesuSsz.Automation2.SignedMaskBranch.ZesuStepSignedMaskBranch;
  ZesuSsz.Automation2.ArrayContinuation.ZesuStepArrayContinuation;
  ZesuSsz.Automation2.WordIdentity.ZesuStepWordIdentity;
  ZesuSsz.Automation2.CodecArrayRead.ZesuStepCodecArrayRead;
  ZesuSsz.Automation2.CodecArrayRange.ZesuStepCodecArrayRange;
  ZesuSsz.Automation2.Hooks.ZesuStepRegcolVMCompute;
  ZesuStepContextCollection; ZesuStepFinisherOnce;
  ZesuSsz.Automation2.HypothesisCast.ZesuStepHypothesisCast;
  ZesuSsz.Automation2.ByteMaskCast.ZesuStepByteMaskCast;
  ZesuSsz.Automation2.ByteReconstruction.ZesuStepByteReconstruction;
  ZesuSsz.Automation2.RewriteBoundGuards.ZesuStepRewriteBoundGuards;
  ZesuSsz.Automation2.Hooks.ZesuStepRegionFaultNormalization; ZesuSsz.Automation2.Hooks.ZesuStepInstructionLookup;
  ZesuSsz.Automation2.Hooks.ZesuStepStackWrite; ZesuSsz.Automation2.Hooks.ZesuStepRamFault; ZesuSsz.Automation2.Hooks.ZesuStepRegionFault;
  ZesuSsz.Automation2.BitvectorFacts.ZesuStepLowMask; ZesuSsz.Automation2.EntryIntro.ZesuStepEntryIntro; ZesuSsz.Automation2.Hooks.ZesuStepIntegerArrayAddress; ZesuSsz.Automation2.Hooks.ZesuStepRecordWitness;
  ZesuSsz.Automation2.Hooks.ZesuStepArrayBounds; ZesuSsz.Automation2.ByteArrays.ZesuStepWordArrayHandoff; ZesuSsz.Automation2.ReturnBundle.ZesuStepReturnBundle;
  ZesuSsz.Automation2.ReturnWand.ZesuStepReturnWand; ZesuSsz.Automation2.BitvectorFacts.ZesuStepStrictSigned; ZesuSsz.Automation2.Hooks.ZesuStepListWitness;
  ZesuSsz.Automation2.Hooks.ZesuStepTupleWitness; ZesuSsz.Automation2.ByteArrayLengths.ZesuStepArrayRegionBounds; ZesuSsz.Automation2.Hooks.ZesuStepPureFactHints;
  ZesuSsz.Automation2.Hooks.ZesuStepKnownPairWitness; ZesuSsz.Automation2.Hooks.ZesuStepPureWitnessConstraints;
  ZesuSsz.Automation2.Hooks.ZesuStepRegisterCollectionSelection; ZesuSsz.Automation2.Hooks.ZesuStepEvarSideconditionGuard;
  ZesuSsz.Automation2.Hooks.ZesuStepEvarImplicationGuard;
  ZesuSsz.Automation2.Hooks.ZesuStepCanonicalAnchor;
  ZesuSsz.Automation2.Hooks.ZesuStepCanonicalPureConjunction;
  ZesuSsz.Automation2.Hooks.ZesuStepByteListContainment;
  ZesuSsz.Automation2.Hooks.ZesuStepRegionFaultCastHypotheses;
  ZesuSsz.Automation2.BitvectorFacts.ZesuStepMaskNormalizer;
  ZesuSsz.Automation2.Hooks.ZesuStepPureFactExistential;
  ZesuSsz.Automation2.IntegerReturn.ZesuStepIntegerReturn;
  ZesuSsz.Automation2.ExitMeaning.ZesuStepExitMeaning;
  ZesuSsz.Automation2.ConjunctMatch.ZesuStepConjunctMatch;
  ZesuSsz.Automation2.BitvectorFacts.ZesuStepBranchGuards;
  ZesuSsz.Automation2.StoreMemoryLookup.ZesuStepStoreMemoryLookup;
  ZesuSsz.Automation2.SymbolicByteCodec.ZesuStepSymbolicByteCodec;
  ZesuSsz.Automation2.FramePacking.ZesuStepFramePacking]).

Ltac zesu_native_entry_tail :=
  EntryWitnessFinish.zesu_entry_witness_finish
    ltac:(progress liAStep)
    ltac:(cbn [li_fst li_snd]; zesu_finish_pure_goal).

Ltac zesu_run :=
  let switches := zesu_search_switches in
  zesu_dispatch_search switches ltac:(fun _ =>
    unshelve (repeat progress
      (zesu_run_pass; try zesu_solve_instances; zesu_finish));
    try zesu_solve_instances;
    try zesu_finish_pure_resources;
    try solve [zesu_array_bounds_if_enabled];
    try zesu_finish;
    try zesu_finish_final_pure);
  try zesu_native_entry_tail.

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
   counted 443 hand lines written only because `zesu_block2` stopped there:
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

Ltac zesu_block_base :=
  try zesu_entry_intro_goal_if_enabled;
  zesu_with_rule_set ltac:(zesu_block_v1) ltac:(zesu_block_v2).

Ltac zesu_block2 :=
  zesu_block_base; try zesu_finish_residual_cascade.

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
