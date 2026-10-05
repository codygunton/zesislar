(** Project-wide Lithium hook redefinitions belong in this module. *)

From iris.proofmode Require Import environments.
Require Import isla.riscv64.riscv64.
Require Export ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Automation.NatBounds.
Require Import ZesuSsz.Automation.BoundedArithmetic.
Require Import ZesuSsz.Automation.TraceTailLemmas.
Require Import ZesuSsz.Automation.InstrPre.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Contracts.ParentHeaderSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldSites.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Automation.ResourceGroups.

(* Keep the selected table named during search and simplification.
   Explicit computation still resolves one selected instruction. *)
Global Typeclasses Opaque selectedCodeLookup.
Arguments selectedCodeLookup : simpl never.

Class ZesuStepInstructionLookup : Prop :=
  zesu_step_instruction_lookup : True.

(* Expose only a code wrapper whose head reduces to a lookup resource. *)
Ltac zesu_expose_instruction_lookup :=
  let _ := constr:(_ : ZesuStepInstructionLookup) in
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindInstrKind _ _) _) =>
      zesu_expose_environment_alias;
      iMatchHyp ltac:(fun H body =>
        lazymatch body with
        | instr_lookup_resources _ => fail
        | _ =>
            let head := get_head body in
            let expanded := eval cbv beta delta [head] in body in
            lazymatch expanded with
            | instr_lookup_resources _ =>
                progress iEval (unfold head) in H;
                iDestruct H as "#?"
            end
        end)
  end.

Global Typeclasses Opaque IslarisContractSpec.
Global Instance : LithiumUnfold (@IslarisContractSpec) := I.
Global Typeclasses Opaque NextUint64InternalHandoffSpec
  ParentHeaderDirectHandoffSpec ParentHeaderTailHandoffSpec.
Global Instance : LithiumUnfold (@NextUint64InternalHandoffSpec) := I.
Global Instance : LithiumUnfold (@ParentHeaderDirectHandoffSpec) := I.
Global Instance : LithiumUnfold (@ParentHeaderTailHandoffSpec) := I.
Global Typeclasses Opaque decodeItemEntryResources decodeItemExitResources.
Global Instance : LithiumUnfold (@decodeItemEntryResources) := I.
Global Instance : LithiumUnfold (@decodeItemExitResources) := I.
Global Typeclasses Opaque decodeItemSelectedCode.
Global Instance : LithiumUnfold (@decodeItemSelectedCode) := I.
Global Typeclasses Opaque ziskMemcpyServiceEntry ziskMemcpyServiceExit
  ziskMemcpyServiceInstrSpec memcpyServicePremise.
Global Instance : LithiumUnfold (@ziskMemcpyServiceEntry) := I.
Global Instance : LithiumUnfold (@ziskMemcpyServiceExit) := I.
Global Instance : LithiumUnfold (@ziskMemcpyServiceInstrSpec) := I.
Global Instance : LithiumUnfold (@memcpyServicePremise) := I.
Global Typeclasses Opaque nextUint64SelectedCode nextUint64SelectedEntry
  nextUint64SelectedExit parentHeaderSelectedCode
  parentHeaderSelectedEntry parentHeaderSelectedExit.
Global Instance : LithiumUnfold (@nextUint64SelectedCode) := I.
Global Instance : LithiumUnfold (@nextUint64SelectedEntry) := I.
Global Instance : LithiumUnfold (@nextUint64SelectedExit) := I.
Global Instance : LithiumUnfold (@parentHeaderSelectedCode) := I.
Global Instance : LithiumUnfold (@parentHeaderSelectedEntry) := I.
Global Instance : LithiumUnfold (@parentHeaderSelectedExit) := I.
Global Typeclasses Opaque decodeItemByteFoldResources
  decodeItemByteFoldStringHeader decodeItemByteFoldListHeader.
Global Instance : LithiumUnfold (@decodeItemByteFoldResources) := I.
Global Instance : LithiumUnfold (@decodeItemByteFoldStringHeader) := I.
Global Instance : LithiumUnfold (@decodeItemByteFoldListHeader) := I.
Global Typeclasses Opaque decodeItemStringFoldAt decodeItemListFoldAt.
Global Instance : LithiumUnfold (@decodeItemStringFoldAt) := I.
Global Instance : LithiumUnfold (@decodeItemListFoldAt) := I.
Global Typeclasses Opaque decodeItemFoldInitResources
  decodeItemFoldCheckedResources decodeItemFoldEntryObligation
  decodeItemFoldPreservationObligation decodeItemFoldExitObligation.
Global Instance : LithiumUnfold (@decodeItemFoldInitResources) := I.
Global Instance : LithiumUnfold (@decodeItemFoldCheckedResources) := I.
Global Instance : LithiumUnfold (@decodeItemFoldEntryObligation) := I.
Global Instance : LithiumUnfold (@decodeItemFoldPreservationObligation) := I.
Global Instance : LithiumUnfold (@decodeItemFoldExitObligation) := I.
Global Typeclasses Opaque decodeItemEntryAt800d6a24
  decodeItemEntryAt800d6ac4 decodeItemBodyAt800d6a24
  decodeItemBodyAt800d6ac4.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a24) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6ac4) := I.
Global Instance : LithiumUnfold (@decodeItemBodyAt800d6a24) := I.
Global Instance : LithiumUnfold (@decodeItemBodyAt800d6ac4) := I.
Global Typeclasses Opaque decodeItemBranchContinuationAt
  decodeItemBranchContinuation decodeItemBranchBase
  decodeItemEntryAt800d6974 decodeItemEntryAt800d697c
  decodeItemEntryAt800d69a4 decodeItemEntryAt800d69d8
  decodeItemEntryAt800d69e0 decodeItemEntryAt800d69e8
  decodeItemEntryAt800d6a00 decodeItemEntryAt800d6a08
  decodeItemEntryAt800d6a14 decodeItemEntryAt800d6a38
  decodeItemEntryAt800d6a64 decodeItemEntryAt800d6a6c
  decodeItemEntryAt800d6aa8 decodeItemEntryAt800d6ab4
  decodeItemEntryAt800d6ad8.
Global Instance : LithiumUnfold (@decodeItemBranchContinuationAt) := I.
Global Instance : LithiumUnfold (@decodeItemBranchContinuation) := I.
Global Instance : LithiumUnfold (@decodeItemBranchBase) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6974) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d697c) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d69a4) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d69d8) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d69e0) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d69e8) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a00) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a08) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a14) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a38) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a64) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a6c) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6aa8) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6ab4) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6ad8) := I.
Global Typeclasses Opaque decodeItemReturnEntryCore
  decodeItemEntryAt800d698c decodeItemEntryAt800d69b0
  decodeItemEntryAt800d6a40 decodeItemEntryAt800d6a78
  decodeItemEntryAt800d6ae0 decodeItemEntryAt800d6b08
  decodeItemReturnOkExit decodeItemReturnErrorExit
  decodeItemReturnBlockObligation
  decodeItemReturnAt800d698c decodeItemReturnAt800d69b0
  decodeItemReturnAt800d6a40 decodeItemReturnAt800d6a78
  decodeItemReturnAt800d6ae0 decodeItemReturnAt800d6b08.
Global Instance : LithiumUnfold (@decodeItemReturnEntryCore) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d698c) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d69b0) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a40) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6a78) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6ae0) := I.
Global Instance : LithiumUnfold (@decodeItemEntryAt800d6b08) := I.
Global Instance : LithiumUnfold (@decodeItemReturnOkExit) := I.
Global Instance : LithiumUnfold (@decodeItemReturnErrorExit) := I.
Global Instance : LithiumUnfold (@decodeItemReturnBlockObligation) := I.
Global Instance : LithiumUnfold (@decodeItemReturnAt800d698c) := I.
Global Instance : LithiumUnfold (@decodeItemReturnAt800d69b0) := I.
Global Instance : LithiumUnfold (@decodeItemReturnAt800d6a40) := I.
Global Instance : LithiumUnfold (@decodeItemReturnAt800d6a78) := I.
Global Instance : LithiumUnfold (@decodeItemReturnAt800d6ae0) := I.
Global Instance : LithiumUnfold (@decodeItemReturnAt800d6b08) := I.
Global Typeclasses Opaque decodeItemJoinTransferObligation
  decodeItemJoin698cFrom697c decodeItemJoin698cFrom69e8
  decodeItemJoin6a24From6a14 decodeItemJoin6a24Backedge
  decodeItemJoin6ac4From6ab4 decodeItemJoin6ac4Backedge
  decodeItemJoin6ae0From6970 decodeItemJoin6ae0From69e0
  decodeItemJoin6ae0From6a08 decodeItemJoin6ae0From6a38
  decodeItemJoin6ae0From6a6c decodeItemJoin6ae0From6aa8
  decodeItemJoin6ae0From6ad8.
Global Instance : LithiumUnfold (@decodeItemJoinTransferObligation) := I.
Global Instance : LithiumUnfold (@decodeItemJoin698cFrom697c) := I.
Global Instance : LithiumUnfold (@decodeItemJoin698cFrom69e8) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6a24From6a14) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6a24Backedge) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ac4From6ab4) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ac4Backedge) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From6970) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From69e0) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From6a08) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From6a38) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From6a6c) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From6aa8) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0From6ad8) := I.

(** Give Lithium its separating-conjunction goal form. *)
Ltac zesu_prepare_uninit_goal :=
  lazymatch goal with
  | |- envs_entails _ (?address ↦ₘ? ?count)%I =>
      iEval (rewrite -(right_id True%I _ (address ↦ₘ? count)%I))
  end.

(** Normalize the reviewed map before bitvector arithmetic. *)
Ltac zesu_normalize_machine_map :=
  cbv [mapRamBase mapRamSize mapIoContextAddress mapTextBase
    machineRamEnd machineOutputAddress machineOutputSizeAddress
    machineExitAddress machinePc defaultMap] in *.

Ltac zesu_has_initialized_array_root root spatial :=
  lazymatch spatial with
  | Esnoc ?rest _ ((?address ↦ₘ∗ _)%I) =>
      first [lazymatch address with
             | bv_unsigned ?actualRoot => constr_eq actualRoot root
             | (bv_unsigned ?actualRoot + _)%Z => constr_eq actualRoot root
             end
            | zesu_has_initialized_array_root root rest]
  | Esnoc ?rest _ _ => zesu_has_initialized_array_root root rest
  end.

(** Name a machine bound after normalizing its reviewed map fields. *)
Ltac zesu_name_machine_bound expected name :=
  let normalizedExpected := eval cbv [mapRamBase mapRamSize
    mapIoContextAddress mapTextBase machineRamEnd machineOutputAddress
    machineOutputSizeAddress machineExitAddress machinePc defaultMap Z.add Z.sub]
    in expected in
  match goal with
  | H : ?actual |- _ =>
      let normalizedActual := eval cbv [mapRamBase mapRamSize
        mapIoContextAddress mapTextBase machineRamEnd machineOutputAddress
        machineOutputSizeAddress machineExitAddress machinePc defaultMap Z.add Z.sub]
        in actual in
      constr_eq normalizedActual normalizedExpected;
      rename H into name
  end.

(* Library solvers also call this primitive without passing through the
   project finisher. The call set supplies the timeout switch. *)
Ltac lia ::= zesu_bounded_arithmetic ltac:(Zify.zify; xlia zchecker).
Ltac bv_solve ::= zesu_bounded_arithmetic ltac:(
  bv_simplify_arith;
  bv_saturate_unsigned;
  bv_solve_unfold_tac;
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned in *;
  simpl; lia).

Ltac zesu_solve_machine_bounds :=
  zesu_bounded_arithmetic ltac:(solve [zesu_normalize_binary_nat_hypotheses;
    zesu_normalize_binary_nat_goal; zesu_normalize_machine_map; bv_solve]).
Ltac zesu_solve_machine_linear :=
  first [zesu_bounded_arithmetic ltac:(zesu_byte_index_arithmetic)
    | zesu_bounded_arithmetic ltac:(first [solve [repeat match goal with
           | Hnat : (_ <= _)%nat |- _ => clear Hnat
           | Hnat : (_ < _)%nat |- _ => clear Hnat
           end; zesu_normalize_machine_map; lia] |
    solve [zesu_normalize_binary_nat_hypotheses;
      zesu_normalize_binary_nat_goal; zesu_normalize_machine_map; lia]])].
(* Preserve the machine normalization used by the existing finisher. *)
Ltac zesu_finish_lia ::= zesu_solve_machine_linear.

Tactic Notation "lia" := zesu_solve_machine_linear.

Tactic Notation "bv_solve" := zesu_solve_machine_bounds.

Ltac zesu_normalize_symbolic_mem_address :=
  repeat match goal with
  | Hlocal := _ |- envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      lazymatch address with context[Hlocal] => unfold Hlocal in *; clear Hlocal end
  end;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo (bv_unsigned ?pointer)) _) =>
    let expanded := eval cbv beta zeta in pointer in
    lazymatch expanded with
    | bv_add ?base ?offset =>
      first [lazymatch base with
             | bv_add ?root ?displacement => is_var root
             | bv_sub ?root ?displacement => is_var root
             end
            | is_var base;
              lazymatch goal with
              | |- envs_entails ?context _ =>
                  let spatial := eval cbn [env_spatial] in (env_spatial context) in
                  zesu_has_initialized_array_root base spatial
              end];
      let integer := eval vm_compute in (bv_unsigned offset) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac end;
      let Heq := fresh "HmemoryAddress" in
      assert (Heq : bv_unsigned pointer = (bv_unsigned base + integer)%Z) by
        (repeat match goal with
         | Hnat : (_ <= _)%nat |- _ => clear Hnat
         | Hnat : (_ < _)%nat |- _ => clear Hnat
         end; bv_solve);
      rewrite Heq; clear Heq
    end
  end.

Ltac zesu_has_known_word_address expected spatial :=
  lazymatch spatial with
  | Esnoc ?rest _ ((?actual ↦ₘ{?q} ?word)%I) =>
      first [constr_eq actual expected | zesu_has_known_word_address expected rest]
  | Esnoc ?rest _ _ => zesu_has_known_word_address expected rest
  end.
Ltac zesu_normalize_known_word_address :=
  repeat match goal with
  | Hlocal := _ |- envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      lazymatch address with context[Hlocal] => unfold Hlocal in *; clear Hlocal end
  end;
  lazymatch goal with
  | |- envs_entails ?context
      (find_in_context (FindMemMapsTo (bv_unsigned ?pointer)) _) =>
      let expanded := eval cbv beta zeta in pointer in
      lazymatch expanded with bv_add ?base ?offset =>
      is_var base;
      let integer := eval vm_compute in (bv_unsigned offset) in
      let expected := constr:((bv_unsigned base + integer)%Z) in
      let spatial := eval cbn [env_spatial] in (env_spatial context) in
      zesu_has_known_word_address expected spatial;
      let Heq := fresh "HknownWordAddress" in
      assert (Heq : bv_unsigned pointer = expected) by bv_solve;
      rewrite Heq; clear Heq
      end
  end.
Ltac zesu_normalize_find_mem_address :=
  first [zesu_normalize_symbolic_mem_address | zesu_normalize_known_word_address].

Class ZesuStepStackWrite : Prop := zesu_step_stack_write : True.

Ltac zesu_stack_arithmetic :=
  repeat first [progress zesu_split_folded_pure |
    match goal with H : _ /\ _ |- _ => destruct H end];
  repeat match goal with
  | H : ?statement |- _ =>
      lazymatch type of statement with Prop => idtac end;
      lazymatch statement with
      | Z.le _ _ => fail
      | Z.lt _ _ => fail
      | @eq Z _ _ => fail
      | _ => clear H
      end
  end;
  repeat match goal with
  | H : context[?term] |- _ =>
      lazymatch type of term with Z => progress reduce_closed term end
  | |- context[?term] =>
      lazymatch type of term with Z => progress reduce_closed term end
  end;
  bv_solve.

Ltac zesu_stack_integer_address pointer :=
  lazymatch pointer with
  | bv_add (bv_add (Z_to_bv 64 ?base) ?first) ?second =>
      let left := eval vm_compute in (bv_signed first) in
      let right := eval vm_compute in (bv_signed second) in
      constr:((base + left + right)%Z)
  | bv_add (Z_to_bv 64 ?base) ?offset =>
      let displacement := eval vm_compute in (bv_signed offset) in
      constr:((base + displacement)%Z)
  | bv_sub (Z_to_bv 64 ?base) ?offset =>
      let displacement := eval vm_compute in (bv_unsigned offset) in
      constr:((base - displacement)%Z)
  | Z_to_bv 64 ?base => constr:(base)
  end.

(* Select only an owned uninitialized region. Bounds justify address conversion. *)
Ltac zesu_stack_write_if_enabled :=
  let _ := constr:(_ : ZesuStepStackWrite) in
  zesu_expose_environment_alias;
  repeat match goal with
  | Hlocal := _ |- envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      lazymatch address with context[Hlocal] => unfold Hlocal in *; clear Hlocal end
  end;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      lazymatch address with
      | bv_unsigned ?pointer =>
          let expanded := eval cbv beta zeta in pointer in
          let integer := zesu_stack_integer_address expanded in
          iMatchHyp ltac:(fun H body =>
            lazymatch body with
            | (?lower ↦ₘ? ?count)%I =>
                let Heq := fresh "HstackAddress" in
                assert (Heq : address = integer) by
                  (timeout 2 zesu_stack_arithmetic);
                let Hbound := fresh "HstackRegion" in
                assert (Hbound : (lower <= integer < lower + count)%Z) by
                  (timeout 2 zesu_stack_arithmetic);
                rewrite Heq; clear Heq;
                iRename H into "HstackWriteFrame";
                iExists (MKUninit lower count);
                iSplitL "HstackWriteFrame"; [iExact "HstackWriteFrame" |]
            end)
      end
  end.


Ltac zesu_unfold_bv_bindings :=
  repeat match goal with
  | Hlocal := _ : bv _ |- _ => unfold Hlocal in *; clear Hlocal
  end.

Ltac zesu_normalize_memory_cell H expected :=
  let selected := iTypeOf (INamed H) in
  lazymatch selected with
  | Some (_, (?actual ↦ₘ{?q} ?value)%I) =>
      let Heq := fresh "HcellAddress" in
      assert (Heq : actual = expected) by bv_solve;
      iEval (rewrite Heq) in H; clear Heq
  end.

Ltac zesu_solve_pending_sidecond :=
  lazymatch goal with
  | |- envs_entails _ _ => fail
  | _ => prepare_sidecond; first [assumption | bv_solve | lia]
  end.

Ltac zesu_tuple_witness T :=
  lazymatch T with
  | li_prod ?A ?B =>
      let head := open_constr:(_ : A) in
      let tail := zesu_tuple_witness B in constr:(li_pair head tail)
  | unit => constr:(tt)
  end.

Ltac zesu_liInstrPreMatch :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T ?body) =>
      let witness := zesu_tuple_witness T in
      let instantiated := eval cbv beta in (body witness) in
      lazymatch instantiated with
      | zesu_instr_pre_match _ _ _ =>
          notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod
      end
  | |- envs_entails _ (zesu_instr_pre_match ?available ?requested _) =>
      first
        [ unify available requested with typeclass_instances;
          notypeclasses refine
            (tac_fast_apply
              (zesu_instr_pre_match_identity _ _ _ eq_refl) _)
        | assert_fails (has_evar requested);
          notypeclasses refine
            (tac_fast_apply (zesu_instr_pre_match_wand _ _ _) _) ]
  end.

Ltac zesu_normalize_output_address :=
  lazymatch goal with
  | |- envs_entails _
      (WPasm (WriteMem _ _ (RVal_Bits (bv_to_bvn ?address)) _ _ _ _ :t: _)) =>
      first [let output := eval vm_compute in (machineOutputAddress defaultMap) in
             lazymatch output with
             | Some ?output => replace address with (Z_to_bv 64 output)
                 by (vm_compute; bv_solve)
             end
            |let size := eval vm_compute in (machineOutputSizeAddress defaultMap) in
             lazymatch size with
             | Some ?size => replace address with (Z_to_bv 64 size)
                 by (vm_compute; bv_solve)
             end
            |idtac]
  | _ => idtac
  end.

Ltac zesu_liAReadMem :=
  lazymatch goal with
  | |- envs_entails ?Delta
      (WPasm (ReadMem _ _ _ _ _ _ :t: _)) =>
      notypeclasses refine
        (tac_fast_apply (li_wp_read_mem_zesu _ _ _ _ _ _ _ _) _)
  end.

Ltac zesu_liAWriteMem :=
  lazymatch goal with
  | |- envs_entails ?Delta
      (WPasm (WriteMem _ _ _ _ _ _ _ :t: _)) =>
      unshelve (notypeclasses refine
        (tac_fast_apply (li_wp_write_mem_zesu _ _ _ _ _ _ _ _ _) _))
  end.

Ltac zesu_liAWriteMemFocused :=
  zesu_normalize_output_address;
  lazymatch goal with
  | |- envs_entails ?Delta
      (WPasm (WriteMem _ _ _ _ _ _ _ :t: _)) =>
      notypeclasses refine
        (tac_fast_apply (li_wp_write_mem_zesu _ _ _ _ _ _ _ _ _) _)
  end.

Ltac zesu_liAAsmNoWrite :=
  lazymatch goal with
  | |- envs_entails _ (WPasm (WriteMem _ _ _ _ _ _ _ :t: _)) => fail 1
  | _ => liAAsm
  end.

Ltac zesu_liAAsmBeforeObservable :=
  lazymatch goal with
  | |- envs_entails _ (WPasm (WriteMem _ _ _ _ _ _ _ :t: _)) => fail 1
  | |- envs_entails _ (WPasm tnil) => fail 1
  | _ => liAAsm
  end.

Ltac zesu_liAStepNoWrite :=
 liEnsureInvariant;
 try liAIntroduceLetInGoal;
 first [
    zesu_normalize_find_mem_address
  | zesu_liAReadMem
  | zesu_liAAsmNoWrite
  | liAExp
  | liAOther
  | liUnfoldEarly
  | liStep
  | liLetBindHint
  | liUnfoldLate
 ]; liSimpl.

Ltac zesu_liAStepBeforeObservable :=
 liEnsureInvariant;
 try liAIntroduceLetInGoal;
 first [
    zesu_normalize_find_mem_address
  | zesu_liAReadMem
  | zesu_liAAsmBeforeObservable
  | liAExp
  | liAOther
  | liUnfoldEarly
  | liStep
  | liLetBindHint
  | liUnfoldLate
 ]; liSimpl.

Ltac zesu_liAStepGenericWrite :=
 liEnsureInvariant;
 try liAIntroduceLetInGoal;
 zesu_liAWriteMemFocused.

(* Keep a map-bounded current-address witness before Lithium simplifies it. *)
Ltac zesu_preserve_current_unsigned :=
  lazymatch goal with
  | |- bv_unsigned (Z_to_bv 64 ?current) = ?current -> _ =>
          let ramBase := eval cbv [mapRamBase defaultMap] in
            (mapRamBase defaultMap) in
          let ramEnd := eval cbv [machineRamEnd mapRamSize mapRamBase
            defaultMap Z.add] in (machineRamEnd defaultMap) in
          match goal with
          | Hlow : (?lower <= current)%Z,
            Hhigh : (current + ?extent < ?upper)%Z |- _ =>
              let reducedLower := eval cbv [mapRamBase defaultMap] in lower in
              let reducedUpper := eval cbv [machineRamEnd mapRamSize mapRamBase
                defaultMap Z.add] in upper in
              constr_eq reducedLower ramBase;
              constr_eq reducedUpper ramEnd;
              intro H7
          end
  end.

(* Signed widened addresses retain the unsigned source value.
   Close an impossible branch before Lithium searches exception registers. *)
Ltac zesu_signed_address_if_enabled :=
  let _ := constr:(_ : ZesuStepSignedAddress) in
  match goal with
  | H : ~ ?bound |- _ =>
      lazymatch bound with Z.le _ _ => idtac | Z.ge _ _ => idtac end;
      lazymatch bound with
      | context [bv_zero_extend 128 _] => idtac
      end
  end;
  solve [unLET;
    progress (repeat match goal with
    | H : context [bv_signed (bv_zero_extend 128 ?value + ?offset)] |- _ =>
        rewrite (zesu_signed_zero_extend_add_64_128 value offset) in H;
          last bv_solve
    | H : context [bv_signed (bv_zero_extend 128 ?value)] |- _ =>
        rewrite (zesu_signed_zero_extend_64_128 value) in H
    end);
    repeat match goal with
    | H : context [bv_unsigned (?left + ?right)] |- _ =>
        first [rewrite bv_add_unsigned bv_wrap_small in H; last bv_solve
              |rewrite (zesu_unsigned_add_signed_64 left right) in H;
                 last bv_solve]
    | H : context [bv_unsigned (?left - ?right)] |- _ =>
        rewrite (zesu_unsigned_sub_no_wrap_64 left right) in H; last bv_solve
    end;
    exfalso; bv_solve].

Class ZesuStepRamFault : Prop := zesu_step_ram_fault : True.

(* Entry layout bounds refute a negated widened RAM bound. *)
Ltac zesu_ram_fault_if_enabled :=
  let _ := constr:(_ : ZesuStepRamFault) in
  match goal with
  | Hfault : ~ ?bound |- _ =>
      lazymatch bound with Z.le _ _ => idtac | Z.ge _ _ => idtac end;
      lazymatch bound with context [bv_zero_extend 128 _] => idtac end;
      solve [exfalso; apply Hfault; timeout 2 zesu_stack_arithmetic]
  end.

Ltac zesu_liAStep :=
 liEnsureInvariant;
 try progress (unfold TRACE_LET);
 try liAIntroduceLetInGoal;
 first [
    zesu_expose_instruction_lookup
  | zesu_ram_fault_if_enabled
  | zesu_signed_address_if_enabled
  | zesu_stack_write_if_enabled
  | zesu_normalize_find_mem_address
  | zesu_liAWriteMem
  | zesu_liAReadMem
  | liAAsm
  | liAExp
  | liAOther
  | liUnfoldEarly
  | zesu_liInstrPreMatch
  | zesu_preserve_current_unsigned
  | liStep
  | liLetBindHint
  | liUnfoldLate
 ]; liSimpl.

Ltac liAStep ::= zesu_liAStep.

(* C1: the trace tail a call returns with.

   The corpus calls this the line every segment proof repeats. A call
   returns with its events still open, so the block is asked for a spec `x`
   with `scons_snap event accept x ⊆ scons event tail`. The witness is
   always the caller's tail, the second argument of the `scons` on the
   right. About 70 proofs and 300 hand lines in the backlog (rows 8, 12,
   13, 16, 18) are this one step.

   Supplying the witness when the existential is opened is not optional.
   Splitting `∃ x : spec *ₗ (), body x` into evars and letting Lithium
   continue does not return: with the spec open, `instr_pre … ?x` matches
   anything in the context. A probe with that rule ran 171 s and was killed
   at its 6 GiB cap, and wired into the automation it took `check-iris`
   past the 200 GiB batch cap twice, against 75 GiB without it. The tail
   does not mention the bound variable, so it reads out from under the
   binder; the inclusion is discharged in the same step, so the search
   never sees a half-instantiated spec. *)
Ltac zesu_close_trace_inclusion :=
  iPureIntro; exact (zesu_scons_snap_subseteq_scons _ _ _).

Ltac zesu_open_trace_exist :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec unit) _) =>
      match goal with
      | |- context [scons _ ?tail] =>
          iExists (tail, tt)ₗ;
          try (iSplit; [zesu_close_trace_inclusion |])
      end
  end.

(* The same step reached as a side condition rather than at the
   existential. The events are compared syntactically and the open spec
   must be an evar: a `unify` on these terms runs a conversion check over
   the whole event history, and the first version did not finish the
   suffix-entry segment in forty minutes. *)
Ltac zesu_finish_trace_tail :=
  lazymatch goal with
  | |- scons_snap ?event _ ?open ⊆ scons ?expected ?tail =>
      is_evar open; constr_eq event expected;
      unify open tail;
      exact (zesu_scons_snap_subseteq_scons _ _ _)
  | |- scons ?event ?open ⊆ scons ?expected ?tail =>
      is_evar open; constr_eq event expected;
      unify open tail;
      exact (zesu_scons_subseteq_scons _ _)
  end.
