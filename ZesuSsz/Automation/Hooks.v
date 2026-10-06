(** Project-wide Lithium hook redefinitions belong in this module. *)

From iris.proofmode Require Import environments.
Require Import isla.riscv64.riscv64.
Require Export ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Automation.NatBounds.
Require Export ZesuSsz.Automation.ByteArrayLengths.
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
Require Import ZesuSsz.Contracts.DecodeItemErrorBranch.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Automation.ResourceGroups.

(* Expose the exact input boundary before the column lookup computes. *)
Global Hint Unfold decodeItemSysRegs : regcol_compute_unfold.

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
  decodeItemJoin698cTarget decodeItemJoin6ae0Target
  decodeItemJoin698cFrom697c decodeItemJoin698cFrom69e8
  decodeItemJoin6a24From6a14 decodeItemJoin6a24Backedge
  decodeItemJoin6ac4From6ab4 decodeItemJoin6ac4Backedge
  decodeItemJoin6ae0From6970 decodeItemJoin6ae0From69e0
  decodeItemJoin6ae0From6a08 decodeItemJoin6ae0From6a38
  decodeItemJoin6ae0From6a6c decodeItemJoin6ae0From6aa8
  decodeItemJoin6ae0From6ad8.
Global Instance : LithiumUnfold (@decodeItemJoinTransferObligation) := I.
Global Instance : LithiumUnfold (@decodeItemJoin698cTarget) := I.
Global Instance : LithiumUnfold (@decodeItemJoin6ae0Target) := I.
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
Global Typeclasses Opaque decodeItemErrorBranchEntry.
Global Instance : LithiumUnfold (@decodeItemErrorBranchEntry) := I.

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

(* Keep low-bit mask equalities symbolic before general arithmetic unfolds them. *)
Ltac zesu_low_mask_if_enabled :=
  let _ := constr:(_ : ZesuStepLowMask) in
  repeat first [
    lazymatch goal with |- bv_unsigned ?masked = _ =>
      match goal with Hlocal := _ |- _ =>
        constr_eq masked Hlocal; unfold Hlocal
      end
    end
    | lazymatch goal with |- bv_unsigned (bv_and ?sum _) = _ =>
        match goal with Hlocal := _ |- _ =>
          constr_eq sum Hlocal; unfold Hlocal
        end
      end];
  lazymatch goal with
  | |- bv_unsigned (bv_and (bv_add ?value ?offset) ?mask) =
       bv_unsigned (Z_to_bv ?low ?result) =>
      lazymatch type of value with bv ?width =>
        let Hwidth := fresh "HmaskWidth" in
        assert (Hwidth : (low <= width)%N) by
          first [assumption | vm_compute; congruence];
        let Hmask := fresh "HlowMask" in
        assert (Hmask : bv_unsigned mask = Z.ones (Z.of_N low)) by
          first [assumption | vm_compute; reflexivity];
        first [lazymatch result with (bv_unsigned ?root + ?integer)%Z =>
            constr_eq root value;
            lazymatch integer with bv_unsigned _ => fail | _ => idtac end;
            let Hoffset := fresh "HmaskOffset" in
            assert (Hoffset : offset = Z_to_bv width integer) by
              first [reflexivity | apply bv_eq; vm_compute; reflexivity];
            first [exact (zesu_unsigned_low_mask_add_integer width low value mask integer Hwidth Hmask)
              | rewrite Hoffset;
                exact (zesu_unsigned_low_mask_add_integer width low value mask integer Hwidth Hmask)]
          end
        | solve [
            rewrite (zesu_unsigned_low_mask_add width low value offset mask Hwidth Hmask);
            reflexivity
          ]]
      end
  end.

(* A widened strict comparison retains the source unsigned order. *)
Ltac zesu_strict_signed_if_enabled :=
  let _ := constr:(_ : ZesuStepStrictSigned) in
  lazymatch goal with
  | |- bv_signed (bv_zero_extend 128 ?left) <
       bv_signed (bv_zero_extend 128 ?right) =>
      lazymatch type of left with bv 64 => idtac end;
      lazymatch type of right with bv 64 => idtac end;
      match goal with
      | Hlt : bv_unsigned left < bv_unsigned right |- _ =>
          exact (zesu_unsigned_lt_signed_zero_extend_64_128 left right Hlt)
      end
  end.

(* Library solvers also call these primitives without the project finisher. *)
Ltac lia ::= zesu_bounded_arithmetic ltac:(Zify.zify; xlia zchecker).
Ltac bv_solve ::= first [solve [zesu_strict_signed_if_enabled] |
  solve [zesu_low_mask_if_enabled] |
  zesu_bounded_arithmetic ltac:(
  bv_simplify_arith;
  bv_saturate_unsigned;
  bv_solve_unfold_tac;
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned in *;
  simpl; lia)].

Ltac zesu_solve_machine_bounds :=
  first [solve [zesu_low_mask_if_enabled] |
    zesu_bounded_arithmetic ltac:(solve [zesu_normalize_binary_nat_hypotheses;
      zesu_normalize_binary_nat_goal; zesu_normalize_machine_map; bv_solve])].
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

(* Check only the candidate term. Local aliases do not require context reduction. *)
Ltac zesu_stack_closed_term term :=
  tryif has_evar term then fail 0 else
  let expanded := eval cbv beta zeta in term in
  tryif is_var expanded then
    let body := eval unfold expanded in expanded in
    zesu_stack_closed_term body
  else lazymatch expanded with
  | (fun _ => _) => fail 0
  | (forall _, _) => fail 0
  | ?function ?argument =>
      zesu_stack_closed_term function; zesu_stack_closed_term argument
  | _ => idtac
  end.

Ltac zesu_stack_reduce_closed term :=
  zesu_stack_closed_term term;
  let reduced := eval vm_compute in term in
  change_no_check term with reduced in *.

(* Normalize the selected hypothesis without searching other hypotheses. *)
Ltac zesu_stack_normalize_hypothesis hypothesis := once (
  repeat (
    let statement := type of hypothesis in
    match statement with
    | context[?term] =>
        lazymatch type of term with Z => progress (
          zesu_stack_closed_term term;
          let reduced := eval vm_compute in term in
          change_no_check term with reduced in * ) end
    end)).

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
  once (repeat match goal with
  | H : ?statement |- _ =>
      lazymatch statement with
      | Z.le _ _ => idtac
      | Z.lt _ _ => idtac
      | @eq Z _ _ => idtac
      end;
      progress (zesu_stack_normalize_hypothesis H)
  end);
  once (repeat match goal with
  | |- context[?term] =>
      lazymatch type of term with Z => progress (
        zesu_stack_closed_term term;
        let reduced := eval vm_compute in term in
        change_no_check term with reduced) end
  end);
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
                  (zesu_stack_arithmetic);
                let Hbound := fresh "HstackRegion" in
                assert (Hbound : (lower <= integer < lower + count)%Z) by
                  (zesu_stack_arithmetic);
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

Class ZesuStepRecordWitness : Prop :=
  zesu_step_record_witness : True.

Class ZesuStepListWitness : Prop :=
  zesu_step_list_witness : True.
Class ZesuStepTupleWitness : Prop :=
  zesu_step_tuple_witness : True.

Class ZesuStepPureFactHints : Prop :=
  zesu_step_pure_fact_hints : True.

Class ZesuPureFactIntro {Sigma} (target source : iProp Sigma) : Prop :=
  zesu_pure_fact_intro : source ⊢ target.
#[global] Hint Mode ZesuPureFactIntro + + - : typeclass_instances.

(* Structural leaves retain owned facts. At least one leaf needs a hint. *)
Ltac zesu_pure_fact_evidence P :=
  constr:(ltac:(first [
    let evidence := constr:(_ : SimplAnd P True) in
    exact ((proj1 evidence I, true))
  | lazymatch P with
    | ?left /\ ?right =>
        let left_evidence := zesu_pure_fact_evidence left in
        let right_evidence := zesu_pure_fact_evidence right in
        lazymatch left_evidence with (?lp, ?lh) =>
          lazymatch right_evidence with (?rp, ?rh) =>
            exact (conj lp rp, orb lh rh)
          end
        end
    end
  | match goal with Howned : P |- _ => exact (Howned, false) end
  | let evidence := constr:(eq_refl : P) in exact (evidence, false) ])
    : (P * bool)%type).

Ltac zesu_registered_pure_fact P :=
  let evidence := zesu_pure_fact_evidence P in
  lazymatch evidence with (?proof, ?used) =>
    let used := eval cbv in used in
    lazymatch used with true => constr:(proof) end
  end.

(* Registered introductions retain their resource and pure obligations. *)
Ltac zesu_pure_fact_hints_if_enabled :=
  let _ := constr:(_ : ZesuStepPureFactHints) in
  lazymatch goal with
  | |- envs_entails _ ?target =>
      first [
        lazymatch target with
        | bi_pure ?P =>
            let evidence := zesu_registered_pure_fact P in
            iPureIntro; exact evidence
        end
      | let evidence := constr:(_ : ZesuPureFactIntro target _) in
        lazymatch type of evidence with
        | ZesuPureFactIntro _ ?source =>
            iApply (@zesu_pure_fact_intro _ target source evidence)
        end
      | iMatchHyp ltac:(fun name source =>
          let evidence := constr:(_ : ZesuPureFactIntro target source) in
          iApply (@zesu_pure_fact_intro _ target source evidence)) ]
  | |- ?P =>
      let evidence := zesu_registered_pure_fact P in exact evidence
  end.

(* Only the requested list shape permits extraction of owned pure facts. *)
Ltac zesu_list_cons_witness_if_enabled :=
  let _ := constr:(_ : ZesuStepListWitness) in
  lazymatch goal with
  | |- exists (head : ?A) (tail : list ?A),
      ?values = head :: tail /\ length tail = ?count =>
      eapply zesu_list_cons_witness;
      first [assumption |
        zesu_saturate_derived_facts;
        repeat first [progress zesu_split_folded_pure |
          match goal with H : _ /\ _ |- _ => destruct H end];
        assumption]
  end.

Ltac zesu_primitive_tuple_witness T :=
  let guard := constr:(ltac:(assert_fails (has_evar T); exact I) : True) in
  lazymatch T with
  | li_prod ?A ?B =>
      let allowed := lazymatch A with
        | Z => constr:(true) | nat => constr:(true) | N => constr:(true)
        | bool => constr:(true) | list _ => constr:(true) | bv _ => constr:(true)
      end in
      let head := open_constr:(_ : A) in
      let tail := zesu_primitive_tuple_witness B in
      constr:(li_pair head tail)
  | unit => constr:(tt)
  end.

(* Resource matching must determine these data evars before Qed can close. *)
Ltac zesu_primitive_tuple_if_enabled :=
  let _ := constr:(_ : ZesuStepTupleWitness) in
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod ?A ?B) ?body) =>
      let T := constr:(li_prod A B) in
      assert_fails (has_evar T);
      let witness := zesu_primitive_tuple_witness T in
      notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod
  end.

(* Tuple guards use the owned widened comparison without adding a premise. *)
Ltac zesu_primitive_tuple_guard_if_enabled :=
  let _ := constr:(_ : ZesuStepTupleWitness) in
  lazymatch goal with
  | |- Z.lt _ _ => idtac | |- Z.le _ _ => idtac | |- Z.ge _ _ => idtac
  end;
  solve [progress (repeat match goal with
    | H : context [bv_signed (bv_zero_extend 128 ?value)] |- _ =>
        rewrite (zesu_signed_zero_extend_64_128 value) in H
    end); first [assumption | bv_solve]].

Class ZesuStepKnownPairWitness : Prop :=
  zesu_step_known_pair_witness : True.

(* An owned pure fact selects the value before resource matching starts. *)
Ltac zesu_known_pair_witness_if_enabled :=
  let _ := constr:(_ : ZesuStepKnownPairWitness) in
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod ?A unit) ?body) =>
      assert_fails (has_evar A);
      match goal with
      | H : ?predicate ?value |- _ =>
          let T := type of value in constr_eq T A;
          assert_fails (has_evar value);
          let witness := constr:(li_pair value tt) in
          let instantiated := eval cbv beta iota delta [li_fst li_snd] in
            (body witness) in
          let owned := type of H in
          lazymatch instantiated with
          | context [@bi_pure _ ?fact] =>
              constr_eq fact owned;
              notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod
          end
      end
  end.

Class ZesuStepPureWitnessConstraints : Prop :=
  zesu_step_pure_witness_constraints : True.

Ltac zesu_witness_application_head term :=
  lazymatch term with
  | ?function ?argument => zesu_witness_application_head function
  | _ => term
  end.

(* A fixed non-scalar parameter anchors the owned fact to this state. *)
Ltac zesu_witness_fact_anchor term :=
  lazymatch term with
  | ?function ?argument =>
      first [
        assert_fails (has_evar argument);
        is_var argument;
        let T := type of argument in
        let sort := type of T in
        lazymatch sort with Prop => fail | _ => idtac end;
        lazymatch T with
        | Z => fail | nat => fail | N => fail | bool => fail
        | unit => fail | list _ => fail | bv _ => fail
        | _ => idtac
        end
      | zesu_witness_fact_anchor function ]
  end.

Ltac zesu_witness_owned_fact requested :=
  has_evar requested;
  zesu_witness_fact_anchor requested;
  let head := zesu_witness_application_head requested in
  match goal with
  | H : ?owned |- _ =>
      assert_fails (has_evar owned);
      let available := zesu_witness_application_head owned in
      constr_eq head available;
      unify requested owned
  end.

Ltac zesu_witness_pure_constraints requested :=
  lazymatch requested with
  | ?left /\ ?right =>
      try zesu_witness_pure_constraints left;
      try zesu_witness_pure_constraints right
  | _ => try zesu_witness_owned_fact requested
  end.

(* Inspect only the requested proposition; never unfold the Coq context. *)
Ltac zesu_witness_resource_constraints fuel requested :=
  lazymatch requested with
  | @bi_pure _ ?fact => zesu_witness_pure_constraints fact
  | @bi_sep _ ?left ?right =>
      zesu_witness_resource_constraints fuel left;
      zesu_witness_resource_constraints fuel right
  | _ =>
      lazymatch fuel with
      | S ?remaining =>
          try (
            let head := zesu_witness_application_head requested in
            assert_fails (is_var head);
            assert_fails (has_evar head);
            let expanded := eval cbv beta iota delta [head] in requested in
            first [constr_eq requested expanded; idtac |
              zesu_witness_resource_constraints remaining expanded])
      | O => idtac
      end
  end.

Ltac zesu_constraint_witness T :=
  lazymatch T with
  | li_prod _ _ => zesu_primitive_tuple_witness T
  | Z => open_constr:(_ : Z)
  | nat => open_constr:(_ : nat)
  | N => open_constr:(_ : N)
  | bool => open_constr:(_ : bool)
  | list ?A => open_constr:(_ : list A)
  | bv ?width => open_constr:(_ : bv width)
  end.

Ltac zesu_witness_open_existentials fuel :=
  lazymatch fuel with
  | S ?remaining =>
      lazymatch goal with
      | |- envs_entails ?environment (@bi_exist _ ?T ?body) =>
          assert_fails (has_evar T);
          let witness := zesu_constraint_witness T in
          notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod;
          zesu_witness_open_existentials remaining
      | |- envs_entails ?environment ?requested =>
          lazymatch requested with
          | @bi_sep _ _ _ => idtac
          | @bi_pure _ _ => idtac
          | _ =>
              let head := zesu_witness_application_head requested in
              let expanded := eval cbv beta iota delta [head] in requested in
              assert_fails (constr_eq requested expanded);
              change (envs_entails environment expanded);
              zesu_witness_open_existentials remaining
          end
      end
  | O => fail 0 "The witness shape exceeds the structural step limit."
  end.

Ltac zesu_pure_witness_constraints_if_enabled :=
  let _ := constr:(_ : ZesuStepPureWitnessConstraints) in
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ _ _) =>
      let introFuel := constr:(12%nat) in
      zesu_witness_open_existentials introFuel;
      lazymatch goal with
      | |- envs_entails _ ?requested =>
          let unfoldFuel := constr:(4%nat) in
          progress (zesu_witness_resource_constraints unfoldFuel requested)
      end
  end.

Ltac zesu_record_constructor_witness T :=
  let guard := constr:(ltac:(
    assert_fails (has_evar T);
    let probe := fresh "recordConstructorProbe" in
    assert_fails (assert (probe : T) by (econstructor 2; shelve));
    exact I) : True) in
  open_constr:(ltac:(econstructor 1;
    lazymatch goal with
    | |- ?fieldType =>
        let sort := type of fieldType in
        lazymatch sort with Prop => fail 0 "The record has a proof field."
        | _ => shelve end
    end) : T).

Ltac zesu_record_tuple_witness T continuation :=
  lazymatch T with
  | li_prod ?A ?B =>
      first
        [ let head := zesu_record_constructor_witness A in
          zesu_record_tuple_witness B ltac:(fun tail found =>
            continuation constr:(li_pair head tail) constr:(true))
        | let head := open_constr:(_ : A) in
          zesu_record_tuple_witness B ltac:(fun tail found =>
            continuation constr:(li_pair head tail) found) ]
  | unit => continuation constr:(tt) constr:(false)
  | _ =>
      let witness := zesu_record_constructor_witness T in
      continuation witness constr:(true)
  end.

Ltac zesu_record_witness_if_enabled :=
  let _ := constr:(_ : ZesuStepRecordWitness) in
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T ?body) =>
      zesu_record_tuple_witness T ltac:(fun witness found =>
        lazymatch found with true =>
          notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod
        end)
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

(* Refute the fault assertion before its trace reads exception registers. *)
Ltac zesu_ram_fault_assert :=
  lazymatch goal with
  | |- envs_entails _ (WPasm
      (Smt (Assert (Unop Not (Val (Val_Bool ?condition) _) _)) _ :t: _)) =>
      let decision := lazymatch condition with
        | bool_decide _ => constr:(condition)
        | _ => let expanded := eval unfold condition in condition in
            constr:(expanded)
        end in
      lazymatch decision with
      | bool_decide ?bound =>
          lazymatch bound with Z.le _ _ => idtac | Z.ge _ _ => idtac end;
          lazymatch bound with context [bv_zero_extend 128 _] => idtac end;
          let Hpositive := fresh "HramBound" in
          assert (Hpositive : bound) by (zesu_stack_arithmetic);
          let Htrue := fresh "HramDecision" in
          assert (Htrue : condition = true) by
            (apply bool_decide_true; exact Hpositive);
          rewrite Htrue;
          zesu_expose_environment_alias;
          iApply wp_assert; rewrite wp_exp_unfold;
          iExists (Val_Bool false); iSplit; first done;
          iExists false; iSplit; first done;
          iIntros (Hfalse); discriminate
      end
  end.

(* Entry layout bounds refute a negated widened RAM bound. *)
Ltac zesu_ram_fault_if_enabled :=
  let _ := constr:(_ : ZesuStepRamFault) in
  first [solve [zesu_ram_fault_assert]
    | solve [lazymatch goal with
      | |- envs_entails _ ((WPasm _) ∧ True)%I =>
          iSplit; [zesu_ram_fault_assert | done]
      end]
    | match goal with
  | Hfault : ~ ?bound |- _ =>
      lazymatch bound with Z.le _ _ => idtac | Z.ge _ _ => idtac end;
      lazymatch bound with context [bv_zero_extend 128 _] => idtac end;
      solve [exfalso; apply Hfault; zesu_stack_arithmetic]
  end].

Class ZesuStepRegionFault : Prop := zesu_step_region_fault : True.

(* Keep branch bounds while selecting the readable-region alternative. *)
Ltac zesu_region_arithmetic_statement statement :=
  lazymatch statement with
  | Z.le _ _ => idtac
  | Z.lt _ _ => idtac
  | Z.ge _ _ => idtac
  | Z.gt _ _ => idtac
  | @eq Z _ _ => idtac
  | ~ ?bound => zesu_region_arithmetic_statement bound
  | ?left /\ ?right =>
      zesu_region_arithmetic_statement left;
      zesu_region_arithmetic_statement right
  | ?left \/ ?right =>
      zesu_region_arithmetic_statement left;
      zesu_region_arithmetic_statement right
  end.

Ltac zesu_region_fault_arithmetic :=
  lazymatch goal with |- ~ _ => intro | _ => idtac end;
  repeat first [progress zesu_split_folded_pure |
    match goal with H : _ /\ _ |- _ => destruct H end];
  repeat match goal with
  | H : ?statement |- _ =>
      lazymatch type of statement with Prop => idtac end;
      assert_fails (zesu_region_arithmetic_statement statement);
      clear H
  end;
  repeat match goal with
  | H : ?left \/ ?right |- _ =>
      zesu_region_arithmetic_statement left;
      zesu_region_arithmetic_statement right;
      destruct H;
      repeat match goal with Hpair : _ /\ _ |- _ => destruct Hpair end
  end;
  repeat match goal with
  | H : context[?term] |- _ =>
      lazymatch type of term with Z => progress reduce_closed term end
  | |- context[?term] =>
      lazymatch type of term with Z => progress reduce_closed term end
  end;
  try (rewrite zesu_signed_zero_extend_add_64_128; last bv_solve);
  repeat match goal with
  | H : context[bv_signed (bv_zero_extend 128 ?value)] |- _ =>
      rewrite (zesu_signed_zero_extend_64_128 value) in H
  end;
  rewrite ?zesu_signed_zero_extend_64_128;
  first [bv_solve |
    match goal with Hnegative : ~ ?bound |- _ =>
      zesu_region_arithmetic_statement bound;
      exfalso; apply Hnegative; bv_solve
    end].

Ltac zesu_region_fault_bound_if_enabled :=
  let _ := constr:(_ : ZesuStepRegionFault) in
  lazymatch goal with |- ?bound => zesu_region_arithmetic_statement bound end;
  solve [zesu_region_fault_arithmetic].

(* Refute an arithmetic assertion before the trace reads fault registers. *)
Ltac zesu_region_fault_assert :=
  lazymatch goal with
  | |- envs_entails _ (WPasm (Smt (Assert ?expression) _ :t: _)) =>
      let condition := lazymatch expression with
        | Unop Not (Val (Val_Bool ?condition) _) _ => constr:(condition)
        | Val (Val_Bool ?condition) _ => constr:(condition)
        end in
      let decision := lazymatch condition with
        | bool_decide _ => constr:(condition)
        | _ => let expanded := eval unfold condition in condition in
            constr:(expanded)
        end in
      lazymatch decision with bool_decide ?bound =>
        zesu_region_arithmetic_statement bound;
        lazymatch bound with context[bv_zero_extend 128 _] => idtac end;
        let Hdecision := fresh "HregionDecision" in
        lazymatch expression with
        | Unop Not _ _ =>
            let Hpositive := fresh "HregionBound" in
            assert (Hpositive : bound) by zesu_region_fault_arithmetic;
            assert (Hdecision : condition = true) by
              (apply bool_decide_true; exact Hpositive)
        | Val _ _ =>
            let Hnegative := fresh "HregionBound" in
            assert (Hnegative : ~ bound) by zesu_region_fault_arithmetic;
            assert (Hdecision : condition = false) by
              (apply bool_decide_false; exact Hnegative)
        end;
        rewrite Hdecision;
        zesu_expose_environment_alias;
        iApply wp_assert; rewrite wp_exp_unfold;
        iExists (Val_Bool false); iSplit; first done;
        iExists false; iSplit; first done;
        iIntros (Hfalse); discriminate
      end
  end.

Ltac zesu_region_fault_if_enabled :=
  let _ := constr:(_ : ZesuStepRegionFault) in
  first [solve [zesu_region_fault_assert] |
    solve [lazymatch goal with
      | |- envs_entails _ ((WPasm _) ∧ True)%I =>
          iSplit; [zesu_region_fault_assert | done]
      end]].

(* Inspect applications without unfolding the proof context. *)
Ltac zesu_handoff_closed_term term :=
  tryif is_var term then fail 0 else
  tryif has_evar term then fail 0 else
  lazymatch term with
  | (fun _ => _) => fail 0
  | (forall _, _) => fail 0
  | (let _ := _ in _) => fail 0
  | ?function ?argument =>
      zesu_handoff_closed_term function; zesu_handoff_closed_term argument
  | _ => idtac
  end.

(* Evaluate closed integer terms without unfolding symbolic record projections. *)
Ltac zesu_handoff_closed_Z term continuation :=
  tryif zesu_handoff_closed_term term then
    let reduced := eval vm_compute in term in continuation reduced
  else lazymatch term with
  | Z.add ?left ?right =>
      zesu_handoff_closed_Z left ltac:(fun left =>
        zesu_handoff_closed_Z right ltac:(fun right =>
          let reduced := constr:(Z.add left right) in continuation reduced))
  | Z.sub ?left ?right =>
      zesu_handoff_closed_Z left ltac:(fun left =>
        zesu_handoff_closed_Z right ltac:(fun right =>
          let reduced := constr:(Z.sub left right) in continuation reduced))
  | Z.mul ?left ?right =>
      zesu_handoff_closed_Z left ltac:(fun left =>
        zesu_handoff_closed_Z right ltac:(fun right =>
          let reduced := constr:(Z.mul left right) in continuation reduced))
  | Z.opp ?value =>
      zesu_handoff_closed_Z value ltac:(fun value =>
        let reduced := constr:(Z.opp value) in continuation reduced)
  | _ => continuation term
  end.

Ltac zesu_handoff_goal_address_if_enabled :=
  let _ := constr:(_ : ZesuStepWordArrayHandoff) in
  lazymatch goal with
  | |- envs_entails _ ?target =>
      lazymatch target with
      | context [(?address ↦ₘ{?q}∗ _)%I] =>
          zesu_expose_environment_alias;
          iMatchHyp ltac:(fun name body =>
            lazymatch body with
            | (?available ↦ₘ{?fraction} ?value)%I =>
                tryif constr_eq address available then fail 0 else
                zesu_handoff_closed_Z address ltac:(fun addressNorm =>
                  zesu_handoff_closed_Z available ltac:(fun availableNorm =>
                    let Heq := fresh "HhandoffAddress" in
                    assert (Heq : address = available) by
                      (change (addressNorm = availableNorm); ring);
                    rewrite Heq; clear Heq))
            end)
      end
  end.

Ltac zesu_handoff_memory_if_enabled :=
  let _ := constr:(_ : ZesuStepWordArrayHandoff) in
  lazymatch goal with |- envs_entails _ _ => idtac end;
  zesu_expose_environment_alias;
  iMatchHyp ltac:(fun name body =>
    lazymatch body with
    | (?address ↦ₘ{?q}? ?count)%I =>
        zesu_handoff_closed_Z count ltac:(fun normalized =>
          let Hzero := fresh "HhandoffEmpty" in
          assert (Hzero : count = 0%Z) by (change (normalized = 0%Z); lia);
          iEval (rewrite Hzero mem_mapsto_uninit_0) in name;
          clear Hzero; iDestruct name as %?)
    end).

Ltac zesu_handoff_adjacent_words_if_enabled :=
  let _ := constr:(_ : ZesuStepWordArrayHandoff) in
  lazymatch goal with
  | |- envs_entails _ (subsume (?address ↦ₘ ?low) ?requested ?G) =>
      let width := type of low in constr_eq width (bv 64);
      zesu_expose_environment_alias;
      iMatchHyp ltac:(fun name body =>
        lazymatch body with
        | (?other ↦ₘ ?high)%I =>
            let width := type of high in constr_eq width (bv 64);
            zesu_handoff_closed_Z other ltac:(fun otherNorm =>
              zesu_handoff_closed_Z address ltac:(fun addressNorm =>
                let Heq := fresh "HhandoffAdjacent" in
                assert (Heq : other = (address + 8)%Z) by
                  (change (otherNorm = addressNorm + 8)%Z; ring);
                iEval (rewrite Heq) in name; clear Heq;
                iApply (subsume_mem_adjacent_u64_byte_array _ _ _ low high)))
        end)
  end.

Ltac zesu_handoff_facts_if_enabled :=
  let _ := constr:(_ : ZesuStepWordArrayHandoff) in
  lazymatch goal with
  | |- envs_entails _ (subsume _ _ _) =>
      progress zesu_saturate_derived_facts
  end.

Ltac zesu_handoff_integer_equality_if_enabled :=
  let _ := constr:(_ : ZesuStepWordArrayHandoff) in
  lazymatch goal with
  | |- @eq Z ?left ?right =>
      zesu_handoff_closed_Z left ltac:(fun leftNorm =>
        zesu_handoff_closed_Z right ltac:(fun rightNorm =>
          change (leftNorm = rightNorm); solve [lia | ring]))
  end.

Class ZesuStepIntegerArrayAddress : Prop :=
  zesu_step_integer_array_address : True.

Ltac zesu_integer_pointer_root pointer continuation :=
  lazymatch pointer with
  | bv_add ?base ?offset =>
      zesu_handoff_closed_term offset; zesu_integer_pointer_root base continuation
  | bv_sub ?base ?offset =>
      zesu_handoff_closed_term offset; zesu_integer_pointer_root base continuation
  | Z_to_bv 64 ?base => continuation base
  end.

Ltac zesu_integer_array_emit_facts proof :=
  let statement := type of proof in
  let expanded := eval hnf in statement in
  lazymatch expanded with
  | ?left /\ ?right =>
      let leftProof := constr:(@proj1 left right proof) in
      let rightProof := constr:(@proj2 left right proof) in
      zesu_integer_array_emit_facts leftProof;
      zesu_integer_array_emit_facts rightProof
  | _ =>
      lazymatch goal with
      | _ : statement |- _ => idtac
      | _ => let name := fresh "HarrayFact" in pose proof proof as name
      end
  end.

Ltac zesu_integer_array_facts :=
  repeat match goal with
  | H : ?statement |- _ =>
      lazymatch type of statement with Prop => idtac end;
      progress zesu_integer_array_emit_facts H
  end.

Class ZesuStepArrayBounds : Prop :=
  zesu_step_array_bounds : True.

(* Convert an integer address only from its owned no-wrap facts. *)
Ltac zesu_array_bound_integer_casts :=
  repeat match goal with
  | |- context[bv_unsigned (Z_to_bv 64 ?pointer)] =>
      let Hcast := fresh "HarrayBoundCast" in
      assert (Hcast : bv_unsigned (Z_to_bv 64 pointer) = pointer)
        by zesu_stack_arithmetic;
      rewrite Hcast; clear Hcast
  end.

Ltac zesu_array_bounds_if_enabled :=
  let enabled := constr:(_ : ZesuStepArrayBounds) in
  lazymatch goal with
  | |- SHELVED_SIDECOND _ => unshelve_sidecond
  | _ => idtac
  end;
  unLET;
  lazymatch goal with
  | |- 0 <= ?address - ?base =>
      solve [zesu_integer_array_facts; bv_solve | lia]
  | |- (?index + ?width <= length ?storage)%nat =>
      solve [
        zesu_integer_array_facts;
        zesu_array_bound_integer_casts;
        repeat match goal with
        | |- context [?base + ?offset - ?base] =>
            replace (base + offset - base) with offset by lia
        | |- context [?base - ?base] =>
            replace (base - base) with 0 by lia
        end;
        rewrite ?length_app ?length_take ?length_drop;
        cbn [length]; lia]
  end.

Ltac zesu_integer_array_address_if_enabled :=
  let _ := constr:(_ : ZesuStepIntegerArrayAddress) in
  zesu_expose_environment_alias;
  repeat match goal with
  | Hlocal := _ |- envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      lazymatch address with context[Hlocal] => unfold Hlocal in *; clear Hlocal end
  end;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo (bv_unsigned ?pointer)) _) =>
      let expanded := eval cbv beta zeta in pointer in
      zesu_integer_pointer_root expanded ltac:(fun _ =>
      let integer := zesu_stack_integer_address expanded in
      iMatchHyp ltac:(fun H body =>
        lazymatch body with
        | (?lower ↦ₘ{?q}∗ ?values)%I =>
            lazymatch type of values with list (bv ?width) =>
              let Heq := fresh "HarrayAddress" in
              assert (Heq : bv_unsigned pointer = integer) by
                (zesu_stack_arithmetic);
              let Hrange := fresh "HarrayAddressRange" in
              assert (Hrange : (lower <= integer < lower +
                Z.of_nat (length values) * Z.of_N (width `div` 8))%Z) by
                ((repeat first [progress zesu_split_folded_pure |
                  match goal with Hpure : _ /\ _ |- _ => destruct Hpure end];
                  zesu_normalize_binary_nat_hypotheses;
                  first [
                    let enabled := constr:(_ : ZesuStepArrayRegionBounds) in
                    zesu_array_bound_integer_casts;
                    zesu_byte_array_lengths_if_enabled;
                    solve [lia | bv_solve]
                  | bv_solve]));
              zesu_integer_array_facts;
              rewrite Heq; clear Heq
            end
        end))
  end.

Ltac zesu_liAStep :=
 liEnsureInvariant;
 try progress (unfold TRACE_LET);
 try liAIntroduceLetInGoal;
 first [
    zesu_expose_instruction_lookup
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
  | liUnfoldEarly
  | zesu_known_pair_witness_if_enabled
  | zesu_pure_witness_constraints_if_enabled
  | zesu_record_witness_if_enabled
  | zesu_primitive_tuple_if_enabled
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
