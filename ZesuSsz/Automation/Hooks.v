Require Import ZesuSsz.Automation.EntryIntro.
Require Import ZesuSsz.Automation.SwitchDispatch.
(** Project-wide Lithium hook redefinitions belong in this module. *)

From iris.proofmode Require Import environments.
Require Import isla.riscv64.riscv64.
Require Export ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Automation.NatBounds.
Require Export ZesuSsz.Automation.ByteArrayLengths.
Require Import ZesuSsz.Automation.UninitRegions.
Require Import ZesuSsz.Automation.BoundedArithmetic.
Require Import ZesuSsz.Automation.TraceTailLemmas.
Require Import ZesuSsz.Automation.InstrPre.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.PureFacts.
Require Export ZesuSsz.Automation.ExitMeaning.
Require Export ZesuSsz.Automation.IntegerReturn.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import ZesuSsz.Automation.ConjunctMatch.

(* Keep the selected table named during search and simplification.
   Explicit computation still resolves one selected instruction. *)
Global Typeclasses Opaque selectedCodeLookup.
Arguments selectedCodeLookup : simpl never.

Class ZesuStepInstructionLookup : Prop :=
  zesu_step_instruction_lookup : True.

(* Expose only a code wrapper whose head reduces to a lookup resource. *)
Ltac zesu_expose_instruction_lookup :=
  zesu_switch_enabled constr:(ZesuStepInstructionLookup);
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

(* Reduce one complete low-bit wrap before general arithmetic. *)
Ltac zesu_low_mask_integer_offset width offset continuation :=
  lazymatch offset with
  | Z_to_bv width ?integer =>
      assert_fails (has_evar integer); continuation integer
  | _ =>
      is_closed_term offset;
      let integer := eval vm_compute in (bv_unsigned offset) in
      continuation integer
  end.

Ltac zesu_low_mask_sub_modulus_goal :=
  lazymatch goal with
  | |- bv_unsigned (bv_and (bv_add ?value ?offset) ?mask) = ?requested =>
      assert_fails (has_evar value);
      assert_fails (has_evar requested);
      is_closed_term mask;
      lazymatch type of value with bv ?width =>
        is_closed_term width;
        let low := eval vm_compute in
          (N.log2 (Z.to_N (bv_unsigned mask + 1))) in
        let modulus := eval vm_compute in (bv_modulus low) in
        let Hwidth := fresh "HmaskWidth" in
        assert (Hwidth : (low <= width)%N) by (vm_compute; congruence);
        let Hmask := fresh "HmaskBits" in
        assert (Hmask : bv_unsigned mask = Z.ones (Z.of_N low)) by
          (vm_compute; reflexivity);
        zesu_low_mask_integer_offset width offset ltac:(fun integer =>
          let Hoffset := fresh "HmaskOffset" in
          assert (Hoffset : offset = Z_to_bv width integer) by
            first [reflexivity | is_closed_term offset;
              apply bv_eq; vm_compute; reflexivity];
          let Hrange := fresh "HmaskRange" in
          assert (Hrange : modulus <= bv_unsigned value + integer < 2 * modulus)
            by lia;
          first [let checked := constr:(eq_refl :
                   offset = Z_to_bv width integer) in idtac | rewrite Hoffset];
          rewrite (zesu_unsigned_low_mask_add_sub_modulus
            width low value mask integer Hwidth Hmask Hrange);
          solve [reflexivity | change (bv_unsigned value + integer - modulus = requested); lia])
      end
  end.


(* Normalize a branch guard only when it contains a complete low-bit wrap. *)
Ltac zesu_low_mask_branch_hypotheses :=
  repeat match goal with
  | H : context [bv_signed (bv_zero_extend 128
        (bv_and (bv_add ?value ?offset) ?mask))] |- _ =>
      assert_fails (has_evar value);
      assert_fails (has_evar offset);
      is_closed_term mask;
      progress (repeat match type of H with
        | context [bv_signed (bv_zero_extend 128 ?word)] =>
            lazymatch type of word with bv 64 => idtac end;
            assert_fails (has_evar word);
            rewrite (zesu_signed_zero_extend_64_128 word) in H
        end)
  | H : context [bv_unsigned (bv_and (bv_add ?value ?offset) ?mask)] |- _ =>
      assert_fails (has_evar value);
      is_closed_term mask;
      lazymatch type of value with bv ?width =>
        is_closed_term width;
        let low := eval vm_compute in
          (N.log2 (Z.to_N (bv_unsigned mask + 1))) in
        let modulus := eval vm_compute in (bv_modulus low) in
        zesu_low_mask_integer_offset width offset ltac:(fun integer =>
          let Hnormalized := fresh "HmaskNormalized" in
          assert (Hnormalized :
            bv_unsigned (bv_and (value + offset) mask) =
              bv_unsigned value + integer - modulus)
            by zesu_low_mask_sub_modulus_goal;
          progress rewrite Hnormalized in H;
          clear Hnormalized)
      end
  end.


Ltac zesu_low_mask_bv_goal :=
  lazymatch goal with
  | |- bv_and (bv_add ?value ?offset) ?mask = Z_to_bv ?width ?requested =>
      assert_fails (has_evar value);
      assert_fails (has_evar requested);
      is_closed_term mask;
      is_closed_term width;
      let low := eval vm_compute in
        (N.log2 (Z.to_N (bv_unsigned mask + 1))) in
      let modulus := eval vm_compute in (bv_modulus low) in
      let Hwidth := fresh "HmaskWidth" in
      assert (Hwidth : (low <= width)%N) by (vm_compute; congruence);
      let Hmask := fresh "HmaskBits" in
      assert (Hmask : bv_unsigned mask = Z.ones (Z.of_N low)) by
        (vm_compute; reflexivity);
      zesu_low_mask_integer_offset width offset ltac:(fun integer =>
        let Hoffset := fresh "HmaskOffset" in
        assert (Hoffset : offset = Z_to_bv width integer) by
          first [reflexivity | is_closed_term offset;
            apply bv_eq; vm_compute; reflexivity];
        let Hrange := fresh "HmaskRange" in
        assert (Hrange : modulus <= bv_unsigned value + integer < 2 * modulus)
          by lia;
        let Hresult := fresh "HmaskResult" in
        assert (Hresult : requested = bv_unsigned value + integer - modulus)
          by lia;
        first [let checked := constr:(eq_refl :
                 offset = Z_to_bv width integer) in idtac | rewrite Hoffset];
        rewrite Hresult;
        exact (zesu_low_mask_add_bv_sub_modulus
          width low value mask integer Hwidth Hmask Hrange))
  end.

Ltac zesu_low_mask_sub_modulus_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepMaskNormalizer);
  first [solve [zesu_low_mask_sub_modulus_goal]
    | solve [zesu_low_mask_bv_goal]
    | solve [progress zesu_low_mask_branch_hypotheses; lia]].

(* Keep low-bit mask equalities symbolic before general arithmetic unfolds them. *)
Ltac zesu_low_mask_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepLowMask);
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
  zesu_switch_enabled constr:(ZesuStepStrictSigned);
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
Ltac bv_solve ::= first [solve [zesu_strict_signed_if_enabled] |
  solve [zesu_low_mask_sub_modulus_if_enabled] |
  solve [zesu_low_mask_if_enabled] |
  (
  bv_simplify_arith;
  bv_saturate_unsigned;
  bv_solve_unfold_tac;
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned in *;
  simpl; lia)].

Ltac zesu_solve_machine_bounds :=
  first [solve [zesu_low_mask_sub_modulus_if_enabled] |
    solve [zesu_low_mask_if_enabled] |
    (solve [zesu_normalize_binary_nat_hypotheses;
      zesu_normalize_binary_nat_goal; zesu_normalize_machine_map; bv_solve])].
Ltac zesu_solve_machine_linear :=
  first [zesu_byte_index_arithmetic
    | (first [solve [repeat match goal with
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

(* Normalize each selected candidate once. Check local alias bodies separately. *)
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* Keep the original visitor for aliases, binders, and uncommon kernel forms. *)
Ltac zesu_stack_closed_fallback recurse current :=
  let rec visit current :=
    tryif is_var current then
      let body := eval unfold current in current in
      recurse body
    else lazymatch current with
    | (fun _ => _) => fail 0
    | (forall _, _) => fail 0
    | ?function ?argument => visit function; visit argument
    | _ => idtac
    end
  in visit current.

(* Visit each application head and argument without Ltac1 spine matching. *)
Ltac2 rec zesu_stack_closed_visit (term : constr) (fallback : Ltac1.t) :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      zesu_stack_closed_visit head fallback;
      Array.iter (fun argument => zesu_stack_closed_visit argument fallback) arguments
  | Constr.Unsafe.Constant _ _ => ()
  | Constr.Unsafe.Constructor _ _ => ()
  | Constr.Unsafe.Ind _ _ => ()
  | Constr.Unsafe.Sort _ => ()
  | _ => Ltac1.apply fallback [Ltac1.of_constr term] Ltac1.run
  end.
Ltac zesu_stack_closed_term term :=
  tryif has_evar term then fail 0 else
  let expanded := eval cbv beta zeta in term in
  let check := ltac2:(value fallback |-
    zesu_stack_closed_visit (Option.get (Ltac1.to_constr value)) fallback) in
  check expanded ltac:(fun current =>
    zesu_stack_closed_fallback zesu_stack_closed_term current).

Ltac zesu_stack_reduce_closed term :=
  zesu_stack_closed_term term;
  let reduced := eval vm_compute in term in
  change_no_check term with reduced in *.

(* Skip canonical integers with one syntactic constructor walk. *)
(* Inspect the typed constructor tree without reduction or context access. *)
Ltac2 rec zesu_stack_positive_literal_term (term : constr) :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Constructor _ _ => Constr.equal term constr:(BinNums.xH)
  | Constr.Unsafe.App head arguments =>
      if Bool.and (Constr.is_constructor head) (Int.equal (Array.length arguments) 1)
      then zesu_stack_positive_literal_term (Array.get arguments 0)
      else false
  | _ => false
  end.
Ltac2 zesu_stack_integer_literal_term (term : constr) :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Constructor _ _ => Constr.equal term constr:(BinNums.Z0)
  | Constr.Unsafe.App head arguments =>
      if Bool.and (Int.equal (Array.length arguments) 1)
          (Bool.or (Constr.equal head constr:(BinNums.Zpos))
                   (Constr.equal head constr:(BinNums.Zneg)))
      then zesu_stack_positive_literal_term (Array.get arguments 0)
      else false
  | _ => false
  end.
Ltac zesu_stack_integer_literal term :=
  let check := ltac2:(value |-
    if zesu_stack_integer_literal_term (Option.get (Ltac1.to_constr value))
    then () else Control.zero (Tactic_failure None)) in
  check term.

(* Normalize the selected hypothesis without searching other hypotheses. *)
Ltac zesu_stack_normalize_hypothesis hypothesis := once (
  repeat (
    let statement := type of hypothesis in
    match statement with
    | context[?term] =>
        lazymatch type of term with Z => progress (
          tryif zesu_stack_integer_literal term then fail 0 else idtac;
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
  zesu_switch_enabled constr:(ZesuStepStackWrite);
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

Class ZesuPureFactAnchor {Sigma} (target anchor source : iProp Sigma) : Prop :=
  zesu_pure_fact_anchor_intro : ZesuPureFactIntro target source.
#[global] Hint Mode ZesuPureFactAnchor + + + - : typeclass_instances.

Class ZesuStepCanonicalAnchor : Prop := {}.

Class ZesuCanonicalAnchor {Sigma}
    (anchor canonical source : iProp Sigma) : Prop :=
  zesu_canonical_anchor_intro : ZesuPureFactAnchor canonical anchor source.
#[global] Hint Mode ZesuCanonicalAnchor + + - - : typeclass_instances.

Class ZesuStepCanonicalPureConjunction : Prop := {}.

(* The private registry view preserves the global Anchor input modes. *)
From Ltac2 Require Import Ltac2.
Declare ML Module "zesu-signature-gates.plugin".
Ltac2 @ external zesu_target_registration : constr -> unit :=
  "zesu-signature-gates.plugin" "target_registration".
Set Default Proof Mode "Classic".
Ltac zesu_lookup_target_registration :=
  ltac2:(zesu_target_registration '(@ZesuPureFactAnchor)).

(* The result contains a closed introduction and its retained pure proof. *)
Record ZesuTargetRegistration {Sigma} (target : iProp Sigma) : Type := {
  zesu_target_condition : Prop;
  zesu_target_resources : iProp Sigma;
  zesu_target_introduction :
    ZesuPureFactIntro target (⌜zesu_target_condition⌝ ∗ zesu_target_resources)%I;
  zesu_target_derivation : zesu_target_condition
}.

(* Retained pure facts determine hidden certificate arguments. *)
Ltac zesu_closed_target_registration target :=
  constr:(ltac:(
    assert_fails (has_evar target);
    lazymatch type of target with iProp ?Sigma =>
      let evidence := open_constr:(ltac:(zesu_lookup_target_registration)
        : @ZesuPureFactAnchor Sigma target _ _) in
      lazymatch type of evidence with
      | ZesuPureFactAnchor _ ?anchor ?source =>
          let premises := open_constr:(_ : Prop) in
          let resources := open_constr:(_ : iProp Sigma) in
          unify source (⌜premises⌝ ∗ resources)%I;
          let derivation := constr:(ltac:(solve [repeat first
            [eassumption | split | zesu_finish_lia]]) : premises) in
          assert_fails (has_evar evidence);
          assert_fails (has_evar derivation);
          exact {| zesu_target_condition := premises;
            zesu_target_resources := resources;
            zesu_target_introduction :=
              @zesu_pure_fact_anchor_intro Sigma target anchor source evidence;
            zesu_target_derivation := derivation |}
      end
    end) : ZesuTargetRegistration target).

(* Run before resource splitting or existential packaging. *)
Ltac zesu_target_registered_intro_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepCanonicalPureConjunction);
  lazymatch goal with
  | |- envs_entails _ ?requested =>
      let target := lazymatch requested with
        | (?leftTarget ∗ True)%I => constr:(leftTarget)
        | _ => constr:(requested)
        end in
      let registration := zesu_closed_target_registration target in
      let introduction := constr:(@zesu_target_introduction _ target registration) in
      let derivation := constr:(@zesu_target_derivation _ target registration) in
      let source := constr:((⌜@zesu_target_condition _ target registration⌝ ∗
        @zesu_target_resources _ target registration)%I) in
      zesu_expose_environment_alias;
      first [constr_eq requested target | iSplitL; [|done]];
      iApply (@zesu_pure_fact_intro _ target source introduction);
      iSplit; [iPureIntro; exact derivation|]
  end.

(* The owned anchor determines the registered target before conversion. *)
Ltac zesu_canonical_anchor_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepCanonicalAnchor);
  lazymatch goal with
  | |- envs_entails _ ?target =>
      iMatchHyp ltac:(fun name anchor =>
        let registered := constr:(_ : ZesuCanonicalAnchor anchor _ _) in
        lazymatch type of registered with
        | ZesuCanonicalAnchor _ ?canonical ?source =>
            let evidence := constr:(@zesu_canonical_anchor_intro
              _ anchor canonical source registered) in
            let intro := constr:(@zesu_pure_fact_anchor_intro
              _ canonical anchor source evidence : ZesuPureFactIntro target source) in
            iApply (@zesu_pure_fact_intro _ target source intro)
        end)
  end.

Class ZesuStepPureFactExistential : Prop :=
  zesu_step_pure_fact_existential : True.

(* Factor the dependent continuation before registered introduction matching. *)
Ltac zesu_pure_fact_existential_if_enabled :=
  let _ := constr:(_ : ZesuStepPureFactExistential) in
  lazymatch goal with
  | |- envs_entails ?environment ?target =>
      let concrete := eval hnf in environment in
      change (envs_entails concrete target)
  end;
  lazymatch goal with
  | |- envs_entails ?environment (@bi_exist ?Sigma ?T ?body) =>
      assert_fails (has_evar T);
      lazymatch body with
      | (fun witness => @bi_sep _ (@bi_pure _ ?condition) ?rest) =>
          let remainder := constr:(fun witness : T => rest) in
          let continuation := fresh "pureIntroContinuation" in
          pose (continuation := remainder);
          let target := constr:((∃ witness : T, ⌜condition⌝ ∗ continuation witness)%I) in
          change (envs_entails environment target);
          let evidence := constr:(_ : ZesuPureFactIntro target _) in
          lazymatch type of evidence with
          | ZesuPureFactIntro _ ?source =>
              iApply (@zesu_pure_fact_intro _ target source evidence)
          end;
          unfold continuation; clear continuation
      end
  end.

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
  zesu_switch_enabled constr:(ZesuStepPureFactHints);
  lazymatch goal with
  | |- envs_entails _ ?target =>
      first [
        lazymatch target with
        | bi_pure ?P =>
            let evidence := zesu_registered_pure_fact P in
            iPureIntro; exact evidence
        end
      | zesu_canonical_anchor_if_enabled
      | zesu_pure_fact_existential_if_enabled
      | let evidence := constr:(_ : ZesuPureFactIntro target _) in
        lazymatch type of evidence with
        | ZesuPureFactIntro _ ?source =>
            iApply (@zesu_pure_fact_intro _ target source evidence)
        end
      | iMatchHyp ltac:(fun name source =>
          let evidence := constr:(_ : ZesuPureFactIntro target source) in
          iApply (@zesu_pure_fact_intro _ target source evidence))
      | iMatchHyp ltac:(fun name anchor =>
          let evidence := constr:(_ : ZesuPureFactAnchor target anchor _) in
          lazymatch type of evidence with
          | ZesuPureFactAnchor _ _ ?source =>
              let intro := constr:(@zesu_pure_fact_anchor_intro _ target anchor source evidence) in
              iApply (@zesu_pure_fact_intro _ target source intro)
          end) ]
  | |- ?P =>
      let evidence := zesu_registered_pure_fact P in exact evidence
  end.

(* Only the requested list shape permits extraction of owned pure facts. *)
Ltac zesu_list_cons_witness_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepListWitness);
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
  zesu_switch_enabled constr:(ZesuStepTupleWitness);
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ nat _) =>
      fail 0 "leave the nat index to Lithium"
  | |- envs_entails _ (@bi_exist _ (li_prod nat _) _) =>
      fail 0 "leave the protected nat index to Lithium"
  | |- envs_entails _ (@bi_exist _ (li_prod ?A ?B) ?body) =>
      let T := constr:(li_prod A B) in
      assert_fails (has_evar T);
      let witness := zesu_primitive_tuple_witness T in
      notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod
  end.

(* Tuple guards use the owned widened comparison without adding a premise. *)
Ltac zesu_primitive_tuple_guard_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepTupleWitness);
  lazymatch goal with
  | |- Z.lt _ _ => idtac | |- Z.le _ _ => idtac | |- Z.ge _ _ => idtac
  end;
  solve [progress (repeat match goal with
    | H : context [bv_signed (bv_zero_extend 128 ?value)] |- _ =>
        rewrite (zesu_signed_zero_extend_64_128 value) in H
    end); first [assumption | bv_solve]].

Class ZesuStepRegisterCollectionSelection : Prop := {}.

Ltac zesu_register_collection_index r f regs :=
  let cells := eval hnf in regs in
  lazymatch cells with
  | (?key, _) :: ?rest =>
      let member := eval cbv in
        (reg_kind_eqb key (KindField r f) || reg_kind_eqb key (KindReg r)) in
      lazymatch member with
      | true => constr:(O)
      | false =>
          let index := zesu_register_collection_index r f rest in
          constr:(S index)
      end
  end.

Ltac zesu_select_register_collection r f hypotheses :=
  lazymatch hypotheses with
  | Esnoc ?rest ?id (reg_col ?regs) =>
      first [
        assert_fails (has_evar regs);
        let index := zesu_register_collection_index r f regs in
        let Hmember := fresh "HregisterMember" in
        assert (Hmember : is_Some
          (list_find_idx_bool
            (fun x => reg_kind_eqb x.1 (KindField r f) ||
                      reg_kind_eqb x.1 (KindReg r)) regs)) by
          (exists index; reflexivity);
        clear Hmember;
        iApply find_in_context_struct_reg_mapsto_col;
        iExists regs;
        notypeclasses refine (tac_find_hyp _ id _ _ _ _ _);
          [li_pm_reflexivity | li_pm_reduce]
      | zesu_select_register_collection r f rest ]
  | Esnoc ?rest _ _ => zesu_select_register_collection r f rest
  end.

(* Plain register lookup requires the complete register key. A field key alone
   does not establish membership for a complete register lookup. *)
Ltac zesu_plain_register_collection_index r regs :=
  let cells := eval hnf in regs in
  lazymatch cells with
  | (?key, _) :: ?rest =>
      let member := eval cbv in (reg_kind_eqb key (KindReg r)) in
      lazymatch member with
      | true => constr:(O)
      | false =>
          let index := zesu_plain_register_collection_index r rest in
          constr:(S index)
      end
  end.

Ltac zesu_select_plain_register_collection r hypotheses :=
  lazymatch hypotheses with
  | Esnoc ?rest ?id (reg_col ?regs) =>
      first [
        assert_fails (has_evar regs);
        let index := zesu_plain_register_collection_index r regs in
        let Hmember := fresh "HregisterMember" in
        assert (Hmember : is_Some
          (list_find_idx_bool (fun x => reg_kind_eqb x.1 (KindReg r)) regs)) by
          (exists index; reflexivity);
        clear Hmember;
        iApply find_in_context_reg_mapsto_col;
        iExists regs;
        notypeclasses refine (tac_find_hyp _ id _ _ _ _ _);
          [li_pm_reflexivity | li_pm_reduce]
      | zesu_select_plain_register_collection r rest ]
  | Esnoc ?rest _ _ => zesu_select_plain_register_collection r rest
  end.

Lemma zesu_register_shape_collection `{!islaG Sigma} `{!threadG} register shape :
  (∃ value : valu, ⌜valu_has_shape value shape⌝ ∗ register ↦ᵣ value)%I -∗
  reg_col [(KindReg register, shape)].
Proof.
  rewrite reg_col_cons reg_col_nil. iIntros "Hregister". iFrame.
Qed.

Lemma zesu_register_exact_collection `{!islaG Sigma} `{!threadG} register value :
  (register ↦ᵣ value)%I -∗ reg_col [(KindReg register, ExactShape value)].
Proof.
  rewrite reg_col_cons reg_col_nil. iIntros "Hregister".
  iSplitL; [iExists value; iFrame; done | done].
Qed.

(* Restore an owned collection cell after search exposes its existential. *)
Ltac zesu_restore_register_collection r f :=
  iMatchHyp ltac:(fun H body =>
    lazymatch body with
    | (∃ value : valu, ⌜valu_has_shape value ?shape⌝ ∗ ?register ↦ᵣ value)%I =>
        constr_eq register r;
        assert_fails (has_evar shape);
        let selected := eval cbv in
          (regcol_lookup_field r f [(KindReg r, shape)]) in
        lazymatch selected with
        | Some _ => iDestruct (zesu_register_shape_collection r shape with H) as H
        end
    | (?register ↦ᵣ ?value)%I =>
        constr_eq register r;
        assert_fails (has_evar value);
        let selected := eval cbv in
          (regcol_lookup_field r f [(KindReg r, ExactShape value)]) in
        lazymatch selected with
        | Some _ => iDestruct (zesu_register_exact_collection r value with H) as H
        end
    end).

(* Restore a complete register cell before plain register lookup. *)
Ltac zesu_restore_plain_register_collection r :=
  iMatchHyp ltac:(fun H body =>
    lazymatch body with
    | (∃ value : valu, ⌜valu_has_shape value ?shape⌝ ∗ ?register ↦ᵣ value)%I =>
        constr_eq register r;
        assert_fails (has_evar shape);
        iDestruct (zesu_register_shape_collection r shape with H) as H
    end).

Ltac zesu_register_collection_selection_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepRegisterCollectionSelection);
  lazymatch goal with
  | |- envs_entails (Envs ?persistent ?spatial _)
      (find_in_context (FindStructRegMapsTo ?r ?f) _) =>
      first [zesu_select_register_collection r f spatial |
             zesu_select_register_collection r f persistent |
             zesu_restore_register_collection r f;
             zesu_register_collection_selection_if_enabled]
  | |- envs_entails (Envs ?persistent ?spatial _)
      (find_in_context (FindRegMapsTo ?r) _) =>
      first [zesu_select_plain_register_collection r spatial |
             zesu_select_plain_register_collection r persistent |
             zesu_restore_plain_register_collection r;
             zesu_register_collection_selection_if_enabled]
  | Hlocal := (Envs _ _ _) |-
      envs_entails ?environment (find_in_context (FindStructRegMapsTo _ _) _) =>
      constr_eq environment Hlocal;
      unfold Hlocal; zesu_register_collection_selection_if_enabled
  | Hlocal := (Envs _ _ _) |-
      envs_entails ?environment (find_in_context (FindRegMapsTo _) _) =>
      constr_eq environment Hlocal;
      unfold Hlocal; zesu_register_collection_selection_if_enabled
  end.

Class ZesuStepKnownPairWitness : Prop :=
  zesu_step_known_pair_witness : True.

(* Inspect explicit pure leaves without unfolding spatial predicates. *)
Ltac zesu_known_pair_pure_leaf body continuation :=
  lazymatch body with
  | (fun x => @bi_sep _ (@?left x) (@?right x)) =>
      first [zesu_known_pair_pure_leaf left continuation |
             zesu_known_pair_pure_leaf right continuation]
  | (fun x => @bi_pure _ (@?fact x)) =>
      let rec conjunct fact :=
        lazymatch fact with
        | (fun x => @?left x /\ @?right x) =>
            first [conjunct left | conjunct right]
        | (fun x => ?predicate (li_fst x)) =>
            lazymatch predicate with (fun _ => _) => fail | _ => idtac end;
            assert_fails (has_evar predicate);
            continuation predicate fact
        end in conjunct fact
  end.

Ltac zesu_known_pair_has_evar term :=
  first [has_evar term |
    multimatch goal with
    | local := ?value |- _ =>
        lazymatch term with context[local] =>
          zesu_known_pair_has_evar value
        end
    end].

Ltac zesu_known_pair_context_value A predicate continuation :=
  multimatch goal with
  | H : ?head ?value |- _ =>
      constr_eq head predicate;
      let T := type of value in constr_eq T A;
      assert_fails (zesu_known_pair_has_evar value);
      let owned := type of H in
      assert_fails (zesu_known_pair_has_evar owned);
      continuation value owned
  end.

(* Select an existing value before early unfolding expands its resources. *)
Ltac zesu_known_pair_conjunct_witness_if_enabled :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod ?A unit) ?body) =>
      assert_fails (has_evar A);
      zesu_known_pair_pure_leaf body ltac:(fun predicate fact =>
        zesu_switch_enabled constr:(ZesuStepKnownPairWitness);
        zesu_known_pair_context_value A predicate ltac:(fun value owned =>
          tryif (zesu_known_pair_pure_leaf body ltac:(fun other_predicate _ =>
            zesu_known_pair_context_value A other_predicate ltac:(fun other _ =>
              assert_fails (constr_eq value other))))
          then fail 0 "Different facts select different witness values."
          else
            let witness := constr:(li_pair value tt) in
            let selected := eval cbv beta iota delta [li_fst li_snd] in
              (fact witness) in
            constr_eq selected owned;
            notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod)
      )
  end.

(* An owned pure fact selects the value before resource matching starts. *)
Ltac zesu_known_pair_witness_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepKnownPairWitness);
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

Class ZesuStepEvarSideconditionGuard : Prop :=
  zesu_step_evar_sidecondition_guard : True.

(* Refuse unresolved pure side conditions before arithmetic search. *)
Ltac zesu_condition_has_unresolved_evar condition :=
  first [ has_evar condition
        | multimatch goal with
          | local := ?body : _ |- _ =>
              lazymatch condition with
              | context[local] => zesu_condition_has_unresolved_evar body
              end
          end ].


Ltac zesu_defer_unresolved_sidecondition_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepEvarSideconditionGuard);
  lazymatch goal with
  | |- envs_entails _ _ => fail 0
  | |- @bi_entails _ _ _ => fail 0
  | |- ?condition =>
      let sort := type of condition in
      constr_eq sort Prop;
      zesu_condition_has_unresolved_evar condition
  end.

Class ZesuStepEvarImplicationGuard : Prop :=
  zesu_step_evar_implication_guard : True.

(* Keep unresolved implication premises out of typeclass simplification. *)
Ltac zesu_defer_unresolved_implication_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepEvarImplicationGuard);
  lazymatch goal with
  | |- ?premise -> _ =>
      let sort := type of premise in
      constr_eq sort Prop;
      zesu_condition_has_unresolved_evar premise
  end.

Ltac liImpl ::=
  tryif zesu_defer_unresolved_implication_if_enabled
  then fail 0 "unresolved implication premise"
  else normalize_and_simpl_impl false.

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
  zesu_switch_enabled constr:(ZesuStepPureWitnessConstraints);
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


Ltac zesu_conjunct_head_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepConjunctMatch);
  lazymatch goal with
  | _ : @ZesuEntryIntroApplied _ _ _ _,
    _ : ZesuEntryIntroHeads _ |- _ => idtac
  end;
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ _ _) =>
      let introFuel := constr:(12%nat) in
      zesu_witness_open_existentials introFuel
  | |- envs_entails _ _ => idtac
  end;
  lazymatch goal with
  | |- envs_entails _ ?requested =>
      let unfoldFuel := constr:(4%nat) in
      progress (zesu_match_resource_pure_heads
        ltac:(fun premise => zesu_registered_pure_fact premise)
        unfoldFuel requested)
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
  zesu_switch_enabled constr:(ZesuStepRecordWitness);
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
  | zesu_register_collection_selection_if_enabled
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
  | zesu_register_collection_selection_if_enabled
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
  zesu_switch_enabled constr:(ZesuStepSignedAddress);
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
  zesu_switch_enabled constr:(ZesuStepRamFault);
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

Class ZesuStepRegionFaultNormalization : Prop :=
  zesu_step_region_fault_normalization : True.

(* Recognize constructor integers without unfolding local declarations. *)
Ltac zesu_region_positive_literal p :=
  tryif is_var p then fail 0 else
  lazymatch p with
  | xH => idtac
  | xO ?q => zesu_region_positive_literal q
  | xI ?q => zesu_region_positive_literal q
  | _ => fail 0
  end.
Ltac zesu_region_integer_literal value :=
  tryif is_var value then fail 0 else
  lazymatch value with
  | Z0 => idtac
  | Zpos ?p => zesu_region_positive_literal p
  | Zneg ?p => zesu_region_positive_literal p
  | _ => fail 0
  end.

(* Check the selected term without traversing other local declarations. *)
Ltac zesu_region_reduce_closed term :=
  tryif zesu_switch_enabled constr:(ZesuStepRegionFaultNormalization)
  then (
    tryif zesu_region_integer_literal term then fail 0 else (
      zesu_stack_closed_term term;
      let reduced := eval vm_compute in term in
      tryif constr_eq term reduced then fail 0
      else change_no_check term with reduced in * ))
  else reduce_closed term.

Class ZesuStepRegionFaultCastHypotheses : Prop := {}.

(* Normalize retained unsigned conversions without unfolding local definitions. *)
Ltac zesu_region_fault_cast_hypotheses_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepRegionFaultCastHypotheses);
  lazymatch goal with
  | |- ?statement => zesu_region_arithmetic_statement statement
  end;
  progress (repeat match goal with
  | Hcast : context[@bv_unsigned ?width (Z_to_bv ?castWidth ?value)] |- _ =>
      constr_eq width castWidth;
      let statement := type of Hcast in
      lazymatch type of statement with Prop => idtac end;
      zesu_region_arithmetic_statement statement;
      assert_fails (zesu_condition_has_unresolved_evar statement);
      assert_fails (zesu_condition_has_unresolved_evar width);
      assert_fails (zesu_condition_has_unresolved_evar value);
      progress (rewrite (Z_to_bv_unsigned width value) in Hcast)
  end).

Ltac zesu_region_fault_prepare :=
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
  | H : context[?term] |- _ =>
      lazymatch type of term with Z => progress (zesu_region_reduce_closed term) end
  | |- context[?term] =>
      lazymatch type of term with Z => progress (zesu_region_reduce_closed term) end
  end;
  try (rewrite zesu_signed_zero_extend_add_64_128; last bv_solve);
  repeat match goal with
  | H : context[bv_signed (bv_zero_extend 128 ?value)] |- _ =>
      rewrite (zesu_signed_zero_extend_64_128 value) in H
  end;
  rewrite ?zesu_signed_zero_extend_64_128;
  try zesu_region_fault_cast_hypotheses_if_enabled;
  repeat match goal with
  | H : ?left \/ ?right |- _ =>
      zesu_region_arithmetic_statement left;
      zesu_region_arithmetic_statement right;
      destruct H;
      repeat match goal with Hpair : _ /\ _ |- _ => destruct Hpair end
  end.

Ltac zesu_region_fault_arithmetic_full :=
  zesu_region_fault_prepare;
  first [bv_solve |
    match goal with Hnegative : ~ ?bound |- _ =>
      zesu_region_arithmetic_statement bound;
      exfalso; apply Hnegative; bv_solve
    end].

Ltac zesu_region_fault_arithmetic :=
  first [solve [assumption] | zesu_region_fault_arithmetic_full].

Ltac zesu_region_fault_bound_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepRegionFault);
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

(* The late fault path retains the readable-region alternatives. *)
Ltac zesu_region_fault_word_casts :=
  repeat first [
    match goal with
    | Hcast : context[@bv_add ?width ?value ?amount] |- _ =>
      let zero := constr:((0%bv : bv width)) in
      constr_eq amount zero;
      progress (rewrite (bv_add_0_r value zero ltac:(bv_solve)) in Hcast)
    | |- context[@bv_add ?width ?value ?amount] =>
      let zero := constr:((0%bv : bv width)) in
      constr_eq amount zero;
      progress (rewrite (bv_add_0_r value zero ltac:(bv_solve)))
    end |
    match goal with
    | Hcast : context[@bv_unsigned ?width (Z_to_bv ?castWidth ?value)] |- _ =>
      constr_eq width castWidth;
      zesu_stack_closed_term width;
      assert_fails (zesu_condition_has_unresolved_evar value);
      let modulus := eval vm_compute in (bv_modulus width) in
      let Hbound := fresh "HregionCastRange" in
      assert (Hbound : (0 <= value < bv_modulus width)%Z) by
        (change (0 <= value < modulus)%Z; lia);
      progress (rewrite (Z_to_bv_small width value Hbound) in Hcast);
      clear Hbound
    | |- context[@bv_unsigned ?width (Z_to_bv ?castWidth ?value)] =>
      constr_eq width castWidth;
      zesu_stack_closed_term width;
      assert_fails (zesu_condition_has_unresolved_evar value);
      let modulus := eval vm_compute in (bv_modulus width) in
      let Hbound := fresh "HregionCastRange" in
      assert (Hbound : (0 <= value < bv_modulus width)%Z) by
        (change (0 <= value < modulus)%Z; lia);
      progress (rewrite (Z_to_bv_small width value Hbound));
      clear Hbound
    end].

Ltac zesu_region_fault_late_arithmetic :=
  zesu_region_fault_prepare;
  zesu_region_fault_word_casts;
  repeat match goal with
  | H : context[?term] |- _ =>
      lazymatch type of term with Z => progress (zesu_region_reduce_closed term) end
  | |- context[?term] =>
      lazymatch type of term with Z => progress (zesu_region_reduce_closed term) end
  end;
  first [lia | bv_solve].

Ltac zesu_region_fault_array_address address :=
  let address_value := lazymatch address with
    (?cursor + 0)%Z => constr:(cursor) | _ => constr:(address) end in
  match goal with Hfault : ~ ?bound |- _ =>
    lazymatch bound with context[bv_zero_extend 128 ?word] =>
      let word_value := lazymatch word with
        (?cursor + 0)%bv => constr:(cursor) | _ => constr:(word) end in
      lazymatch word_value with Z_to_bv 64 ?cursor =>
        constr_eq address_value cursor
      end
    end
  end.

Ltac zesu_region_fault_readable_array_context :=
  match goal with
  | Hlookup : ?storage !! ?index = Some ?value |- _ =>
    let value_type := type of value in
    constr_eq value_type (bv 8);
    assert_fails (has_evar storage);
    first [
      match goal with
      | Hrange : (?base <= ?address < ?base + Z.of_nat (length storage) * ?stride)%Z,
        Hreadable : ((?low0 <= ?base /\ ?base + ?extent <= ?high0) \/
                     (?low1 <= ?base /\ ?base + ?extent <= ?high1))%Z |- _ =>
        first [constr_eq stride 1%Z |
          constr_eq stride (Z.of_N (8 `div` 8))];
        zesu_region_fault_array_address address
      end |
      match goal with
      | Hrange : (?base <= ?address < ?base + Z.of_nat (length storage))%Z,
        Hreadable : ((?low0 <= ?base /\ ?base + ?extent <= ?high0) \/
                     (?low1 <= ?base /\ ?base + ?extent <= ?high1))%Z |- _ =>
        zesu_region_fault_array_address address
      end]
  end.

Ltac zesu_region_fault_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepRegionFault);
  first [
    lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _
      (WPasm (Smt (Assert (Unop Not _ _)) _ :t: _)) => idtac
  | |- iris.proofmode.environments.envs_entails _
      ((WPasm (Smt (Assert (Unop Not _ _)) _ :t: _)) ∧ True)%I => idtac
  end;
    solve [zesu_region_fault_assert] |
    lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _
      (WPasm (Smt (Assert (Unop Not _ _)) _ :t: _)) => idtac
  | |- iris.proofmode.environments.envs_entails _
      ((WPasm (Smt (Assert (Unop Not _ _)) _ :t: _)) ∧ True)%I => idtac
  end;
    solve [lazymatch goal with
      | |- envs_entails _ ((WPasm _) ∧ True)%I =>
          iSplit; [zesu_region_fault_assert | done]
      end] |
    lazymatch goal with
    | |- False => idtac
    | |- envs_entails _ (find_in_context (FindRegMapsTo "medeleg") _) => idtac
    end;
    unLET;
    zesu_region_fault_readable_array_context;
    match goal with
    | Hfault : ~ ?bound |- _ =>
      zesu_region_arithmetic_statement bound;
      lazymatch bound with context[bv_zero_extend 128 _] => idtac end;
      solve [exfalso; apply Hfault; zesu_region_fault_late_arithmetic]
    end].

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
  zesu_switch_enabled constr:(ZesuStepWordArrayHandoff);
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
  zesu_switch_enabled constr:(ZesuStepWordArrayHandoff);
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
  zesu_switch_enabled constr:(ZesuStepWordArrayHandoff);
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
  zesu_switch_enabled constr:(ZesuStepWordArrayHandoff);
  lazymatch goal with
  | |- envs_entails _ (subsume _ _ _) =>
      progress zesu_saturate_derived_facts
  end.

Ltac zesu_handoff_integer_equality_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepWordArrayHandoff);
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
  ZesuSsz.Automation.PureFacts.zesu_integer_array_emit_facts proof.

Ltac zesu_integer_array_facts :=
  ZesuSsz.Automation.PureFacts.zesu_integer_array_facts.

Class ZesuStepArrayBounds : Prop :=
  zesu_step_array_bounds : True.

Class ZesuStepByteListContainment : Prop := {}.

(* Rewrite one retained list equality before the containment solver.
   Syntactic endpoint matching must not determine unresolved native data. *)
Ltac zesu_byte_list_containment_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepByteListContainment);
  lazymatch goal with
  | |- envs_entails _ _ => fail 0
  | _ => idtac
  end;
  match goal with
  | H : ?statement |- context [length ?values] =>
      let valuesType := type of values in
      constr_eq valuesType (list (bv 8));
      assert_fails (has_evar values);
      assert_fails (has_evar statement);
      assert_fails (has_evar H);
      let expanded := eval hnf in statement in
      lazymatch expanded with
      | @eq (list (bv 8)) ?left ?right =>
          first [
            constr_eq values left;
            assert_fails (constr_eq left right);
            let replacement := eval hnf in right in
            lazymatch replacement with _ :: _ => idtac end;
            progress (rewrite H;
              change (length right) with (length replacement);
              cbn [length])
          | constr_eq values right;
            assert_fails (constr_eq left right);
            let replacement := eval hnf in left in
            lazymatch replacement with _ :: _ => idtac end;
            progress (rewrite <- H;
              change (length left) with (length replacement);
              cbn [length])]
      end
  end.

(* Convert an integer address only from its owned no-wrap facts. *)
Ltac zesu_array_bound_integer_casts :=
  repeat match goal with
  | |- context[bv_unsigned (Z_to_bv 64 ?pointer)] =>
      let Hcast := fresh "HarrayBoundCast" in
      assert (Hcast : bv_unsigned (Z_to_bv 64 pointer) = pointer)
        by zesu_stack_arithmetic;
      rewrite Hcast; clear Hcast
  end.

(* Resolve only an already-selected array resource. The existing region rule
   proves containment or base equality and determines the memory kind. *)
Ltac zesu_array_region_selection_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepArrayRegionBounds);
  lazymatch goal with
  | |- FindHypEqual (ZesuMemRegionSearch _) (_ ↦ₘ∗ _)
      (mem_mapsto_kind_prop _ ?kind) _ =>
      try (is_var kind;
        lazymatch goal with
        | kind := _ : mem_mapsto_kind |- _ => unfold kind
        end);
      solve [apply find_mem_region_array;
        first [right; zesu_array_bound_integer_casts; lia |
               zesu_region_bounds]]
  end.

Ltac zesu_array_bounds_base :=
  zesu_switch_enabled constr:(ZesuStepArrayBounds);
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
  | |- (?index < length ?storage)%nat =>
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

Ltac zesu_array_bounds_extended :=
  zesu_switch_enabled constr:(ZesuStepArrayBounds);
  lazymatch goal with
  | |- SHELVED_SIDECOND _ => unshelve_sidecond
  | _ => idtac
  end;
  unLET;
  lazymatch goal with
  | |- 0 <= ?address - ?base =>
      solve [try autounfold with zesu_contract_constants in *;
        zesu_integer_array_facts; bv_solve | lia]
  | |- (?index + ?width <= length ?storage)%nat =>
      solve [
        try autounfold with zesu_contract_constants in *;
        zesu_integer_array_facts;
        zesu_array_bound_integer_casts;
        repeat match goal with
        | |- context [?base + ?offset - ?base] =>
            replace (base + offset - base) with offset by lia
        | |- context [?base - ?base] =>
            replace (base - base) with 0 by lia
        end;
        repeat progress (rewrite ?length_app ?length_take ?length_drop ?length_insert;
          cbn [length N.to_nat]); lia]
  | |- (?index < length ?storage)%nat =>
      solve [
        try autounfold with zesu_contract_constants in *;
        zesu_integer_array_facts;
        zesu_array_bound_integer_casts;
        repeat match goal with
        | |- context [?base + ?offset - ?base] =>
            replace (base + offset - base) with offset by lia
        | |- context [?base - ?base] =>
            replace (base - base) with 0 by lia
        end;
        repeat progress (rewrite ?length_app ?length_take ?length_drop ?length_insert;
          cbn [length N.to_nat]); lia]
  end.

Ltac zesu_array_bounds_if_enabled :=
  first [zesu_array_bounds_base | zesu_array_bounds_extended].

Ltac zesu_integer_array_address_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepIntegerArrayAddress);
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
                    zesu_switch_enabled constr:(ZesuStepArrayRegionBounds);
                    zesu_array_bound_integer_casts;
                    try zesu_byte_list_containment_if_enabled;
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
