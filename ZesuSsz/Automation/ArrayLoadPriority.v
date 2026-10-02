(* Select the raw load trace when its source is an owned initialized array.
   A failed guard backtracks before instruction selection. *)
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.BoundedArithmetic.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import InstrSpecs.Lookup InstrSpecs.Specs.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.

Class ZesuStepArrayLoadPriority : Prop := zesu_step_array_load_priority : True.

Ltac zesu_array_load_lookup_resource body :=
  lazymatch body with
  | instr_body_lookup_resources ?table => constr:(Some table)
  | instr_lookup_resources ?lookup => constr:((false, lookup))
  | _ =>
      let head := get_head body in
      let unfolded := eval unfold head in body in
      lazymatch unfolded with
      | instr_body_lookup_resources ?table => constr:(Some table)
      | instr_lookup_resources ?lookup => constr:((false, lookup))
      | _ => constr:(false)
      end
  end.

Ltac zesu_array_load_table address persistent :=
  lazymatch persistent with
  | Esnoc ?rest _ ?resource =>
      let wrapped := zesu_array_load_lookup_resource resource in
      lazymatch wrapped with
      | Some ?table =>
          let body := eval hnf in (table address) in
          lazymatch body with
          | Some (zesu_ld_spec _ _ ?baseRegister ?offset) =>
              constr:((baseRegister, offset, 8%Z))
          | Some (zesu_lbu_byte_array_at_spec _ _ ?baseRegister ?offset _ _) =>
              constr:((baseRegister, offset, 1%Z))
          | _ => zesu_array_load_table address rest
          end
      | _ => zesu_array_load_table address rest
      end
  end.

Ltac zesu_array_load_code persistent :=
  lazymatch persistent with
  | Esnoc ?rest _ ?resource =>
      let wrapped := zesu_array_load_lookup_resource resource in
      lazymatch wrapped with
      | (false, ?lookup) => constr:(lookup)
      | _ => zesu_array_load_code rest
      end
  end.

Ltac zesu_array_load_register register spatial :=
  lazymatch spatial with
  | Esnoc ?rest _ (?actual ↦ᵣ RVal_Bits (bv_to_bvn ?value))%I =>
      let equation := constr:(actual = register) in
      lazymatch equation with
      | ?same = ?same => constr:(value)
      | _ => zesu_array_load_register register rest
      end
  | Esnoc ?rest _ _ => zesu_array_load_register register rest
  end.

Ltac zesu_array_load_contains address width spatial :=
  lazymatch spatial with
  | Esnoc ?rest _ (@mem_mapsto_array _ _ ?bits ?start ?fraction ?values) =>
      let stride := eval vm_compute in (Z.of_N (bits / 8)) in
      first [let Hrange := fresh "HarrayLoadRange" in
             assert (Hrange : (start <= address /\
               address + width <= start + Z.of_nat (length values) * stride)%Z)
               by (autorewrite with lithium_rewrite;
                   first [cbn; zesu_finish_lia
                         | zesu_bounded_arithmetic ltac:(zesu_witness_arith)]);
             clear Hrange
            | zesu_array_load_contains address width rest]
  | Esnoc ?rest _ _ => zesu_array_load_contains address width rest
  end.

Ltac zesu_array_load_find_owned address width :=
  first [lazymatch goal with
         | |- envs_entails ?Delta _ =>
             let spatial := eval cbn [env_spatial] in (env_spatial Delta) in
             zesu_array_load_contains address width spatial
         end
        | zesu_open_sealed_covering address;
          repeat iDestruct select (_ ∗ _)%I as "[? ?]";
          zesu_array_load_find_owned address width].

Ltac zesu_array_load_select :=
  lazymatch goal with
  | |- envs_entails ?Delta (find_in_context (FindInstrKind ?address ?later) _) =>
      let _ := constr:(_ : ZesuStepArrayLoadPriority) in
      zesu_expose_environment_alias;
      lazymatch goal with
      | |- envs_entails ?Delta _ =>
      let persistent := eval cbn [env_intuitionistic] in (env_intuitionistic Delta) in
      let load := zesu_array_load_table address persistent in
      lazymatch load with (?register, ?offset, ?width) =>
      let lookup := zesu_array_load_code persistent in
      iApply (find_in_context_instr_lookup_resources address later);
      iExists lookup; iSplit; [iAssumption |];
      iSplit; [iPureIntro; solve [vm_compute; eauto] |];
      let resolved := eval hnf in (lookup address) in
      change (lookup address) with resolved; cbn beta iota zeta;
      lazymatch goal with
      | |- envs_entails _ (_ -∗ _)%I =>
          repeat first
            [liUnfoldEarly
            | lazymatch goal with
              | |- envs_entails _ (_ -∗ _)%I => iIntros "?"
              end
            | liStep | liLetBindHint | liUnfoldLate];
          repeat first
            [progress (repeat iDestruct select (_ ∗ _)%I as "[? ?]")
            | zesu_open_transparent_bundle_with_register register]
      | _ => idtac
      end;
      lazymatch goal with
      | |- envs_entails ?After _ =>
          let spatial := eval cbn [env_spatial] in (env_spatial After) in
          let base := zesu_array_load_register register spatial in
          repeat iDestruct select (⌜_⌝)%I as %?;
          zesu_array_load_find_owned (bv_unsigned base + offset)%Z width
      end
      end
      end
  end.

(* These reductions are opt-in v2 steps. They preserve the owned arrays. *)
Class ZesuStepWordArrayLookup : Prop := zesu_step_word_array_lookup : True.

Ltac zesu_normalize_word_array_lookup :=
  match goal with
  | Hlookup : ?values !! Z.to_nat
      ((bv_unsigned (bv_add ?sp ?offset) - (bv_unsigned ?sp + ?start))
        `div` ?stride) = Some ?loaded |- _ =>
      let integer := eval vm_compute in (bv_unsigned offset) in
      let origin := eval vm_compute in start in
      let width := eval vm_compute in stride in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac end;
      lazymatch origin with Z0 => idtac | Zpos _ => idtac end;
      lazymatch width with Zpos _ => idtac end;
      let index := eval vm_compute in (Z.to_nat ((integer - origin) `div` width)) in
      let Hsum := fresh "HwordArrayAddress" in
      assert (Hsum : bv_unsigned (bv_add sp offset) =
        (bv_unsigned sp + integer)%Z) by
        (try zesu_witness_facts;
         cbv [machineRamEnd mapRamSize mapRamBase defaultMap] in *;
         bv_solve);
      let Hindex := fresh "HwordArrayIndex" in
      assert (Hindex : Z.to_nat
        ((bv_unsigned (bv_add sp offset) - (bv_unsigned sp + start))
          `div` stride) = index) by
        (rewrite Hsum; f_equal; f_equal; lia);
      rewrite Hindex in Hlookup; clear Hsum Hindex;
      rewrite ?lookup_cons ?lookup_nil in Hlookup;
      lazymatch type of Hlookup with
      | Some ?expected = Some ?actual =>
          is_var actual;
          let Hvalue := fresh "HwordArrayValue" in
          injection Hlookup as Hvalue; subst actual
      | _ => idtac
      end
  end.

Ltac zesu_word_array_lookup_if_enabled :=
  let _ := constr:(_ : ZesuStepWordArrayLookup) in
  zesu_normalize_word_array_lookup.


Ltac zesu_array_region_metadata_if_enabled :=
  let _ := constr:(_ : ZesuStepArrayLoadPriority) in
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo _) _) =>
      lazymatch goal with
      | |- context[array_region_start 64 ?base ?base] =>
          progress (autorewrite with lithium_rewrite)
      end
  | |- envs_entails _ _ => fail 0
  | |- context[array_region_start 64 ?base ?base] =>
      progress (autorewrite with lithium_rewrite)
  end.


Ltac zesu_array_load_priority :=
  first [zesu_word_array_lookup_if_enabled |
    zesu_array_region_metadata_if_enabled | zesu_array_load_select].
