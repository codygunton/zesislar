Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.ResourceGroups.
From iris.proofmode Require Import environments.
Import ListNotations.
Open Scope Z_scope.

(* Choose a raw array witness from one exact adjacent pair. *)
Ltac zesu_raw_array_check_word value :=
  assert_fails (has_evar value);
  let T := type of value in
  lazymatch T with bv ?width =>
    zesu_stack_closed_term width;
    let count := eval vm_compute in (N.div width 8) in
    let aligned := eval vm_compute in (N.eqb (N.modulo width 8) 0) in
    constr_eq aligned true;
    tryif constr_eq count 0%N then fail 0 else idtac
  end.

Ltac zesu_raw_array_word_bytes value :=
  let T := type of value in
  lazymatch T with bv ?width =>
    let count := eval vm_compute in (N.div width 8) in
    constr:(bv_to_little_endian (N.to_nat count) 8 (bv_unsigned value))
  end.

Ltac zesu_raw_array_pair_high low_name low_base low_value spatial accumulated continuation :=
  let T := type of low_value in
  lazymatch T with bv ?width =>
    let count := eval vm_compute in (N.div width 8) in
    let rec scan remaining pairs :=
      lazymatch remaining with
      | Enil => continuation pairs
      | Esnoc ?previous ?name ?body =>
        tryif (
          lazymatch body with
          | (?high_base ↦ₘ ?high_value)%I =>
            assert_fails (constr_eq low_name name);
            assert_fails (has_evar high_base);
            zesu_raw_array_check_word high_value;
            let adjacent := constr:((ltac:(lia) : high_base = (low_base + Z.of_N count)%Z)) in
            assert_fails (has_evar adjacent)
          end)
        then scan previous constr:((low_name,name) :: pairs)
        else scan previous pairs
      end in scan spatial accumulated
  end.

Ltac zesu_raw_array_pair_candidates requested spatial continuation :=
  let rec scan remaining pairs :=
    lazymatch remaining with
    | Enil => continuation pairs
    | Esnoc ?previous ?name ?body =>
      tryif (
        lazymatch body with
        | (?low_base ↦ₘ ?low_value)%I =>
          constr_eq low_base requested;
          assert_fails (has_evar low_base);
          zesu_raw_array_check_word low_value
        end)
      then lazymatch body with
        | (?low_base ↦ₘ ?low_value)%I =>
          zesu_raw_array_pair_high name low_base low_value spatial pairs
            ltac:(fun updated => scan previous updated)
        end
      else scan previous pairs
    end in scan spatial constr:(@nil (ident * ident)).

Ltac zesu_raw_array_witness_at requested bytes :=
  is_evar bytes;
  assert_fails (has_evar requested);
  lazymatch goal with
  | |- envs_entails (Envs _ ?spatial _) _ =>
    zesu_raw_array_pair_candidates requested spatial ltac:(fun pairs =>
      lazymatch pairs with
      | (?low_name,?high_name) :: nil =>
        lazymatch iTypeOf low_name with
        | Some (false, (_ ↦ₘ ?low_value)%I) =>
          lazymatch iTypeOf high_name with
          | Some (false, (_ ↦ₘ ?high_value)%I) =>
            let low_bytes := zesu_raw_array_word_bytes low_value in
            let high_bytes := zesu_raw_array_word_bytes high_value in
            let chosen := constr:(low_bytes ++ high_bytes) in
            unify bytes chosen
          end
        end
      | _ => fail 0 "The requested base has no unique adjacent word pair."
      end)
  end.

Ltac zesu_raw_array_witness_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepWordArrayHandoff);
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ ((?base ↦ₘ∗ ?bytes) ∗ _)%I =>
      zesu_raw_array_witness_at base bytes
  | |- envs_entails _ (?base ↦ₘ∗ ?bytes)%I =>
      zesu_raw_array_witness_at base bytes
  end.
