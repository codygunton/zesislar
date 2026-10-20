Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.Rewrites.
Require Import isla.riscv64.riscv64.

Class ZesuStepArrayRegionBounds : Prop :=
  zesu_step_array_region_bounds : True.

(* Preserve ownership while reducing the extent of an updated byte array. *)
Ltac zesu_byte_array_bound_goal_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepArrayRegionBounds);
  lazymatch goal with
  | |- context [length ?values] =>
      let valuesType := type of values in
      constr_eq valuesType (list (bv 8))
  end.

Ltac zesu_byte_array_lengths_base :=
  zesu_byte_array_bound_goal_if_enabled;
  repeat match goal with
  | |- context [?base + ?offset - ?base] =>
      replace (base + offset - base) with offset by lia
  | |- context [?base - ?base] =>
      replace (base - base) with 0 by lia
  end;
  repeat progress (rewrite ?length_app ?length_take ?length_drop; cbn [length]).

Ltac zesu_byte_array_lengths_extended :=
  zesu_byte_array_bound_goal_if_enabled;
  try autounfold with zesu_contract_constants in *;
  repeat match goal with
  | |- context [?base + ?offset - ?base] =>
      replace (base + offset - base) with offset by lia
  | |- context [?base - ?base] =>
      replace (base - base) with 0 by lia
  end;
  repeat progress (rewrite ?length_app ?length_take ?length_drop ?length_insert;
    cbn [length N.to_nat]).


Ltac zesu_byte_array_lengths_if_enabled :=
  first [solve [zesu_byte_array_lengths_base; solve [lia | bv_solve]] |
    zesu_byte_array_lengths_extended].
