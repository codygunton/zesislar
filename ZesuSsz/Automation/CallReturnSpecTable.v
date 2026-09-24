(* Enter a returning call's continuation when the next instruction uses
   the load specification from the instruction table. This rule is opt-in. *)

Require Import ZesuSsz.Automation.PureFacts.
Require Import InstrSpecs.Specs.
Require Import isla.isla.
From iris.proofmode Require Import environments.

Class ZesuStepCallReturnSpecTable : Prop :=
  zesu_step_call_return_spec_table : True.

Ltac zesu_enter_call_return_spec_table :=
  lazymatch goal with
  | |- envs_entails _ ((_ -∗ zesu_ld_spec _ _ _ _) ∗ True)%I =>
      iSplit; [iIntros "?" | done]
  end.

Ltac zesu_enter_call_return_spec_table_if_enabled :=
  let _ := constr:(_ : ZesuStepCallReturnSpecTable) in
  zesu_enter_call_return_spec_table.
