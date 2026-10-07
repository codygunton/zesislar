Require Import ZesuSsz.Automation.SwitchDispatch.
(* Enter the continuation left by a returning call, regardless of its head. *)

Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.isla.
From iris.proofmode Require Import environments.

Class ZesuStepReturnWand : Prop := zesu_step_return_wand : True.

Ltac zesu_enter_return_wand_if_enabled :=
  zesu_switch_enabled constr:(ZesuStepReturnWand);
  lazymatch goal with
  | |- envs_entails _ ((_ -∗ _) ∗ True)%I =>
      iSplit; [iIntros "?" | done]
  end.
