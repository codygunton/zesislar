(* Enter a returning call only when its continuation is in the spec table. *)

Require Import isla.isla.
From iris.proofmode Require Import environments.

Class ZesuStepCallReturnSpec : Prop := zesu_step_call_return_spec : True.
Class ZesuReturnTableEntry {Sigma} (pc : Z) (body : iProp Sigma) : Prop :=
  zesu_return_table_entry : True.

Ltac zesu_enter_call_return_spec_if_enabled :=
  lazymatch goal with
  | |- envs_entails _ ((_ -∗ ?continuation) ∗ True)%I =>
      let _ := constr:(_ : ZesuStepCallReturnSpec) in
      lazymatch continuation with
      | ?head ?pc ?arg1 ?arg2 ?arg3 =>
          let _ := constr:(_ : ZesuReturnTableEntry pc continuation) in
          iSplit; [iIntros "?" | done]
      end
  end.
