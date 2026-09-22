(* The continuation a returning call leaves.

   Islaris turns the raw instruction at a call's return address into the
   `instr_pre` the callee's contract wants -- `subsume_instr_some_pre`
   does it -- and hands back the obligation

     (callee_return … -∗ "PC" ↦ᵣ … -∗ WPasm rest) ∗ True

   which says: given what the callee returns and the program counter,
   keep running. Every hand proof of a segment that calls out writes the
   same three tokens for it,

     iSplit; last done. iIntros "Hreturn HPC".

   and then carries on. The corpus has that line in every proof that
   makes a call.

   Nothing about it is a choice, so it is a rule. The `True` on the
   right is Lithium's frame and `done` closes it; the two introductions
   name nothing, because the C3 tier opens the returned bundle later, on
   demand, when a lookup needs what is inside it. *)

Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.isla.
From iris.proofmode Require Import environments.

Ltac zesu_enter_call_return :=
  lazymatch goal with
  | |- envs_entails _ ((_ -∗ _ -∗ WPasm _) ∗ True)%I =>
      iSplit; [iIntros "?"; iIntros "?" | done]
  | |- envs_entails _ ((_ -∗ WPasm _) ∗ True)%I =>
      iSplit; [iIntros "?" | done]
  end.

(* The switch for this one rule. `Automation/Switch.v` provides it
   with every other v2 step; `Automation/Switches/…` provides it
   alone, which is how one benchmark arm measures one rule. *)
Class ZesuStepCallReturn : Prop := zesu_step_call_return : True.

Ltac zesu_step_call_return_on :=
  let _ := constr:(_ : ZesuStepCallReturn) in idtac.

Ltac zesu_enter_call_return_if_enabled :=
  zesu_step_call_return_on; zesu_enter_call_return.
