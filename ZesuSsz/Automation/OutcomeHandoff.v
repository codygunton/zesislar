(* An opt-in C1 handoff with a list witness fixed by its validity fact.
   The outcome equality must concern that same list. *)

Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.isla.
From iris.proofmode Require Import environments.

Class ZesuStepOutcomeHandoff : Prop := zesu_step_outcome_handoff : True.

Ltac zesu_outcome_handoff :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec (li_prod ?T unit)) _) =>
      match goal with
      | Hvalid : ?valid ?bytes |- _ =>
          match goal with
          | Houtcome : ?outcome bytes = ?result |- _ =>
              iExists (_, bytes, tt)ₗ;
              iSplit; [iPureIntro; exact Hvalid |];
              rewrite Houtcome
          end
      end
  end.

Ltac zesu_outcome_handoff_if_enabled :=
  let _ := constr:(_ : ZesuStepOutcomeHandoff) in
  zesu_outcome_handoff.
