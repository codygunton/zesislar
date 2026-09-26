(* Open only the resources introduced by this return wand. *)
Require Import isla.isla.
Require Import ZesuSsz.Automation.PureFacts.
From iris.proofmode Require Import environments intro_patterns.

Class ZesuStepReturnBundle : Prop := zesu_step_return_bundle : True.

Ltac zesu_open_return_bundle H :=
  lazymatch iTypeOf H with
  | Some (_, ?body) =>
      first
        [ lazymatch body with
          | (_ ∗ _)%I =>
              let left := iFresh in
              let right := iFresh in
              let pattern := constr:(IList [[IIdent left; IIdent right]]) in
              iDestruct H as pattern;
              try zesu_open_return_bundle left;
              try zesu_open_return_bundle right
          end
        | let head := get_head body in
          let _ := constr:(_ : LithiumUnfold head) in
          iEval (progress unfold head; cbv beta zeta) in H;
          zesu_open_return_bundle H ]
  end.

Ltac zesu_enter_return_bundle_if_enabled :=
  let _ := constr:(_ : ZesuStepReturnBundle) in
  lazymatch goal with
  | |- envs_entails _ ((_ -∗ _) ∗ True)%I =>
      iSplit; [let H := iFresh in iIntros H; zesu_open_return_bundle H | done]
  end.
