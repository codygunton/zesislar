(* C9: the continuation a returning call leaves, whatever it continues to.

   `CallReturn.v` opens `(R -∗ WPasm _) ∗ True`, and `CallReturnSpecTable.v`
   opens `(R -∗ zesu_ld_spec …) ∗ True`. The corpus has the same shape with
   other conclusions: a named caller state such as
   `writeSuccessSuffixAt158f0 P`, or another table entry. Nothing about the
   step depends on the conclusion. The callee has returned `R`; the caller
   must now show its continuation `K` from it.

   So the step introduces every wand, drops Lithium's `∗ True` frame, and
   leaves `K` to the search. When `K` is headed by a definition that
   Lithium does not unfold itself (no `LithiumUnfold` instance), the step
   unfolds that head one delta step, so that the search sees the packed
   state (`∃ …, reg_col … ∗ …`) and not a name it cannot read. A table
   entry has a `LithiumUnfold` instance and is left as it is. *)

Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.isla.
From iris.proofmode Require Import environments.

Ltac zesu_return_wand_head term :=
  lazymatch term with
  | ?function _ => zesu_return_wand_head function
  | _ => term
  end.

Ltac zesu_unfold_return_continuation :=
  lazymatch goal with
  | |- envs_entails _ ?continuation =>
      let head := zesu_return_wand_head continuation in
      first
        [let _ := constr:(_ : LithiumUnfold head) in idtac
        |unfold head
        |idtac]
  end.

Ltac zesu_enter_return_wand :=
  lazymatch goal with
  | |- envs_entails _ ((_ -∗ _) ∗ True)%I =>
      iSplit;
      [repeat (lazymatch goal with
               | |- envs_entails _ (_ -∗ _)%I => iIntros "?"
               end);
       zesu_unfold_return_continuation
      | done]
  end.

Class ZesuStepReturnWand : Prop := zesu_step_return_wand : True.

Ltac zesu_enter_return_wand_if_enabled :=
  let _ := constr:(_ : ZesuStepReturnWand) in
  zesu_enter_return_wand.
