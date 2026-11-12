From iris.proofmode Require environments.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* Residual lemmas: the pure tier after the selected-facts solvers.

   A residual module (ZesuSsz/Residuals/<Block>.v) exports exact lemmas for
   the pure goals that the solvers leave open in one block. Each lemma binds
   the goal's variables universally and takes the selected facts as premises.
   The tier applies one lemma whose conclusion matches the goal and closes its
   premises from the context. The search is depth bounded; an empty database
   fails at once. *)
Create HintDb zesu_residual discriminated.
#[export] Hint Constants Opaque : zesu_residual.
#[export] Hint Variables Opaque : zesu_residual.

(* TERM with every local definition of the context substituted, newest
   first, so a body that mentions an older definition is unfolded too. Only
   local definitions are unfolded; no other reduction runs. The residual
   export (ResidualExport.v) writes lemma statements in this form. *)
Ltac2 zesu_residual_unfold_local (term : constr) : constr :=
  List.fold_left (fun current declaration =>
    let (name, body, _) := declaration in
    match body with
    | Some value =>
        Constr.Unsafe.substnl [value] 0 (Constr.Unsafe.closenl [name] 1 current)
    | None => current
    end) term (List.rev (Control.hyps ())).

(* Whether the conclusion mentions a local definition: closing over a
   variable that does not occur leaves a closed term unchanged. *)
Ltac2 zesu_residual_goal_mentions_definition () : bool :=
  let goal := Control.goal () in
  List.exist (fun declaration =>
    let (name, body, _) := declaration in
    match body with
    | Some _ => Bool.neg (Constr.equal (Constr.Unsafe.closenl [name] 1 goal) goal)
    | None => false
    end) (Control.hyps ()).

(* With `Hint Variables Opaque`, a local definition in the goal is a rigid
   symbol for the discrimination net, and no closed lemma can name it. On a
   pure goal whose conclusion mentions one, unfold the local definitions in
   the conclusion; hypotheses keep them (premises still match by
   assumption, which unfolds local definitions). *)
Ltac zesu_residual_unfold_goal :=
  lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _ _ => fail
  | _ => ltac2:(
      if zesu_residual_goal_mentions_definition () then
        let unfolded := zesu_residual_unfold_local (Control.goal ()) in
        Std.change None (fun _ => unfolded) { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }
      else Control.zero (Tactic_failure None))
  end.

(* Depth 2: one residual lemma, then each premise by assumption. A goal
   whose conclusion mentions a local definition gets a second try with the
   definitions unfolded. *)
Ltac zesu_residual_lemma :=
  first [solve [eauto 2 with nocore zesu_residual]
        | solve [zesu_residual_unfold_goal; eauto 2 with nocore zesu_residual]].
