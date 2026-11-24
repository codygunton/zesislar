From iris.proofmode Require environments.
From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Automation2.Telemetry.
Require ZesuSsz.Automation2.ContextCollection.
Set Default Proof Mode "Classic".

(* Residual lemmas: the pure tier after the selected-facts solvers.

   A residual module exports exact lemmas for the pure goals that the
   solvers leave open in one block. Each lemma binds the goal's variables
   universally and takes the selected facts as premises. Two registrations
   exist:
   - the original modules (ZesuSsz/Residuals/Block800d<block>.v) and a few
     contract modules add `Hint Resolve` hints to `zesu_residual`; the tier
     runs `eauto 2` over them;
   - the relocatable modules (ZesuSsz/Residuals/<function>/Block<offset>.v)
     add one `Hint Extern` per lemma to `zesu_residual_exact`, which runs
     `zesu_residual_exact` (below): the lemma is tried only on a goal whose
     conclusion is the lemma's conclusion up to the lemma's binders, and its
     premises close by hypotheses only. No search runs.
   An empty database fails at once. *)
Create HintDb zesu_residual discriminated.
#[export] Hint Constants Opaque : zesu_residual.
#[export] Hint Variables Opaque : zesu_residual.
Create HintDb zesu_residual_exact discriminated.

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

(* Whether Rel INDEX occurs in TERM. The Coq 8.19 primitive
   `Constr.Unsafe.occur_between` returns the negation of its documented
   result; the polarity is measured once per call (as in ResidualExport). *)
Ltac2 zesu_residual_occurs (index : int) (term : constr) : bool :=
  let reported := Constr.Unsafe.occur_between index 1 term in
  let probe := Constr.Unsafe.occur_between 1 1 (Constr.Unsafe.make (Constr.Unsafe.Rel 1)) in
  if probe then reported else Bool.neg reported.

(* The products of TERM, outermost first, each with the term under it, and
   the conclusion under them all. `not` is not unfolded: a lemma that
   concludes `~ P` concludes `~ P`, never `False`. *)
Ltac2 rec zesu_residual_split (term : constr) (binders : (binder * constr) list)
  : (binder * constr) list * constr :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Prod binder body => zesu_residual_split body ((binder, body) :: binders)
  | _ => (List.rev binders, term)
  end.

(* Whether GOAL is PATTERN up to the lemma's binders: PATTERN is a conclusion
   under DEPTH binders of its own; a Rel above DEPTH is a lemma binder and
   matches any term. Globals and variables compare syntactically; a
   construct this check does not look into (match, fixpoint, cast,
   primitive value) is left to the unification of `simple eapply`. *)
Ltac2 rec zesu_residual_matches (depth : int) (pattern : constr) (goal : constr) : bool :=
  match Constr.Unsafe.kind pattern with
  | Constr.Unsafe.Rel index =>
      if Int.le index depth then
        match Constr.Unsafe.kind goal with
        | Constr.Unsafe.Rel other => Int.equal index other
        | _ => false
        end
      else true
  | Constr.Unsafe.App head arguments =>
      match Constr.Unsafe.kind goal with
      | Constr.Unsafe.App goal_head goal_arguments =>
          if Int.equal (Array.length arguments) (Array.length goal_arguments) then
            if zesu_residual_matches depth head goal_head
            then Array.for_all2 (zesu_residual_matches depth) arguments goal_arguments
            else false
          else false
      | _ => false
      end
  | Constr.Unsafe.Prod binder body =>
      match Constr.Unsafe.kind goal with
      | Constr.Unsafe.Prod goal_binder goal_body =>
          if zesu_residual_matches depth (Constr.Binder.type binder) (Constr.Binder.type goal_binder)
          then zesu_residual_matches (Int.add depth 1) body goal_body else false
      | _ => false
      end
  | Constr.Unsafe.Lambda binder body =>
      match Constr.Unsafe.kind goal with
      | Constr.Unsafe.Lambda goal_binder goal_body =>
          if zesu_residual_matches depth (Constr.Binder.type binder) (Constr.Binder.type goal_binder)
          then zesu_residual_matches (Int.add depth 1) body goal_body else false
      | _ => false
      end
  | Constr.Unsafe.LetIn binder value body =>
      match Constr.Unsafe.kind goal with
      | Constr.Unsafe.LetIn _ goal_value goal_body =>
          if zesu_residual_matches depth value goal_value
          then zesu_residual_matches (Int.add depth 1) body goal_body else false
      | _ => false
      end
  | Constr.Unsafe.Constant _ _ => Constr.equal pattern goal
  | Constr.Unsafe.Ind _ _ => Constr.equal pattern goal
  | Constr.Unsafe.Constructor _ _ => Constr.equal pattern goal
  | Constr.Unsafe.Var _ => Constr.equal pattern goal
  | _ => true
  end.

(* One premise: a hypothesis whose type is the premise syntactically, else
   `assumption` (which also sees through local definitions). *)
Ltac2 zesu_residual_premise () : unit :=
  let goal := Control.goal () in
  match List.find_opt (fun declaration => let (_, _, typ) := declaration in Constr.equal typ goal)
          (Control.hyps ()) with
  | Some declaration => let (name, _, _) := declaration in Control.refine (fun () => Control.hyp name)
  | None => ltac1:(assumption)
  end.

(* Apply LEMMA to the goal when the goal is its conclusion up to its binders.
   A binder that the conclusion fixes is found by unification; any other
   binder that a premise mentions is the context variable of the same name
   (the export keeps the names of the context it was taken from); each
   premise closes by a hypothesis. A missing variable or premise fails the
   lemma; nothing else is tried. Which binders the rest of the statement
   mentions is computed only once the conclusion matched. *)
Ltac2 zesu_residual_exact_apply (lemma : constr) : unit :=
  let (binders, conclusion) := zesu_residual_split (Constr.type lemma) [] in
  if zesu_residual_matches 0 conclusion (Control.goal ()) then
    let names := List.map (fun declaration => let (name, _, _) := declaration in name) (Control.hyps ()) in
    let (bindings, _) := List.fold_left (fun state entry =>
      let (bindings, index) := state in
      let (binder, body) := entry in
      let next := Int.sub index 1 in
      if (if zesu_residual_occurs index conclusion then false else zesu_residual_occurs 1 body) then
        match Constr.Binder.name binder with
        | Some name =>
            if List.mem Ident.equal name names
            then ((Std.NamedHyp name, Control.hyp name) :: bindings, next)
            else Control.zero (Tactic_failure None)
        | None => Control.zero (Tactic_failure None)
        end
      else (bindings, next)) ([], List.length binders) binders in
    let bindings := match bindings with
      | [] => Std.NoBindings
      | _ => Std.ExplicitBindings bindings
      end in
    Std.apply false true [fun () => (lemma, bindings)] None;
    Control.enter zesu_residual_premise
  else Control.zero (Tactic_failure None).

(* The registered tactic of a relocatable residual lemma. *)
Ltac zesu_residual_exact lemma :=
  let apply_exact := ltac2:(lemma |- zesu_residual_exact_apply (Option.get (Ltac1.to_constr lemma))) in
  apply_exact lemma.

(* `Hint Resolve` lemmas: depth 2, one residual lemma, then each premise by
   assumption. `Hint Extern` lemmas: one call of `zesu_residual_exact`,
   dispatched by `typeclasses eauto 1`, which unlike `eauto` builds no hint
   database from the context (measured: 80 hypotheses, empty database,
   `eauto 1` 1.2 ms a call, `typeclasses eauto 1` 5 us). A goal whose
   conclusion mentions a local definition gets one more try of both with the
   definitions unfolded (unfolded once). A context with a fact above the node
   limit gets a last try of all of these with the fact's pieces posed, as the
   exporter states them (`ContextCollection.zesu_large_fact_pieces`, which
   fails at once when there is no such fact). Telemetry names each try:
   kind=alt|altfail
   site=residual_hint|residual_exact|residual_unfolded|residual_pieces. *)
Ltac zesu_residual_lemma :=
  first [zesu_talt residual_hint (idtac; solve [eauto 2 with nocore zesu_residual])
        | zesu_talt residual_exact (idtac; solve [typeclasses eauto 1 with zesu_residual_exact])
        | zesu_talt residual_unfolded (idtac;
            solve [zesu_residual_unfold_goal;
                   first [solve [eauto 2 with nocore zesu_residual]
                         | solve [typeclasses eauto 1 with zesu_residual_exact]]])
        | zesu_talt residual_pieces (idtac;
            solve [ZesuSsz.Automation2.ContextCollection.zesu_large_fact_pieces;
                   first [solve [eauto 2 with nocore zesu_residual]
                         | solve [typeclasses eauto 1 with zesu_residual_exact]
                         | solve [zesu_residual_unfold_goal;
                                  first [solve [eauto 2 with nocore zesu_residual]
                                        | solve [typeclasses eauto 1 with zesu_residual_exact]]]]])].
