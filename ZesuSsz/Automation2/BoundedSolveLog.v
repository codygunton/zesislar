Require Import ZesuSsz.Automation2.SwitchDispatch ZesuSsz.Automation2.ContextCollection ZesuSsz.Automation2.RecordFieldPruning ZesuSsz.Automation2.LinearFirstLia ZesuSsz.Automation2.BoundedSolve.
(* SolverBound measurement prelude: logs the context size at every solver arm and saturation. *)
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Ltac2 bsm_big () := 1000000000.
Ltac2 bsm_nodes () :=
  let b := bsm_big () in
  Int.sub b (ZesuSsz.Automation2.LinearFirstLia.zesu_linear_facts_remaining
    (ZesuSsz.Automation2.LinearFirstLia.zesu_linear_remaining b (Control.goal ())) (Control.hyps ())).
Ltac2 bsm_props () :=
  List.length (List.filter (fun declaration =>
    let (_, body, typ) := declaration in
    match body with
    | Some _ => false
    | None => ZesuSsz.Automation2.LinearFirstLia.zesu_linear_is_prop typ
    end) (Control.hyps ())).

(* Rounds of the record-field relevance fixpoint (RecordFieldPruning.a3n_relevance, the pruned arm's prune). *)
Ltac2 rec bsm_relevance (facts : (ident * constr list) list) (keys : constr list) (names : ident list) (rounds : int) :=
  let (next_keys, next_names) := List.fold_left (fun found fact =>
    let (found_keys, found_names) := found in
    let (name, variables) := fact in
    if ZesuSsz.Automation2.ContextCollection.zesu_context_member name found_names then found
    else if Bool.or (Int.equal (List.length variables) 0)
        (List.exist (fun term => ZesuSsz.Automation2.RecordFieldPruning.a3n_member term found_keys) variables) then
      (ZesuSsz.Automation2.RecordFieldPruning.a3n_union found_keys variables, name :: found_names)
    else found) (keys, names) facts in
  if Int.equal (List.length next_names) (List.length names) then rounds
  else bsm_relevance facts next_keys next_names (Int.add rounds 1).
Ltac2 bsm_rounds () :=
  match Control.case (fun () =>
    let hyps := Control.hyps () in
    let records := List.fold_left (fun found declaration =>
      let (name, _, _) := declaration in
      if ZesuSsz.Automation2.RecordFieldPruning.a3n_record_variable (Constr.Unsafe.make (Constr.Unsafe.Var name))
      then name :: found else found) [] hyps in
    let facts := List.fold_left (fun found declaration =>
      let (name, body, ty) := declaration in
      match body with Some _ => found | None =>
        if ZesuSsz.Automation2.ContextCollection.zesu_context_proposition ty
        then (name, ZesuSsz.Automation2.RecordFieldPruning.a3n_unfold_keys records hyps
                      (ZesuSsz.Automation2.RecordFieldPruning.a3n_keys records ty)) :: found else found end) [] hyps in
    bsm_relevance facts (ZesuSsz.Automation2.RecordFieldPruning.a3n_unfold_keys records hyps
      (ZesuSsz.Automation2.RecordFieldPruning.a3n_keys records (Control.goal ()))) [] 0) with
  | Val (r, _) => r
  | Err _ => -1
  end.

Ltac2 bsm_print (tag : string) (outcome : string) (n : int) (h : int) (r : int) (extra : int) :=
  Message.print (Message.concat (Message.of_string "@@BS ")
    (Message.concat (Message.of_string tag)
    (Message.concat (Message.of_string " ")
    (Message.concat (Message.of_string outcome)
    (Message.concat (Message.of_string " n=")
    (Message.concat (Message.of_int n)
    (Message.concat (Message.of_string " h=")
    (Message.concat (Message.of_int h)
    (Message.concat (Message.of_string " r=")
    (Message.concat (Message.of_int r)
    (Message.concat (Message.of_string " x=") (Message.of_int extra)))))))))))).

Ltac2 bsm_numgoals () :=
  let c := Ref.ref 0 in
  Control.enter (fun () => Ref.set c (Int.add (Ref.get c) 1));
  Ref.get c.

Ltac2 bsm_arm (tag : string) (closer : Ltac1.t) :=
  if Int.equal (bsm_numgoals ()) 1 then
    let n := bsm_nodes () in
    let h := bsm_props () in
    let r := bsm_rounds () in
    match Control.case (fun () =>
      Ltac1.run closer;
      if Int.equal (bsm_numgoals ()) 0 then () else Control.zero (Tactic_failure None)) with
    | Val _ => bsm_print tag "ok" n h r 0
    | Err e => bsm_print tag "fail" n h r 0; Control.zero e
    end
  else Ltac1.run closer.

(* BoundedSolve logging (heads with zesu_bounded_search). @@BS <kind>.p|<kind>.w ok|fail n=context nodes;
   search.p; sat.skip (n = context, a skipped saturation); vm (n = goal + context, x = goal-only nodes). *)
Ltac2 bsl_kind (kind : constr) : string :=
  if Constr.equal kind constr:(ZesuSsz.Automation2.BoundedSolve.zesu_solver_lia) then "lia"
  else if Constr.equal kind constr:(ZesuSsz.Automation2.BoundedSolve.zesu_solver_bv) then "bv"
  else if Constr.equal kind constr:(ZesuSsz.Automation2.BoundedSolve.zesu_solver_search) then "search"
  else if Constr.equal kind constr:(ZesuSsz.Automation2.BoundedSolve.zesu_solver_saturation) then "sat"
  else "vm".
Ltac2 bsl_arm (kind : Ltac1.t) (suffix : string) (closer : Ltac1.t) :=
  bsm_arm (String.app (bsl_kind (Option.get (Ltac1.to_constr kind))) suffix) closer.
Ltac bsl_p kind closer := let f := ltac2:(k c |- bsl_arm k ".p" c) in f kind closer.
Ltac bsl_w kind closer := let f := ltac2:(k c |- bsl_arm k ".w" c) in f kind closer.
Ltac2 bsl_goal_nodes () :=
  let b := bsm_big () in Int.sub b (ZesuSsz.Automation2.LinearFirstLia.zesu_linear_remaining b (Control.goal ())).
Ltac2 bsl_skip () := bsm_print "sat.skip" "ok" (bsm_nodes ()) (bsm_props ()) 0 0.
Ltac2 bsl_vm () := bsm_print "vm" "ok" (bsm_nodes ()) (bsm_props ()) 0 (bsl_goal_nodes ()).

Ltac ZesuSsz.Automation2.BoundedSolve.zesu_bounded_solve kind closer ::=
  tryif ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation2.ContextCollection.ZesuStepFinisherOnce)
  then first [solve [ZesuSsz.Automation2.BoundedSolve.zesu_bounded_prune_goal;
                     bsl_p kind ltac:(ZesuSsz.Automation2.BoundedSolve.zesu_bounded_pruned kind; closer)]
             | bsl_w kind ltac:(ZesuSsz.Automation2.BoundedSolve.zesu_bounded_whole kind; closer)]
  else bsl_w kind ltac:(ZesuSsz.Automation2.BoundedSolve.zesu_bounded_whole kind; closer).

Ltac ZesuSsz.Automation2.BoundedSolve.zesu_bounded_saturate saturation ::=
  tryif ZesuSsz.Automation2.BoundedSolve.zesu_bounded_whole constr:(ZesuSsz.Automation2.BoundedSolve.zesu_solver_saturation)
  then saturation else ltac2:(Control.enter bsl_skip).

Ltac ZesuSsz.Automation2.BoundedSolve.zesu_vm_compute_goal ::=
  ltac2:(Control.enter bsl_vm);
  ltac2:(Control.enter (fun () => ZesuSsz.Automation2.BoundedSolve.zesu_bounded_goal_within
    constr:(ZesuSsz.Automation2.BoundedSolve.zesu_solver_vm)));
  vm_compute.
