Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.ContextCollection.
Require ZesuSsz.Automation2.ResidualExport.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* Refusal diagnostics.

   Every hook here is off unless the caller imports `DiagnosticsOn`, the
   only module with a `ZesuDiagnosticsOn` instance. Off, a hook costs one
   failed instance lookup. On, a hook only prints: it never changes the goal
   or the context, and a printing error is swallowed. The step hook always
   fails, so a search loop that tries it as its first alternative goes on
   to its real alternatives. `tools/block/refusal_report.py` reads the
   output. *)
Class ZesuDiagnosticsOn : Prop := zesu_diagnostics_on : True.

Ltac zesu_diag_on := let _ := constr:(_ : ZesuDiagnosticsOn) in idtac.

(* A skeleton of a term: subterms below the depth become `__`; numerals and
   other closed constructor trees stay whole; binders become `__`. *)
Ltac2 zesu_diag_hole () :=
  Constr.Unsafe.make (Constr.Unsafe.Var (Option.get (Ident.of_string "__"))).

Ltac2 rec zesu_diag_literal (term : constr) : bool :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.Ind _ _ => true
  | Constr.Unsafe.App head arguments =>
      match Constr.Unsafe.kind head with
      | Constr.Unsafe.Constructor _ _ =>
          Array.fold_left (fun ok argument => if ok then zesu_diag_literal argument else false)
            true arguments
      | _ => false
      end
  | _ => false
  end.

Ltac2 rec zesu_diag_skeleton (depth : int) (term : constr) : constr :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      if zesu_diag_literal term then term
      else if Int.le depth 0 then zesu_diag_hole ()
      else Constr.Unsafe.make (Constr.Unsafe.App (zesu_diag_skeleton depth head)
        (Array.map (zesu_diag_skeleton (Int.sub depth 1)) arguments))
  | Constr.Unsafe.Lambda _ _ => zesu_diag_hole ()
  | Constr.Unsafe.LetIn _ _ _ => zesu_diag_hole ()
  | Constr.Unsafe.Case _ _ _ _ _ => zesu_diag_hole ()
  | Constr.Unsafe.Fix _ _ _ _ => zesu_diag_hole ()
  | Constr.Unsafe.Prod _ _ => zesu_diag_hole ()
  | Constr.Unsafe.Cast value _ _ => zesu_diag_skeleton depth value
  | _ => term
  end.

Ltac2 zesu_diag_print (label : string) (term : constr) :=
  let shown := match Control.case (fun () =>
      Message.of_constr (zesu_diag_skeleton 3 term)) with
    | Val (message, _) => message
    | Err _ => Message.of_string "?"
    end in
  Message.print (Message.concat (Message.of_string label) shown).

Ltac2 zesu_diag_print_term (label : string) (term : Ltac1.t) :=
  match Ltac1.to_constr term with
  | Some value => zesu_diag_print label value
  | None => ()
  end.

(* The Coq hypotheses that are propositions, without local definitions. *)
Ltac2 zesu_diag_props () :=
  List.filter (fun declaration =>
    let (_, body, typ) := declaration in
    match body with
    | None => ZesuSsz.Automation2.ContextCollection.zesu_context_proposition typ
    | Some _ => false
    end) (Control.hyps ()).

(* Small facts with their statements, larger facts by name only. *)
Ltac2 zesu_diag_print_facts () :=
  let props := zesu_diag_props () in
  List.iter (fun declaration =>
    let (name, _, typ) := declaration in
    if ZesuSsz.Automation2.ContextCollection.zesu_select_small 256 typ then
      Message.print (Message.concat (Message.of_string "@@D fact ")
        (Message.concat (Message.of_ident name)
          (Message.concat (Message.of_string " : ") (Message.of_constr typ))))
    else Message.print (Message.concat (Message.of_string "@@D bigfact ")
      (Message.of_ident name))) props;
  Message.print (Message.concat (Message.of_string "@@D facts-end ")
    (Message.of_int (List.length props))).

(* The names of the context facts, at each step: the report finds the step
   where a fact first appears by its name. *)
Ltac2 zesu_diag_print_names () :=
  Message.print (List.fold_left (fun message declaration =>
    let (name, _, _) := declaration in
    Message.concat message (Message.concat (Message.of_string " ") (Message.of_ident name)))
    (Message.of_string "@@D names") (zesu_diag_props ())).

(* The facts that share an atom with the goal (the ContextCollection atom). *)
Ltac2 zesu_diag_print_relevant () :=
  let goal_atoms := Ref.ref [] in
  let _ := ZesuSsz.Automation2.ContextCollection.zesu_select_atoms goal_atoms (Control.goal ()) in
  let known := Ref.get goal_atoms in
  let names := List.fold_left (fun found declaration =>
    let (name, _, typ) := declaration in
    let mine := Ref.ref [] in
    let _ := ZesuSsz.Automation2.ContextCollection.zesu_select_atoms mine typ in
    if List.exist (fun atom => List.exist (fun goal_atom => Constr.equal atom goal_atom) known)
      (Ref.get mine) then name :: found else found) [] (zesu_diag_props ()) in
  Message.print (List.fold_left (fun message name =>
    Message.concat message (Message.concat (Message.of_string " ") (Message.of_ident name)))
    (Message.of_string "@@D relevant") (List.rev names)).

Ltac zesu_diag_print_head :=
  lazymatch goal with
  | |- environments.envs_entails _ ?target =>
      let print := ltac2:(term |- zesu_diag_print_term "@@D head " term) in print target
  | |- SHELVED_SIDECOND ?target =>
      let print := ltac2:(term |- zesu_diag_print_term "@@D head " term) in print target
  | |- ?target =>
      let print := ltac2:(term |- zesu_diag_print_term "@@D head " term) in print target
  end.

Ltac zesu_diag_print_step :=
  idtac "@@D step";
  lazymatch goal with
  | |- environments.envs_entails _ (find_in_context (FindInstrKind ?address _) _) =>
      idtac "@@D pc" address
  | |- environments.envs_entails _ (instr_body ?address _) =>
      idtac "@@D pc" address
  | |- environments.envs_entails _ (bi_sep (bi_pure ?condition) _) =>
      let print := ltac2:(term |- zesu_diag_print_term "@@D sidecond " term) in print condition
  | _ => idtac
  end;
  zesu_diag_print_head;
  ltac2:(zesu_diag_print_names ()).

(* The printer of `orch/joins/make_printer.py`: definitions, hypotheses,
   conclusion. *)
Ltac zesu_diag_print_goal :=
  match goal with
  | |- ?goal =>
      idtac "@@GOAL-BEGIN";
      try (match goal with H := ?value |- _ => idtac "@@DEF" H ":=" value; fail end);
      try (match goal with H : ?statement |- _ => idtac "@@HYP" H ":" statement; fail end);
      idtac "@@CONCL" goal; idtac "@@GOAL-END"
  end.

Ltac zesu_diag_print_refusal kind :=
  idtac "@@D refuse" kind;
  zesu_diag_print_head;
  lazymatch goal with
  | |- SHELVED_SIDECOND ?target =>
      let print := ltac2:(term |- zesu_diag_print_term "@@D sidecond " term) in print target
  | |- environments.envs_entails _ _ => idtac
  | |- ?target =>
      let print := ltac2:(term |- zesu_diag_print_term "@@D sidecond " term) in print target
  end;
  ltac2:(zesu_diag_print_relevant ());
  ltac2:(zesu_diag_print_facts ());
  zesu_diag_print_goal.

(* The hooks. Each one is a no-op (or, for the step hook, a plain failure)
   when no `ZesuDiagnosticsOn` instance exists. *)
Ltac zesu_diag_step := zesu_diag_on; try zesu_diag_print_step; fail.

Ltac zesu_diag_stage name :=
  tryif zesu_diag_on
  then try (idtac "@@D stage" name; zesu_diag_print_head; ltac2:(zesu_diag_print_facts ()))
  else idtac.

(* The end of a stepping loop, on a goal that is still an Iris goal. *)
Ltac zesu_diag_step_end :=
  tryif zesu_diag_on
  then try (lazymatch goal with
    | |- environments.envs_entails _ _ => idtac "@@D step-end"; zesu_diag_print_head
    end)
  else idtac.

(* Residual export (ResidualExport.v): a second switch, so an export run
   prints no step or stage records. Each hook prints one `@@X` record for
   the focused goal: the exact source of its statement for a pure goal, or a
   skip line with the reason. It never changes the goal or the context. *)
Class ZesuResidualExportOn : Prop := zesu_residual_export_on : True.

Ltac zesu_diag_export_on := let _ := constr:(_ : ZesuResidualExportOn) in idtac.

(* At the split point: a pure conjunct that the package route split off,
   before the finisher runs on it. *)
Ltac zesu_diag_export_split :=
  tryif zesu_diag_export_on then try (
    lazymatch goal with
    | |- environments.envs_entails _ _ => idtac "@@X skip split spatial"
    | _ => ltac2:(ZesuSsz.Automation2.ResidualExport.zesu_export_goal "split")
    end)
  else idtac.

(* At the refusal point: each goal still open at the end of the block. *)
Ltac zesu_diag_export_final :=
  tryif zesu_diag_export_on then try (
    lazymatch goal with
    | |- environments.envs_entails _ _ => idtac "@@X skip final spatial"
    | _ => ltac2:(ZesuSsz.Automation2.ResidualExport.zesu_export_goal "final")
    end)
  else idtac.

Ltac zesu_diag_refusal kind :=
  (tryif zesu_diag_on then try zesu_diag_print_refusal kind else idtac);
  zesu_diag_export_final.
