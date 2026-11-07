From Coq Require Import ZArith.ZArith NArith.NArith.
From Coq Require Export Strings.String.
From Ltac2 Require Import Ltac2 Ref List Int Array Ident.
Require Import ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.SolverContextPolicy.
Set Default Proof Mode "Classic".

(* Budgets count attempted operations, including backtracking. Exhaustion is
   checked outside each repeat, so repeat cannot turn exhaustion into success. *)
Ltac2 zesu_budget_take failed remaining :=
  let n := Ref.get remaining in
  if Bool.or (Ref.get failed) (Int.le n 0) then (
    Ref.set failed true;
    Control.zero (Tactic_failure (Some (Message.of_string "arithmetic search budget exhausted"))))
  else Ref.set remaining (Int.sub n 1).

Ltac2 zesu_budget_check failed :=
  if Ref.get failed then
    Control.zero (Tactic_failure (Some (Message.of_string "arithmetic search budget exhausted")))
  else ().

Ltac2 zesu_budget_tick failed limit :=
  let remaining := Ref.ref limit in
  Ltac1.lambda (fun _ =>
    zesu_budget_take failed remaining;
    Ltac1.of_constr constr:(tt)).

Ltac2 zesu_budget_checker failed :=
  Ltac1.lambda (fun _ =>
    zesu_budget_check failed;
    Ltac1.of_constr constr:(tt)).

Ltac2 rec zesu_count_nodes failed remaining term :=
  zesu_budget_take failed remaining;
  let visit := zesu_count_nodes failed remaining in
  let binder b := visit (Constr.Binder.type b) in
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head args => visit head; Array.iter visit args
  | Constr.Unsafe.Cast value _ typ => visit value; visit typ
  | Constr.Unsafe.Prod b body => binder b; visit body
  | Constr.Unsafe.Lambda b body => binder b; visit body
  | Constr.Unsafe.LetIn b value body => binder b; visit value; visit body
  | Constr.Unsafe.Case _ predicate invert value branches =>
      let (typ, _) := predicate in visit typ; visit value;
      Array.iter visit branches;
      match invert with
      | Constr.Unsafe.NoInvert => ()
      | Constr.Unsafe.CaseInvert indices => Array.iter visit indices
      end
  | Constr.Unsafe.Fix _ _ binders bodies => Array.iter binder binders; Array.iter visit bodies
  | Constr.Unsafe.CoFix _ binders bodies => Array.iter binder binders; Array.iter visit bodies
  | Constr.Unsafe.Proj _ _ value => visit value
  | Constr.Unsafe.Array _ values default typ => Array.iter visit values; visit default; visit typ
  | Constr.Unsafe.Evar _ args => Array.iter visit args
  | _ => ()
  end.

(* These bounds exceed twice the largest completed fallback input. *)
Ltac2 zesu_atomic_input_bound () :=
  let failed := Ref.ref false in
  let hyps := Control.hyps () in
  if Int.gt (List.length hyps) 512 then
    Control.zero (Tactic_failure (Some (Message.of_string "arithmetic context is too large")))
  else ();
  zesu_count_nodes failed (Ref.ref 1024) (Control.goal ());
  let total := Ref.ref 131072 in
  List.iter (fun h =>
    let (_, _, typ) := h in
    zesu_count_nodes failed (Ref.ref 16384) typ;
    zesu_count_nodes failed total typ) hyps;
  zesu_budget_check failed.

Ltac zesu_closed_goal_steps visits rewrites :=
  once (repeat match goal with
  | |- context[?term] =>
      let _ := visits constr:(tt) in
      lazymatch type of term with Z =>
        lazymatch term with
        | Z0 => fail | Zpos _ => fail | Zneg _ => fail
        | _ =>
            let value := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed term in
            let _ := rewrites constr:(tt) in
            progress change_no_check term with value
        end
      end
  end).

Ltac2 zesu_reduce_closed_goal () :=
  let failed := Ref.ref false in
  Ltac1.apply (Ltac1.ref [@ZesuSsz; @Automation2; @SearchBudget; @zesu_closed_goal_steps])
    [zesu_budget_tick failed 1024; zesu_budget_tick failed 32] Ltac1.run;
  zesu_budget_check failed.

Ltac zesu_normalize_closed_goal := ltac2:(zesu_reduce_closed_goal ()).
Ltac zesu_check_atomic_input := ltac2:(zesu_atomic_input_bound ()).

(* Solver limits apply to the selected proof context. *)
Ltac2 rec zesu_solver_positive value :=
  lazy_match! value with
  | xH => 1
  | xO ?tail => Int.mul 2 (zesu_solver_positive tail)
  | xI ?tail => Int.add 1 (Int.mul 2 (zesu_solver_positive tail))
  end.
Ltac2 zesu_solver_limit value :=
  if Constr.has_evar value then Control.zero (Tactic_failure None) else ();
  let value := Std.eval_hnf value in
  if Constr.has_evar value then Control.zero (Tactic_failure None) else ();
  lazy_match! value with
  | Z0 => 0
  | Zpos ?positive => zesu_solver_positive positive
  | _ => Control.zero (Tactic_failure (Some (Message.of_string "Invalid solver context limit")))
  end.
Ltac2 zesu_prop_context_bound () :=
  let limit := zesu_solver_limit constr:(SolverContextPolicy.zesu_solver_prop_limit) in
  let count := List.fold_left (fun count declaration =>
    let (_, _, typ) := declaration in
    if Constr.equal (Constr.type typ) constr:(Prop)
    then Int.add count 1 else count) 0 (Control.hyps ()) in
  if Int.gt count limit then
    Control.zero (Tactic_failure (Some (Message.concat
      (Message.of_string "Solver context exceeds its Prop limit: ") (Message.of_int count))))
  else ().
Ltac2 zesu_solver_context_bound () :=
  zesu_prop_context_bound ();
  let failed := Ref.ref false in
  let limit := zesu_solver_limit constr:(SolverContextPolicy.zesu_solver_node_limit) in
  let remaining := Ref.ref limit in
  zesu_count_nodes failed remaining (Control.goal ());
  List.iter (fun declaration =>
    let (_, body, typ) := declaration in
    zesu_count_nodes failed remaining typ;
    match body with
    | None => ()
    | Some value => zesu_count_nodes failed remaining value
    end) (Control.hyps ());
  zesu_budget_check failed.
Ltac zesu_solve_selected site closer :=
  tryif ltac2:(zesu_solver_context_bound ()) then closer
  else fail 0 "Solver context refused at" site.
