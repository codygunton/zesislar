Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require ZesuSsz.Automation2.SearchBudget.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Class ZesuStepContextCollection : Prop := zesu_context_collection_enabled : True.
Class ZesuStepFinisherOnce : Prop := zesu_finisher_once_enabled : True.

Ltac2 rec zesu_context_member (name : ident) (names : ident list) :=
  match names with
  | [] => false
  | head :: rest => if Ident.equal name head then true else zesu_context_member name rest
  end.

Ltac2 zesu_context_add (names : ident list) (name : ident) :=
  if zesu_context_member name names then names else name :: names.

Ltac2 zesu_context_union (left : ident list) (right : ident list) :=
  List.fold_left zesu_context_add left right.

(* Unsupported syntax refuses the filtered branch. It never changes the term. *)
Ltac2 rec zesu_context_variables (term : constr) :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Var name => [name]
  | Constr.Unsafe.Rel _ => []
  | Constr.Unsafe.Sort _ => []
  | Constr.Unsafe.Constant _ _ => []
  | Constr.Unsafe.Ind _ _ => []
  | Constr.Unsafe.Constructor _ _ => []
  | Constr.Unsafe.Uint63 _ => []
  | Constr.Unsafe.Float _ => []
  | Constr.Unsafe.App head arguments =>
      Array.fold_left (fun found argument =>
        zesu_context_union found (zesu_context_variables argument)) (zesu_context_variables head) arguments
  | Constr.Unsafe.Cast body _ ty =>
      zesu_context_union (zesu_context_variables body) (zesu_context_variables ty)
  | Constr.Unsafe.Prod binder body =>
      zesu_context_union (zesu_context_variables (Constr.Binder.type binder)) (zesu_context_variables body)
  | Constr.Unsafe.Lambda binder body =>
      zesu_context_union (zesu_context_variables (Constr.Binder.type binder)) (zesu_context_variables body)
  | Constr.Unsafe.LetIn binder value body =>
      zesu_context_union (zesu_context_variables (Constr.Binder.type binder))
        (zesu_context_union (zesu_context_variables value) (zesu_context_variables body))
  | Constr.Unsafe.Proj _ _ body => zesu_context_variables body
  | _ => Control.zero (Tactic_failure None)
  end.

Ltac2 zesu_context_proposition (ty : constr) :=
  Constr.equal (Constr.type ty) constr:(Prop).

Ltac2 zesu_context_intersects (left : ident list) (right : ident list) :=
  List.exist (fun name => zesu_context_member name right) left.

Ltac2 zesu_context_declaration_variables (body : constr option) (ty : constr) :=
  match body with
  | None => zesu_context_variables ty
  | Some value => zesu_context_union (zesu_context_variables ty) (zesu_context_variables value)
  end.

Ltac2 rec zesu_context_relevance (hyps : (ident * constr option * constr) list)
    (relevant : ident list) :=
  let next := List.fold_left (fun found declaration =>
    let (name, body, ty) := declaration in
    let variables := zesu_context_declaration_variables body ty in
    let selected :=
      if zesu_context_member name found then true
      else match body with
      | Some _ => false
      | None => if zesu_context_proposition ty then
          if Int.equal (List.length variables) 0 then true
          else zesu_context_intersects variables found
        else false
      end in
    if selected then zesu_context_add (zesu_context_union found variables) name else found)
    relevant hyps in
  if Int.equal (List.length next) (List.length relevant) then next
  else zesu_context_relevance hyps next.

Ltac2 rec zesu_context_dependencies (hyps : (ident * constr option * constr) list)
    (kept : ident list) :=
  let next := List.fold_left (fun found declaration =>
    let (name, body, ty) := declaration in
    if zesu_context_member name found then
      zesu_context_union found (zesu_context_declaration_variables body ty)
    else found) kept hyps in
  if Int.equal (List.length next) (List.length kept) then next
  else zesu_context_dependencies hyps next.

Ltac2 zesu_context_prune () :=
  let hyps := Control.hyps () in
  let target := Control.goal () in
  if Constr.has_evar target then Control.zero (Tactic_failure None) else ();
  List.iter (fun declaration =>
    let (_, body, ty) := declaration in
    if Constr.has_evar ty then Control.zero (Tactic_failure None) else ();
    match body with
    | None => ()
    | Some value => if Constr.has_evar value
        then Control.zero (Tactic_failure None) else ()
    end) hyps;
  let relevant := zesu_context_relevance hyps (zesu_context_variables target) in
  let kept := List.fold_left (fun names declaration =>
    let (name, body, ty) := declaration in
    match body with
    | Some _ => zesu_context_add names name
    | None => if zesu_context_proposition ty then names else zesu_context_add names name
    end) relevant hyps in
  let kept := zesu_context_dependencies hyps kept in
  List.iter (fun declaration =>
    let (name, body, ty) := declaration in
    if zesu_context_member name kept then () else
    match body with
    | Some _ => Control.zero (Tactic_failure None)
    | None => if zesu_context_proposition ty then Std.clear [name]
        else Control.zero (Tactic_failure None)
    end) (List.rev hyps).

Ltac zesu_context_prune_goal := ltac2:(zesu_context_prune ()).
Ltac zesu_context_filtered closer := first [solve [zesu_context_prune_goal; closer] | closer].

Ltac2 zesu_context_collect_live (roots : constr list) :=
  let hyps := Control.hyps () in
  let target := Control.goal () in
  if Constr.has_evar target then Control.zero (Tactic_failure None) else ();
  List.iter (fun root =>
    if Constr.has_evar root then Control.zero (Tactic_failure None) else ()) roots;
  List.iter (fun declaration =>
    let (_, body, ty) := declaration in
    if Constr.has_evar ty then Control.zero (Tactic_failure None) else ();
    match body with
    | None => ()
    | Some value => if Constr.has_evar value
        then Control.zero (Tactic_failure None) else ()
    end) hyps;
  let seeds := List.fold_left (fun found root =>
    zesu_context_union found (zesu_context_variables root)) (zesu_context_variables target) roots in
  (* Local definitions can carry facts required by the continuation. *)
  let seeds := List.fold_left (fun found declaration =>
    let (name, body, ty) := declaration in
    match body with
    | None => found
    | Some value =>
        zesu_context_add
          (zesu_context_union found (zesu_context_declaration_variables body ty)) name
    end) seeds hyps in
  let kept := zesu_context_dependencies hyps (zesu_context_relevance hyps seeds) in
  List.iter (fun declaration =>
    let (name, _, _) := declaration in
    if zesu_context_member name kept then () else Std.clear [name]) (List.rev hyps).


Ltac zesu_context_collect := ltac2:(zesu_context_collect_live []).
Polymorphic Inductive zesu_context_finish_attempted {A : Type} (target : A) : Prop :=
  zesu_context_finish_token : zesu_context_finish_attempted target.

Inductive zesu_context_collection_off : Prop := zesu_context_collection_off_intro.

Ltac zesu_context_has_evar :=
  first [
    lazymatch goal with |- ?target => has_evar target end
  | multimatch goal with
    | _ := ?value : ?ty |- _ => first [has_evar value | has_evar ty]
    end
  | multimatch goal with
    | _ : ?ty |- _ => has_evar ty
    end].

Ltac zesu_context_finish_resolved target closer :=
  tryif zesu_context_has_evar then closer else
  first [
    multimatch goal with
    | _ : @zesu_context_finish_attempted _ ?previous |- _ =>
        constr_eq previous target
    end
  | let marker := fresh "zesuFinishAttempted" in
    pose proof (@zesu_context_finish_token _ target) as marker;
    try closer].

Ltac zesu_context_finish_once closer :=
  lazymatch goal with
  | |- SHELVED_SIDECOND ?target => zesu_context_finish_resolved target closer
  | |- ?target =>
    first [
      match goal with
      | _ : @zesu_context_finish_attempted _ _ |- _ => zesu_context_finish_resolved target closer
      end
    | closer]
  end.

Ltac zesu_context_filter closer :=
  tryif zesu_switch_enabled constr:(ZesuStepFinisherOnce)
  then zesu_context_filtered closer else closer.

Ltac zesu_collect_if_enabled :=
  tryif zesu_switch_enabled constr:(ZesuStepContextCollection)
  then tryif (match goal with _ : zesu_context_collection_off |- _ => idtac end)
       then idtac else (try zesu_context_collect)
  else idtac.

Ltac zesu_finish_once_if_enabled closer :=
  tryif zesu_switch_enabled constr:(ZesuStepFinisherOnce)
  then zesu_context_finish_once closer else closer.

(* A solver call reads the facts its goal reaches, never the whole context.
   An atom is a closed subterm of an integer, natural, or bitvector type
   that mentions a local name; its subterms are atoms too. A fact is kept
   when it shares an atom with the goal or with a fact kept in an earlier
   round. Facts above the node limit are never kept: a solver cannot use
   their full expressions, and they make it spin. The guard in
   SearchBudget then checks the kept context against the solver policy. *)
Ltac2 zesu_select_arith (typ : constr) : bool :=
  if Constr.equal typ constr:(Z) then true else
  if Constr.equal typ constr:(nat) then true else
  if Constr.equal typ constr:(N) then true else
  match Constr.Unsafe.kind typ with
  | Constr.Unsafe.App head _ => Constr.equal head constr:(bv)
  | _ => false
  end.

Ltac2 zesu_select_add (atoms : constr list ref) (term : constr) :=
  if List.exist (fun known => Constr.equal known term) (Ref.get atoms) then ()
  else Ref.set atoms (term :: Ref.get atoms).

Ltac2 rec zesu_select_atoms (atoms : constr list ref) (term : constr) : bool :=
  let visit := zesu_select_atoms atoms in
  let pair := fun left right => let found := visit left in let other := visit right in Bool.or found other in
  let local := match Constr.Unsafe.kind term with
    | Constr.Unsafe.Var _ => true
    | Constr.Unsafe.App head arguments =>
        Array.fold_left (fun found argument =>
          let inner := visit argument in Bool.or found inner) (visit head) arguments
    | Constr.Unsafe.Cast value _ typ => pair value typ
    | Constr.Unsafe.Prod binder body => pair (Constr.Binder.type binder) body
    | Constr.Unsafe.Lambda binder body => pair (Constr.Binder.type binder) body
    | Constr.Unsafe.LetIn binder value body =>
        let found := visit (Constr.Binder.type binder) in
        let other := pair value body in Bool.or found other
    | Constr.Unsafe.Proj _ _ value => visit value
    | Constr.Unsafe.Case _ predicate _ value branches =>
        let (typ, _) := predicate in
        Array.fold_left (fun found branch =>
          let inner := visit branch in Bool.or found inner) (pair typ value) branches
    | _ => false
    end in
  (if local then
     if Constr.Unsafe.is_closed term then
       if zesu_select_arith (Constr.type term) then zesu_select_add atoms term else ()
     else ()
   else ());
  local.

Ltac2 rec zesu_select_size (budget : int ref) (term : constr) : unit :=
  if Int.le (Ref.get budget) 0 then () else (
  Ref.set budget (Int.sub (Ref.get budget) 1);
  let visit := zesu_select_size budget in
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments => visit head; Array.iter visit arguments
  | Constr.Unsafe.Cast value _ typ => visit value; visit typ
  | Constr.Unsafe.Prod binder body => visit (Constr.Binder.type binder); visit body
  | Constr.Unsafe.Lambda binder body => visit (Constr.Binder.type binder); visit body
  | Constr.Unsafe.LetIn binder value body =>
      visit (Constr.Binder.type binder); visit value; visit body
  | Constr.Unsafe.Proj _ _ value => visit value
  | Constr.Unsafe.Case _ predicate _ value branches =>
      let (typ, _) := predicate in visit typ; visit value; Array.iter visit branches
  | _ => ()
  end).

Ltac2 zesu_select_small (limit : int) (term : constr) : bool :=
  let budget := Ref.ref (Int.add limit 1) in
  zesu_select_size budget term;
  Int.gt (Ref.get budget) 0.

Ltac2 zesu_select_goal_facts (depth : int) (cap : int) (limit : int) :=
  let hyps := Control.hyps () in
  let props := List.filter (fun declaration =>
    let (_, body, typ) := declaration in
    match body with
    | None => Constr.equal (Constr.type typ) constr:(Prop)
    | Some _ => false
    end) hyps in
  let eligible := List.filter (fun declaration =>
    let (_, _, typ) := declaration in
    if Constr.has_evar typ then false else zesu_select_small limit typ) props in
  let facts := List.map (fun declaration =>
    let (name, _, typ) := declaration in
    let found := Ref.ref [] in
    let _ := zesu_select_atoms found typ in (name, Ref.get found)) (List.rev eligible) in
  let atoms := Ref.ref [] in
  let _ := zesu_select_atoms atoms (Control.goal ()) in
  let kept := Ref.ref [] in
  let rec round remaining :=
    if Int.le remaining 0 then () else (
    let current := Ref.get atoms in
    let fresh := List.filter (fun fact =>
      let (name, mine) := fact in
      if List.mem Ident.equal name (Ref.get kept) then false else
      List.exist (fun atom => List.exist (fun known => Constr.equal known atom) current) mine) facts in
    List.iter (fun fact =>
      let (name, mine) := fact in
      if Int.lt (List.length (Ref.get kept)) cap then (
        Ref.set kept (name :: Ref.get kept);
        List.iter (zesu_select_add atoms) mine)
      else ()) fresh;
    round (Int.sub remaining 1)) in
  round depth;
  (* Each clear commits. A failed solver call never retries the facts it dropped. *)
  List.iter (fun declaration =>
    let (name, _, _) := declaration in
    if List.mem Ident.equal name (Ref.get kept) then ()
    else match Control.case (fun () => Std.clear [name]) with
      | Val _ => ()
      | Err _ => ()
      end) (List.rev props).

Ltac zesu_select_goal_facts := ltac2:(zesu_select_goal_facts 2 48 2048).
Ltac zesu_solve_goal_selected site closer :=
  solve [once zesu_select_goal_facts;
    ZesuSsz.Automation2.SearchBudget.zesu_solve_selected site closer].
(* A fact above the node limit is not a solver input. *)
Ltac zesu_small_fact term :=
  let check := ltac2:(fact |-
    if zesu_select_small 2048 (Option.get (Ltac1.to_constr fact)) then ()
    else Control.zero (Tactic_failure None)) in
  check term.
