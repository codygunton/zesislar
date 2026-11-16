Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.ContextCollection.
(* Scratch arithmetic relevance: record fields do not share one variable key. *)
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 a3n_member (term : constr) (terms : constr list) :=
  List.exist (Constr.equal term) terms.
Ltac2 a3n_add (terms : constr list) (term : constr) :=
  if a3n_member term terms then terms else term :: terms.
Ltac2 a3n_union (left : constr list) (right : constr list) :=
  List.fold_left a3n_add left right.
Ltac2 a3n_record_variable (term : constr) :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Var _ =>
    let ty := Constr.type term in
    lazy_match! ty with
    | bv _ => false
    | _ =>
      let head := match Constr.Unsafe.kind ty with
        | Constr.Unsafe.App head _ => head | _ => ty end in
      match Constr.Unsafe.kind head with
      | Constr.Unsafe.Ind ind _ => Int.equal (Ind.nconstructors (Ind.data ind)) 1
      | _ => false
      end
    end
  | _ => false
  end.
Ltac2 a3n_record_name (records : ident list) (term : constr) :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Var name => ZesuSsz.Automation2.ContextCollection.zesu_context_member name records
  | _ => false
  end.
Ltac2 rec a3n_keys (records : ident list) (term : constr) :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Var _ => [term]
  | Constr.Unsafe.Rel _ => []
  | Constr.Unsafe.Sort _ => []
  | Constr.Unsafe.Constant _ _ => []
  | Constr.Unsafe.Ind _ _ => []
  | Constr.Unsafe.Constructor _ _ => []
  | Constr.Unsafe.Uint63 _ => []
  | Constr.Unsafe.Float _ => []
  | Constr.Unsafe.App head arguments =>
      let record := Array.fold_left (fun found argument =>
        if found then true else a3n_record_name records argument) false arguments in
      if record then [term] else
        Array.fold_left (fun found argument => a3n_union found (a3n_keys records argument))
          (a3n_keys records head) arguments
  | Constr.Unsafe.Cast body _ ty => a3n_union (a3n_keys records body) (a3n_keys records ty)
  | Constr.Unsafe.Prod binder body =>
      a3n_union (a3n_keys records (Constr.Binder.type binder)) (a3n_keys records body)
  | Constr.Unsafe.Lambda binder body =>
      a3n_union (a3n_keys records (Constr.Binder.type binder)) (a3n_keys records body)
  | Constr.Unsafe.LetIn binder value body =>
      a3n_union (a3n_keys records (Constr.Binder.type binder))
        (a3n_union (a3n_keys records value) (a3n_keys records body))
  | Constr.Unsafe.Proj _ _ body =>
      if a3n_record_name records body then [term] else a3n_keys records body
  | _ => Control.zero (Tactic_failure None)
  end.
Ltac2 rec a3n_relevance (facts : (ident * constr list) list)
    (keys : constr list) (names : ident list) :=
  let (next_keys, next_names) := List.fold_left (fun found fact =>
    let (found_keys, found_names) := found in
    let (name, variables) := fact in
    if ZesuSsz.Automation2.ContextCollection.zesu_context_member name found_names then found
    else if Bool.or (Int.equal (List.length variables) 0)
        (List.exist (fun term => a3n_member term found_keys) variables) then
      (a3n_union found_keys variables, name :: found_names)
    else found) (keys, names) facts in
  if Int.equal (List.length next_names) (List.length names) then next_names
  else a3n_relevance facts next_keys next_names.
(* A local definition stands for its body: a key that names one also brings
   the keys of its body, so facts about the fields behind it stay relevant. *)
Ltac2 rec a3n_unfold_keys (records : ident list)
    (hyps : (ident * constr option * constr) list) (keys : constr list) :=
  let next := List.fold_left (fun found key =>
    match Constr.Unsafe.kind key with
    | Constr.Unsafe.Var name =>
        List.fold_left (fun found declaration =>
          let (other, body, _) := declaration in
          if Ident.equal name other then
            match body with
            | Some value => a3n_union found (a3n_keys records value)
            | None => found
            end
          else found) found hyps
    | _ => found
    end) keys keys in
  if Int.equal (List.length next) (List.length keys) then keys
  else a3n_unfold_keys records hyps next.
Ltac2 a3n_prune () :=
  let hyps := Control.hyps () in
  let target := Control.goal () in
  if Constr.has_evar target then Control.zero (Tactic_failure None) else ();
  List.iter (fun declaration =>
    let (_, body, ty) := declaration in
    if Constr.has_evar ty then Control.zero (Tactic_failure None) else ();
    match body with None => () | Some value =>
      if Constr.has_evar value then Control.zero (Tactic_failure None) else () end) hyps;
  (* Types stay fixed until the final clear. Classify each local once. *)
  let records := List.fold_left (fun found declaration =>
    let (name, _, _) := declaration in
    if a3n_record_variable (Constr.Unsafe.make (Constr.Unsafe.Var name))
    then name :: found else found) [] hyps in
  let facts := List.fold_left (fun found declaration =>
    let (name, body, ty) := declaration in
    match body with Some _ => found | None =>
      if ZesuSsz.Automation2.ContextCollection.zesu_context_proposition ty
      then (name, a3n_unfold_keys records hyps (a3n_keys records ty)) :: found else found end) [] hyps in
  let relevant := a3n_relevance facts (a3n_unfold_keys records hyps (a3n_keys records target)) [] in
  let kept := List.fold_left (fun names declaration =>
    let (name, body, ty) := declaration in
    match body with
    | Some _ => ZesuSsz.Automation2.ContextCollection.zesu_context_add names name
    | None => if ZesuSsz.Automation2.ContextCollection.zesu_context_proposition ty then names
        else ZesuSsz.Automation2.ContextCollection.zesu_context_add names name
    end) relevant hyps in
  let kept := ZesuSsz.Automation2.ContextCollection.zesu_context_dependencies hyps kept in
  List.iter (fun declaration =>
    let (name, _, _) := declaration in
    if ZesuSsz.Automation2.ContextCollection.zesu_context_member name kept then ()
    else Std.clear [name]) (List.rev hyps).
