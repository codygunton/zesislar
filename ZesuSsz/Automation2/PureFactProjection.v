From Coq Require Import Lists.List ZArith.ZArith.
From stdpp.bitvector Require Import definitions.
From Ltac2 Require Import Ltac2 Ref List Int Array Ident String Constant Ind.
Require Import ZesuSsz.Automation2.SearchBudget.
Set Default Proof Mode "Classic".

(* The owning hint umbrella marks heads. The core knows no contract names. *)
Polymorphic Class ZesuPureFactHead {A : Type} (head : A) : Prop :=
  zesu_pure_fact_head : True.
#[global] Typeclasses Opaque ZesuPureFactHead.

Ltac zesu_pure_head_marked head :=
  let registered := constr:(_ : @ZesuPureFactHead _ head) in
  assert_fails (has_evar registered).
Ltac zesu_pure_projection_pose evidence typ :=
  let name := fresh "HrangeFact" in assert (name : typ) by exact evidence.

Ltac2 zesu_projection_marked head :=
  Control.once (fun () => Control.plus (fun () =>
    Ltac1.apply (Ltac1.ref
      [@ZesuSsz; @Automation2; @PureFactProjection; @zesu_pure_head_marked])
      [Ltac1.of_constr head] Ltac1.run;
    true) (fun _ => false)).

Ltac2 rec zesu_projection_member value values :=
  match values with
  | [] => false
  | first :: rest =>
      if Constr.equal value first then true
      else zesu_projection_member value rest
  end.

Ltac2 zesu_projection_count failed remaining value :=
  SearchBudget.zesu_count_nodes failed remaining value;
  SearchBudget.zesu_budget_check failed.

(* Inspect structured scalar/list terms, but never descend into record data. *)
Ltac2 rec zesu_projection_syntax term :=
  let typ := Constr.type term in
  let inspect :=
    if Constr.equal typ constr:(Prop) then true else
    if Constr.equal typ constr:(Z) then true else
    if Constr.equal typ constr:(nat) then true else
    if Constr.equal typ constr:(N) then true else
    if Constr.equal typ constr:(bool) then true else
    lazy_match! typ with | list _ => true | bv _ => true | _ => false end in
  let children := if inspect then
    match Constr.Unsafe.kind term with
    | Constr.Unsafe.App _ args =>
        Array.fold_left (fun found arg =>
          List.append found (zesu_projection_syntax arg)) [] args
    | Constr.Unsafe.Cast value _ _ => zesu_projection_syntax value
    | _ => []
    end else [] in
  term :: children.

Ltac2 rec zesu_projection_open term :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Var _ => true
  | Constr.Unsafe.Rel _ => true
  | Constr.Unsafe.App _ args =>
      Array.fold_left (fun found arg =>
        Bool.or found (zesu_projection_open arg)) false args
  | Constr.Unsafe.Cast value _ _ => zesu_projection_open value
  | _ => false
  end.

Ltac2 zesu_projection_matches atoms typ :=
  let syntax := zesu_projection_syntax typ in
  List.exist (fun atom => zesu_projection_member atom syntax) atoms.

Ltac2 zesu_projection_selected name :=
  let text := Ident.to_string name in
  let prefix := "HrangeFact" in
  let rec same offset :=
    if Int.equal offset (String.length prefix) then true else
    if Int.ge offset (String.length text) then false else
    if Char.equal (String.get text offset) (String.get prefix offset)
    then same (Int.add offset 1) else false in
  same 0.

Ltac2 zesu_projection_atom term :=
  let typ := Constr.type term in
  let scalar :=
    if Constr.equal typ constr:(Z) then true else
    if Constr.equal typ constr:(nat) then true else
    if Constr.equal typ constr:(N) then true else
    if Constr.equal typ constr:(bool) then true else
    lazy_match! typ with | list _ => true | bv _ => true | _ => false end in
  Bool.and scalar (zesu_projection_open term).

(* A shared record argument is not an atom. Extend only explicit binder links. *)
Ltac2 zesu_projection_accessor term :=
  if Bool.neg (zesu_projection_open term) then false else
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Proj _ _ _ => true
  | Constr.Unsafe.App _ args =>
      if Int.equal (Array.length args) 1 then
        let argument := Array.get args 0 in
        let typ := Constr.type argument in
        if Constr.equal typ constr:(Prop) then false else
        if Constr.equal typ constr:(Z) then false else
        if Constr.equal typ constr:(nat) then false else
        if Constr.equal typ constr:(N) then false else
        if Constr.equal typ constr:(bool) then false else
        lazy_match! typ with | list _ => false | bv _ => false | _ => true end
      else false
  | _ => false
  end.

Ltac2 zesu_projection_binder term :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Var _ => zesu_projection_atom term
  | Constr.Unsafe.App head args =>
      match Constr.Unsafe.kind head with
      | Constr.Unsafe.Constant name _ =>
          match Constr.Unsafe.kind constr:(@bv_unsigned) with
          | Constr.Unsafe.Constant expected _ =>
              if Constant.equal name expected then
                match Constr.Unsafe.kind (Array.get args (Int.sub (Array.length args) 1)) with
                | Constr.Unsafe.Var _ => true
                | _ => false
                end
              else false
          | _ => false
          end
      | _ => false
      end
  | _ => false
  end.

Ltac2 zesu_projection_links (typ : constr) : constr list :=
  match Constr.Unsafe.kind typ with
  | Constr.Unsafe.App head args =>
      match Constr.Unsafe.kind head with
      | Constr.Unsafe.Ind name _ =>
          match Constr.Unsafe.kind constr:(@eq) with
          | Constr.Unsafe.Ind expected _ =>
              if Ind.equal name expected then (
                let lhs := Array.get args 1 in let rhs := Array.get args 2 in
                if Bool.or
                  (Bool.and (zesu_projection_binder lhs) (zesu_projection_accessor rhs))
                  (Bool.and (zesu_projection_binder rhs) (zesu_projection_accessor lhs))
                then [lhs; rhs] else [])
              else []
          | _ => []
          end
      | _ => []
      end
  | _ => []
  end.

(* Gathering changes no proof state. Refusal therefore commits no projections. *)
Ltac2 zesu_project_pure_facts_impl () :=
  let limit := fun value => SearchBudget.zesu_solver_limit value in
  let depth := limit constr:(SolverContextPolicy.zesu_projection_depth_limit) in
  let body_limit := limit constr:(SolverContextPolicy.zesu_projection_body_nodes_limit) in
  let generated := Ref.ref
    (limit constr:(SolverContextPolicy.zesu_projection_generated_nodes_limit)) in
  let inspected := Ref.ref
    (limit constr:(SolverContextPolicy.zesu_projection_inspected_nodes_limit)) in
  let fact_limit := limit constr:(SolverContextPolicy.zesu_solver_prop_limit) in
  let failed := Ref.ref false in
  let hypotheses := Control.hyps () in
  zesu_projection_count failed inspected (Control.goal ());
  List.iter (fun declaration => let (_, body, typ) := declaration in
    zesu_projection_count failed inspected typ;
    match body with
    | None => ()
    | Some value => zesu_projection_count failed inspected value
    end) hypotheses;
  let atoms := Ref.ref (List.filter zesu_projection_atom
    (zesu_projection_syntax (Control.goal ()))) in
  let visited := Ref.ref [] in
  let leaves := Ref.ref [] in
  let selected := Ref.ref [] in
  let selected_types := Ref.ref [] in
  List.iter (fun declaration => let (name, _, typ) := declaration in
    if zesu_projection_selected name then
      Ref.set selected_types (typ :: Ref.get selected_types) else ()) hypotheses;
  let rec project remaining evidence typ :=
    if Constr.has_evar typ then () else
    if zesu_projection_member typ (Ref.get visited) then () else (
      Ref.set visited (typ :: Ref.get visited);
      let keep := fun () => Ref.set leaves ((evidence, typ) :: Ref.get leaves) in
      match Constr.Unsafe.kind typ with
      | Constr.Unsafe.App head args =>
          if Constr.equal head constr:(and) then (
            let left := Array.get args 0 in let right := Array.get args 1 in
            project remaining constr:(@proj1 $left $right $evidence) left;
            project remaining constr:(@proj2 $left $right $evidence) right)
          else if zesu_projection_marked head then (
            if Int.equal remaining 0 then
              Control.zero (Tactic_failure
                (Some (Message.of_string "Pure projection exceeds marked head depth")))
            else ();
            match Constr.Unsafe.kind head with
            | Constr.Unsafe.Constant constant _ =>
                let exposed := Std.eval_cbv
                  { Std.rStrength := Std.Head; Std.rBeta := true;
                    Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
                    Std.rZeta := true; Std.rDelta := false;
                    Std.rConst := [Std.ConstRef constant] } typ in
                zesu_projection_count failed (Ref.ref body_limit) exposed;
                zesu_projection_count failed generated exposed;
                zesu_projection_count failed inspected exposed;
                project (Int.sub remaining 1) evidence exposed
            | _ => keep ()
            end)
          else keep ()
      | _ => keep ()
      end) in
  List.iter (fun declaration => let (name, _, typ) := declaration in
    if Constr.equal (Constr.type typ) constr:(Prop) then
      project depth (Control.hyp name) typ else ()) hypotheses;
  let rec select remaining :=
    if Int.equal remaining 0 then () else (
      List.iter (fun pair => let (evidence, typ) := pair in
        if zesu_projection_matches (Ref.get atoms) typ then (
          if zesu_projection_member typ (Ref.get selected_types) then () else (
            if Int.ge (List.length (Ref.get selected_types)) fact_limit then
              Control.zero (Tactic_failure
                (Some (Message.of_string "Pure projection exceeds selected Prop limit")))
            else ();
            zesu_projection_count failed generated typ;
            Ref.set selected ((evidence, typ) :: Ref.get selected);
            Ref.set selected_types (typ :: Ref.get selected_types);
            List.iter (fun atom =>
              if zesu_projection_member atom (Ref.get atoms) then () else
                Ref.set atoms (atom :: Ref.get atoms))
              (zesu_projection_links typ))) else ())
        (List.rev (Ref.get leaves));
      select (Int.sub remaining 1)) in
  select depth;
  List.iter (fun pair => let (evidence, typ) := pair in
    Ltac1.apply (Ltac1.ref
      [@ZesuSsz; @Automation2; @PureFactProjection; @zesu_pure_projection_pose])
      [Ltac1.of_constr evidence; Ltac1.of_constr typ] Ltac1.run)
    (List.rev (Ref.get selected)).

Ltac2 zesu_project_pure_facts () :=
  Control.plus zesu_project_pure_facts_impl (fun error =>
    Message.print (Message.of_string "Pure projection refused; input state preserved");
    Message.print (Message.of_exn error);
    Control.zero error).

Ltac zesu_project_pure_facts := ltac2:(zesu_project_pure_facts ()).

Ltac2 zesu_projection_isolate () :=
  let erased := List.fold_left (fun erased declaration =>
    let (name, _, typ) := declaration in
    if Constr.equal (Constr.type typ) constr:(Prop) then
      if zesu_projection_selected name then erased else name :: erased
    else erased) [] (Control.hyps ()) in
  Std.clear erased.

Ltac zesu_projected_context closer :=
  tryif solve [zesu_project_pure_facts;
    ltac2:(zesu_projection_isolate ());
    SearchBudget.zesu_solve_selected ("pure projection"%string) closer]
  then idtac
  else fail 0 "Selected pure projection refused; input state preserved".
