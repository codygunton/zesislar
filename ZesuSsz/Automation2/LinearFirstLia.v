From Coq Require Import ZArith.ZArith micromega.Lia micromega.Zify omega.PreOmega.
From Ltac2 Require Ltac2.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

Ltac zesu_zify_prefix :=
  intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs);
  Zify.zify_to_euclidean_division_equations.

Ltac zesu_lia_has_divmod :=
  match goal with
  | |- context [Z.div _ _] => idtac
  | |- context [Z.modulo _ _] => idtac
  | |- context [Z.quot _ _] => idtac
  | |- context [Z.rem _ _] => idtac
  | _ : context [Z.div _ _] |- _ => idtac
  | _ : context [Z.modulo _ _] |- _ => idtac
  | _ : context [Z.quot _ _] |- _ => idtac
  | _ : context [Z.rem _ _] |- _ => idtac
  end.

Inductive zesu_divmod_done (x y : Z) : Prop := zesu_divmod_done_intro.

Ltac zesu_zlit t :=
  lazymatch t with
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
  | Z.pow ?a ?b => zesu_zlit a; zesu_zlit b
  | Z.add ?a ?b => zesu_zlit a; zesu_zlit b
  | Z.sub ?a ?b => zesu_zlit a; zesu_zlit b
  | Z.mul ?a ?b => zesu_zlit a; zesu_zlit b
  | Z.opp ?a => zesu_zlit a
  | Z.of_N ?n => lazymatch n with N0 => idtac | Npos _ => idtac end
  | Z.of_nat ?n => zesu_nlit n
  end
with zesu_nlit t :=
  lazymatch t with
  | O => idtac | S ?n => zesu_nlit n
  end.

Ltac zesu_poslit y :=
  zesu_zlit y; assert_succeeds (assert (0 < y) by exact (proj1 (Z.ltb_lt 0 y) eq_refl)).

Ltac zesu_divmod_all_literal :=
  assert_fails (idtac; match goal with
  | |- context [Z.div _ ?y] => assert_fails (idtac; zesu_poslit y)
  | |- context [Z.modulo _ ?y] => assert_fails (idtac; zesu_poslit y)
  | _ : context [Z.div _ ?y] |- _ => assert_fails (idtac; zesu_poslit y)
  | _ : context [Z.modulo _ ?y] |- _ => assert_fails (idtac; zesu_poslit y)
  | |- context [Z.quot _ _] => idtac
  | |- context [Z.rem _ _] => idtac
  | _ : context [Z.quot _ _] |- _ => idtac
  | _ : context [Z.rem _ _] |- _ => idtac
  end).

Ltac zesu_divmod_fact x y :=
  lazymatch goal with
  | _ : zesu_divmod_done x y |- _ => fail
  | _ =>
    let Hpos := fresh "Hpos" in
    assert (Hpos : 0 < y) by exact (proj1 (Z.ltb_lt 0 y) eq_refl);
    pose proof (Z.div_mod x y (Z.neq_sym _ _ (Z.lt_neq _ _ Hpos)));
    pose proof (Z.mod_pos_bound x y Hpos);
    clear Hpos;
    pose proof (zesu_divmod_done_intro x y)
  end.

Ltac zesu_divmod_literal_facts :=
  repeat match goal with
  | |- context [Z.div ?x ?y] => zesu_divmod_fact x y
  | |- context [Z.modulo ?x ?y] => zesu_divmod_fact x y
  | _ : context [Z.div ?x ?y] |- _ => zesu_divmod_fact x y
  | _ : context [Z.modulo ?x ?y] |- _ => zesu_divmod_fact x y
  end.

Inductive zesu_divmod_seen (t : Z) : Prop := zesu_divmod_seen_intro.

Ltac zesu_divmod_mark t :=
  lazymatch goal with
  | _ : zesu_divmod_seen t |- _ => fail
  | _ => pose proof (zesu_divmod_seen_intro t)
  end.

Ltac zesu_divmod_mark_all :=
  repeat match goal with
  | |- context [Z.div ?x ?y] => zesu_divmod_mark (Z.div x y)
  | |- context [Z.modulo ?x ?y] => zesu_divmod_mark (Z.modulo x y)
  | |- context [Z.quot ?x ?y] => zesu_divmod_mark (Z.quot x y)
  | |- context [Z.rem ?x ?y] => zesu_divmod_mark (Z.rem x y)
  | _ : context [Z.div ?x ?y] |- _ => zesu_divmod_mark (Z.div x y)
  | _ : context [Z.modulo ?x ?y] |- _ => zesu_divmod_mark (Z.modulo x y)
  | _ : context [Z.quot ?x ?y] |- _ => zesu_divmod_mark (Z.quot x y)
  | _ : context [Z.rem ?x ?y] |- _ => zesu_divmod_mark (Z.rem x y)
  end.

Ltac2 zesu_divmod_count () : Ltac2.Init.int :=
  Ltac2.List.length (Ltac2.List.filter (fun h =>
    let (_, _, ty) := h in
    match Ltac2.Constr.Unsafe.kind ty with
    | Ltac2.Constr.Unsafe.App f _ => Ltac2.Constr.equal f constr:(zesu_divmod_seen)
    | _ => Ltac2.Init.false
    end) (Ltac2.Control.hyps ())).

Ltac2 zesu_divmod_bound () : Ltac2.Init.int := 24.

Ltac2 zesu_divmod_within_bound () :=
  if Ltac2.Int.gt (zesu_divmod_count ()) (zesu_divmod_bound ())
  then Ltac2.Control.zero (Ltac2.Init.Tactic_failure Ltac2.Init.None) else ().

Ltac zesu_divmod_guard :=
  assert_succeeds (zesu_divmod_mark_all; ltac2:(zesu_divmod_within_bound ())).

Ltac zesu_lia_divmod_step :=
  first [ zesu_divmod_all_literal; zesu_divmod_literal_facts
        | zesu_divmod_guard; Zify.zify_post_hook ].

Ltac zesu_lia_linear_first3 :=
  zesu_zify_prefix;
  first [ solve [Zify.zify_saturate; xlia Lia.zchecker]
        | zesu_lia_has_divmod;
          zesu_lia_divmod_step; Zify.zify_saturate; xlia Lia.zchecker ].

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* Linear arithmetic interprets these heads. Every other term is one atom. *)
Ltac2 zesu_linear_heads () :=
  [constr:(Z.add); constr:(Z.sub); constr:(Z.mul); constr:(Z.opp); constr:(Z.succ);
   constr:(Z.pred); constr:(Z.pow); constr:(Z.max); constr:(Z.min); constr:(Z.abs);
   constr:(Z.modulo); constr:(Z.div); constr:(Z.quot); constr:(Z.rem);
   constr:(Z.of_nat); constr:(Z.of_N); constr:(Z.to_nat); constr:(Z.to_N);
   constr:(Nat.add); constr:(Nat.sub); constr:(Nat.mul); constr:(Nat.pred);
   constr:(Nat.min); constr:(Nat.max); constr:(N.add); constr:(N.sub); constr:(N.mul);
   constr:(N.of_nat); constr:(N.to_nat); constr:(Z.le); constr:(Z.lt); constr:(Z.ge);
   constr:(Z.gt); constr:(le); constr:(lt); constr:(ge); constr:(gt); constr:(N.le);
   constr:(N.lt); constr:(and); constr:(or); constr:(not); constr:(iff)].

Ltac2 zesu_linear_member (term : constr) (terms : constr list) :=
  List.exist (Constr.equal term) terms.

Ltac2 zesu_linear_add (terms : constr list) (term : constr) :=
  if zesu_linear_member term terms then terms else term :: terms.

(* Constants, constructors, and bound variables carry no atom. *)
Ltac2 rec zesu_linear_atoms (heads : constr list) (term : constr) (found : constr list) :=
  let visit := Array.fold_left (fun found argument =>
    zesu_linear_atoms heads argument found) found in
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Rel _ => found
  | Constr.Unsafe.Sort _ => found
  | Constr.Unsafe.Constant _ _ => found
  | Constr.Unsafe.Constructor _ _ => found
  | Constr.Unsafe.Ind _ _ => found
  | Constr.Unsafe.Cast body _ _ => zesu_linear_atoms heads body found
  | Constr.Unsafe.Prod binder body =>
      zesu_linear_atoms heads body (zesu_linear_atoms heads (Constr.Binder.type binder) found)
  | Constr.Unsafe.App head arguments =>
      if Constr.equal head constr:(@eq) then
        zesu_linear_atoms heads (Array.get arguments 2)
          (zesu_linear_atoms heads (Array.get arguments 1) found)
      else match Constr.Unsafe.kind head with
      | Constr.Unsafe.Constructor _ _ => visit arguments
      | _ => if zesu_linear_member head heads then visit arguments
             else zesu_linear_add found term
      end
  | _ => zesu_linear_add found term
  end.

(* A fact without atoms stays: it can close the goal by itself. Linking runs
   at most `rounds` rounds: a fact reached only through longer chains is
   unrelated. *)
Ltac2 rec zesu_linear_unlinked (rounds : int) (facts : (ident * constr list) list) (linked : constr list) :=
  let (linked, rest, changed) := List.fold_left (fun state fact =>
    let (linked, rest, changed) := state in
    let (_, atoms) := fact in
    if Bool.or (Int.equal (List.length atoms) 0)
         (List.exist (fun atom => zesu_linear_member atom linked) atoms)
    then (List.fold_left zesu_linear_add linked atoms, rest, true)
    else (linked, fact :: rest, changed)) (linked, [], false) facts in
  if Bool.and changed (Int.lt 1 rounds) then zesu_linear_unlinked (Int.sub rounds 1) rest linked
  else List.map (fun fact => let (name, _) := fact in name) rest.

(* The budget left after the nodes of a term, stopping at zero. One pass
   without a reference cell or a closure per node. Every Ltac2 call and
   binding costs an environment insertion, so a leaf head and one or two
   arguments take no extra call: a 120005-node term walks in 190 ms instead
   of 370 ms. *)
Ltac2 rec zesu_linear_remaining (budget : int) (term : constr) : int :=
  if Int.le budget 0 then budget else
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      let budget := match Constr.Unsafe.kind head with
        | Constr.Unsafe.Constant _ _ => Int.sub budget 2
        | Constr.Unsafe.Constructor _ _ => Int.sub budget 2
        | Constr.Unsafe.Ind _ _ => Int.sub budget 2
        | Constr.Unsafe.Var _ => Int.sub budget 2
        | _ => zesu_linear_remaining (Int.sub budget 1) head
        end in
      let length := Array.length arguments in
      if Int.equal length 2 then
        zesu_linear_remaining (zesu_linear_remaining budget (Array.get arguments 0)) (Array.get arguments 1)
      else if Int.equal length 1 then zesu_linear_remaining budget (Array.get arguments 0)
      else zesu_linear_remaining_arguments budget arguments 0 length
  | Constr.Unsafe.Prod binder body =>
      zesu_linear_remaining (zesu_linear_remaining (Int.sub budget 1) (Constr.Binder.type binder)) body
  | Constr.Unsafe.Lambda binder body =>
      zesu_linear_remaining (zesu_linear_remaining (Int.sub budget 1) (Constr.Binder.type binder)) body
  | Constr.Unsafe.LetIn binder value body =>
      zesu_linear_remaining
        (zesu_linear_remaining (zesu_linear_remaining (Int.sub budget 1) (Constr.Binder.type binder)) value) body
  | Constr.Unsafe.Cast value _ typ => zesu_linear_remaining (zesu_linear_remaining (Int.sub budget 1) value) typ
  | _ => Int.sub budget 1
  end
with zesu_linear_remaining_arguments (budget : int) (arguments : constr array) (index : int) (length : int) : int :=
  if Int.equal index length then budget
  else zesu_linear_remaining_arguments
         (zesu_linear_remaining budget (Array.get arguments index)) arguments (Int.add index 1) length.

Ltac2 rec zesu_linear_codomain (typ : constr) (count : int) : constr option :=
  if Int.equal count 0 then Some typ else
  match Constr.Unsafe.kind typ with
  | Constr.Unsafe.Prod _ body => zesu_linear_codomain body (Int.sub count 1)
  | _ => None
  end.

(* A statement is a proposition. An application's sort is read off its head's
   type, so only the head is typed; other statements are typed whole. Typing
   every fact whole cost about 45 ms per call on a 267-fact context. *)
Ltac2 zesu_linear_is_prop (statement : constr) : bool :=
  let sort :=
    match Constr.Unsafe.kind statement with
    | Constr.Unsafe.App head arguments =>
        match zesu_linear_codomain (Constr.type head) (Array.length arguments) with
        | Some result =>
            match Constr.Unsafe.kind result with
            | Constr.Unsafe.Sort _ => result
            | _ => Constr.type statement
            end
        | None => Constr.type statement
        end
    | _ => Constr.type statement
    end in
  Constr.equal sort constr:(Prop).

(* Linking rounds and the node budget of the goal and the facts kept. *)
Ltac2 zesu_linear_rounds () := 2.
Ltac2 zesu_linear_node_budget () := 16384.

(* Clear the facts that share no linear atom with the goal, directly or
   through other facts within the linking rounds. Fail when the goal has no
   atom, nothing is clear, or the goal and the kept facts exceed the node
   budget: on a decodeParentHeader slice premise the unbounded closure kept
   58 facts of 66555 nodes, and `xlia` on them grew past 24 GiB. *)
Ltac2 zesu_linear_clear_unrelated () :=
  let heads := zesu_linear_heads () in
  let goal_atoms := zesu_linear_atoms heads (Control.goal ()) [] in
  if Int.equal (List.length goal_atoms) 0 then Control.zero (Tactic_failure None) else ();
  let unrelated := zesu_linear_unlinked (zesu_linear_rounds ()) (List.fold_left (fun facts declaration =>
    let (name, body, typ) := declaration in
    match body with
    | Some _ => facts
    | None =>
        if zesu_linear_is_prop typ
        then (name, zesu_linear_atoms heads typ []) :: facts else facts
    end) [] (Control.hyps ())) goal_atoms in
  if Int.equal (List.length unrelated) 0 then Control.zero (Tactic_failure None) else ();
  let budget := zesu_linear_remaining (zesu_linear_node_budget ()) (Control.goal ()) in
  let budget := List.fold_left (fun budget declaration =>
    let (name, body, typ) := declaration in
    match body with
    | Some _ => budget
    | None =>
        if Int.le budget 0 then budget
        else if List.exist (Ident.equal name) unrelated then budget
        else if zesu_linear_is_prop typ then zesu_linear_remaining budget typ
        else budget
    end) budget (Control.hyps ()) in
  if Int.le budget 0 then Control.zero (Tactic_failure None) else ();
  (* Each clear commits, so a failed call never retries clear combinations. *)
  List.iter (fun name =>
    match Control.case (fun () => Std.clear [name]) with
    | Val _ => ()
    | Err _ => ()
    end) unrelated.

(* The library solver on the facts linked to the goal. *)
Ltac zesu_lia_linked_facts :=
  once ltac2:(zesu_linear_clear_unrelated ()); Zify.zify; xlia Lia.zchecker.

(* The goal and every Prop fact fit a node budget. Guards a solver call on the
   whole context: on the decodeItem blocks every whole-context `lia` that
   succeeded ran on at most 26708 nodes (16384 lost a closure), while failing
   ones reached 212738 nodes. Guards a solver call on the pruned context with a
   larger budget: pruned closures on the decodeItem blocks reached 64499
   nodes (32768 lost 5 blocks), while on decodeParentHeader 0300's final pure
   tail pruned contexts of 136615 nodes and more grew past 8 GiB. *)
Ltac2 zesu_linear_context_node_budget () := 32768.
Ltac2 zesu_linear_pruned_context_node_budget () := 98304.

Ltac2 rec zesu_linear_facts_remaining (budget : int) (hyps : (ident * constr option * constr) list) : int :=
  if Int.le budget 0 then budget else
  match hyps with
  | [] => budget
  | declaration :: rest =>
      let (_, body, typ) := declaration in
      match body with
      | Some _ => zesu_linear_facts_remaining budget rest
      | None =>
          if zesu_linear_is_prop typ
          then zesu_linear_facts_remaining (zesu_linear_remaining budget typ) rest
          else zesu_linear_facts_remaining budget rest
      end
  end.

Ltac2 zesu_linear_context_within (nodes : int) :=
  let budget := zesu_linear_remaining nodes (Control.goal ()) in
  if Int.le (zesu_linear_facts_remaining budget (Control.hyps ())) 0
  then Control.zero (Tactic_failure None) else ().

Ltac zesu_lia_context_within_budget :=
  ltac2:(zesu_linear_context_within (zesu_linear_context_node_budget ())).
Ltac zesu_lia_pruned_context_within_budget :=
  ltac2:(zesu_linear_context_within (zesu_linear_pruned_context_node_budget ())).
