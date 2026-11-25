From Coq Require Import ZArith.ZArith micromega.Lia micromega.Zify omega.PreOmega.
From Ltac2 Require Ltac2.
Require Import ZesuSsz.Automation2.Telemetry.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

Ltac zesu_zify_prefix :=
  let run := ltac2:(tac |- zesu_telemetry_ltac1 "zify" "zesu_zify_prefix" tac) in
  run ltac:(intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs);
    Zify.zify_to_euclidean_division_equations).

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
  let run_xlia := ltac2:(tac |- zesu_telemetry_ltac1 "xlia" "zesu_lia_linear_first3" tac) in
  let run_saturate :=
    ltac2:(tac |- zesu_telemetry_ltac1 "zify_saturate" "zesu_lia_linear_first3" tac) in
  zesu_zify_prefix;
  first [ solve [run_saturate ltac:(Zify.zify_saturate); run_xlia ltac:(xlia Lia.zchecker)]
        | zesu_lia_has_divmod;
          zesu_lia_divmod_step; run_saturate ltac:(Zify.zify_saturate);
          run_xlia ltac:(xlia Lia.zchecker) ].

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

(* A numeral, or a power of two numerals (the bitvector modulus `2 ^ 64`).
   Narrower than `zesu_zlit`, which accepts `2 ^ Z.of_N 128` and
   `2 ^ (8 * Z.of_nat 7)`: exactly the divisors this closer must refuse. *)
Ltac zesu_probe_numeral t :=
  lazymatch t with
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
  | Z.pow ?b ?e => zesu_probe_numeral b; zesu_probe_numeral e
  end.

(* Neither the goal nor a fact divides by a term that is not a numeral.
   `Zify.zify` pulls every `div`/`mod` out of the context, also those inside
   list terms linear arithmetic treats as atoms; with a divisor such as
   `2 ^ Z.of_N 128` each becomes case-split implications and `xlia` grew to
   8 GiB without returning (berlinGasCalc 3f00, 3edc, nextUint64 00b8). *)
Ltac zesu_no_symbolic_divisor :=
  assert_fails (idtac; match goal with
  | |- context [Z.div _ ?y] => assert_fails (idtac; zesu_probe_numeral y)
  | |- context [Z.modulo _ ?y] => assert_fails (idtac; zesu_probe_numeral y)
  | _ : context [Z.div _ ?y] |- _ => assert_fails (idtac; zesu_probe_numeral y)
  | _ : context [Z.modulo _ ?y] |- _ => assert_fails (idtac; zesu_probe_numeral y)
  end).

(* The library solver on the facts linked to the goal, refused when a linked
   fact or the goal divides by a term that is not a numeral, or when they
   hold more distinct divisions and remainders than the linear-first path
   accepts (`zesu_divmod_guard`). txAccessList 0264 (bench r53) spent the rest
   of the 3600 s cap here on a 4,922-node goal with 37 distinct remainders
   (the unfolded bit-vector wraps of one address); on that block's other 37
   calls the goal and facts held at most 5, and each ended within 0.04 s. *)
Ltac zesu_lia_linked_facts :=
  let run_zify := ltac2:(tac |- zesu_telemetry_ltac1 "zify" "zesu_lia_linked_facts" tac) in
  let run_xlia := ltac2:(tac |- zesu_telemetry_ltac1 "xlia" "zesu_lia_linked_facts" tac) in
  once ltac2:(zesu_linear_clear_unrelated ()); zesu_no_symbolic_divisor;
  zesu_divmod_guard;
  run_zify ltac:(Zify.zify);
  run_xlia ltac:(xlia Lia.zchecker).

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

(* The binary digits of a positive literal; -1 for any other term. *)
Ltac2 rec zesu_linear_positive_bits (term : constr) : int :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      if Bool.and (Int.equal (Array.length arguments) 1)
           (Bool.or (Constr.equal head constr:(xO)) (Constr.equal head constr:(xI)))
      then
        let bits := zesu_linear_positive_bits (Array.get arguments 0) in
        if Int.lt bits 0 then -1 else Int.add bits 1
      else -1
  | _ => if Constr.equal term constr:(xH) then 1 else -1
  end.

(* A machine-word wrap divides by `2 ^ w` (or by a literal of more than 32
   binary digits): `bv_unsigned` of a sum or a sign view unfolds to such a
   remainder, and the facts in that form carry the address bounds. *)
Ltac2 zesu_linear_wrap_divisor (divisor : constr) : bool :=
  match Constr.Unsafe.kind divisor with
  | Constr.Unsafe.App head arguments =>
      if Constr.equal head constr:(Z.pow) then true
      else if Bool.and (Constr.equal head constr:(Zpos)) (Int.equal (Array.length arguments) 1)
      then Int.lt 32 (zesu_linear_positive_bits (Array.get arguments 0))
      else false
  | _ => false
  end.

(* A term without variables (a constant such as `2 ^ 128 / 2`). *)
Ltac2 rec zesu_linear_constant (term : constr) : bool :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Var _ => false
  | Constr.Unsafe.Rel _ => false
  | Constr.Unsafe.Evar _ _ => false
  | Constr.Unsafe.App head arguments =>
      if zesu_linear_constant head then Array.for_all zesu_linear_constant arguments else false
  | Constr.Unsafe.Constant _ _ => true
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.Ind _ _ => true
  | _ => false
  end.

(* Whether a term divides: `Z.divide`, or `Z.div`, `Z.modulo`, `Z.quot`,
   `Z.rem` of a non-constant by anything but a wrap divisor, anywhere in it. *)
Ltac2 rec zesu_linear_divides (term : constr) : bool :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      if Constr.equal head constr:(Z.divide) then true
      else if (if List.exist (Constr.equal head)
                    [constr:(Z.div); constr:(Z.modulo); constr:(Z.quot); constr:(Z.rem)]
               then
                 if Int.equal (Array.length arguments) 2
                 then Bool.neg (if zesu_linear_wrap_divisor (Array.get arguments 1) then true
                                else zesu_linear_constant term)
                 else true
               else false)
      then true
      else if zesu_linear_divides head then true
      else Array.exist zesu_linear_divides arguments
  | Constr.Unsafe.Prod binder body =>
      if zesu_linear_divides (Constr.Binder.type binder) then true
      else zesu_linear_divides body
  | Constr.Unsafe.Cast value _ _ => zesu_linear_divides value
  | _ => false
  end.

(* On a goal that does not divide, clear the facts that do. Zify turns each
   division, remainder and divisibility into fresh integer variables with
   bounds, and on an unprovable goal the solver's branch and bound over them
   did not end: txAccessList 0248 and 048c (bench r53) each spent the rest
   of the 3600 s cap in one whole-context call on `2684354560 <=
   arrayListPointer l` (92 and 103 facts; 2 to 5 of them divide). Without the
   dividing facts the same calls fail in 0.3 s; on every whole-context call
   of those blocks and of 0264 that succeeded, the call without them
   succeeded too (diag P/Q runs, rules11 handoff). A goal `False` keeps
   every fact: a refutation may rest on a dividing fact alone
   (keysEnsureCapacity Block0164's residual closes `False` from a size
   quotient). So does a goal with any integer division, remainder or bit
   operation, wraps included (`zesu_linear_bit_arithmetic`): zify turns
   shifts and masks into divisions, and a byte-image residual (decodeItem
   Block800d6a40) closes its shifted bytes from remainder facts. *)
Ltac2 rec zesu_linear_bit_arithmetic (term : constr) : bool :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      if List.exist (Constr.equal head)
           [constr:(Z.div); constr:(Z.modulo); constr:(Z.quot); constr:(Z.rem);
            constr:(Z.divide); constr:(Z.shiftr); constr:(Z.shiftl); constr:(Z.land);
            constr:(Z.lor); constr:(Z.lxor); constr:(Z.ldiff); constr:(Z.testbit);
            constr:(Z.ones)]
      then true
      else if zesu_linear_bit_arithmetic head then true
      else Array.exist zesu_linear_bit_arithmetic arguments
  | Constr.Unsafe.Prod binder body =>
      if zesu_linear_bit_arithmetic (Constr.Binder.type binder) then true
      else zesu_linear_bit_arithmetic body
  | Constr.Unsafe.Cast value _ _ => zesu_linear_bit_arithmetic value
  | _ => false
  end.

Ltac2 zesu_linear_clear_dividing_facts () :=
  if Constr.equal (Control.goal ()) constr:(False) then () else
  if zesu_linear_bit_arithmetic (Control.goal ()) then () else
  List.iter (fun (name, body, typ) =>
    match body with
    | Some _ => ()
    | None =>
        if zesu_linear_is_prop typ then
          if zesu_linear_divides typ then
            match Control.case (fun () => Std.clear [name]) with
            | Val _ => () | Err _ => ()
            end
          else ()
        else ()
    end) (Control.hyps ()).

Ltac zesu_lia_clear_dividing_facts := ltac2:(zesu_linear_clear_dividing_facts ()).

(* The distinct `Z.div`, `Z.modulo`, `Z.quot` and `Z.rem` subterms of a term. *)
Ltac2 rec zesu_linear_division_terms (found : constr list) (term : constr) : constr list :=
  let found :=
    match Constr.Unsafe.kind term with
    | Constr.Unsafe.App head arguments =>
        if Bool.and (Int.equal (Array.length arguments) 2)
             (List.exist (Constr.equal head)
                [constr:(Z.div); constr:(Z.modulo); constr:(Z.quot); constr:(Z.rem)])
        then (if List.exist (Constr.equal term) found then found else term :: found)
        else found
    | _ => found
    end in
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      Array.fold_left zesu_linear_division_terms (zesu_linear_division_terms found head) arguments
  | Constr.Unsafe.Prod binder body =>
      zesu_linear_division_terms
        (zesu_linear_division_terms found (Constr.Binder.type binder)) body
  | Constr.Unsafe.Cast value _ _ => zesu_linear_division_terms found value
  | _ => found
  end.

(* On a large context (40 or more facts), a goal with more distinct
   divisions and remainders than the linear-first path accepts
   (`zesu_divmod_bound`) goes to no whole-context run: txAccessList 0264
   (bench r53, r56) spent the rest of its cap in one xlia call on a
   4,922-node goal with 37 distinct remainders and 129 facts after zify. A
   small context keeps such a goal: decodeItem Block800d6a40's residual
   proves a byte-reassembly identity with about 30 nested remainders in
   0.03 s. *)
Ltac2 zesu_linear_large_context_divisions_within () :=
  let facts := List.length (List.filter (fun (_, body, typ) =>
    match body with
    | Some _ => false
    | None => zesu_linear_is_prop typ
    end) (Control.hyps ())) in
  if Int.lt facts 40 then ()
  else if Int.gt (List.length (zesu_linear_division_terms [] (Control.goal ()))) (zesu_divmod_bound ())
  then Control.zero (Tactic_failure None) else ().

Ltac zesu_lia_large_context_divisions_within :=
  ltac2:(zesu_linear_large_context_divisions_within ()).

(* A lower bound of `zesu_linear_remaining` on a term after a tactic that turns
   every application of a `collapsed` head into one node (a projection into a
   `match` when unfolded, a closed operation into a literal when reduced) and
   only grows the rest of the term. *)
Ltac2 rec zesu_linear_collapsed_remaining (collapsed : constr list) (budget : int) (term : constr) : int :=
  if Int.le budget 0 then budget else
  let walk := zesu_linear_collapsed_remaining collapsed in
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      if List.exist (Constr.equal head) collapsed then Int.sub budget 1 else
      let budget := match Constr.Unsafe.kind head with
        | Constr.Unsafe.Constant _ _ => Int.sub budget 2
        | Constr.Unsafe.Constructor _ _ => Int.sub budget 2
        | Constr.Unsafe.Ind _ _ => Int.sub budget 2
        | Constr.Unsafe.Var _ => Int.sub budget 2
        | _ => walk (Int.sub budget 1) head
        end in
      Array.fold_left walk budget arguments
  | Constr.Unsafe.Prod binder body => walk (walk (Int.sub budget 1) (Constr.Binder.type binder)) body
  | Constr.Unsafe.Lambda binder body => walk (walk (Int.sub budget 1) (Constr.Binder.type binder)) body
  | Constr.Unsafe.LetIn binder value body =>
      walk (walk (walk (Int.sub budget 1) (Constr.Binder.type binder)) value) body
  | Constr.Unsafe.Cast value _ typ => walk (walk (Int.sub budget 1) value) typ
  | _ => Int.sub budget 1
  end.

(* The Prop facts (not the goal) fit `nodes` by that lower bound. *)
Ltac2 zesu_linear_collapsed_facts_within (collapsed : constr list) (nodes : int) :=
  let rest := List.fold_left (fun budget declaration =>
    let (_, body, typ) := declaration in
    match body with
    | Some _ => budget
    | None =>
        if Int.le budget 0 then budget
        else if zesu_linear_is_prop typ then zesu_linear_collapsed_remaining collapsed budget typ
        else budget
    end) nodes (Control.hyps ()) in
  if Int.le rest 0 then Control.zero (Tactic_failure None) else ().
