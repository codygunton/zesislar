Require ZesuSsz.Automation2.ContextCollection.
From Coq Require Import BinNums.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* Exact source for pure residual goals (diagnostic only; no production
   tactic calls these definitions).

   A printed goal is not source: the default printer drops literal widths
   (`bv_unsigned 4` for `BV 64 4`) and cuts deep terms. This module writes
   Rocq source from the term itself:
   - every global reference is fully qualified and written with `@` (in
     parentheses when it is not applied), so every implicit argument,
     width included, is explicit;
   - positive, N, Z and nat literals are written as numerals with their
     scope key (hexadecimal above 2^30); other constructor trees are
     written as applications;
   - binders keep their names; a name that an outer binder already uses
     gets a fresh suffix.
   A term with a match, a fixpoint, an evar or a primitive value is refused.

   The statement of a goal is `forall (x1 : T1) ... (xn : Tn), C` over the
   hypotheses that the conclusion reaches: the facts that share a local
   variable with the conclusion or with a fact already kept (to a fixpoint),
   without facts above the node limit and without facts that mention no
   local variable (switch and marker facts), plus the variables these terms
   mention. Local definitions are unfolded into the statement. Each binder
   keeps the name of its hypothesis, so `intros.` restores the names.

   Reparsing the printed statement and printing it again gives the same
   text exactly when the reparsed term is the exported term (up to binder
   names that are not printed and universe instances).
   `tools/block/residual_loop.py` checks this for every exported goal. *)

Ltac2 Type exn ::= [ ZesuExportRefused (string) ].

Ltac2 zesu_export_refuse (why : string) := Control.zero (ZesuExportRefused why).

Ltac2 zesu_export_str (text : string) := Message.of_string text.

Ltac2 zesu_export_cats (parts : message list) :=
  List.fold_left Message.concat (Message.of_string "") parts.

Ltac2 zesu_export_int_text (value : int) := Message.to_string (Message.of_int value).

(* Whether Rel INDEX occurs in TERM. The Coq 8.19 primitive
   `Constr.Unsafe.occur_between` returns the negation of its documented
   result; the polarity is measured once per call, so the check stays right
   when a later Rocq fixes the primitive. *)
Ltac2 zesu_export_occurs (index : int) (term : constr) : bool :=
  let reported := Constr.Unsafe.occur_between index 1 term in
  let probe := Constr.Unsafe.occur_between 1 1 (Constr.Unsafe.make (Constr.Unsafe.Rel 1)) in
  if probe then reported else Bool.neg reported.

(* ---- literals ---- *)

Ltac2 Type zesu_export_literals := {
  positive_type : inductive;
  n_type : inductive;
  z_type : inductive;
  nat_type : inductive
}.

Ltac2 zesu_export_inductive (term : constr) : inductive :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Ind ind _ => ind
  | _ => zesu_export_refuse "literal types"
  end.

Ltac2 zesu_export_literal_types () : zesu_export_literals := {
  positive_type := zesu_export_inductive 'positive;
  n_type := zesu_export_inductive 'N;
  z_type := zesu_export_inductive 'Z;
  nat_type := zesu_export_inductive 'nat
}.

(* The constructor of TERM when TERM is a constructor of IND, with its index. *)
Ltac2 zesu_export_constructor_of (ind : inductive) (term : constr) : int option :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Constructor k _ =>
      if Ind.equal (Constructor.inductive k) ind then Some (Constructor.index k) else None
  | _ => None
  end.

(* The bits of a closed positive, least significant first, the leading one
   included. Constructor order: xI, xO, xH. *)
Ltac2 rec zesu_export_positive_bits (lits : zesu_export_literals) (term : constr)
    : int list option :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      if Int.equal (Array.length arguments) 1 then
        match zesu_export_constructor_of (lits.(positive_type)) head with
        | Some index =>
            if Int.lt index 2 then
              match zesu_export_positive_bits lits (Array.get arguments 0) with
              | Some bits => Some ((if Int.equal index 0 then 1 else 0) :: bits)
              | None => None
              end
            else None
        | None => None
        end
      else None
  | _ =>
      match zesu_export_constructor_of (lits.(positive_type)) term with
      | Some index => if Int.equal index 2 then Some [1] else None
      | None => None
      end
  end.

Ltac2 rec zesu_export_hex_digits (bits : int list) : string list :=
  match bits with
  | [] => []
  | b0 :: rest0 =>
      let (b1, rest1) := match rest0 with [] => (0, []) | b :: r => (b, r) end in
      let (b2, rest2) := match rest1 with [] => (0, []) | b :: r => (b, r) end in
      let (b3, rest3) := match rest2 with [] => (0, []) | b :: r => (b, r) end in
      let digit := Int.add b0 (Int.add (Int.mul 2 b1) (Int.add (Int.mul 4 b2) (Int.mul 8 b3))) in
      String.make 1 (String.get "0123456789abcdef" digit) :: zesu_export_hex_digits rest3
  end.

(* Decimal up to 30 bits, hexadecimal above (Ltac2 integers are 63-bit). *)
Ltac2 zesu_export_positive_text (bits : int list) : string :=
  if Int.le (List.length bits) 30 then
    zesu_export_int_text (List.fold_right (fun bit value => Int.add (Int.mul 2 value) bit) bits 0)
  else String.app "0x" (String.concat "" (List.rev (zesu_export_hex_digits bits))).

Ltac2 rec zesu_export_nat_value (lits : zesu_export_literals) (budget : int) (term : constr)
    : int option :=
  if Int.le budget 0 then None else
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      if Int.equal (Array.length arguments) 1 then
        match zesu_export_constructor_of (lits.(nat_type)) head with
        | Some index =>
            if Int.equal index 1 then
              match zesu_export_nat_value lits (Int.sub budget 1) (Array.get arguments 0) with
              | Some value => Some (Int.add value 1)
              | None => None
              end
            else None
        | None => None
        end
      else None
  | _ =>
      match zesu_export_constructor_of (lits.(nat_type)) term with
      | Some index => if Int.equal index 0 then Some 0 else None
      | None => None
      end
  end.

Ltac2 zesu_export_scoped (text : string) (key : string) : message :=
  zesu_export_str (String.concat "" ["("; text; ")%"; key]).

(* A numeral for a closed positive, N, Z (non-negative) or nat literal. *)
Ltac2 zesu_export_literal (lits : zesu_export_literals) (term : constr) : message option :=
  let positive_arg (head : constr) (arguments : constr array) (ind : inductive) (index : int) :=
    if Int.equal (Array.length arguments) 1 then
      match zesu_export_constructor_of ind head with
      | Some found =>
          if Int.equal found index then zesu_export_positive_bits lits (Array.get arguments 0)
          else None
      | None => None
      end
    else None in
  match zesu_export_positive_bits lits term with
  | Some bits => Some (zesu_export_scoped (zesu_export_positive_text bits) "positive")
  | None =>
  match zesu_export_nat_value lits 4096 term with
  | Some value => Some (zesu_export_scoped (zesu_export_int_text value) "nat")
  | None =>
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      match positive_arg head arguments (lits.(n_type)) 1 with
      | Some bits => Some (zesu_export_scoped (zesu_export_positive_text bits) "N")
      | None =>
      match positive_arg head arguments (lits.(z_type)) 1 with
      | Some bits => Some (zesu_export_scoped (zesu_export_positive_text bits) "Z")
      | None => None
      end
      end
  | _ =>
      match zesu_export_constructor_of (lits.(n_type)) term with
      | Some index => if Int.equal index 0 then Some (zesu_export_scoped "0" "N") else None
      | None =>
      match zesu_export_constructor_of (lits.(z_type)) term with
      | Some index => if Int.equal index 0 then Some (zesu_export_scoped "0" "Z") else None
      | None => None
      end
      end
  end
  end
  end.

(* ---- terms ---- *)

Ltac2 zesu_export_path (reference : Std.reference) : message :=
  zesu_export_str (String.app "@"
    (String.concat "." (List.map Ident.to_string (Env.path reference)))).

Ltac2 zesu_export_global (term : constr) : message option :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Constant c _ => Some (zesu_export_path (Std.ConstRef c))
  | Constr.Unsafe.Ind ind _ => Some (zesu_export_path (Std.IndRef ind))
  | Constr.Unsafe.Constructor k _ => Some (zesu_export_path (Std.ConstructRef k))
  | _ => None
  end.

Ltac2 rec zesu_export_fresh (base : string) (index : int) (names : string list) : string :=
  let candidate := String.concat "" [base; "_"; zesu_export_int_text index] in
  if List.mem String.equal candidate names then zesu_export_fresh base (Int.add index 1) names
  else candidate.

(* The printed name of a binder. NAMES are the names of the enclosing binders,
   innermost first. *)
Ltac2 zesu_export_binder_name (binder : binder) (names : string list) : string :=
  match Constr.Binder.name binder with
  | Some id =>
      let text := Ident.to_string id in
      if List.mem String.equal text names then zesu_export_fresh text 1 names else text
  | None => zesu_export_fresh "x" 1 names
  end.

Ltac2 rec zesu_export_term (lits : zesu_export_literals) (names : string list) (term : constr)
    : message :=
  let recur := zesu_export_term lits in
  match zesu_export_literal lits term with
  | Some literal => literal
  | None =>
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Rel index =>
      if Int.le index (List.length names) then zesu_export_str (List.nth names (Int.sub index 1))
      else zesu_export_refuse "unbound index"
  | Constr.Unsafe.Var id => Message.of_ident id
  | Constr.Unsafe.Sort _ =>
      if Constr.equal term 'Prop then zesu_export_str "Prop"
      else if Constr.equal term 'Set then zesu_export_str "Set"
      else if Constr.equal term 'SProp then zesu_export_str "SProp"
      else zesu_export_str "Type"
  | Constr.Unsafe.Constant _ _ => zesu_export_cats [zesu_export_str "("; Option.get (zesu_export_global term); zesu_export_str ")"]
  | Constr.Unsafe.Ind _ _ => zesu_export_cats [zesu_export_str "("; Option.get (zesu_export_global term); zesu_export_str ")"]
  | Constr.Unsafe.Constructor _ _ => zesu_export_cats [zesu_export_str "("; Option.get (zesu_export_global term); zesu_export_str ")"]
  | Constr.Unsafe.App head arguments =>
      let shown := match zesu_export_global head with
        | Some global => global
        | None => recur names head
        end in
      zesu_export_cats [zesu_export_str "("; shown;
        Array.fold_left (fun message argument =>
          zesu_export_cats [message; zesu_export_str " "; recur names argument])
          (zesu_export_str "") arguments;
        zesu_export_str ")"]
  | Constr.Unsafe.Cast value kind typ =>
      let symbol :=
        if Constr.Cast.equal kind Constr.Cast.vm then " <: "
        else if Constr.Cast.equal kind Constr.Cast.native then " <<: "
        else " : " in
      zesu_export_cats [zesu_export_str "("; recur names value; zesu_export_str symbol;
        recur names typ; zesu_export_str ")"]
  | Constr.Unsafe.Prod binder body =>
      let typ := recur names (Constr.Binder.type binder) in
      match Constr.Binder.name binder with
      | None =>
          if zesu_export_occurs 1 body then
            let name := zesu_export_binder_name binder names in
            zesu_export_cats [zesu_export_str "(forall ("; zesu_export_str name;
              zesu_export_str " : "; typ; zesu_export_str "), "; recur (name :: names) body;
              zesu_export_str ")"]
          else
            zesu_export_cats [zesu_export_str "("; typ; zesu_export_str " -> ";
              recur ("_" :: names) body; zesu_export_str ")"]
      | Some _ =>
          let name := zesu_export_binder_name binder names in
          zesu_export_cats [zesu_export_str "(forall ("; zesu_export_str name;
            zesu_export_str " : "; typ; zesu_export_str "), "; recur (name :: names) body;
            zesu_export_str ")"]
      end
  | Constr.Unsafe.Lambda binder body =>
      let name := zesu_export_binder_name binder names in
      zesu_export_cats [zesu_export_str "(fun ("; zesu_export_str name; zesu_export_str " : ";
        recur names (Constr.Binder.type binder); zesu_export_str ") => ";
        recur (name :: names) body; zesu_export_str ")"]
  | Constr.Unsafe.LetIn binder value body =>
      let name := zesu_export_binder_name binder names in
      zesu_export_cats [zesu_export_str "(let "; zesu_export_str name; zesu_export_str " : ";
        recur names (Constr.Binder.type binder); zesu_export_str " := "; recur names value;
        zesu_export_str " in "; recur (name :: names) body; zesu_export_str ")"]
  | Constr.Unsafe.Proj projection _ value =>
      match Proj.to_constant projection with
      | Some c =>
          zesu_export_cats [zesu_export_str "("; recur names value; zesu_export_str ").(";
            zesu_export_path (Std.ConstRef c); zesu_export_str ")"]
      | None => zesu_export_refuse "projection"
      end
  | Constr.Unsafe.Case _ _ _ _ _ => zesu_export_refuse "match"
  | Constr.Unsafe.Fix _ _ _ _ => zesu_export_refuse "fixpoint"
  | Constr.Unsafe.CoFix _ _ _ => zesu_export_refuse "cofixpoint"
  | Constr.Unsafe.Evar _ _ => zesu_export_refuse "evar"
  | Constr.Unsafe.Meta _ => zesu_export_refuse "meta"
  | Constr.Unsafe.Uint63 _ => zesu_export_refuse "primitive integer"
  | Constr.Unsafe.Float _ => zesu_export_refuse "primitive float"
  | Constr.Unsafe.Array _ _ _ _ => zesu_export_refuse "primitive array"
  end
  end.

Ltac2 zesu_export_source (term : constr) : message :=
  zesu_export_term (zesu_export_literal_types ()) [] term.

(* ---- statements ---- *)

Ltac2 zesu_export_member (name : ident) (names : ident list) := List.mem Ident.equal name names.

(* The local variables of TERM; None when TERM has syntax that the printer
   refuses. *)
Ltac2 zesu_export_variables (term : constr) : ident list option :=
  match Control.case (fun () => ZesuSsz.Automation2.ContextCollection.zesu_context_variables term) with
  | Val (found, _) => Some found
  | Err _ => None
  end.

(* Substitute every local definition of the context into TERM, newest first,
   so a body that mentions an older definition is unfolded too. *)
Ltac2 zesu_export_unfold_local (term : constr) : constr :=
  List.fold_left (fun current declaration =>
    let (name, body, _) := declaration in
    match body with
    | Some value =>
        Constr.Unsafe.substnl [value] 0 (Constr.Unsafe.closenl [name] 1 current)
    | None => current
    end) term (List.rev (Control.hyps ())).

Ltac2 zesu_export_proposition (typ : constr) : bool :=
  match Control.case (fun () => Constr.equal (Constr.type typ) 'Prop) with
  | Val (answer, _) => answer
  | Err _ => false
  end.

(* The closed statement over the facts FACTS (names of context hypotheses)
   and the variables that the conclusion and these facts mention. *)
Ltac2 zesu_export_statement (facts : ident list) : constr * ident list :=
  let hyps := List.filter (fun declaration =>
    let (_, body, _) := declaration in
    match body with None => true | Some _ => false end) (Control.hyps ()) in
  let conclusion := zesu_export_unfold_local (Control.goal ()) in
  let typed := List.map (fun declaration =>
    let (name, _, typ) := declaration in (name, zesu_export_unfold_local typ)) hyps in
  let mentioned (term : constr) :=
    match zesu_export_variables term with
    | Some found => found
    | None => zesu_export_refuse "unsupported syntax"
    end in
  let needed := Ref.ref (mentioned conclusion) in
  List.iter (fun entry =>
    let (name, typ) := entry in
    if zesu_export_member name facts then
      Ref.set needed (ZesuSsz.Automation2.ContextCollection.zesu_context_union
        (name :: Ref.get needed) (mentioned typ))
    else ()) typed;
  (* The types of kept variables may mention older variables. *)
  List.iter (fun entry =>
    let (name, typ) := entry in
    if zesu_export_member name (Ref.get needed) then
      Ref.set needed (ZesuSsz.Automation2.ContextCollection.zesu_context_union
        (Ref.get needed) (mentioned typ))
    else ()) (List.rev typed);
  let kept := List.filter (fun entry =>
    let (name, _) := entry in zesu_export_member name (Ref.get needed)) typed in
  let statement := List.fold_right (fun entry body =>
    let (name, typ) := entry in
    Constr.Unsafe.make (Constr.Unsafe.Prod (Constr.Binder.make (Some name) typ)
      (Constr.Unsafe.closenl [name] 1 body))) kept conclusion in
  match Constr.Unsafe.check statement with
  | Val checked => (checked, List.map (fun entry => let (name, _) := entry in name) kept)
  | Err _ => zesu_export_refuse "ill-typed statement"
  end.

(* The facts that the conclusion reaches: a fact is kept when it shares a
   local variable with the conclusion or with a kept fact. Facts above LIMIT
   nodes, facts without local variables, and facts with refused syntax are
   never kept. *)
Ltac2 zesu_export_reach (limit : int) : ident list * int * int :=
  let candidates := List.fold_right (fun declaration found =>
    let (name, body, typ) := declaration in
    match body with
    | Some _ => found
    | None =>
        let typ := zesu_export_unfold_local typ in
        if zesu_export_proposition typ then
          match zesu_export_variables typ with
          | Some variables =>
              if Int.equal (List.length variables) 0 then found
              else if ZesuSsz.Automation2.ContextCollection.zesu_select_small limit typ
              then (name, variables) :: found else found
          | None => found
          end
        else found
    end) (Control.hyps ()) [] in
  let props := List.length (List.filter (fun declaration =>
    let (_, body, typ) := declaration in
    match body with None => zesu_export_proposition typ | Some _ => false end) (Control.hyps ())) in
  let reached := Ref.ref (match zesu_export_variables (zesu_export_unfold_local (Control.goal ())) with
    | Some found => found
    | None => zesu_export_refuse "unsupported syntax"
    end) in
  let kept := Ref.ref [] in
  let rec grow () :=
    let fresh := List.filter (fun entry =>
      let (name, variables) := entry in
      if zesu_export_member name (Ref.get kept) then false
      else ZesuSsz.Automation2.ContextCollection.zesu_context_intersects variables (Ref.get reached))
      candidates in
    match fresh with
    | [] => ()
    | _ =>
        List.iter (fun entry =>
          let (name, variables) := entry in
          Ref.set kept (name :: Ref.get kept);
          Ref.set reached (ZesuSsz.Automation2.ContextCollection.zesu_context_union
            (Ref.get reached) variables)) fresh;
        grow ()
    end in
  grow ();
  let kept := Ref.get kept in
  let ordered := List.fold_right (fun entry found =>
    let (name, _) := entry in if zesu_export_member name kept then name :: found else found) candidates [] in
  (ordered, props, List.length candidates).

(* The local definitions that the conclusion mentions: the residual tier
   matches local definitions only syntactically, so it cannot apply a lemma
   whose conclusion unfolds them. *)
Ltac2 zesu_export_conclusion_definitions () : ident list :=
  let found := match zesu_export_variables (Control.goal ()) with
    | Some names => names
    | None => []
    end in
  List.fold_right (fun declaration names =>
    let (name, body, _) := declaration in
    match body with
    | Some _ => if zesu_export_member name found then name :: names else names
    | None => names
    end) (Control.hyps ()) [].

Ltac2 zesu_export_names (label : string) (names : ident list) :=
  Message.print (List.fold_left (fun message name =>
    zesu_export_cats [message; zesu_export_str " "; Message.of_ident name])
    (zesu_export_str label) names).

(* The export record of the focused pure goal. KIND names the export point. *)
Ltac2 zesu_export_record (kind : string) (limit : int) :=
  let goal := Control.goal () in
  if Constr.has_evar goal then zesu_export_refuse "evar in goal" else ();
  if zesu_export_proposition goal then () else zesu_export_refuse "not a proposition";
  let (facts, props, small) := zesu_export_reach limit in
  let (statement, binders) := zesu_export_statement facts in
  let source := zesu_export_source statement in
  Message.print (zesu_export_str (String.concat "" ["@@X begin "; kind]));
  zesu_export_names "@@X binders" binders;
  zesu_export_names "@@X conclusion-definitions" (zesu_export_conclusion_definitions ());
  Message.print (zesu_export_cats [zesu_export_str "@@X counts props=";
    Message.of_int props; zesu_export_str " small="; Message.of_int small;
    zesu_export_str " kept="; Message.of_int (List.length facts)]);
  Message.print (zesu_export_cats [zesu_export_str "@@X stmt "; source]);
  Message.print (zesu_export_str "@@X end").

Ltac2 zesu_export_goal (kind : string) :=
  match Control.case (fun () => zesu_export_record kind 2048) with
  | Val _ => ()
  | Err error =>
      let why := match error with
        | ZesuExportRefused reason => reason
        | _ => "error"
        end in
      Message.print (zesu_export_str (String.concat "" ["@@X skip "; kind; " "; why]))
  end.

(* ---- checks used by the loop tool ---- *)

(* The source of the focused goal (a closed statement): the round-trip check
   prints a reparsed statement with the same printer. *)
Ltac2 zesu_export_roundtrip () :=
  Message.print (zesu_export_cats [zesu_export_str "@@X roundtrip "; zesu_export_source (Control.goal ())]).

(* Premise minimization. On a goal `forall b1 ... bn, C` after `intros`
   restored the binder names, with REFERENCE a transparent proof of that
   statement: the facts whose binders occur in the proof body. A proof that
   is not a function of every binder is applied to the remaining binders, so
   it counts as using all of them. *)
Ltac2 zesu_export_used_facts (reference : Std.reference) : ident list :=
  let proof := Std.eval_unfold [(reference, Std.AllOccurrences)] (Env.instantiate reference) in
  let hyps := Control.hyps () in
  let count := List.length hyps in
  let rec peel (remaining : int) (term : constr) :=
    if Int.le remaining 0 then term else
    match Constr.Unsafe.kind term with
    | Constr.Unsafe.Lambda _ body => peel (Int.sub remaining 1) body
    | _ =>
        let rec indices (index : int) :=
          if Int.le index 0 then []
          else Constr.Unsafe.make (Constr.Unsafe.Rel index) :: indices (Int.sub index 1) in
        Constr.Unsafe.make (Constr.Unsafe.App (Constr.Unsafe.liftn remaining 1 term)
          (Array.of_list (indices remaining)))
    end in
  let body := peel count proof in
  let (used, _) := List.fold_left (fun state declaration =>
    let (found, position) := state in
    let (name, _, typ) := declaration in
    let keep := if zesu_export_proposition typ
      then zesu_export_occurs (Int.sub count position) body else false in
    ((if keep then name :: found else found), Int.add position 1)) ([], 0) hyps in
  List.rev used.

(* The statement over the used facts, printed for the loop tool. *)
Ltac2 zesu_export_minimized (reference : Std.reference) :=
  let (statement, binders) := zesu_export_statement (zesu_export_used_facts reference) in
  zesu_export_names "@@X binders" binders;
  Message.print (zesu_export_cats [zesu_export_str "@@X minimized "; zesu_export_source statement]).

Ltac2 zesu_export_minimized_of (lemma : constr) :=
  match Constr.Unsafe.kind lemma with
  | Constr.Unsafe.Constant c _ => zesu_export_minimized (Std.ConstRef c)
  | _ => zesu_export_refuse "not a constant"
  end.
