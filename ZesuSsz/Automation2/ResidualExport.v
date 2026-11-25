Require ZesuSsz.Automation2.ContextCollection.
Require ZesuSsz.Automation2.ResidualLemmas.
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
   - a `match` on `bool` or `sumbool` (`if b then ..`, `if decide P then ..`)
     whose branches do not use the constructor's argument is written as
     `(if s as x return P then t else e)`, which elaborates to the same
     match.
   Any other match, a fixpoint, an evar or a primitive value is refused.

   The statement of a goal is `forall (x1 : T1) ... (xn : Tn), C` over the
   hypotheses that the conclusion reaches: the facts that share a local
   variable with the conclusion or with a fact already kept (to a fixpoint),
   without facts above the node limit and without facts that mention no
   local variable (switch and marker facts), plus the variables these terms
   mention. A fact above the limit takes part through its pieces below it
   (`ContextCollection.zesu_large_fact_pieces`); a residual lemma premise
   over a piece closes from the whole fact (`ResidualLemmas.zesu_residual_premise`).
   Local definitions are unfolded into the statement.
   Each binder keeps the name of its hypothesis, so `intros.` restores the
   names.

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
  nat_type : inductive;
  bool_type : inductive;
  sumbool_type : inductive
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
  nat_type := zesu_export_inductive 'nat;
  bool_type := zesu_export_inductive 'bool;
  sumbool_type := zesu_export_inductive 'sumbool
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
  | Constr.Unsafe.Case _ predicate _ scrutinee branches =>
      let (returned, _) := predicate in
      (* The return predicate `fun (x : I ..) => P` names the inductive: `bool`
         (constructors without arguments) or `sumbool A B` (one argument). *)
      let shape := match Constr.Unsafe.kind returned with
        | Constr.Unsafe.Lambda binder body =>
            let head := match Constr.Unsafe.kind (Constr.Binder.type binder) with
              | Constr.Unsafe.App head _ => head
              | _ => Constr.Binder.type binder
              end in
            match Constr.Unsafe.kind head with
            | Constr.Unsafe.Ind ind _ =>
                if Ind.equal ind (lits.(bool_type)) then Some (binder, body, 0)
                else if Ind.equal ind (lits.(sumbool_type)) then Some (binder, body, 1)
                else None
            | _ => None
            end
        | _ => None
        end in
      match shape with
      | None => zesu_export_refuse "match"
      | Some (binder, body, fields) =>
          if Int.equal (Array.length branches) 2 then () else zesu_export_refuse "match";
          let name := zesu_export_binder_name binder names in
          let branch (term : constr) :=
            if Int.equal fields 0 then recur names term else
            match Constr.Unsafe.kind term with
            | Constr.Unsafe.Lambda _ inner =>
                if zesu_export_occurs 1 inner then zesu_export_refuse "dependent branch"
                else recur ("_" :: names) inner
            | _ => zesu_export_refuse "match"
            end in
          zesu_export_cats [zesu_export_str "(if "; recur names scrutinee;
            zesu_export_str " as "; zesu_export_str name; zesu_export_str " return ";
            recur (name :: names) body; zesu_export_str " then ";
            branch (Array.get branches 0); zesu_export_str " else ";
            branch (Array.get branches 1); zesu_export_str ")"]
      end
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
  match Control.case (fun () => ZesuSsz.Automation2.ContextCollection.zesu_context_variables_in true term) with
  | Val (found, _) => Some found
  | Err _ => None
  end.

(* Substitute every local definition of the context into TERM: the form in
   which the residual tier matches a goal whose conclusion mentions a local
   definition (ResidualLemmas.v). *)
Ltac2 zesu_export_unfold_local (term : constr) : constr :=
  ZesuSsz.Automation2.ResidualLemmas.zesu_residual_unfold_local term.

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

(* The head of a fact's type: the applied constant or inductive. *)
Ltac2 zesu_export_head (typ : constr) : constr option :=
  let term := match Constr.Unsafe.kind typ with
    | Constr.Unsafe.App applied _ => applied
    | _ => typ
    end in
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Constant _ _ => Some term
  | Constr.Unsafe.Ind _ _ => Some term
  | _ => None
  end.

(* Whether NEEDLE occurs in TERM syntactically. *)
Ltac2 rec zesu_export_mentions (needle : constr) (term : constr) : bool :=
  if Constr.equal needle term then true else
  let visit := zesu_export_mentions needle in
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments => if visit head then true else Array.exist visit arguments
  | Constr.Unsafe.Prod binder body => if visit (Constr.Binder.type binder) then true else visit body
  | Constr.Unsafe.Lambda binder body => if visit (Constr.Binder.type binder) then true else visit body
  | Constr.Unsafe.LetIn binder value body =>
      if visit (Constr.Binder.type binder) then true else if visit value then true else visit body
  | Constr.Unsafe.Cast value _ typ => if visit value then true else visit typ
  | Constr.Unsafe.Proj _ _ value => visit value
  | Constr.Unsafe.Case _ predicate _ scrutinee branches =>
      let (returned, _) := predicate in
      if visit returned then true else if visit scrutinee then true else Array.exist visit branches
  | _ => false
  end.

(* A record fact: its head is a predicate of its own, not a connective, an
   equation or a comparison (which any conclusion mentions). *)
Ltac2 zesu_export_record_head (typ : constr) : constr option :=
  match zesu_export_head typ with
  | Some head =>
      if List.exist (fun other => Constr.equal head other)
        ['and; 'or; 'not; 'iff; '(@eq); 'BinInt.Z.le; 'BinInt.Z.lt; 'BinInt.Z.ge;
         'BinInt.Z.gt; 'le; 'lt; 'ge; 'gt; 'True; 'False; '(@ex)]
      then None else Some head
  | None => None
  end.

(* A large fact that the statement keeps: a record fact whose head SCOPE
   mentions (an existential that restates a call record over its binders
   needs the record; a conjunct of it gets the record with its large
   subterms abstracted, `zesu_export_abstract`). *)
Ltac2 zesu_export_keep_whole (scope : constr) (typ : constr) : bool :=
  match zesu_export_record_head typ with
  | Some head => zesu_export_mentions head scope
  | None => false
  end.

(* The facts that the conclusion reaches: a fact is kept when it shares a
   local variable with the conclusion or with a kept fact. A conclusion
   without local variables (`False` of a contradictory path) reaches every
   candidate fact. Facts above LIMIT nodes (unless kept for SCOPE), facts
   without local variables, and facts with refused syntax are never kept. *)
Ltac2 zesu_export_reach_in (limit : int) (scope : constr) : ident list * int * int :=
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
              else if Bool.or (ZesuSsz.Automation2.ContextCollection.zesu_select_small limit typ)
                (zesu_export_keep_whole scope typ)
              then (name, variables) :: found else found
          | None => found
          end
        else found
    end) (Control.hyps ()) [] in
  let props := List.length (List.filter (fun declaration =>
    let (_, body, typ) := declaration in
    match body with None => zesu_export_proposition typ | Some _ => false end) (Control.hyps ())) in
  let reached := Ref.ref (match zesu_export_variables (zesu_export_unfold_local (Control.goal ())) with
    | Some [] => List.fold_right (fun entry found =>
        let (_, variables) := entry in
        ZesuSsz.Automation2.ContextCollection.zesu_context_union found variables) candidates []
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

Ltac2 zesu_export_reach (limit : int) : ident list * int * int :=
  zesu_export_reach_in limit (zesu_export_unfold_local (Control.goal ())).

Ltac2 zesu_export_node_cap := 1000000.

(* The facts the statement leaves out for size: a proposition over local
   variables above LIMIT nodes that shares a variable with the conclusion or
   with a kept fact of FACTS (with a conclusion without local variables:
   every such fact), so `zesu_export_reach` would keep it but for its size.
   Each comes with its node count (at most `zesu_export_node_cap`) and the
   head of its type: the applied constant, inductive or variable as source,
   `forall` for a product, `-` otherwise. *)
Ltac2 zesu_export_dropped (limit : int) (facts : ident list) : (ident * int * message) list :=
  let variables_of (term : constr) :=
    match zesu_export_variables term with
    | Some found => found
    | None => []
    end in
  let hyps := Control.hyps () in
  let conclusion := variables_of (zesu_export_unfold_local (Control.goal ())) in
  let reached := List.fold_left (fun found declaration =>
    let (name, body, typ) := declaration in
    match body with
    | None =>
        if zesu_export_member name facts then
          ZesuSsz.Automation2.ContextCollection.zesu_context_union found
            (variables_of (zesu_export_unfold_local typ))
        else found
    | Some _ => found
    end) conclusion hyps in
  let head (typ : constr) :=
    let term := match Constr.Unsafe.kind typ with
      | Constr.Unsafe.App applied _ => applied
      | _ => typ
      end in
    match Constr.Unsafe.kind term with
    | Constr.Unsafe.Constant _ _ => Some term
    | Constr.Unsafe.Ind _ _ => Some term
    | Constr.Unsafe.Var _ => Some term
    | _ => None
    end in
  List.fold_right (fun declaration found =>
    let (name, body, typ) := declaration in
    match body with
    | Some _ => found
    | None =>
        let typ := zesu_export_unfold_local typ in
        let variables := variables_of typ in
        if Bool.or (Bool.neg (zesu_export_proposition typ)) (Int.equal (List.length variables) 0) then found
        else if ZesuSsz.Automation2.ContextCollection.zesu_select_small limit typ then found
        else if zesu_export_member name facts then found
        else if Bool.and (Bool.neg (Int.equal (List.length conclusion) 0))
          (Bool.neg (ZesuSsz.Automation2.ContextCollection.zesu_context_intersects variables reached))
        then found
        else
          let budget := Ref.ref zesu_export_node_cap in
          ZesuSsz.Automation2.ContextCollection.zesu_select_size budget typ;
          let shown := match head typ with
            | Some term =>
                match Control.case (fun () => zesu_export_source term) with
                | Val (text, _) => text
                | Err _ => zesu_export_str "-"
                end
            | None =>
                match Constr.Unsafe.kind typ with
                | Constr.Unsafe.Prod _ _ => zesu_export_str "forall"
                | _ => zesu_export_str "-"
                end
            end in
          (name, Int.sub zesu_export_node_cap (Ref.get budget), shown) :: found
    end) hyps [].

(* The local definitions that the conclusion mentions. The residual tier
   unfolds them in the goal before its second try, so a lemma in the
   exported form (definitions unfolded) matches. *)
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

(* ---- large record facts ---- *)

(* Subterms smaller than this many nodes are not abstracted and say nothing
   specific about a large fact: `bv_unsigned (txInputPointer args)` is 20
   nodes with its width literal and occurs in every input bound. *)
Ltac2 zesu_export_abstract_nodes := 64.

(* The application subterms of TERM of at least `zesu_export_abstract_nodes`
   nodes that mention no variable bound inside TERM, each with its node
   count, collected into FOUND; occurrences of SKIP are not entered (they
   count one node). Returns the node count of TERM and its highest loose de
   Bruijn index (0 when none). *)
Ltac2 rec zesu_export_subterms (skip : constr option) (found : (int * constr) list ref)
    (term : constr) : int * int :=
  let skipped := match skip with
    | Some needle => Constr.equal needle term
    | None => false
    end in
  if skipped then (1, 0) else
  let visit := zesu_export_subterms skip found in
  let join (a : int * int) (b : int * int) :=
    let (n1, r1) := a in
    let (n2, r2) := b in
    (Int.add n1 n2, if Int.lt r1 r2 then r2 else r1) in
  let under (a : int * int) :=
    let (n, r) := a in (n, if Int.le r 1 then 0 else Int.sub r 1) in
  let (nodes, loose) := match Constr.Unsafe.kind term with
    | Constr.Unsafe.Rel index => (0, index)
    | Constr.Unsafe.App head arguments =>
        Array.fold_left (fun acc argument => join acc (visit argument)) (visit head) arguments
    | Constr.Unsafe.Prod binder body => join (visit (Constr.Binder.type binder)) (under (visit body))
    | Constr.Unsafe.Lambda binder body => join (visit (Constr.Binder.type binder)) (under (visit body))
    | Constr.Unsafe.LetIn binder value body =>
        join (join (visit (Constr.Binder.type binder)) (visit value)) (under (visit body))
    | Constr.Unsafe.Cast value _ typ => join (visit value) (visit typ)
    | Constr.Unsafe.Proj _ _ value => visit value
    | Constr.Unsafe.Case _ predicate _ scrutinee branches =>
        let (returned, _) := predicate in
        Array.fold_left (fun acc branch => join acc (visit branch))
          (join (visit returned) (visit scrutinee)) branches
    | _ => (0, 0)
    end in
  let nodes := Int.add nodes 1 in
  (match Constr.Unsafe.kind term with
   | Constr.Unsafe.App _ _ =>
       if Bool.and (Int.equal loose 0) (Int.le zesu_export_abstract_nodes nodes)
       then Ref.set found ((nodes, term) :: Ref.get found) else ()
   | _ => ()
   end);
  (nodes, loose).

(* The terms of the statement: the conclusion and the facts it may keep (the
   facts within LIMIT nodes and the record facts SCOPE names). *)
Ltac2 zesu_export_statement_terms (limit : int) (scope : constr) (conclusion : constr) : constr list :=
  List.fold_left (fun terms declaration =>
    let (_, body, typ) := declaration in
    match body with
    | Some _ => terms
    | None =>
        if Bool.and (zesu_export_proposition typ)
          (Bool.or (ZesuSsz.Automation2.ContextCollection.zesu_select_small limit typ)
            (zesu_export_keep_whole scope typ))
        then typ :: terms else terms
    end) [conclusion] (Control.hyps ()).

(* A subterm that a variable may replace everywhere: a value (not a proof,
   not a type) without evar that the conclusion does not mention, none of
   whose large subterms occurs in TERMS outside its own occurrences. The
   replacement then cuts no relation the statement states (txAccessList
   0188: call4's argument words read from the input and its argument
   pointer's byte word go; call4's argument record, and the unsigned view
   of its pointer word that the bound facts state, stay). *)
Ltac2 zesu_export_abstractable (conclusion : constr) (terms : constr list) (term : constr) : bool :=
  if Constr.has_evar term then false
  else if zesu_export_mentions term conclusion then false
  else
    let typed := match Control.case (fun () => Constr.type term) with
      | Val (typ, _) =>
          if zesu_export_proposition typ then false
          else match Constr.Unsafe.kind typ with
            | Constr.Unsafe.Sort _ => false
            | _ => true
            end
      | Err _ => false
      end in
    if Bool.neg typed then false
    else
      let outside := Ref.ref [] in
      List.iter (fun other => let _ := zesu_export_subterms (Some term) outside other in ()) terms;
      let inner := Ref.ref [] in
      let _ := zesu_export_subterms None inner term in
      List.for_all (fun entry =>
        let (_, subterm) := entry in
        if Constr.equal subterm term then true
        else Bool.neg (List.exist (fun found => let (_, other) := found in Constr.equal other subterm)
          (Ref.get outside)))
        (Ref.get inner).

(* Replaces the largest abstractable subterm of fact NAME by a new variable
   `zesu_abs*` everywhere in the context. Whether a subterm was replaced. *)
Ltac2 zesu_export_abstract_one (name : ident) (conclusion : constr) (terms : constr list)
    (refused : constr list ref) : bool :=
  let found := Ref.ref [] in
  let _ := zesu_export_subterms None found (Constr.type (Control.hyp name)) in
  let ordered := List.sort (fun a b => let (n1, _) := a in let (n2, _) := b in Int.compare n2 n1)
    (Ref.get found) in
  let set_term := ltac1val:(term |-
    let abstracted := fresh "zesu_abs" in set (abstracted := term) in *; clearbody abstracted) in
  let rec first (entries : (int * constr) list) :=
    match entries with
    | [] => false
    | entry :: rest =>
        let (_, term) := entry in
        if List.exist (fun other => Constr.equal other term) (Ref.get refused) then first rest
        else if zesu_export_abstractable conclusion terms term then
          match Control.case (fun () => Ltac1.run (set_term (Ltac1.of_constr term))) with
          | Val _ => true
          | Err _ => Ref.set refused (term :: Ref.get refused); first rest
          end
        else (Ref.set refused (term :: Ref.get refused); first rest)
    end in
  first ordered.

(* A record fact above LIMIT whose head SCOPE mentions but the conclusion
   does not (a call record that the existential this conjunct comes from
   restated): its largest abstractable subterms are replaced by variables,
   until it fits the limit or no such subterm is left (`zesu_export_reach_in`
   keeps it either way). The statement's terms are taken again after each
   replacement. Replacing a term by a variable everywhere gives a statement
   that implies the original one, and the residual tier finds the variable
   by unification. *)
Ltac2 zesu_export_abstract (limit : int) (scope : constr) :=
  let conclusion := zesu_export_unfold_local (Control.goal ()) in
  let records := List.filter (fun declaration =>
    let (_, body, typ) := declaration in
    match body with
    | Some _ => false
    | None =>
        if zesu_export_proposition typ then
          if ZesuSsz.Automation2.ContextCollection.zesu_select_small limit typ then false
          else match zesu_export_record_head typ with
            | Some head =>
                Bool.and (zesu_export_mentions head scope)
                  (Bool.neg (zesu_export_mentions head conclusion))
            | None => false
            end
        else false
    end) (Control.hyps ()) in
  List.iter (fun declaration =>
    let (name, _, _) := declaration in
    let refused := Ref.ref [] in
    let rec shrink (budget : int) :=
      if Int.le budget 0 then ()
      else if ZesuSsz.Automation2.ContextCollection.zesu_select_small limit
        (Constr.type (Control.hyp name)) then ()
      else if zesu_export_abstract_one name conclusion
        (zesu_export_statement_terms limit scope conclusion) refused
      then shrink (Int.sub budget 1) else () in
    shrink 24) records.

(* The export record of the focused pure goal. KIND names the export point;
   SCOPE is the statement the goal comes from (the goal itself, or the
   existential whose conjunct it is). *)
Ltac2 zesu_export_record (kind : string) (limit : int) (scope : constr) :=
  let goal := Control.goal () in
  if Constr.has_evar goal then zesu_export_refuse "evar in goal" else ();
  if zesu_export_proposition goal then () else zesu_export_refuse "not a proposition";
  zesu_export_abstract limit scope;
  let (facts, props, small) := zesu_export_reach_in limit scope in
  let (statement, binders) := zesu_export_statement facts in
  let dropped := zesu_export_dropped limit facts in
  let source := zesu_export_source statement in
  Message.print (zesu_export_str (String.concat "" ["@@X begin "; kind]));
  zesu_export_names "@@X binders" binders;
  zesu_export_names "@@X conclusion-definitions" (zesu_export_conclusion_definitions ());
  Message.print (zesu_export_cats [zesu_export_str "@@X counts props=";
    Message.of_int props; zesu_export_str " small="; Message.of_int small;
    zesu_export_str " kept="; Message.of_int (List.length facts)]);
  List.iter (fun entry =>
    let (name, nodes, shown) := entry in
    Message.print (zesu_export_cats [zesu_export_str "@@X dropped-fact "; Message.of_ident name;
      zesu_export_str " "; Message.of_int nodes; zesu_export_str " "; shown])) dropped;
  Message.print (zesu_export_cats [zesu_export_str "@@X stmt "; source]);
  Message.print (zesu_export_str "@@X end").

Ltac2 zesu_export_goal_here (kind : string) (scope : constr) :=
  match Control.case (fun () => zesu_export_record kind 2048 scope) with
  | Val _ => ()
  | Err error =>
      let why := match error with
        | ZesuExportRefused reason => reason
        | _ => "error"
        end in
      Message.print (zesu_export_str (String.concat "" ["@@X skip "; kind; " "; why]))
  end.

Ltac2 Type exn ::= [ ZesuExportRestore ].

(* The record is printed with the pieces of the large facts in the context;
   the failure that follows restores the goal and the context. *)
Ltac2 zesu_export_goal_in (kind : string) (scope : constr) :=
  let _ := Control.case (fun () =>
    let _ := ZesuSsz.Automation2.ContextCollection.zesu_large_fact_pieces () in
    zesu_export_goal_here kind scope;
    Control.zero ZesuExportRestore) in
  ().

Ltac2 zesu_export_goal (kind : string) := zesu_export_goal_in kind (Control.goal ()).

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
