(* Goal normaliser of tools/oblig/normalise.py (inlined into its probe files;
   not a module of the build). Untrusted: what it prints is used only through
   the link lemma, which the kernel checks with the plain Ltac1 script printed
   here.

   On a closed pure goal `forall .., C`:
   1. intros; then, to a fixpoint, each hypothesis whose head is
      - `and`: destructed; `ex`: destructed, the witness a new variable;
      - `True` or an Automation2 marker inductive: cleared;
      - a sealed constant `c` of a ZesuSsz module with a lemma `c_eq`
        (`Global Opaque` + unfold lemma): rewritten with `c_eq`;
      - any other constant of a ZesuSsz module: unfolded.
      Library constants (arithmetic, lists, bitvectors) are never unfolded.
   2. the conclusion: ZesuSsz heads unfolded the same way, `and` split; each
      leaf is one part.
   3. per part, at LEVEL 2: each ZesuSsz definition applied to a variable of a
      ZesuSsz record type is unfolded, and each record projection of such a
      variable (innermost first) becomes a fresh variable of the field's type
      (`set` + `clearbody`), named by its projection path; a record variable
      that no longer occurs is cleared. LEVEL 1 skips this step.
   4. per part, the exporter of ZesuSsz/Automation2/ResidualExport.v writes the
      statement over the facts the conclusion reaches (the slice).

   Output lines (`@@N `):
     part <k> binders <names>      the binders of part k's statement
     part <k> stmt <source>        part k's statement (exporter source)
     part <k> refused <why>        the exporter refused part k
     link <script>                 the Ltac1 proof of the original goal from
                                   hypotheses zn_part_1 .. zn_part_n
     done <level> <parts>          *)

Ltac2 zn_say (text : string) := Message.print (Message.of_string (String.app "@@N " text)).

Ltac2 zn_cat (parts : string list) : string := String.concat "" parts.

Ltac2 zn_id (text : string) : ident := Option.get (Ident.of_string text).

Ltac2 zn_path (reference : Std.reference) : string list :=
  List.map Ident.to_string (Env.path reference).

Ltac2 zn_qual (reference : Std.reference) : string := String.concat "." (zn_path reference).

Ltac2 zn_project (reference : Std.reference) : bool :=
  match zn_path reference with
  | top :: _ => String.equal top "ZesuSsz"
  | [] => false
  end.

Ltac2 zn_marker_module (reference : Std.reference) : bool :=
  match zn_path reference with
  | top :: rest =>
      match rest with
      | sub :: _ => Bool.and (String.equal top "ZesuSsz") (String.equal sub "Automation2")
      | [] => false
      end
  | [] => false
  end.

Ltac2 zn_head (term : constr) : constr * constr list :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments => (head, Array.to_list arguments)
  | _ => (term, [])
  end.

Ltac2 zn_is_prop (term : constr) : bool :=
  match Control.case (fun () => Constr.equal (Constr.type term) 'Prop) with
  | Val (answer, _) => answer
  | Err _ => false
  end.

Ltac2 zn_ind (term : constr) : inductive :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Ind ind _ => ind
  | _ => Control.throw Not_found
  end.

Ltac2 zn_and () := zn_ind 'and.
Ltac2 zn_ex () := zn_ind '@ex.
Ltac2 zn_true () := zn_ind 'True.

(* The unfold lemma `c_eq` of a sealed constant, when its module has one. *)
Ltac2 zn_seal_eq (reference : Std.reference) : Std.reference option :=
  let path := Env.path reference in
  match List.rev path with
  | last :: prefix =>
      let name := String.app (Ident.to_string last) "_eq" in
      Env.get (List.rev (zn_id name :: prefix))
  | [] => None
  end.

Ltac2 zn_fresh (base : string) (avoid : ident list) : ident :=
  Fresh.fresh (Fresh.Free.union (Fresh.Free.of_goal ()) (Fresh.Free.of_ids avoid)) (zn_id base).

Ltac2 zn_hyp_clause (h : ident) : Std.clause :=
  { Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)]; Std.on_concl := Std.NoOccurrences }.

Ltac2 zn_concl_clause () : Std.clause := { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }.

Ltac2 zn_all_clause () : Std.clause := { Std.on_hyps := None; Std.on_concl := Std.AllOccurrences }.

Ltac2 zn_printable (term : constr) : bool :=
  match ZesuSsz.Automation2.ResidualExport.zesu_export_variables term with
  | Some _ => true
  | None => false
  end.

(* Unfold REFERENCE in CLAUSE; undone (the call fails) when one of the terms
   AFTER gives has syntax the exporter refuses (a match, a fixpoint). *)
Ltac2 zn_unfold (reference : Std.reference) (clause : Std.clause) (after : unit -> constr list) :=
  Std.unfold [(reference, Std.AllOccurrences)] clause;
  if List.for_all zn_printable (after ()) then () else Control.zero (Tactic_failure None).

Ltac2 zn_context_terms () : constr list :=
  Control.goal () :: List.map (fun (_, _, t) => t) (Control.hyps ()).

Ltac2 zn_rewrite (lemma : Std.reference) (clause : Std.clause) :=
  Std.rewrite false [ { Std.rew_orient := Some Std.LTR; Std.rew_repeat := Std.Precisely 1;
                       Std.rew_equatn := (fun () => (Env.instantiate lemma, Std.NoBindings)) }]
    clause None.

Ltac2 zn_destruct (h : ident) (a : ident) (b : ident) :=
  ltac1:(h a b |- destruct h as [a b]) (Ltac1.of_ident h) (Ltac1.of_ident a) (Ltac1.of_ident b).

(* The witness name of `ex (fun x => P)`. *)
Ltac2 zn_witness (arguments : constr list) : string :=
  match List.rev arguments with
  | predicate :: _ =>
      match Constr.Unsafe.kind predicate with
      | Constr.Unsafe.Lambda binder _ =>
          match Constr.Binder.name binder with
          | Some id => Ident.to_string id
          | None => "w"
          end
      | _ => "w"
      end
  | [] => "w"
  end.

(* One step on hypothesis H of type T; the Ltac1 text of the step, or None. *)
Ltac2 zn_hyp_step (witnesses : ident list Ref.ref) (h : ident) (t : constr) : string option :=
  if Bool.neg (zn_is_prop t) then None else
  let (head, arguments) := zn_head t in
  let hs := Ident.to_string h in
  match Constr.Unsafe.kind head with
  | Constr.Unsafe.Ind ind _ =>
      if Ind.equal ind (zn_and ()) then
        let a := zn_fresh "Hn" [] in
        let b := zn_fresh "Hn" [a] in
        zn_destruct h a b;
        Some (zn_cat ["destruct "; hs; " as ["; Ident.to_string a; " "; Ident.to_string b; "]."])
      else if Ind.equal ind (zn_ex ()) then
        let a := zn_fresh (zn_witness arguments) [] in
        let b := zn_fresh "Hn" [a] in
        zn_destruct h a b;
        Ref.set witnesses (a :: Ref.get witnesses);
        Some (zn_cat ["destruct "; hs; " as ["; Ident.to_string a; " "; Ident.to_string b; "]."])
      else if Bool.or (Ind.equal ind (zn_true ())) (zn_marker_module (Std.IndRef ind)) then
        Std.clear [h];
        Some (zn_cat ["clear "; hs; "."])
      else None
  | Constr.Unsafe.Constant c _ =>
      let reference := Std.ConstRef c in
      if Bool.neg (zn_project reference) then None else
      match zn_seal_eq reference with
      | Some lemma =>
          match Control.case (fun () => zn_rewrite lemma (zn_hyp_clause h)) with
          | Val _ => Some (zn_cat ["rewrite @"; zn_qual lemma; " in "; hs; "."])
          | Err _ => None
          end
      | None =>
          match Control.case (fun () => zn_unfold reference (zn_hyp_clause h) (fun () => [Constr.type (Control.hyp h)])) with
          | Val _ =>
              let after := Constr.type (Control.hyp h) in
              if Constr.equal after t then None
              else Some (zn_cat ["unfold "; zn_qual reference; " in "; hs; "."])
          | Err _ => None
          end
      end
  | Constr.Unsafe.Prod _ body =>
      (* `A -> D x`: a transparent ZesuSsz definition D at the head of the
         consequence is unfolded (no destruct under the implication). *)
      if Bool.neg (Constr.Unsafe.is_closed body) then None else
      let (inner, _) := zn_head body in
      match Constr.Unsafe.kind inner with
      | Constr.Unsafe.Constant c _ =>
          let reference := Std.ConstRef c in
          let sealed := match zn_seal_eq reference with Some _ => true | None => false end in
          if Bool.or (Bool.neg (zn_project reference)) sealed then None else
          match Control.case (fun () => zn_unfold reference (zn_hyp_clause h) (fun () => [Constr.type (Control.hyp h)])) with
          | Val _ =>
              if Constr.equal (Constr.type (Control.hyp h)) t then None
              else Some (zn_cat ["unfold "; zn_qual reference; " in "; hs; "."])
          | Err _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Ltac2 rec zn_hyps (witnesses : ident list Ref.ref) (script : string list Ref.ref) (fuel : int) :=
  if Int.le fuel 0 then zn_say "fuel hypotheses" else
  let rec scan (hyps : (ident * constr option * constr) list) :=
    match hyps with
    | [] => None
    | (h, body, t) :: rest =>
        match body with
        | Some _ => scan rest
        | None => match zn_hyp_step witnesses h t with Some text => Some text | None => scan rest end
        end
    end in
  match scan (Control.hyps ()) with
  | Some text => Ref.set script (text :: Ref.get script); zn_hyps witnesses script (Int.sub fuel 1)
  | None => ()
  end.

(* ---- level 2: record fields as variables ---- *)

Ltac2 zn_record_var (h : ident) : bool :=
  match Control.case (fun () => Constr.type (Control.hyp h)) with
  | Err _ => false
  | Val (t, _) =>
      if zn_is_prop t then false else
      let (head, _) := zn_head t in
      match Constr.Unsafe.kind head with
      | Constr.Unsafe.Ind ind _ =>
          Bool.and (zn_project (Std.IndRef ind)) (Int.equal (Ind.nconstructors (Ind.data ind)) 1)
      | _ => false
      end
  end.

(* The first (innermost) application `c .. v` in TERM with V a record variable,
   C a constant not in SKIP, and the application closed. *)
Ltac2 rec zn_find (records : ident list) (skip : constant list) (term : constr)
    : (constant * constr * ident) option :=
  let recur := zn_find records skip in
  let rec many (terms : constr list) :=
    match terms with
    | [] => None
    | t :: rest => match recur t with Some found => Some found | None => many rest end
    end in
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      match many (head :: Array.to_list arguments) with
      | Some found => Some found
      | None =>
          match Constr.Unsafe.kind head with
          | Constr.Unsafe.Constant c _ =>
              match List.rev (Array.to_list arguments) with
              | last :: _ =>
                  match Constr.Unsafe.kind last with
                  | Constr.Unsafe.Var v =>
                      if Bool.and (List.mem Ident.equal v records)
                           (Bool.and (Bool.neg (List.mem Constant.equal c skip)) (Constr.Unsafe.is_closed term))
                      then Some (c, term, v) else None
                  | _ => None
                  end
              | [] => None
              end
          | _ => None
          end
      end
  | Constr.Unsafe.Prod binder body => many [Constr.Binder.type binder; body]
  | Constr.Unsafe.Lambda binder body => many [Constr.Binder.type binder; body]
  | Constr.Unsafe.LetIn binder value body => many [Constr.Binder.type binder; value; body]
  | Constr.Unsafe.Cast value _ typ => many [value; typ]
  | Constr.Unsafe.Case _ predicate _ scrutinee branches =>
      let (returned, _) := predicate in
      many (returned :: scrutinee :: Array.to_list branches)
  | Constr.Unsafe.Proj _ _ value => recur value
  | _ => None
  end.

Ltac2 zn_find_any (records : ident list) (skip : constant list) : (constant * constr * ident) option :=
  let rec scan (terms : constr list) :=
    match terms with
    | [] => None
    | t :: rest => match zn_find records skip t with Some found => Some found | None => scan rest end
    end in
  scan (Control.goal () :: List.map (fun (_, _, t) => t) (Control.hyps ())).

(* A projection: head normal form is a match on the variable itself. *)
Ltac2 zn_projection (term : constr) (v : ident) : bool :=
  match Control.case (fun () => Std.eval_hnf term) with
  | Err _ => false
  | Val (reduced, _) =>
      match Constr.Unsafe.kind reduced with
      | Constr.Unsafe.Case _ _ _ scrutinee _ =>
          match Constr.Unsafe.kind scrutinee with
          | Constr.Unsafe.Var w => Ident.equal v w
          | _ => false
          end
      | _ => false
      end
  end.

Ltac2 rec zn_lookup (name : ident) (table : (ident * constr) list) : constr option :=
  match table with
  | [] => None
  | (key, value) :: rest => if Ident.equal key name then Some value else zn_lookup name rest
  end.

(* Replace each generalised variable of TERM by its term over the original context. *)
Ltac2 zn_full (table : (ident * constr) list) (term : constr) : constr :=
  List.fold_left (fun t entry =>
    let (name, value) := entry in
    Constr.Unsafe.substnl [value] 0 (Constr.Unsafe.closenl [name] 1 t)) term table.

(* Phase 1 unfolds the ZesuSsz definitions applied to record variables (a
   projection is skipped there); phase 2 turns one projection into a variable
   and returns to phase 1, so that a definition over a new record variable is
   unfolded before any of that variable's fields is generalised. *)
Ltac2 zn_generalise (table : (ident * constr) list Ref.ref) (fuel : int) :=
  let skip := Ref.ref [] in
  let rec loop (phase : int) (passed : constant list) (fuel : int) :=
    if Int.le fuel 0 then zn_say "fuel generalise" else
    let records := List.filter zn_record_var (List.map (fun (h, _, _) => h) (Control.hyps ())) in
    match zn_find_any records (List.append passed (Ref.get skip)) with
    | None => if Int.equal phase 1 then loop 2 [] fuel else ()
    | Some (c, term, v) =>
        let reference := Std.ConstRef c in
        if zn_projection term v then
          if Int.equal phase 1 then loop phase (c :: passed) (Int.sub fuel 1) else
          let field := List.last (zn_path reference) in
          let base := match zn_lookup v (Ref.get table) with
            | Some _ => zn_cat [Ident.to_string v; "_"; field]
            | None => field
            end in
          let x := zn_fresh base [] in
          let full := zn_full (Ref.get table) term in
          Std.set false (fun () => (Some x, term)) (zn_all_clause ());
          Std.clearbody [x];
          Ref.set table ((x, full) :: Ref.get table);
          let _ := Control.case (fun () => Std.clear [v]) in
          loop 1 [] (Int.sub fuel 1)
        else
          ((if Bool.and (zn_project reference) (Bool.neg (zn_is_prop term)) then
             match Control.case (fun () => zn_unfold reference (zn_all_clause ()) zn_context_terms) with
             | Val _ => ()
             | Err _ => Ref.set skip (c :: Ref.get skip)
             end
           else Ref.set skip (c :: Ref.get skip));
           loop phase passed (Int.sub fuel 1))
    end in
  loop 1 [] fuel.

(* ---- parts ---- *)

(* Clear each fact whose type repeats an earlier fact's type. *)
Ltac2 zn_dedup () :=
  let seen := Ref.ref [] in
  List.iter (fun (h, body, t) =>
    match body with
    | Some _ => ()
    | None =>
        if Bool.neg (zn_is_prop t) then () else
        if List.exist (fun u => Constr.equal t u) (Ref.get seen) then
          let _ := Control.case (fun () => Std.clear [h]) in ()
        else Ref.set seen (t :: Ref.get seen)
    end) (Control.hyps ()).

(* The screen statement of a part (tools/oblig/normalise.py's snapshot screen):
   the part without the facts on witnesses of destructed existentials (history
   ghosts), whose values no machine state fixes; printed after the part, when
   the focused goal is no longer needed. *)
Ltac2 zn_screen (witnesses : ident list) (ks : string) :=
  List.iter (fun (h, body, t) =>
    match body with
    | Some _ => ()
    | None =>
        if Bool.neg (zn_is_prop t) then () else
        match ZesuSsz.Automation2.ResidualExport.zesu_export_variables t with
        | Some found =>
            if List.exist (fun v => List.mem Ident.equal v witnesses) found
            then let _ := Control.case (fun () => Std.clear [h]) in () else ()
        | None => ()
        end
    end) (Control.hyps ());
  match Control.case (fun () =>
    let (facts, _, _) := ZesuSsz.Automation2.ResidualExport.zesu_export_reach 2048 in
    ZesuSsz.Automation2.ResidualExport.zesu_export_statement facts) with
  | Val ((statement, _), _) =>
      zn_say (zn_cat ["part "; ks; " screen ";
                      Message.to_string (ZesuSsz.Automation2.ResidualExport.zesu_export_source statement)])
  | Err _ => ()
  end.

Ltac2 zn_leaf (witnesses : ident list) (level : int) (count : int Ref.ref) : string :=
  let k := Int.add (Ref.get count) 1 in
  Ref.set count k;
  let ks := Message.to_string (Message.of_int k) in
  let table := Ref.ref [] in
  (if Int.ge level 2 then zn_generalise table 400 else ());
  zn_dedup ();
  match Control.case (fun () =>
    let (facts, _, _) := ZesuSsz.Automation2.ResidualExport.zesu_export_reach 2048 in
    ZesuSsz.Automation2.ResidualExport.zesu_export_statement facts) with
  | Err error =>
      let why := match error with
        | ZesuSsz.Automation2.ResidualExport.ZesuExportRefused reason => reason
        | _ => "error"
        end in
      zn_say (zn_cat ["part "; ks; " refused "; why]); "fail"
  | Val ((statement, binders), _) =>
      let source := Message.to_string (ZesuSsz.Automation2.ResidualExport.zesu_export_source statement) in
      zn_say (zn_cat ["part "; ks; " binders"; String.concat "" (List.map (fun b => String.app " " (Ident.to_string b)) binders)]);
      zn_say (zn_cat ["part "; ks; " stmt "; source]);
      let arguments := List.map (fun b =>
        match zn_lookup b (Ref.get table) with
        | Some term => zn_cat [" ("; Message.to_string (ZesuSsz.Automation2.ResidualExport.zesu_export_source term); ")"]
        | None => String.app " " (Ident.to_string b)
        end) binders in
      zn_screen witnesses ks;
      zn_cat ["exact (zn_part_"; ks; String.concat "" arguments; ")"]
  end.

Ltac2 rec zn_concl (witnesses : ident list) (level : int) (count : int Ref.ref) (fuel : int) : string :=
  let goal := Control.goal () in
  let (head, _) := zn_head goal in
  let leaf () := zn_leaf witnesses level count in
  if Int.le fuel 0 then leaf () else
  match Constr.Unsafe.kind head with
  | Constr.Unsafe.Ind ind _ =>
      if Ind.equal ind (zn_and ()) then
        ltac1:(split);
        let left := Ref.ref "" in
        let right := Ref.ref "" in
        Control.dispatch [(fun () => Ref.set left (zn_concl witnesses level count (Int.sub fuel 1)));
                          (fun () => Ref.set right (zn_concl witnesses level count (Int.sub fuel 1)))];
        zn_cat ["split; [ "; Ref.get left; " | "; Ref.get right; " ]"]
      else leaf ()
  | Constr.Unsafe.Constant c _ =>
      let reference := Std.ConstRef c in
      if Bool.neg (Bool.and (zn_project reference) (zn_is_prop goal)) then leaf () else
      match zn_seal_eq reference with
      | Some lemma =>
          match Control.case (fun () => zn_rewrite lemma (zn_concl_clause ())) with
          | Val _ => zn_cat ["rewrite @"; zn_qual lemma; "; "; zn_concl witnesses level count (Int.sub fuel 1)]
          | Err _ => leaf ()
          end
      | None =>
          match Control.case (fun () => zn_unfold reference (zn_concl_clause ()) (fun () => [Control.goal ()])) with
          | Val _ =>
              if Constr.equal (Control.goal ()) goal then leaf ()
              else zn_cat ["unfold "; zn_qual reference; "; "; zn_concl witnesses level count (Int.sub fuel 1)]
          | Err _ => leaf ()
          end
      end
  | _ => leaf ()
  end.

Ltac2 zn_normalise (level : int) :=
  ltac1:(intros);
  let script := Ref.ref [] in
  let witnesses := Ref.ref [] in
  zn_hyps witnesses script 400;
  let count := Ref.ref 0 in
  let tail := zn_concl (Ref.get witnesses) level count 64 in
  zn_say (zn_cat ["link intros. "; String.concat " " (List.rev (Ref.get script)); " "; tail; "."]);
  zn_say (zn_cat ["done "; Message.to_string (Message.of_int level); " ";
                  Message.to_string (Message.of_int (Ref.get count))]).
