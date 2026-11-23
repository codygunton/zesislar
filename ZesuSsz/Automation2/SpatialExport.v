Require Import isla.riscv64.riscv64.
Require ZesuSsz.Automation2.ContextCollection.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* Spatial leftover export (diagnostic only; no production tactic changes a
   goal through this module).

   `zesu_diag_export_final` (Diagnostics.v) prints `@@X skip final spatial`
   for an Iris goal that is still open at the end of a block. With the
   switch `ZesuSpatialExportOn` (import `SpatialExportOn`), it prints one
   `@@S` record after that line: what the stuck judgment seeks, the owned
   resources of the context, and the pure facts that share a local variable
   with the sought term. `tools/oblig/package.py` turns the record into a
   diagnosis task. The record never changes the goal or the context; an
   error while building it prints `@@S skip <kind> error` and nothing else.

   Record grammar (one line per item; every line starts with `@@S `; no item
   contains a line break, because the printer's breaks and indentation runs
   are folded into one space, inside string literals too):

     record   ::= begin head seek seekarg* seekvars res* def* fact* counts end
     begin    ::= "@@S begin " KIND                    KIND: the export point (`final`)
     head     ::= "@@S head " PATH [" " PATH]          the qualified head of the
                                                       judgment; for `find_in_context`,
                                                       also the qualified find kind
     seek     ::= "@@S seek " SORT
     seekarg  ::= "@@S seek-arg " SHOWN                one line per sought argument, in
                                                       the order of the table below
     SORT     ::= "reg"         find_in_context (FindRegMapsTo r):          args r
                | "struct-reg"  find_in_context (FindStructRegMapsTo r f):  args r, f
                | "mem"         find_in_context (FindMemMapsTo a):          args a
                | "instr"       find_in_context (FindInstrKind a l):        args a
                | "direct"      find_in_context (FindDirect P):             args P
                | "find"        another find_in_context kind:               args the kind
                | "subsume"     subsume P Q T:                              args P, Q
                | "pc"          instr_pre' l a P (instr_body, instr_pre):   args a
                | "pure"        ⌜c⌝ ∗ T:                                    args c
                | "none"        any other judgment:                         no args
     seekvars ::= "@@S seek-vars" (" " IDENT)*         local variables of the sought
                                                       terms, closed under the bodies
                                                       of local definitions
     res      ::= "@@S res " ("p" | "s") " " NAME " " SHOWN
                                                       one line per resource of the
                                                       intuitionistic (p) and the
                                                       spatial (s) environment, oldest
                                                       first
                | "@@S res ? ? opaque"                 the only res line when the
                                                       environments are not literal
                                                       `Envs`/`Esnoc` values; then
                                                       both environment counts are 0
     NAME     ::= the string literal of an `INamed` name, or "~" N (decimal) for `IAnon N`
     def      ::= "@@S def " IDENT " " SHOWN           a sought local definition (its body)
     fact     ::= "@@S fact " IDENT " " SHOWN          a Prop hypothesis whose local
                                                       variables meet seek-vars, in
                                                       context order
     counts   ::= "@@S counts persistent=" N " spatial=" N " facts=" N " shared=" N
                                                       facts: every Prop hypothesis
                                                       without a body; shared: fact lines
     SHOWN    ::= "full " TEXT                         at most 512 term nodes
                | "big " PATH (" " IDENT)*             larger: head and local variables
                                                       (one "?" when the term has
                                                       syntax ContextCollection refuses)
     TEXT     ::= the default printer's text of the term, on one line
     PATH     ::= a dot-separated qualified name, or "?" for a non-global head *)
Class ZesuSpatialExportOn : Prop := zesu_spatial_export_on_instance : True.

Ltac zesu_spatial_export_on := let _ := constr:(_ : ZesuSpatialExportOn) in idtac.

Ltac2 Type exn ::= [ ZesuSpatialOpaque ].

(* Line breaks and runs of blanks become one space. *)
Ltac2 zesu_spatial_flat (text : string) : string :=
  let length := String.length text in
  let rec go (index : int) (blank : bool) (parts : string list) :=
    if Int.equal index length then String.concat "" (List.rev parts) else
    let code := Char.to_int (String.get text index) in
    if Bool.or (Int.equal code 10) (Bool.or (Int.equal code 32)
        (Bool.or (Int.equal code 13) (Int.equal code 9))) then
      if blank then go (Int.add index 1) true parts
      else go (Int.add index 1) true (" " :: parts)
    else go (Int.add index 1) false (String.make 1 (String.get text index) :: parts) in
  go 0 false [].

Ltac2 zesu_spatial_text (term : constr) : string :=
  zesu_spatial_flat (Message.to_string (Message.of_constr term)).

Ltac2 zesu_spatial_path (term : constr) : string :=
  let path (reference : Std.reference) :=
    String.concat "." (List.map Ident.to_string (Env.path reference)) in
  let head := match Constr.Unsafe.kind term with
    | Constr.Unsafe.App head _ => head
    | _ => term
    end in
  match Constr.Unsafe.kind head with
  | Constr.Unsafe.Constant c _ => path (Std.ConstRef c)
  | Constr.Unsafe.Ind ind _ => path (Std.IndRef ind)
  | Constr.Unsafe.Constructor k _ => path (Std.ConstructRef k)
  | Constr.Unsafe.Var name => Ident.to_string name
  | _ => "?"
  end.

(* Local variables, or None for syntax that ContextCollection refuses. *)
Ltac2 zesu_spatial_variables (term : constr) : ident list option :=
  match Control.case (fun () => ZesuSsz.Automation2.ContextCollection.zesu_context_variables term) with
  | Val (found, _) => Some (List.rev found)
  | Err _ => None
  end.

Ltac2 zesu_spatial_shown (term : constr) : string :=
  if ZesuSsz.Automation2.ContextCollection.zesu_select_small 512 term
  then String.app "full " (zesu_spatial_text term)
  else
    let variables := match zesu_spatial_variables term with
      | Some found => List.map (fun name => String.app " " (Ident.to_string name)) found
      | None => [" ?"]
      end in
    String.concat "" ("big " :: zesu_spatial_path term :: variables).

(* An Iris environment `Esnoc (... (Enil)) i P` as (name, resource) pairs,
   oldest first. *)
Ltac2 rec zesu_spatial_env (env : constr) : (constr * constr) list :=
  match Constr.Unsafe.kind env with
  | Constr.Unsafe.App head arguments =>
      match Constr.Unsafe.kind head with
      | Constr.Unsafe.Constructor _ _ =>
          if Int.equal (Array.length arguments) 4 then
            List.append (zesu_spatial_env (Array.get arguments 1))
              [(Array.get arguments 2, Array.get arguments 3)]
          else if Int.equal (Array.length arguments) 1 then []
          else Control.zero ZesuSpatialOpaque
      | _ => Control.zero ZesuSpatialOpaque
      end
  | _ => Control.zero ZesuSpatialOpaque
  end.

(* A closed positive (constructors xI, xO, xH) as an integer. *)
Ltac2 rec zesu_spatial_positive (term : constr) : int option :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      match Constr.Unsafe.kind head with
      | Constr.Unsafe.Constructor k _ =>
          if Int.equal (Array.length arguments) 1 then
            match zesu_spatial_positive (Array.get arguments 0) with
            | Some value =>
                if Int.equal (Constructor.index k) 0 then Some (Int.add (Int.mul 2 value) 1)
                else if Int.equal (Constructor.index k) 1 then Some (Int.mul 2 value)
                else None
            | None => None
            end
          else None
      | _ => None
      end
  | Constr.Unsafe.Constructor k _ => if Int.equal (Constructor.index k) 2 then Some 1 else None
  | _ => None
  end.

(* `INamed "H"` prints as its string literal, `IAnon n` as `~n`. *)
Ltac2 zesu_spatial_name (name : constr) : string :=
  match Constr.Unsafe.kind name with
  | Constr.Unsafe.App head arguments =>
      match Constr.Unsafe.kind head with
      | Constr.Unsafe.Constructor k _ =>
          if Int.equal (Constructor.index k) 0 then
            match zesu_spatial_positive (Array.get arguments 0) with
            | Some value => String.app "~" (Message.to_string (Message.of_int value))
            | None => String.app "~" (zesu_spatial_text (Array.get arguments 0))
            end
          else zesu_spatial_text (Array.get arguments 0)
      | _ => zesu_spatial_text name
      end
  | _ => zesu_spatial_text name
  end.

(* The (intuitionistic, spatial) environments of an `envs_entails` goal. *)
Ltac2 zesu_spatial_envs (goal : constr) : ((constr * constr) list * (constr * constr) list) option :=
  match Control.case (fun () =>
    match Constr.Unsafe.kind goal with
    | Constr.Unsafe.App _ arguments =>
        let envs := Array.get arguments (Int.sub (Array.length arguments) 2) in
        match Constr.Unsafe.kind envs with
        | Constr.Unsafe.App head parts =>
            match Constr.Unsafe.kind head with
            | Constr.Unsafe.Constructor _ _ =>
                if Int.equal (Array.length parts) 4 then
                  (zesu_spatial_env (Array.get parts 1), zesu_spatial_env (Array.get parts 2))
                else Control.zero ZesuSpatialOpaque
            | _ => Control.zero ZesuSpatialOpaque
            end
        | _ => Control.zero ZesuSpatialOpaque
        end
    | _ => Control.zero ZesuSpatialOpaque
    end) with
  | Val (pair, _) => Some pair
  | Err _ => None
  end.

Ltac2 zesu_spatial_member (name : ident) (names : ident list) :=
  ZesuSsz.Automation2.ContextCollection.zesu_context_member name names.

(* The variables of the sought terms, closed under local definition bodies. *)
Ltac2 zesu_spatial_seek_variables (sought : constr list) : ident list :=
  let add (found : ident list) (name : ident) :=
    if zesu_spatial_member name found then found else List.append found [name] in
  let start := List.fold_left (fun found term =>
    match zesu_spatial_variables term with
    | Some names => List.fold_left add found names
    | None => found
    end) [] sought in
  let reached := Ref.ref start in
  let rec close () :=
    let grown := List.fold_left (fun found declaration =>
      let (name, body, _) := declaration in
      match body with
      | Some value =>
          if zesu_spatial_member name found then
            match zesu_spatial_variables value with
            | Some names => List.fold_left add found names
            | None => found
            end
          else found
      | None => found
      end) (Ref.get reached) (Control.hyps ()) in
    if Int.equal (List.length grown) (List.length (Ref.get reached)) then ()
    else (Ref.set reached grown; close ()) in
  close ();
  Ref.get reached.

Ltac2 zesu_spatial_lines (kind : string) (sort : string) (sought : constr list) : string list :=
  let goal := Control.goal () in
  let target := match Constr.Unsafe.kind goal with
    | Constr.Unsafe.App _ arguments => Array.get arguments (Int.sub (Array.length arguments) 1)
    | _ => goal
    end in
  let finds := ["reg"; "struct-reg"; "mem"; "instr"; "direct"; "find"] in
  let head := match Constr.Unsafe.kind target with
    | Constr.Unsafe.App _ arguments =>
        if List.mem String.equal sort finds
        then String.concat " " [zesu_spatial_path target;
          zesu_spatial_path (Array.get arguments (Int.sub (Array.length arguments) 2))]
        else zesu_spatial_path target
    | _ => zesu_spatial_path target
    end in
  let seek := List.map (fun term => String.app "@@S seek-arg " (zesu_spatial_shown term)) sought in
  let variables := zesu_spatial_seek_variables sought in
  let seek_vars := String.concat "" ("@@S seek-vars" ::
    List.map (fun name => String.app " " (Ident.to_string name)) variables) in
  let (resources, persistent, spatial) := match zesu_spatial_envs goal with
    | Some (intuitionistic, owned) =>
        let line (tag : string) (entry : constr * constr) :=
          let (name, resource) := entry in
          String.concat "" ["@@S res "; tag; " "; zesu_spatial_name name; " ";
            zesu_spatial_shown resource] in
        (List.append (List.map (line "p") intuitionistic) (List.map (line "s") owned),
         List.length intuitionistic, List.length owned)
    | None => (["@@S res ? ? opaque"], 0, 0)
    end in
  let hyps := Control.hyps () in
  let definitions := List.fold_right (fun declaration found =>
    let (name, body, _) := declaration in
    match body with
    | Some value =>
        if zesu_spatial_member name variables then
          String.concat "" ["@@S def "; Ident.to_string name; " "; zesu_spatial_shown value] :: found
        else found
    | None => found
    end) hyps [] in
  let facts := List.filter (fun declaration =>
    let (_, body, typ) := declaration in
    match body with
    | None => ZesuSsz.Automation2.ContextCollection.zesu_context_proposition typ
    | Some _ => false
    end) hyps in
  let shared := List.fold_right (fun declaration found =>
    let (name, _, typ) := declaration in
    match zesu_spatial_variables typ with
    | Some names =>
        if ZesuSsz.Automation2.ContextCollection.zesu_context_intersects names variables then
          String.concat "" ["@@S fact "; Ident.to_string name; " "; zesu_spatial_shown typ] :: found
        else found
    | None => found
    end) facts [] in
  let counts := String.concat "" ["@@S counts persistent=";
    Message.to_string (Message.of_int persistent); " spatial=";
    Message.to_string (Message.of_int spatial); " facts=";
    Message.to_string (Message.of_int (List.length facts)); " shared=";
    Message.to_string (Message.of_int (List.length shared))] in
  List.concat [
    [String.app "@@S begin " kind; String.app "@@S head " head; String.app "@@S seek " sort];
    seek; [seek_vars];
    resources; definitions; shared; [counts; "@@S end"]].

(* The record of the focused goal. All lines are built before the first is
   printed, so a failure prints only the skip line. *)
Ltac2 zesu_spatial_record (kind : string) (sort : string) (sought : constr list) :=
  match Control.case (fun () => zesu_spatial_lines kind sort sought) with
  | Val (lines, _) => List.iter (fun line => Message.print (Message.of_string line)) lines
  | Err _ => Message.print (Message.of_string (String.concat "" ["@@S skip "; kind; " error"]))
  end.

Ltac2 zesu_spatial_record1 (sort : string) (terms : Ltac1.t list) :=
  zesu_spatial_record "final" sort
    (List.map (fun term => Option.get (Ltac1.to_constr term)) terms).

(* The `@@S` record of the focused Iris goal at the end of a block. *)
Ltac zesu_spatial_export_final :=
  lazymatch goal with
  | |- environments.envs_entails _ ?target =>
      lazymatch target with
      | find_in_context (FindRegMapsTo ?r) _ =>
          let run := ltac2:(r |- zesu_spatial_record1 "reg" [r]) in run r
      | find_in_context (FindStructRegMapsTo ?r ?f) _ =>
          let run := ltac2:(r f |- zesu_spatial_record1 "struct-reg" [r; f]) in run r f
      | find_in_context (FindMemMapsTo ?a) _ =>
          let run := ltac2:(a |- zesu_spatial_record1 "mem" [a]) in run a
      | find_in_context (FindInstrKind ?a _) _ =>
          let run := ltac2:(a |- zesu_spatial_record1 "instr" [a]) in run a
      | find_in_context (FindDirect ?P) _ =>
          let run := ltac2:(p |- zesu_spatial_record1 "direct" [p]) in run P
      | find_in_context ?kind _ =>
          let run := ltac2:(k |- zesu_spatial_record1 "find" [k]) in run kind
      | subsume ?P ?Q _ =>
          let run := ltac2:(p q |- zesu_spatial_record1 "subsume" [p; q]) in run P Q
      | instr_pre' _ ?a _ =>
          let run := ltac2:(a |- zesu_spatial_record1 "pc" [a]) in run a
      | bi_sep (bi_pure ?c) _ =>
          let run := ltac2:(c |- zesu_spatial_record1 "pure" [c]) in run c
      | _ => ltac2:(zesu_spatial_record1 "none" [])
      end
  end.
