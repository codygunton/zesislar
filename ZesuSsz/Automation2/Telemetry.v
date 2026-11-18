From Ltac2 Require Import Ltac2.
Declare ML Module "zesu-signature-gates.plugin".
Set Default Proof Mode "Classic".

(* Per-call solver telemetry. Off unless coqc runs with ZESU_TELEMETRY=1 in
   its environment (read once); callers stay unchanged. Off, a wrapped call
   costs one flag read and runs its tactic as is. On, each wrapped call prints
   one line on stdout when it first succeeds or finally fails:

     @@T kind=<k> site=<ltac name> stage=<stage> facts=<n> nodes=<n>
         goal_nodes=<n> ms=<wall> ok=<0|1> cpu_ms=<cpu> ts_us=<start, epoch us>
         rss0_kb=<before> rss1_kb=<after>
         [caller=<frames> shape=<goal class> origins=<modules>]

   `facts` counts the Prop hypotheses without a body, `nodes` their nodes and
   `goal_nodes` the goal's, in the units of LinearFirstLia's node budgets
   (-1 off a single focused goal). `stage` is the innermost enclosing
   `zesu_telemetry_stage`. With ZESU_TELEMETRY_CALLERS=1 as well, an Ltac1
   site adds `caller`, its Ltac call stack, innermost first, as
   `name@module:line` frames joined by `>` (`-` when Coq kept none),
   `shape`, a coarse class of the goal, and `origins`, the modules of the
   globals in the goal (and, marked `~`, of its variables' type heads). The
   wrapper never changes the goal, the context, the result or the failure. *)
Ltac2 @ external zesu_telemetry_enabled : unit -> bool :=
  "zesu-signature-gates.plugin" "telemetry_enabled".
Ltac2 @ external zesu_telemetry_sample : unit -> int list :=
  "zesu-signature-gates.plugin" "telemetry_sample".
Ltac2 @ external zesu_telemetry_sizes : unit -> int list :=
  "zesu-signature-gates.plugin" "telemetry_sizes".
Ltac2 @ external zesu_telemetry_caller : Ltac1.t -> string :=
  "zesu-signature-gates.plugin" "telemetry_caller".
Ltac2 @ external zesu_telemetry_emit :
  string -> string -> string -> int list -> int list -> bool -> unit :=
  "zesu-signature-gates.plugin" "telemetry_emit".
Ltac2 @ external zesu_telemetry_stage_swap : string -> string :=
  "zesu-signature-gates.plugin" "telemetry_stage_swap".

(* One line at the first success or at the final failure. Later successes
   after backtracking print again; a failure after a success prints nothing. *)
Ltac2 zesu_telemetry_measure_from (kind : string) (site : string) (caller : string)
    (tac : unit -> 'a) : 'a :=
  let sizes := zesu_telemetry_sizes () in
  let start := zesu_telemetry_sample () in
  let succeeded := Ref.ref false in
  Control.plus (fun () =>
      let result := tac () in
      Ref.set succeeded true;
      zesu_telemetry_emit kind site caller sizes start true;
      result)
    (fun error =>
      (if Ref.get succeeded then ()
       else zesu_telemetry_emit kind site caller sizes start false);
      Control.zero error).

Ltac2 zesu_telemetry_measure (kind : string) (site : string) (tac : unit -> 'a) : 'a :=
  zesu_telemetry_measure_from kind site "-" tac.

Ltac2 zesu_telemetry_run (kind : string) (site : string) (tac : unit -> 'a) : 'a :=
  if zesu_telemetry_enabled () then zesu_telemetry_measure kind site tac else tac ().

(* A stage line (kind=stage) around the tactic; solver lines inside it carry
   its name. *)
Ltac2 zesu_telemetry_stage (stage : string) (tac : unit -> 'a) : 'a :=
  if zesu_telemetry_enabled () then
    let outer := zesu_telemetry_stage_swap stage in
    Control.plus (fun () =>
        let result := zesu_telemetry_measure "stage" stage tac in
        let _ := zesu_telemetry_stage_swap outer in
        result)
      (fun error => let _ := zesu_telemetry_stage_swap outer in Control.zero error)
  else tac ().

(* Ltac1 entries: `zesu_telemetry_call kind site tac` needs Ltac2 strings, so
   each Ltac1 site binds its labels with
   `ltac2:(tac |- zesu_telemetry_ltac1 "kind" "site" tac)`. The closure `tac`
   carries the Ltac call stack of the site. *)
Ltac2 zesu_telemetry_ltac1 (kind : string) (site : string) (tac : Ltac1.t) :=
  if zesu_telemetry_enabled ()
  then zesu_telemetry_measure_from kind site (zesu_telemetry_caller tac) (fun () => Ltac1.run tac)
  else Ltac1.run tac.
Ltac2 zesu_telemetry_stage_ltac1 (stage : string) (tac : Ltac1.t) :=
  zesu_telemetry_stage stage (fun () => Ltac1.run tac).

(* Step and alternative records (off unless ZESU_TELEMETRY=1, like the rest).
   `zesu_tstep (T)` wraps one iteration of a pass's search loop and prints
   kind=step site=<skeleton of the Lithium goal before the step> (ok=0 when
   no alternative applied and the loop ends). `zesu_talt NAME (idtac; T)`
   wraps one alternative and prints kind=alt site=NAME when it succeeds and
   kind=altfail site=NAME when it fails after using more than 1 ms CPU
   (cheaper failures are left out to keep the log small; the step record's
   time minus its alternatives' is their sum). Each record covers the
   wrapped tactic's own time only. When a later failure backtracks into a
   wrapper that succeeded, it prints kind=backtrack site=NAME (a step:
   kind=stepbacktrack site=<skeleton>) with the time from its success to
   the backtrack, spent in the continuation (above 1 ms CPU; the backtrack
   records of nested wrappers cover the same continuation), and its clock
   restarts: a further success or failure of T counts from there. A step
   that ends after a success prints no further step record. Write the
   alternative as `(idtac; T)`: Ltac1 runs a match-bodied argument (inline
   or through a tactic name) when it reads the notation's argument, before
   the wrapper starts, which would put its time outside the record. Off,
   both wrappers cost one flag read and run their tactic as is. *)
Ltac2 rec zesu_telemetry_literal (term : constr) : bool :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.Ind _ _ => true
  | Constr.Unsafe.App head arguments =>
      match Constr.Unsafe.kind head with
      | Constr.Unsafe.Constructor _ _ =>
          Array.fold_left (fun ok argument => if ok then zesu_telemetry_literal argument else false)
            true arguments
      | _ => false
      end
  | _ => false
  end.

Ltac2 zesu_telemetry_hole () :=
  Constr.Unsafe.make (Constr.Unsafe.Var (Option.get (Ident.of_string "__"))).

(* The goal down to `depth` application levels; closed constructor terms
   stay whole, binders, matches, fixpoints and deeper subterms become `__`. *)
Ltac2 rec zesu_telemetry_skeleton (depth : int) (term : constr) : constr :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      if zesu_telemetry_literal term then term
      else if Int.le depth 0 then zesu_telemetry_hole ()
      else Constr.Unsafe.make (Constr.Unsafe.App (zesu_telemetry_skeleton depth head)
        (Array.map (zesu_telemetry_skeleton (Int.sub depth 1)) arguments))
  | Constr.Unsafe.Lambda _ _ => zesu_telemetry_hole ()
  | Constr.Unsafe.LetIn _ _ _ => zesu_telemetry_hole ()
  | Constr.Unsafe.Case _ _ _ _ _ => zesu_telemetry_hole ()
  | Constr.Unsafe.Fix _ _ _ _ => zesu_telemetry_hole ()
  | Constr.Unsafe.Prod _ _ => zesu_telemetry_hole ()
  | Constr.Unsafe.Cast value _ _ => zesu_telemetry_skeleton depth value
  | _ => term
  end.

(* At most 160 characters, white space as `_`: one token of the record. *)
Ltac2 zesu_telemetry_token (s : string) : string :=
  let n := if Int.lt 160 (String.length s) then 160 else String.length s in
  let out := String.make n (Char.of_int 95) in
  let rec go i :=
    if Int.lt i n then
      ((if Int.le (Char.to_int (String.get s i)) 32 then () else String.set out i (String.get s i));
       go (Int.add i 1))
    else () in
  go 0; out.

Ltac2 zesu_telemetry_ends_with (s : string) (suffix : string) : bool :=
  let n := String.length s in
  let m := String.length suffix in
  if Int.lt n m then false else
  let rec go i :=
    if Int.lt i m then
      (if Int.equal (Char.to_int (String.get s (Int.add (Int.sub n m) i)))
                    (Char.to_int (String.get suffix i))
       then go (Int.add i 1) else false)
    else true in
  go 0.

(* The skeleton of the focused goal; of an `envs_entails` goal, its target.
   `?` unless exactly one goal is focused: Control.goal would throw
   Not_focussed, which Control.case does not catch. *)
Ltac2 zesu_telemetry_goal_head () : string :=
  let goals := Ref.ref 0 in
  Control.enter (fun () => Ref.set goals (Int.add (Ref.get goals) 1));
  if Int.equal (Ref.get goals) 1 then
    match Control.case (fun () =>
      let concl := Control.goal () in
      let target := match Constr.Unsafe.kind concl with
        | Constr.Unsafe.App head arguments =>
            if zesu_telemetry_ends_with (Message.to_string (Message.of_constr head)) "envs_entails"
            then Array.get arguments (Int.sub (Array.length arguments) 1) else concl
        | _ => concl
        end in
      Message.to_string (Message.of_constr (zesu_telemetry_skeleton 2 target))) with
    | Val (s, _) => zesu_telemetry_token s
    | Err _ => "?"
    end
  else "?".

Ltac2 zesu_telemetry_cpu_us (sample : int list) : int :=
  match sample with
  | [_; cpu; _] => cpu
  | _ => 0
  end.

(* The measuring paths; the switched entries below run them only when on. *)
Ltac2 zesu_telemetry_over_1ms (start : int list) : bool :=
  Int.lt 1000 (Int.sub (zesu_telemetry_cpu_us (zesu_telemetry_sample ())) (zesu_telemetry_cpu_us start)).

(* Run right after a wrapper's success: a choice point without a further
   success. A later failure backtracking into the wrapper reaches its
   handler first, which prints `kind` with the time since the success and
   restarts the wrapper's clock `start` at the re-entry; then the failure
   goes on into the wrapped tactic unchanged. *)
Ltac2 zesu_telemetry_on_backtrack (kind : string) (site : string) (start : int list Ref.ref) : unit :=
  let success := zesu_telemetry_sample () in
  Control.plus (fun () => ())
    (fun error =>
      (if zesu_telemetry_over_1ms success
       then zesu_telemetry_emit kind site "-" [-1; -1; -1] success false else ());
      Ref.set start (zesu_telemetry_sample ());
      Control.zero error).

Ltac2 zesu_telemetry_alt_measured (name : string) (tac : Ltac1.t) : unit :=
  let start := Ref.ref (zesu_telemetry_sample ()) in
  Control.plus (fun () =>
      Ltac1.run tac;
      zesu_telemetry_emit "alt" name "-" [-1; -1; -1] (Ref.get start) true;
      zesu_telemetry_on_backtrack "backtrack" name start)
    (fun error =>
      (if zesu_telemetry_over_1ms (Ref.get start)
       then zesu_telemetry_emit "altfail" name "-" [-1; -1; -1] (Ref.get start) false else ());
      Control.zero error).

Ltac2 zesu_telemetry_step_measured (tac : Ltac1.t) : unit :=
  let head := zesu_telemetry_goal_head () in
  let start := Ref.ref (zesu_telemetry_sample ()) in
  let succeeded := Ref.ref false in
  Control.plus (fun () =>
      Ltac1.run tac;
      zesu_telemetry_emit "step" head "-" [-1; -1; -1] (Ref.get start) true;
      Ref.set succeeded true;
      zesu_telemetry_on_backtrack "stepbacktrack" head start)
    (fun error =>
      (if Ref.get succeeded then ()
       else zesu_telemetry_emit "step" head "-" [-1; -1; -1] (Ref.get start) false);
      Control.zero error).

Ltac2 zesu_telemetry_alt (name : string) (tac : Ltac1.t) : unit :=
  if zesu_telemetry_enabled () then zesu_telemetry_alt_measured name tac else Ltac1.run tac.

Ltac2 zesu_telemetry_step (tac : Ltac1.t) : unit :=
  if zesu_telemetry_enabled () then zesu_telemetry_step_measured tac else Ltac1.run tac.

Tactic Notation "zesu_talt" ident(i) tactic3(t) :=
  let w := ltac2:(i t |- zesu_telemetry_alt (Ident.to_string (Option.get (Ltac1.to_ident i))) t) in w i t.
Tactic Notation "zesu_tstep" tactic3(t) :=
  let w := ltac2:(t |- zesu_telemetry_step t) in w t.

(* Succeeds exactly when the switch is on. *)
Ltac zesu_telemetry_on :=
  ltac2:(if zesu_telemetry_enabled () then () else Control.zero (Tactic_failure None)).
