From Ltac2 Require Import Ltac2.
Declare ML Module "zesu-signature-gates.plugin".
Set Default Proof Mode "Classic".

(* Per-call solver telemetry. Off unless coqc runs with ZESU_TELEMETRY=1 in
   its environment (read once); callers stay unchanged. Off, a wrapped call
   costs one flag read and runs its tactic as is. On, each wrapped call prints
   one line on stdout when it first succeeds or finally fails:

     @@T kind=<k> site=<ltac name> stage=<stage> facts=<n> nodes=<n>
         goal_nodes=<n> ms=<wall> ok=<0|1> cpu_ms=<cpu> ts_us=<start, epoch us>
         rss0_kb=<before> rss1_kb=<after> [caller=<frames> shape=<goal class>]

   `facts` counts the Prop hypotheses without a body, `nodes` their nodes and
   `goal_nodes` the goal's, in the units of LinearFirstLia's node budgets
   (-1 off a single focused goal). `stage` is the innermost enclosing
   `zesu_telemetry_stage`. With ZESU_TELEMETRY_CALLERS=1 as well, an Ltac1
   site adds `caller`, its Ltac call stack, innermost first, as
   `name@module:line` frames joined by `>` (`-` when Coq kept none), and
   `shape`, a coarse class of the goal. The wrapper never changes the goal,
   the context, the result or the failure. *)
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

(* Succeeds exactly when the switch is on. *)
Ltac zesu_telemetry_on :=
  ltac2:(if zesu_telemetry_enabled () then () else Control.zero (Tactic_failure None)).
