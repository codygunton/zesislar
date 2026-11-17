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

   `facts` counts the Prop hypotheses without a body, `nodes` their nodes and
   `goal_nodes` the goal's (LinearFirstLia's int walk; -1 off a single focused
   goal). `stage` is the innermost enclosing `zesu_telemetry_stage`. The
   wrapper never changes the goal, the context, the result or the failure. *)
Ltac2 @ external zesu_telemetry_enabled : unit -> bool :=
  "zesu-signature-gates.plugin" "telemetry_enabled".
Ltac2 @ external zesu_telemetry_sample : unit -> int list :=
  "zesu-signature-gates.plugin" "telemetry_sample".
Ltac2 @ external zesu_telemetry_emit :
  string -> string -> int -> int -> int -> int list -> bool -> unit :=
  "zesu-signature-gates.plugin" "telemetry_emit".
Ltac2 @ external zesu_telemetry_stage_swap : string -> string :=
  "zesu-signature-gates.plugin" "telemetry_stage_swap".
(* Measurement only: goal and pruned-context hashes (gk pk pn wk). *)
Ltac2 @ external zesu_telemetry_key : unit -> int list :=
  "zesu-signature-gates.plugin" "telemetry_key".

Ltac2 zesu_telemetry_goal_key () :=
  match Control.case (fun () => let _ := Control.goal () in zesu_telemetry_key ()) with
  | Val (key, _) => key
  | Err _ => []
  end.

(* The node walk lives in LinearFirstLia, which sets these. *)
Ltac2 mutable zesu_telemetry_nodes : constr -> int := fun _ => -1.
Ltac2 mutable zesu_telemetry_is_prop : constr -> bool := fun _ => true.

Ltac2 zesu_telemetry_sizes () :=
  match Control.case (fun () =>
    let goal_nodes := zesu_telemetry_nodes (Control.goal ()) in
    List.fold_left (fun counts declaration =>
      let (facts, nodes, goal_nodes) := counts in
      let (_, body, typ) := declaration in
      match body with
      | Some _ => counts
      | None =>
          if zesu_telemetry_is_prop typ
          then (Int.add facts 1, Int.add nodes (zesu_telemetry_nodes typ), goal_nodes)
          else counts
      end) (0, 0, goal_nodes) (Control.hyps ())) with
  | Val (counts, _) => counts
  | Err _ => (-1, -1, -1)
  end.

(* One line at the first success or at the final failure. Later successes
   after backtracking print again; a failure after a success prints nothing. *)
Ltac2 zesu_telemetry_measure (kind : string) (site : string) (tac : unit -> 'a) : 'a :=
  let (facts, nodes, goal_nodes) := zesu_telemetry_sizes () in
  let key := zesu_telemetry_goal_key () in
  let start := List.append (zesu_telemetry_sample ()) key in
  let succeeded := Ref.ref false in
  Control.plus (fun () =>
      let result := tac () in
      Ref.set succeeded true;
      zesu_telemetry_emit kind site facts nodes goal_nodes start true;
      result)
    (fun error =>
      (if Ref.get succeeded then ()
       else zesu_telemetry_emit kind site facts nodes goal_nodes start false);
      Control.zero error).

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
   `ltac2:(tac |- zesu_telemetry_ltac1 "kind" "site" tac)`. *)
Ltac2 zesu_telemetry_ltac1 (kind : string) (site : string) (tac : Ltac1.t) :=
  zesu_telemetry_run kind site (fun () => Ltac1.run tac).
Ltac2 zesu_telemetry_stage_ltac1 (stage : string) (tac : Ltac1.t) :=
  zesu_telemetry_stage stage (fun () => Ltac1.run tac).

(* Succeeds exactly when the switch is on. *)
Ltac zesu_telemetry_on :=
  ltac2:(if zesu_telemetry_enabled () then () else Control.zero (Tactic_failure None)).
