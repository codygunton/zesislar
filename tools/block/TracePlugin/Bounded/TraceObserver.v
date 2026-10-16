From Ltac2 Require Import Ltac2 Ref.
Declare ML Module "p0-bounded-trace.trace-observer".
Ltac2 @ external trace_bounded_filtered :
  string -> (unit -> bool) -> (string * (unit -> unit)) list -> (unit -> unit) -> unit :=
  "p0-bounded-trace.trace-observer" "filtered".
Ltac2 @ external trace_bounded_snapshot : string -> unit :=
  "p0-bounded-trace.trace-observer" "snapshot".
Ltac2 @ external trace_bounded_checkpoint : string -> constr -> unit :=
  "p0-bounded-trace.trace-observer" "checkpoint".
Ltac2 trace_bounded_ltac1_guard (prefix : unit -> unit) (test : Ltac1.t) :=
  prefix ();
  let result := Ref.ref None in
  Ltac1.apply test [Ltac1.of_constr constr:(tt)] (fun value =>
    match Ltac1.to_constr value with
    | Some term =>
        if Constr.equal term constr:(true) then Ref.set result (Some true)
        else if Constr.equal term constr:(false) then Ref.set result (Some false)
        else Control.throw (Invalid_argument (Some (Message.of_string "The typed guard did not return a Boolean constructor")))
    | None => Control.throw (Invalid_argument (Some (Message.of_string "The typed guard did not return a constr")))
    end);
  match Ref.get result with
  | Some value => value
  | None => Control.throw (Invalid_argument (Some (Message.of_string "The typed guard returned no value")))
  end.

Ltac2 @ external trace_bounded_status : unit -> string :=
  "p0-bounded-trace.trace-observer" "status".
Ltac2 @ external trace_bounded_complete : unit -> bool :=
  "p0-bounded-trace.trace-observer" "complete".
