From Ltac2 Require Import Ltac2.

Declare ML Module "zesu-signature-gates.trace-observer".

Ltac2 @ external trace_block_around :
  string -> (string * (unit -> unit)) list -> (unit -> unit) -> unit :=
  "zesu-signature-gates.trace-observer" "around".

Ltac2 @ external trace_block_snapshot : string -> unit :=
  "zesu-signature-gates.trace-observer" "snapshot".
