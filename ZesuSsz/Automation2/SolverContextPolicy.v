(* Generated declarations from Evidence/solver_context_policy.json. *)
From Coq Require Import ZArith.ZArith Lists.List Strings.String Lia Ring Zify.
Declare ML Module "zesu-solver-context.plugin".
Global Set Zesu Solver PropLimit 64.
Global Set Zesu Solver NodeLimit 173732.
Global Set Zesu Solver Guard.
Notation zesu_solver_prop_limit := (64%Z) (only parsing).
Notation zesu_solver_node_limit := (173732%Z) (only parsing).
Definition zesu_solver_exception_labels : list string := nil.
