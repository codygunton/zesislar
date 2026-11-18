(* Generated declarations from Evidence/solver_context_policy.json. *)
From Coq Require Import ZArith.ZArith Lists.List Strings.String.
Notation zesu_solver_prop_limit := (64%Z) (only parsing).
Notation zesu_solver_node_limit := (173732%Z) (only parsing).
Notation zesu_projection_depth_limit := (4%Z) (only parsing).
Notation zesu_projection_body_nodes_limit := (4096%Z) (only parsing).
Notation zesu_projection_generated_nodes_limit := (16384%Z) (only parsing).
Notation zesu_projection_inspected_nodes_limit := (65536%Z) (only parsing).
Definition zesu_solver_exception_labels : list string := nil.
