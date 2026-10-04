From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.

(* Global library axioms are kernel constants, not theorem parameters. *)
Ltac2 approved_library_axioms () : constr list := [].

(* Runtime contracts belong in reviewed theorem types, not this axiom list.
   Rung 1 has no approved runtime contract premise. *)
Ltac2 approved_runtime_premises () : constr list := ['memcpyServicePremise].
