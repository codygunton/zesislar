From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.

(* Global library axioms are kernel constants, not theorem parameters. *)
Ltac2 approved_library_axioms () : constr list := [].

(* Runtime contracts belong in reviewed theorem types, not this axiom list.
   Rung 1 has no approved runtime contract premise. *)
Ltac2 approved_runtime_premises () : constr list :=
  ['memcpyCallPremise; 'ziskMemcpyCallPremise; 'altFlAllocCallPremise;
   'altFlRemapCallPremise; 'altFlFreeCallPremise].
