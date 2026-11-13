Require Export ZesuSsz.Compliance.ParentHeaderUnfoldRegistrations.
Require Import ZesuSsz.Contracts.ParentHeaderLookupCode.

(* Measurement setup: the callers read the selected code through its definition,
   as the W0, free and nextUint64 callers do. *)
Global Typeclasses Transparent parentHeaderLookupCode.
