Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Compliance.NextUint64CallBridge.

(* This marker exposes only the exact call-state predicate to Lithium. *)
Global Typeclasses Opaque NextUint64CallState800d62b4.
Global Instance nextUint64CallStateUnfoldRegistered :
  LithiumUnfold (@NextUint64CallState800d62b4) := I.
