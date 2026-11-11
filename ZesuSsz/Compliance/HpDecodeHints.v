Require Export ZesuSsz.Compliance.HpDecodeUnfoldRegistrations.
Require Import ZesuSsz.Contracts.HpDecodeSelected.

(* W0 setup: the callers read the selected code through its definition, as the
   free and nextUint64 callers do (their selected code is not opaque there). *)
Global Typeclasses Transparent hpDecodeSelectedCode.
