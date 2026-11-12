Require Export ZesuSsz.Compliance.BerlinGasCalcUnfoldRegistrations.
Require Import ZesuSsz.Contracts.BerlinGasCalcSelected.

(* W0 setup: the callers read the selected code through its definition, as the
   free and nextUint64 callers do (their selected code is not opaque there). *)
Global Typeclasses Transparent berlinGasCalcSelectedCode.
