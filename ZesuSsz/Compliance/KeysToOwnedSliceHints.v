Require Export ZesuSsz.Compliance.KeysToOwnedSliceUnfoldRegistrations.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.

(* The callers read the selected code through its definition, as the free and nextUint64 callers do. *)
Global Typeclasses Transparent keysToOwnedSliceSelectedCode.
