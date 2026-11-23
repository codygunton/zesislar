Require Export ZesuSsz.Compliance.KeysToOwnedSliceUnfoldRegistrations.
(* The block domain's ranges as plain facts (DomainRanges.v). *)
Require Export ZesuSsz.Compliance.KeysToOwnedSliceDomainRanges.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
(* Spatial leftovers of these callers print their `@@S` diagnosis record (plan A3 item 4). *)
Require Export ZesuSsz.Automation2.SpatialExportOn.

(* The callers read the selected code through its definition, as the free and nextUint64 callers do. *)
Global Typeclasses Transparent keysToOwnedSliceSelectedCode.
