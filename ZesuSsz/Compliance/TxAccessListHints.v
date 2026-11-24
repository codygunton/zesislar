(* The block domain's links as plain facts (DomainRanges.v). *)
Require Export ZesuSsz.Compliance.TxAccessListDomainRanges.
Require Import ZesuSsz.Contracts.TxAccessListSelected.
(* Spatial leftovers of these callers print their `@@S` diagnosis record (plan A3 item 4). *)
Require Export ZesuSsz.Automation2.SpatialExportOn.

(* The callers read the selected code through its definition, as the array-list callers do. *)
Global Typeclasses Transparent txAccessListSelectedCode.
