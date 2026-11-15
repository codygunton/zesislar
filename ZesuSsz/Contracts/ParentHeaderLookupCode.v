(* Own-map selected code of rlp_decode.decodeParentHeader in the F55 shape;
   callee code enters only through call specs (F57). *)
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Stock.Closure.index_decodeParentHeader.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import InstrSpecs.Lookup.

Definition parentHeaderLookupCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_decodeParentHeader.instr_map).

Global Instance : LithiumUnfold (@parentHeaderLookupCode) := I.
Global Typeclasses Opaque parentHeaderLookupCode.
