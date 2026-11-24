(* Charged instruction resources of rlp.decodeItem (plan Stage T, T7): the same
   closure map as DecodeItemSelected.v; each fetch of one of these
   instructions consumes one step credit. *)
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.LookupCharged.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.

Definition decodeItemChargedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources_charged
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_decodeItem.instr_map).
Global Instance : LithiumUnfold (@decodeItemChargedCode) := I.
Global Typeclasses Opaque decodeItemChargedCode.
