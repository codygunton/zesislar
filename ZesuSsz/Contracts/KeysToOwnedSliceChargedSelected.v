(* Charged instruction resources of the region (plan Stage T, T8): the same
   closure map as KeysToOwnedSliceSelected.v; each fetch of one of these
   instructions consumes one step credit. *)
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.LookupCharged.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import ZesuSsz.Stock.Closure.index_sliceBytes32.

Definition keysToOwnedSliceChargedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources_charged
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_sliceBytes32.instr_map).
Global Instance : LithiumUnfold (@keysToOwnedSliceChargedCode) := I.
Global Typeclasses Opaque keysToOwnedSliceChargedCode.
