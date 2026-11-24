(* Charged instruction resources of the region (plan Stage T, T8): the same
   closure map as EntriesToOwnedSliceSelected.v; each fetch of one of these
   instructions consumes one step credit. *)
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.LookupCharged.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import ZesuSsz.Stock.Closure.index_sliceAccessList.

Definition entriesToOwnedSliceChargedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources_charged
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_sliceAccessList.instr_map).
Global Instance : LithiumUnfold (@entriesToOwnedSliceChargedCode) := I.
Global Typeclasses Opaque entriesToOwnedSliceChargedCode.
