(* Charged instruction resources of the region (plan Stage T, T6): the same
   closure map as KeysEnsureCapacitySelected.v; each fetch of one of these
   instructions consumes one step credit. *)
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.LookupCharged.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import ZesuSsz.Stock.Closure.index_ensureTotalCapacity.

Definition keysEnsureCapacityChargedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources_charged
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_ensureTotalCapacity.instr_map).
Global Instance : LithiumUnfold (@keysEnsureCapacityChargedCode) := I.
Global Typeclasses Opaque keysEnsureCapacityChargedCode.
