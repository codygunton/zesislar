(* Instruction resources of the region; its own closure map only. *)
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import ZesuSsz.Stock.Closure.index_ensureTotalCapacity.

Definition keysEnsureCapacitySelectedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_ensureTotalCapacity.instr_map).
Global Instance : LithiumUnfold (@keysEnsureCapacitySelectedCode) := I.
Global Typeclasses Opaque keysEnsureCapacitySelectedCode.
