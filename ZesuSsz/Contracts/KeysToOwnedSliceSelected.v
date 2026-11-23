(* Instruction resources of the region; its own closure map only. *)
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import ZesuSsz.Stock.Closure.index_sliceBytes32.

Definition keysToOwnedSliceSelectedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_sliceBytes32.instr_map).
Global Instance : LithiumUnfold (@keysToOwnedSliceSelectedCode) := I.
Global Typeclasses Opaque keysToOwnedSliceSelectedCode.
