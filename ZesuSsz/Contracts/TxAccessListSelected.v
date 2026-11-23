From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import ZesuSsz.Stock.Closure.index_txAccessList.

Open Scope Z_scope.

(* The selected code of rlp_decode.txAccessList (sym_rlp_decode_txAccessList):
   its own instruction map only (F55). The closure index
   ZesuSsz.Stock.Closure.index_txAccessList covers all 323 instructions,
   +0x0 .. +0x508, and lists its 12 call sites (txAccessList_call_sites).
   Callee code enters through the table-level bridge (F57): decodeItem and
   the three array-list regions by their selected code, memcpy and the
   allocator entries by their premises. *)
Definition txAccessListSelectedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_txAccessList.instr_map).
Global Instance : LithiumUnfold (@txAccessListSelectedCode) := I.
Global Typeclasses Opaque txAccessListSelectedCode.
