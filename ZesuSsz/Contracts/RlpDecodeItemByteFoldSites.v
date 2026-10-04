From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Import ListNotations.
Open Scope Z_scope.

(* These are chain-driver hints at the exact stock-ELF block entries.
   The resource predicate in Q20 binds x10, x11, x12, x13, x14, x15,
   x16, x2, x1, x8, both arrays, and the saved stack frame.
   No block proof or edge adapter follows from these definitions. *)
Definition decodeItemStringFoldPC : Z := 0x800d6a24.
Definition decodeItemListFoldPC : Z := 0x800d6ac4.

Definition decodeItemStringFoldAt `{!islaG Sigma} `{!threadG}
    (pc : Z) (args : DecodeItemArgs) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) : iProp Sigma :=
  (⌜pc = decodeItemStringFoldPC /\ i < n⌝ ∗
   decodeItemByteFoldStringHeader args n i payloadStart
     lengthBytes frameBytes loaded)%I.

Definition decodeItemListFoldAt `{!islaG Sigma} `{!threadG}
    (pc : Z) (args : DecodeItemArgs) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) : iProp Sigma :=
  (⌜pc = decodeItemListFoldPC /\ i < n⌝ ∗
   decodeItemByteFoldListHeader args n i payloadStart
     lengthBytes frameBytes loaded)%I.
