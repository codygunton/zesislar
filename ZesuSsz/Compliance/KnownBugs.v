From Coq Require Import Lists.List.

Import ListNotations.

(** Reviewed divergence classes for the pinned stock Zesu endpoint. *)
Inductive KnownBug : Type :=
(* build/stock-zisk/static-sites/sites.json records selected-object DWARF.
   It links src/stateless/mpt/rlp.zig:52 to the
   long-string add at 0x800d6a38 (3387e600) and bltu at 0x800d6a3c
   (6362e60a). It links rlp.zig:67 to the long-list add at 0x800d6ad8
   (3387e600) and bgeu at 0x800d6adc (6376e602). These selected-ELF
   sites add the payload and header lengths modulo 2^64. *)
| RlpLongLengthWrap.

(** This fixed list prevents later proofs from adding exceptions. *)
Definition knownBugs : list KnownBug := [RlpLongLengthWrap].
