From Coq Require Import Lists.List.

Import ListNotations.

(** Reviewed divergence classes for the pinned stock Zesu endpoint. *)
Inductive KnownBug : Type :=
(* Stock rlp.zig adds the decoded payload length to the long-string and
   long-list header lengths without rejecting uint64 wrap. The selected ELF
   has add/bltu at 0x800d6a38/0x800d6a3c for strings and add/bgeu at
   0x800d6ad8/0x800d6adc for lists. Earlier pilot addresses are superseded
   by these selected-ELF sites. *)
| RlpLongLengthWrap.

(** This fixed list prevents later proofs from adding exceptions. *)
Definition knownBugs : list KnownBug := [RlpLongLengthWrap].
