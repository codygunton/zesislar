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

(* decodeParentHeader: excluded inputs, unsafe downstream read.
   decodeParentHeader's first decodeItem call (0x800d5cf4) decodes the whole
   input. When it takes the RlpLongLengthWrap branch on a list, it reports
   success with payload length at least 2^64 - 9, and the next decodeItem
   call (0x800d5d34, block 0x800d5d20) receives that payload range, so it
   would read beyond the input. parentHeaderArgsWellFormed
   (ParentHeaderContract.v) excludes exactly these inputs through
   parentHeaderOuterListWrap; ParentHeaderOuterWrapFacts.v proves the
   exclusion exact. A wrapped string at the first call stays in the domain:
   it fails the list check and the function returns with no further call. A
   wrap at any later call stays in the domain as well: the parent advances
   past that item by the call's consumed count, which its C1-B result bounds
   by the length of the slice it was passed, so no later call reads beyond the
   input. A later block that needs a later-call exclusion is a separate
   contract change and review item. *)
