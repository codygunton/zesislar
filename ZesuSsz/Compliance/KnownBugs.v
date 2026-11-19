From Coq Require Import Lists.List.

Import ListNotations.

(** Reviewed divergence classes for the pinned stock Zesu endpoint. Each
    class names an input on which the binary's result differs from Sail's.
    The trigger of each decodeParentHeader class is
    ZesuSsz/Contracts/ParentHeaderBugTriggers.v; decodeItem uses only
    RlpLongLengthWrap. *)
Inductive KnownBug : Type :=
(* build/stock-zisk/static-sites/sites.json records selected-object DWARF.
   It links src/stateless/mpt/rlp.zig:52 to the
   long-string add at 0x800d6a38 (3387e600) and bltu at 0x800d6a3c
   (6362e60a). It links rlp.zig:67 to the long-list add at 0x800d6ad8
   (3387e600) and bgeu at 0x800d6adc (6376e602). These selected-ELF
   sites add the payload and header lengths modulo 2^64. *)
| RlpLongLengthWrap
(* decodeParentHeader rejects a header with fewer than twelve fields (the
   checks after calls 0x800d5d34..0x800d5ec4 and the decodeItem error on an
   empty slice for fields 9..11); Sail accepts any field count. *)
| ParentHeaderMissingRequiredField
(* decodeParentHeader reads only the outer item; bytes after it are never
   read. Sail rejects them (rlp_single_ref). *)
| ParentHeaderTrailingBytes
(* decodeParentHeader skips fields 0..8, 12..14 and 16 whatever their item
   shape. Sail decodes parent hash (field 0) and state root (field 3) as
   words and rejects a list there. *)
| ParentHeaderSkippedFieldShape
(* decodeParentHeader returns blob gas used (field 17) as read. Sail rejects
   a value that is not a multiple of the 2^17 gas per blob. *)
| ParentHeaderBlobGasUnaligned
(* nextUint64 and the inlined integer reads fold a payload with leading
   zero bytes. Sail rejects a non-canonical integer. *)
| RlpUintNonCanonical
(* nextUint64 rejects a payload longer than 8 bytes. Sail decodes base fee
   (field 15) as a 256-bit integer and accepts it. *)
| ParentHeaderUintOver8
(* decodeParentHeader rejects a gas limit, gas used or timestamp item
   (fields 9..11) that is present but is a list, is longer than 8 bytes or
   does not decode. Sail does not decode those fields as integers and
   accepts a list or a long string there. *)
| ParentHeaderUndecodedFieldRejected.

(** This fixed list prevents later proofs from adding exceptions. *)
Definition knownBugs : list KnownBug :=
  [RlpLongLengthWrap; ParentHeaderMissingRequiredField;
   ParentHeaderTrailingBytes; ParentHeaderSkippedFieldShape;
   ParentHeaderBlobGasUnaligned; RlpUintNonCanonical;
   ParentHeaderUintOver8; ParentHeaderUndecodedFieldRejected].
