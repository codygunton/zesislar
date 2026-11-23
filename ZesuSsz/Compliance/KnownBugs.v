From Coq Require Import Lists.List.

Import ListNotations.

(** Reviewed divergence classes for the pinned stock Zesu endpoint. Each
    class names an input on which the binary's result differs from Sail's.
    The trigger of each decodeParentHeader class is
    ZesuSsz/Contracts/ParentHeaderBugTriggers.v; decodeItem uses only
    RlpLongLengthWrap; the AccessList* classes belong to txAccessList
    (ZesuSsz/Contracts/TxAccessListBugTriggers.v). *)
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
   words and rejects a list or a string longer than 32 bytes there. *)
| ParentHeaderSkippedFieldShape
(* decodeParentHeader returns blob gas used (field 17) as read. Sail rejects
   a value that is not a multiple of the 2^17 gas per blob or whose blob
   count is above the schedule maximum (21). *)
| ParentHeaderBlobGasUnaligned
(* nextUint64 folds a payload of at most 8 bytes at fields 15, 17 and 18
   whatever its framing. Sail rejects a non-canonical integer there: a
   leading zero byte, or a header that is not the short canonical form. *)
| RlpUintNonCanonical
(* nextUint64 rejects a payload longer than 8 bytes. Sail decodes base fee
   (field 15) as a 256-bit integer and accepts a canonical one of up to 32
   bytes. *)
| ParentHeaderUintOver8
(* decodeParentHeader rejects a gas limit, gas used or timestamp item
   (fields 9..11) that decodes but is a list or longer than 8 bytes. Sail
   does not decode those fields as integers and accepts it. *)
| ParentHeaderUndecodedFieldRejected
(* decodeParentHeader returns excess blob gas (field 18) as read. Sail
   rejects a value above the profile's excess blob gas limit
   (2992193280). *)
| ParentHeaderExcessBlobGasAboveLimit
(* decodeParentHeader never reads the outer payload after field 18. Sail
   decodes every further item and rejects one that does not decode. *)
| ParentHeaderTrailingItemMalformed
(* rlp_decode.txAccessList rejects an entry address whose byte string is
   not exactly 20 bytes (rlp_decode.zig:509). Sail decodes the address with
   rlp_decode_word, which accepts any string of at most 32 bytes and keeps
   its low 20 bytes (word_to_address). Reviewed 2026-11-23 (plan B1). *)
| AccessListAddressLength
(* rlp_decode.txAccessList rejects a storage key whose byte string is not
   exactly 32 bytes (rlp_decode.zig:526). Sail's rlp_decode_word accepts a
   string of fewer than 32 bytes. Reviewed 2026-11-23 (plan B1). *)
| AccessListKeyLength
(* rlp_decode.txAccessList never reads the bytes after an entry's keys list
   (rlp_decode.zig:513-535). Sail rejects them (rlp_cursor_expect_end in
   _rec_decode_access_list_entries). Reviewed 2026-11-23 (plan B1). *)
| AccessListEntryTrailingBytes.

(** This fixed list prevents later proofs from adding exceptions. *)
Definition knownBugs : list KnownBug :=
  [RlpLongLengthWrap; ParentHeaderMissingRequiredField;
   ParentHeaderTrailingBytes; ParentHeaderSkippedFieldShape;
   ParentHeaderBlobGasUnaligned; RlpUintNonCanonical;
   ParentHeaderUintOver8; ParentHeaderUndecodedFieldRejected;
   ParentHeaderExcessBlobGasAboveLimit; ParentHeaderTrailingItemMalformed;
   AccessListAddressLength; AccessListKeyLength;
   AccessListEntryTrailingBytes].
