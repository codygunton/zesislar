From Coq Require Import List.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Import ListNotations.

(* Complete 40-byte Ok image, including the caller's padding. *)
Definition decodeItemOkBytes (before pointerBytes lengthBytes consumedBytes : list byte)
    (isList : bool) : list byte :=
  pointerBytes ++ lengthBytes ++ [Z_to_bv 8 (if isList then 1 else 0)] ++
  firstn 7 (skipn 17 before) ++ consumedBytes ++
  [Z_to_bv 8 0; Z_to_bv 8 0] ++ firstn 6 (skipn 34 before).
