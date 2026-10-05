From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Import ListNotations.
Open Scope Z_scope.

Definition decodeItemSailSuccess (args : DecodeItemArgs)
    (isList : bool) (headerLength payloadLength : Z) : Prop :=
  exists fullLength contentLength
      (field : RlpFieldRef 0 fullLength contentLength),
    runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
      Success (@existT Z (fun full => {content : Z & RlpFieldRef 0 full content})
        fullLength
        (@existT Z (fun content => RlpFieldRef 0 fullLength content)
          contentLength field)) /\
    RlpFieldRef_is_list field = isList /\
    fullLength - contentLength = headerLength /\
    contentLength = payloadLength.


(* These facts describe available input data before an outcome is known. *)
Definition decodeItemInputHead (args : DecodeItemArgs)
    (prefix : byte) (rest : list byte) : Prop :=
  decodeItemInputBytes args = prefix :: rest.

Definition decodeItemAcceptedFacts (args : DecodeItemArgs)
    (isList : bool) (headerLength payloadLength : Z) : Prop :=
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess isList headerLength payloadLength /\
  decodeItemSailSuccess args isList headerLength payloadLength.

Definition decodeItemLongAcceptedFacts (args : DecodeItemArgs)
    (isList : bool) (headerLength payloadLength : Z) : Prop :=
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess isList headerLength payloadLength /\
  ((headerLength + payloadLength < word64Modulus /\
    decodeItemSailSuccess args isList headerLength payloadLength) \/
   (binaryWrapCase headerLength payloadLength
      ((headerLength + payloadLength) mod word64Modulus) /\
    runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
      Reject RlpDecode)).

Definition decodeItemRejectedFacts (args : DecodeItemArgs) : Prop :=
  candidateDecodeItem (decodeItemInputBytes args) = candidateError /\
  runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
    Reject RlpDecode.

Definition decodeItemFoldProvenance (args : DecodeItemArgs) (isList : bool)
    (prefix : byte) (rest : list byte) (n payloadStart : Z)
    (lengthBytes : list byte) : Prop :=
  decodeItemInputHead args prefix rest /\
  (if isList then 248 <= bv_unsigned prefix <= 255
   else 184 <= bv_unsigned prefix <= 191) /\
  n = bv_unsigned prefix - (if isList then 247 else 183) /\
  payloadStart = decodeItemInputPointer args + 1 /\
  lengthBytes = firstn (Z.to_nat n) rest.
