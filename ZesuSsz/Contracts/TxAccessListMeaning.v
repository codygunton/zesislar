From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Values.
Require Import EvmSailRlp.evm_rlp_types.
Require EvmSailTransactions.evm_decode_access_list_tx_types.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.SailRunAccessList.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListBugTriggers.

Import ListNotations.
Open Scope Z_scope.

Module AccessListSail := EvmSailTransactions.evm_decode_access_list_tx_types.

(* Owner: contract fact (review packet b1-tx). *)

(* Sail's decode_access_list fails (fatal_error RlpDecode) on a field whose
   source is longer than 2^30 bytes (sail/lib/rlp/codecs/transactions.sail:103). *)
Notation accessListSailSourceLimit := ((2 ^ 30) : Z) (only parsing).

(* The Sail field of the first item of `rest`: the item spans [0, h + p) of
   the input with content length p; is_list as decoded. *)
Definition accessListSailField (isList : bool) (headerLength payloadLength : Z)
    : AccessListSail.RlpFieldRef 0 (headerLength + payloadLength) payloadLength :=
  @AccessListSail.Build_RlpFieldRef 0 (headerLength + payloadLength) payloadLength
    (@AccessListSail.Build_StatelessInputSliceFields 0
       (headerLength + payloadLength) 0 (headerLength + payloadLength))
    isList payloadLength.

(* Sail's encoded slice as (offset, length) in the input. *)
Definition accessListEncodedSpan (ref : AccessListSail.AccessListRef) : Z * Z :=
  let slice := projT2 (projT2 (AccessListSail.AccessListRef_encoded ref)) in
  (AccessListSail.StatelessInputSliceFields_bytes slice,
   AccessListSail.StatelessInputSliceFields_len slice).

Definition txAccessListSail (input : list byte)
    : option (SailOutcome AccessListSail.AccessListRef) :=
  match candidateDecodeItem input with
  | candidateSuccess isList headerLength payloadLength =>
      Some (runDecodeAccessList input
              (accessListSailField isList headerLength payloadLength))
  | candidateError => None
  end.

(* Domain of the meaning: no reached long length wraps 2^64, and the first
   item, when it decodes, is within Sail's 2^30-byte source limit. *)
Definition txAccessListDomain (input : list byte) : Prop :=
  accessListHeadersFit input /\
  match candidateDecodeItem input with
  | candidateSuccess _ headerLength payloadLength =>
      headerLength + payloadLength <= accessListSailSourceLimit
  | candidateError => True
  end.

(* Sail agrees with the candidate. When the first item does not decode,
   decode_access_list has no field to run on: its caller's item decoder
   decides, and that is decodeItem's own Sail agreement, so nothing is
   stated here. Otherwise Sail succeeds exactly when the candidate accepts;
   on success its address count is the number of entries, its slot count
   the total number of keys, and its encoded slice is the payload of the
   first item ([h, h + p), the consumed bytes without the list header). *)
Definition txAccessListSailAgrees (input : list byte) : Prop :=
  match candidateDecodeItem input with
  | candidateError => True
  | candidateSuccess _ headerLength payloadLength =>
      match candidateAccessList input with
      | accessListAccepted entries _ =>
          exists ref,
            txAccessListSail input = Some (Success ref) /\
            accessListCounts (Success ref) =
              Some (Z.of_nat (List.length entries), accessListKeyCount entries) /\
            accessListEncodedSpan ref = (headerLength, payloadLength)
      | accessListRejected _ =>
          txAccessListSail input = Some (Reject RlpDecode)
      end
  end.

(* The meaning of one txAccessList call: the input is in the domain, the
   outcome class and `rest` advance are the candidate's, and Sail agrees
   with the candidate or the input triggers a registered KnownBug class. *)
Definition TxAccessListMeaningModuloKnownBugs (input : list byte)
    (outcome : TxAccessListOutcomeClass) (consumed : Z) : Prop :=
  txAccessListDomain input /\
  txAccessListOutcomeAllowed input outcome consumed /\
  (txAccessListSailAgrees input \/
   exists bug, List.In bug knownBugs /\
     txAccessListBugTrigger bug input = true).
