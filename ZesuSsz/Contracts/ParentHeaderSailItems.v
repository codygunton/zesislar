From Coq Require Import Bool List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.

Import ListNotations.
Open Scope Z_scope.

(* Owner: contract fact. Item-level pieces of the pinned Sail parent-header
   decoder (_rec_decode_parent_header_fields in
   generated/evm-sail-coq/rlp/evm_rlp.v) and of the candidate walk, stated
   on byte lists. The KnownBug triggers (ParentHeaderBugTriggers.v) and the
   Sail agreement of plan step 2.4 (M2) both use them, so they are defined
   once here. *)

(* Sail's default execution profile: schema 0x15 falls through to Amsterdam
   in schema_protocol_profile. sailBlobMax mirrors that profile's
   blob_schedule.max (21); sailExcessBlobGasLimit mirrors its
   excess_blob_gas_limit, compute_profile_excess_blob_gas_limit of
   max 21 and target 14: 256 * 11684671 + (21 - 14) * 2^17 = 2992193280.
   sailGasPerBlob mirrors sizeof(gas_per_blob_value) = 2^17, and
   sailWordLengthLimit mirrors RLP_WORD_LENGTH_LIMIT = 32. *)
Notation sailBlobMax := 21 (only parsing).
Notation sailExcessBlobGasLimit := (256 * 11684671 + (21 - 14) * 2 ^ 17) (only parsing).
Notation sailGasPerBlob := (2 ^ 17) (only parsing).
Notation sailWordLengthLimit := 32 (only parsing).

(* rlp_decode_item on a cursor holding exactly [r]: the same header as
   candidateDecodeItem, without the 2^64 wrap of the binary. *)
Definition sailDecodeItem (r : list byte) : candidateItem :=
  match candidateDecodeItem r with
  | candidateSuccess isList headerLength payloadLength =>
      if headerLength + payloadLength <=? Z.of_nat (List.length r)
      then candidateSuccess isList headerLength payloadLength
      else candidateError
  | candidateError => candidateError
  end.

Definition itemPayload (r : list byte) (headerLength payloadLength : Z)
    : list byte :=
  firstn (Z.to_nat payloadLength) (skipn (Z.to_nat headerLength) r).

(* rlp_item_uint_canonical (rlp_ref_bytes_canonical, rlp_ref_framing_canonical
   and the leading-zero check) for an item of at most 55 payload bytes.
   Above 55 Sail's integer decoders reject anyway (32 and 8 byte limits). *)
Definition sailShortUintCanonical (r : list byte) (isList : bool)
    (headerLength payloadLength : Z) : bool :=
  negb isList && (payloadLength <=? 55) &&
  match r, itemPayload r headerLength payloadLength with
  | [], _ => false
  | first :: _, [] =>
      (payloadLength =? 0) && (headerLength =? 1) && (bv_unsigned first =? 128)
  | first :: _, lead :: _ =>
      negb (payloadLength =? 0) && negb (bv_unsigned lead =? 0) &&
      (if (payloadLength =? 1) && (bv_unsigned lead <? 128)
       then headerLength =? 0
       else (headerLength =? 1) && (bv_unsigned first =? 128 + payloadLength))
  end.

(* Field index 19 (Sail's cursor saturates there): every further item is
   decoded by rlp_decode_item and discarded. *)
Fixpoint sailSkipItems (fuel : nat) (r : list byte) : bool :=
  match r with
  | [] => true
  | _ :: _ =>
      match fuel with
      | O => false
      | S fuel' =>
          match sailDecodeItem r with
          | candidateError => false
          | candidateSuccess _ headerLength payloadLength =>
              sailSkipItems fuel' (skipn (Z.to_nat (headerLength + payloadLength)) r)
          end
      end
  end.

(* The candidate's step on one reached field (the body of
   parentHeaderFieldWalk). *)
Inductive CandidateStep :=
| candidateStepReject
| candidateStepContinue (rest : list byte) (values : list Z).

Definition candidateFieldStep (kind : ParentHeaderFieldKind) (r : list byte)
    (values : list Z) : CandidateStep :=
  match candidateDecodeItem r with
  | candidateError => candidateStepReject
  | candidateSuccess isList headerLength payloadLength =>
      let rest := skipn
        (Z.to_nat ((headerLength + payloadLength) mod word64Modulus)) r in
      if parentHeaderFieldIsInteger kind then
        if isList || (8 <? payloadLength) then candidateStepReject
        else candidateStepContinue rest
          (values ++ [bigEndian (firstn (Z.to_nat payloadLength)
                       (skipn (Z.to_nat headerLength) r))])
      else candidateStepContinue rest values
  end.

(* The item's header and payload lengths run past the bytes left: the
   binary's sum wrapped 2^64 (headerFits holds for the outer item). *)
Definition candidateWrapb (r : list byte) : bool :=
  match candidateDecodeItem r with
  | candidateSuccess _ headerLength payloadLength =>
      Z.of_nat (List.length r) <? headerLength + payloadLength
  | candidateError => false
  end.

(* The candidate walk over the whole schedule: the bytes of the outer
   payload left after field 18, or None when the walk rejects or ends at a
   missing field first. *)
Fixpoint parentHeaderWalkRest (schedule : list (Z * ParentHeaderFieldKind))
    (remaining : list byte) (values : list Z) : option (list byte) :=
  match schedule with
  | [] => Some remaining
  | (_, kind) :: later =>
      match remaining with
      | [] => None
      | _ :: _ =>
          match candidateFieldStep kind remaining values with
          | candidateStepReject => None
          | candidateStepContinue rest values' =>
              parentHeaderWalkRest later rest values'
          end
      end
  end.
