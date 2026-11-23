From Coq Require Import Bool List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.

Import ListNotations.
Open Scope Z_scope.

(* Owner: contract fact (review packet b1-tx). Skeleton: for each KnownBug
   class, a decidable condition on the bytes of `rest` under which the
   binary's decision (candidateAccessList) may differ from Sail's
   decode_access_list. No class registered in KnownBugs.v applies to
   txAccessList inside its domain (RlpLongLengthWrap is excluded by
   accessListHeadersFit), so every class maps to false. The divergences the
   review packet proposes are stated below as conditions only; registering
   them as KnownBug constructors waits for the user's review. *)
Definition txAccessListBugTrigger (bug : KnownBug) (input : list byte) : bool :=
  match bug with
  | _ => false
  end.

(* A reached call at [site] whose item decodes as a byte string with a
   payload length satisfying [test]. *)
Definition accessListStringAtb (site : Z) (test : Z -> bool)
    (call : AccessListCall) : bool :=
  (fst call =? site) &&
  match candidateDecodeItem (snd call) with
  | candidateSuccess false _ payloadLength => test payloadLength
  | candidateSuccess true _ _ | candidateError => false
  end.

(* Proposed D1 (AccessListAddressLength): an entry address is a byte string
   of at most 32 bytes but not 20. The binary rejects it
   (rlp_decode.zig:509); Sail decodes the address with rlp_decode_word,
   which accepts any string of at most 32 bytes, and keeps its low 20
   bytes (word_to_address). *)
Definition accessListAddressLengthb (input : list byte) : bool :=
  List.existsb
    (accessListStringAtb accessListAddressCall
       (fun length => negb (length =? accessListAddressBytes) &&
                      (length <=? 32)))
    (accessListCalls input).

(* Proposed D2 (AccessListKeyLength): a storage key is a byte string of
   fewer than 32 bytes. The binary rejects it (rlp_decode.zig:526); Sail's
   rlp_decode_word accepts it. *)
Definition accessListKeyLengthb (input : list byte) : bool :=
  List.existsb
    (accessListStringAtb accessListKeyCall
       (fun length => length <? accessListKeyBytes))
    (accessListCalls input).

(* Proposed D3 (AccessListEntryTrailingBytes): bytes follow the keys list
   inside an entry. The binary never reads them (rlp_decode.zig:513-535);
   Sail rejects them (rlp_cursor_expect_end). *)
Definition accessListEntryTrailingb (input : list byte) : bool :=
  List.existsb (fun call =>
    (fst call =? accessListKeysCall) &&
    match candidateDecodeItem (snd call) with
    | candidateSuccess true headerLength payloadLength =>
        negb (Nat.eqb
          (List.length (itemRest (snd call) headerLength payloadLength)) 0)
    | candidateSuccess false _ _ | candidateError => false
    end) (accessListCalls input).

(* The proposed classes an input triggers. *)
Definition accessListProposedTriggers (input : list byte) : list bool :=
  [accessListAddressLengthb input; accessListKeyLengthb input;
   accessListEntryTrailingb input].
