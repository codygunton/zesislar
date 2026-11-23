From Coq Require Import Bool List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.

Import ListNotations.
Open Scope Z_scope.

(* Owner: contract fact (review packet b1-tx). The reference decoder of
   rlp_decode.txAccessList (sym_rlp_decode_txAccessList), as a total,
   computable function on the bytes of the `rest` slice at entry. It follows
   src/stateless/rlp_decode.zig:485-538 (zesu b5483dda) and the pinned ELF,
   not Sail:

   - Call +0x64 decodes the first item of `rest`. An error, or a byte
     string, rejects with `rest` unchanged. A list advances `rest` by the
     item's consumed length (+0x88..+0x98) before anything else, so every
     later outcome reports that advance.
   - The payload is walked entry by entry while bytes remain (+0xc4). Each
     entry (call +0xd4) must decode as a list. Inside it, the address (call
     +0x108) must decode as a byte string of exactly 20 bytes, and the next
     item (call +0x158) must decode as a list: the keys list. Bytes after the
     keys list inside the entry are never read (the source never checks
     them): they do not change the result.
   - The keys payload is walked key by key while bytes remain (+0x18c). Each
     key (call +0x19c) must decode as a byte string of exactly 32 bytes.
   - The entries are returned in input order, each with its address and its
     keys in input order.

   decodeItem is candidateDecodeItem (RlpDecodeItem.v). Its consumed length
   is (header + payload) mod 2^64, as the machine computes it; the domain
   (accessListHeadersFit) excludes a wrap at every reached call, so inside
   the domain every consumed length is exact and at least 1. The fuel below
   (the byte count) is then never exhausted. *)

(* Call sites of rlp.decodeItem, as offsets from sym_rlp_decode_txAccessList. *)
Notation accessListOuterCall := ((0x64) : Z) (only parsing).
Notation accessListEntryCall := ((0xd4) : Z) (only parsing).
Notation accessListAddressCall := ((0x108) : Z) (only parsing).
Notation accessListKeysCall := ((0x158) : Z) (only parsing).
Notation accessListKeyCall := ((0x19c) : Z) (only parsing).
Notation accessListAddressBytes := ((20) : Z) (only parsing).
Notation accessListKeyBytes := ((32) : Z) (only parsing).

Record AccessListEntryValue := {
  entryAddress : list byte;
  entryKeys : list (list byte)
}.

(* What the candidate decides. [accessListRejected consumed]: the result is
   error.InvalidBlock; [consumed] is [Some n] when the first item decoded as
   a list (then `rest` advanced by n), [None] when `rest` is unchanged. *)
Inductive AccessListCandidate :=
| accessListRejected (consumed : option Z)
| accessListAccepted (entries : list AccessListEntryValue) (consumed : Z).

(* The payload and the bytes after one decoded item. *)
Definition itemPayload (input : list byte) (headerLength payloadLength : Z)
    : list byte :=
  firstn (Z.to_nat payloadLength) (skipn (Z.to_nat headerLength) input).

Definition itemConsumed (headerLength payloadLength : Z) : Z :=
  (headerLength + payloadLength) mod word64Modulus.

Definition itemRest (input : list byte) (headerLength payloadLength : Z)
    : list byte :=
  skipn (Z.to_nat (itemConsumed headerLength payloadLength)) input.

(* A reached decodeItem call: its call-site offset and its input slice. *)
Definition AccessListCall : Type := (Z * list byte)%type.

Fixpoint accessListKeysWalk (fuel : nat) (keys : list byte)
    : list AccessListCall * option (list (list byte)) :=
  match keys with
  | [] => ([], Some [])
  | _ :: _ =>
      match fuel with
      | O => ([], None)
      | S fuel' =>
          let here := (accessListKeyCall, keys) in
          match candidateDecodeItem keys with
          | candidateSuccess false headerLength payloadLength =>
              if payloadLength =? accessListKeyBytes then
                let '(trace, later) := accessListKeysWalk fuel'
                  (itemRest keys headerLength payloadLength) in
                (here :: trace,
                 option_map (cons (itemPayload keys headerLength payloadLength))
                   later)
              else ([here], None)
          | candidateSuccess true _ _ | candidateError => ([here], None)
          end
      end
  end.

(* One entry: its address and keys, or a rejection, with the calls it
   reaches. *)
Definition accessListEntry (entry : list byte)
    : list AccessListCall * option AccessListEntryValue :=
  let addressCall := (accessListAddressCall, entry) in
  match candidateDecodeItem entry with
  | candidateSuccess false addressHeader addressLength =>
      if addressLength =? accessListAddressBytes then
        let afterAddress := itemRest entry addressHeader addressLength in
        let keysCall := (accessListKeysCall, afterAddress) in
        match candidateDecodeItem afterAddress with
        | candidateSuccess true keysHeader keysLength =>
            let keysPayload := itemPayload afterAddress keysHeader keysLength in
            let '(trace, keys) :=
              accessListKeysWalk (List.length keysPayload) keysPayload in
            (addressCall :: keysCall :: trace,
             option_map (fun keys =>
               {| entryAddress := itemPayload entry addressHeader addressLength;
                  entryKeys := keys |}) keys)
        | candidateSuccess false _ _ | candidateError =>
            ([addressCall; keysCall], None)
        end
      else ([addressCall], None)
  | candidateSuccess true _ _ | candidateError => ([addressCall], None)
  end.

Fixpoint accessListEntriesWalk (fuel : nat) (entries : list byte)
    : list AccessListCall * option (list AccessListEntryValue) :=
  match entries with
  | [] => ([], Some [])
  | _ :: _ =>
      match fuel with
      | O => ([], None)
      | S fuel' =>
          let here := (accessListEntryCall, entries) in
          match candidateDecodeItem entries with
          | candidateSuccess true entryHeader entryLength =>
              let '(entryTrace, entry) :=
                accessListEntry (itemPayload entries entryHeader entryLength) in
              match entry with
              | Some value =>
                  let '(trace, later) := accessListEntriesWalk fuel'
                    (itemRest entries entryHeader entryLength) in
                  (here :: entryTrace ++ trace, option_map (cons value) later)
              | None => (here :: entryTrace, None)
              end
          | candidateSuccess false _ _ | candidateError => ([here], None)
          end
      end
  end.

(* The whole walk: the reached calls in machine order and the decision. *)
Definition accessListWalk (input : list byte)
    : list AccessListCall * AccessListCandidate :=
  let outer := (accessListOuterCall, input) in
  match candidateDecodeItem input with
  | candidateSuccess true headerLength payloadLength =>
      let consumed := itemConsumed headerLength payloadLength in
      let payload := itemPayload input headerLength payloadLength in
      let '(trace, entries) :=
        accessListEntriesWalk (List.length payload) payload in
      (outer :: trace,
       match entries with
       | Some values => accessListAccepted values consumed
       | None => accessListRejected (Some consumed)
       end)
  | candidateSuccess false _ _ | candidateError =>
      ([outer], accessListRejected None)
  end.

Definition candidateAccessList (input : list byte) : AccessListCandidate :=
  snd (accessListWalk input).

Definition accessListCalls (input : list byte) : list AccessListCall :=
  fst (accessListWalk input).

(* Domain: no reached decodeItem call sees a long length that wraps 2^64
   (RlpLongLengthWrap is outside this function's theorem). *)
Definition accessListHeadersFit (input : list byte) : Prop :=
  List.Forall (fun call => headerFits (snd call)) (accessListCalls input).

Definition accessListHeadersFitb (input : list byte) : bool :=
  List.forallb (fun call =>
    match snd call with
    | [] => true
    | prefix :: rest =>
        let width := longLengthWidth (bv_unsigned prefix) in
        (width =? 0) || (Z.of_nat (List.length rest) <? width) ||
        (1 + width + bigEndian (firstn (Z.to_nat width) rest) <? word64Modulus)
    end) (accessListCalls input).

(* `rest` advance of a candidate outcome (0 when `rest` is unchanged). *)
Definition accessListCandidateConsumed (candidate : AccessListCandidate) : Z :=
  match candidate with
  | accessListAccepted _ consumed => consumed
  | accessListRejected (Some consumed) => consumed
  | accessListRejected None => 0
  end.

Definition accessListKeyCount (entries : list AccessListEntryValue) : Z :=
  fold_right (fun entry total => Z.of_nat (List.length (entryKeys entry)) + total)
    0 entries.

(* The machine outcome classes. The machine result is the same error union
   (error code 3, error.InvalidBlock) for [txAccessListInvalidInput] and
   [txAccessListAllocationFailure]: rlp_decode.zig maps every allocation
   failure to error.InvalidBlock. The cause is kept as a separate class
   because the owned heap differs and because an allocation failure may
   occur on well-formed input. *)
Inductive TxAccessListOutcomeClass :=
| txAccessListOk (entries : list AccessListEntryValue)
| txAccessListInvalidInput
| txAccessListAllocationFailure.

(* The outcomes the candidate allows, with the `rest` advance [consumed].
   An allocation failure is allowed once the first item decoded as a list
   with a non-empty payload: the first allocator call is reached only inside
   the entry loop. It is not narrowed further (to walks that reach an append
   whose capacity is exhausted): the allocator premise decides whether a
   call fails. *)
Definition txAccessListOutcomeAllowed (input : list byte)
    (outcome : TxAccessListOutcomeClass) (consumed : Z) : Prop :=
  match outcome with
  | txAccessListOk entries =>
      candidateAccessList input = accessListAccepted entries consumed
  | txAccessListInvalidInput =>
      (exists rejected, candidateAccessList input = accessListRejected rejected) /\
      consumed = accessListCandidateConsumed (candidateAccessList input)
  | txAccessListAllocationFailure =>
      exists headerLength payloadLength,
        candidateDecodeItem input =
          candidateSuccess true headerLength payloadLength /\
        0 < payloadLength /\
        consumed = itemConsumed headerLength payloadLength
  end.
