From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.

Import ListNotations.
Open Scope Z_scope.

(* The pure links of txAccessList's loop cuts to the candidate decoder
   (Candidates/AccessListCandidate.v). They are annotation facts (plan B5
   step 2), not reviewed statements: every block that enters a cut proves
   them, and the exit bridges read them.

   Outer cut (+0xc4): the cursor s4 lies `offset` bytes into the input; the
   input's first item is a list whose payload starts at `headerLength`; the
   entries walked so far are `done`, and the walk of the whole payload is
   `done` followed by the walk of the rest. *)
Definition txAccessListOuterWalked (input : list byte) (offset : Z)
    (done : list AccessListEntryValue) : Prop :=
  exists headerLength payloadLength,
    candidateDecodeItem input = candidateSuccess true headerLength payloadLength /\
    headerLength <= offset <= headerLength + payloadLength /\
    let payload := itemPayload input headerLength payloadLength in
    let rest := skipn (Z.to_nat (offset - headerLength)) payload in
    snd (accessListEntriesWalk (List.length payload) payload) =
      option_map (app done) (snd (accessListEntriesWalk (List.length rest) rest)).

(* Inner cut (+0x18c): `keysPayload` is the current entry's keys payload,
   `offset` the bytes of it walked, `doneKeys` the keys accepted so far. *)
Definition txAccessListKeysWalked (keysPayload : list byte) (offset : Z)
    (doneKeys : list (list byte)) : Prop :=
  0 <= offset <= Z.of_nat (List.length keysPayload) /\
  let rest := skipn (Z.to_nat offset) keysPayload in
  snd (accessListKeysWalk (List.length keysPayload) keysPayload) =
    option_map (app doneKeys) (snd (accessListKeysWalk (List.length rest) rest)).
