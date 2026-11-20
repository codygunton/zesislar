From Coq Require Import Bool List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.

Import ListNotations.
Open Scope Z_scope.

(* Owner: contract fact. The candidate states, as a function on the input
   bytes, what the pinned ELF's decodeParentHeader (0x800d5cb8..0x800d6274)
   returns. It follows the machine code, not the Sail decoder:

   - The outer item (call 0x800d5cf4) must decode, be a list, and have a
     non-empty payload that lies inside the input (0x800d5cfc..0x800d5d1c);
     otherwise the result is the error union.
   - The fields of parentHeaderFieldSchedule are then read in order from the
     payload. Before each field: if nothing is left, a required field is an
     error (the checks after calls 0..7 at 0x800d5d5c..0x800d5ed4, and
     decodeItem's error on an empty slice for fields 9..11), and an optional
     field ends the walk with success (0x800d6070, 0x800d60d0, 0x800d60fc,
     0x800d6140, 0x800d6180, 0x800d61c4, 0x800d6240).
   - A field whose item does not decode is an error.
   - A skipped field advances by the item's consumed length, whatever its
     shape (list or string). The consumed length is decodeItem's
     (header + payload) mod 2^64, so a nested length wrap advances by the
     wrapped amount, as the machine does.
   - An integer field (decodeItem inlined for fields 9..11, nextUint64 for
     15, 17, 18) is an error when its item is a list or its payload is longer
     than 8 bytes; otherwise its value is the big-endian fold of the payload
     (nextUint64ByteFold). No canonical-form check is made.
   - After field 18, and after the outer item, the remaining bytes are never
     read: they do not change the result.

   The candidate is total and computable (vm_compute). It agrees with the
   machine on inputs whose outer header fits (headerFits); on an outer
   length wrap the machine reads past the input and the candidate's error
   result is not the machine's. *)

Inductive ParentHeaderCandidate :=
| candidateHeaderError
| candidateHeaderSuccess (header : ParentHeaderValue).

Definition parentHeaderFieldIsInteger (kind : ParentHeaderFieldKind) : bool :=
  match kind with
  | RequiredUint64 | OptionalUint64 => true
  | RequiredSkip | OptionalSkip => false
  end.

Definition parentHeaderFieldIsRequired (kind : ParentHeaderFieldKind) : bool :=
  match kind with
  | RequiredSkip | RequiredUint64 => true
  | OptionalSkip | OptionalUint64 => false
  end.

(* A field the walk reaches with at least one byte left: its position in
   parentHeaderFieldSchedule (0-based), its kind, and the bytes left at that
   point (its item starts at the first of them). *)
Record ParentHeaderReachedField := {
  reachedFieldIndex : nat;
  reachedFieldKind : ParentHeaderFieldKind;
  reachedFieldBytes : list byte;
}.

(* How the walk ends. [walkValues] lists the integer field values in
   schedule order: gas limit, gas used, timestamp, then the optional base
   fee, blob gas used and excess blob gas that were present. *)
Inductive ParentHeaderWalkEnd :=
| walkRejectOuter
| walkMissingField (index : nat)
| walkRejectField (index : nat)
| walkAccept (walkValues : list Z).

Fixpoint parentHeaderFieldWalk (index : nat)
    (schedule : list (Z * ParentHeaderFieldKind))
    (remaining : list byte) (values : list Z)
    : list ParentHeaderReachedField * ParentHeaderWalkEnd :=
  match schedule with
  | [] => ([], walkAccept values)
  | (_, kind) :: later =>
      match remaining with
      | [] =>
          ([], if parentHeaderFieldIsRequired kind
               then walkMissingField index else walkAccept values)
      | _ :: _ =>
          let here := {| reachedFieldIndex := index;
                         reachedFieldKind := kind;
                         reachedFieldBytes := remaining |} in
          let '(trace, final) :=
            match candidateDecodeItem remaining with
            | candidateError => ([], walkRejectField index)
            | candidateSuccess isList headerLength payloadLength =>
                let rest := skipn
                  (Z.to_nat ((headerLength + payloadLength) mod word64Modulus))
                  remaining in
                if parentHeaderFieldIsInteger kind then
                  if isList || (8 <? payloadLength) then
                    ([], walkRejectField index)
                  else
                    parentHeaderFieldWalk (S index) later rest
                      (values ++ [bigEndian (firstn (Z.to_nat payloadLength)
                                   (skipn (Z.to_nat headerLength) remaining))])
                else parentHeaderFieldWalk (S index) later rest values
            end in
          (here :: trace, final)
      end
  end.

(* The outer item: a list with a non-empty payload inside the input. *)
Definition parentHeaderWalk (bytes : list byte)
    : list ParentHeaderReachedField * ParentHeaderWalkEnd :=
  match candidateDecodeItem bytes with
  | candidateSuccess true headerLength payloadLength =>
      if (0 <? payloadLength) &&
         (headerLength + payloadLength <=? Z.of_nat (List.length bytes))
      then parentHeaderFieldWalk 0 parentHeaderFieldSchedule
             (firstn (Z.to_nat payloadLength)
               (skipn (Z.to_nat headerLength) bytes)) []
      else ([], walkRejectOuter)
  | _ => ([], walkRejectOuter)
  end.

Definition parentHeaderWalkTrace (bytes : list byte)
    : list ParentHeaderReachedField :=
  fst (parentHeaderWalk bytes).

Definition parentHeaderWalkEnd (bytes : list byte) : ParentHeaderWalkEnd :=
  snd (parentHeaderWalk bytes).

(* On acceptance the three required values are always present (the walk
   accepts only at an optional field or after the schedule), so the default
   0 of the first three positions is never used. *)
Definition candidateHeaderOfValues (values : list Z) : ParentHeaderValue := {|
  parentGasLimit := nth 0 values 0;
  parentGasUsed := nth 1 values 0;
  parentTimestamp := nth 2 values 0;
  parentBaseFee := nth_error values 3;
  parentBlobGas := nth_error values 4;
  parentExcessBlobGas := nth_error values 5;
|}.

Definition candidateParentHeader (bytes : list byte) : ParentHeaderCandidate :=
  match parentHeaderWalkEnd bytes with
  | walkAccept values => candidateHeaderSuccess (candidateHeaderOfValues values)
  | walkRejectOuter | walkMissingField _ | walkRejectField _ =>
      candidateHeaderError
  end.

(* The result bytes the candidate allows: the success record or the error
   union (tag 3 at byte 72). *)
Definition parentHeaderCandidateResult (bytes result : list byte) : Prop :=
  match candidateParentHeader bytes with
  | candidateHeaderSuccess header => parentHeaderResult80 result header
  | candidateHeaderError => parentHeaderError80 result
  end.

(* Each integer value of the walk is nextUint64's fold of its payload. *)
Lemma candidateIntegerFold (payload : list byte) :
  (List.length payload <= 8)%nat ->
  nextUint64ByteFold payload (bigEndian payload).
Proof. intros Hlength. split; [exact Hlength | reflexivity]. Qed.
