Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.

Import ListNotations.

(** The first 720 decoded bytes contain 90 words.  The final 128 bytes contain
    the witness, chain configuration, and public-key slice. *)
Definition writeSuccessPostSourceWords (sourceBytes : list (bv 8)) :
    list (bv 64) :=
  u64s_of_bytes 90 sourceBytes.

Definition writeSuccessPostTailWords (decodedBytes : list (bv 8)) :
    list (bv 64) :=
  u64s_of_bytes 16 (take 128 (drop 720 decodedBytes)).

Definition writeSuccessPostWord (words : list (bv 64)) (index : nat) :
    bv 64 :=
  default (BV 64 0) (words !! index).

Definition writeSuccessPostDescriptor (words : list (bv 64))
    (dataIndex sizeIndex : nat) : WriteOutputDescriptor :=
  (writeSuccessPostWord words dataIndex,
   writeSuccessPostWord words sizeIndex).

Definition writeSuccessOptionalU64Words
    (payload present : bv 64) (value : option (bv 64)) : Prop :=
  (bv_extract 0 8 present = BV 8 0 /\ value = None) \/
  (bv_extract 0 8 present <> BV 8 0 /\ value = Some payload).

Definition writeSuccessOptionalBytesWords
    (data size : bv 64) (value : option WriteOutputDescriptor) : Prop :=
  (data = BV 64 0 /\ value = None) \/
  (data <> BV 64 0 /\ value = Some (data, size)).

Definition writeSuccessDescriptorResources `{!islaG Sigma}
    (descriptor : WriteOutputDescriptor) (bytes : list (bv 8)) : iProp Sigma :=
  (bv_unsigned descriptor.1 ↦ₘ∗ bytes ∗
   ⌜bv_unsigned descriptor.2 = Z.of_nat (length bytes)⌝)%I.

Definition writeSuccessHashesResources `{!islaG Sigma}
    (pointer : bv 64) (count : nat) (bytes : list (bv 8)) : iProp Sigma :=
  (bv_unsigned pointer ↦ₘ∗ bytes ∗
   ⌜length bytes = (32 * count)%nat⌝)%I.

Definition writeSuccessOptionalDescriptorResources `{!islaG Sigma}
    (descriptor : option WriteOutputDescriptor)
    (bytes : option (list (bv 8))) : iProp Sigma :=
  match descriptor, bytes with
  | None, None => True
  | Some value, Some payload => writeSuccessDescriptorResources value payload
  | _, _ => False
  end.

(** These equalities follow the pinned [StatelessInput] DWARF layout. *)
Definition writeSuccessPostTransactionDataFacts
    (sp : bv 64) (sourceBytes decodedBytes : list (bv 8))
    (data : WriteSuccessPostTransactionData) : Prop :=
  let source := writeSuccessPostSourceWords sourceBytes in
  let tail := writeSuccessPostTailWords decodedBytes in
  writeSuccessOptionalU64Words
    (writeSuccessPostWord source 15) (writeSuccessPostWord source 16)
    (writeSuccessPostOptional15700 data) /\
  writeSuccessPostBytes1571c data = writeSuccessPostDescriptor source 17 18 /\
  bv_unsigned (writeSuccessPostWord source 75) =
    Z.of_nat (writeSuccessPostHashesCount data) /\
  writeSuccessPostBytes158e0 data = writeSuccessPostDescriptor source 76 77 /\
  writeSuccessPostBytes158f0 data = writeSuccessPostDescriptor source 78 79 /\
  writeSuccessPostBytes15900 data = writeSuccessPostDescriptor source 80 81 /\
  writeSuccessPostBytes15910 data = writeSuccessPostDescriptor source 82 83 /\
  writeSuccessPostBytes15920 data = writeSuccessPostDescriptor source 84 85 /\
  writeSuccessTransactionsPost15674ByteListFacts sp
    (writeSuccessPostWord tail 0) (writeSuccessPostWord tail 1)
    (writeSuccessPostByteLists15930 data) /\
  writeSuccessTransactionsPost15674ByteListFacts sp
    (writeSuccessPostWord tail 2) (writeSuccessPostWord tail 3)
    (writeSuccessPostByteLists15940 data) /\
  writeSuccessTransactionsPost15674ByteListFacts sp
    (writeSuccessPostWord tail 4) (writeSuccessPostWord tail 5)
    (writeSuccessPostByteLists15950 data) /\
  writeSuccessOptionalBytesWords
    (writeSuccessPostWord tail 7) (writeSuccessPostWord tail 8)
    (writeSuccessPostConditional1596c data) /\
  writeSuccessOptionalU64Words
    (writeSuccessPostWord tail 10) (writeSuccessPostWord tail 11)
    (writeSuccessPostOptional159b0 data) /\
  writeSuccessOptionalU64Words
    (writeSuccessPostWord tail 12) (writeSuccessPostWord tail 13)
    (writeSuccessPostOptional159bc data) /\
  writeSuccessTransactionsPost15674ByteListFacts sp
    (writeSuccessPostWord tail 14) (writeSuccessPostWord tail 15)
    (writeSuccessPostByteLists159c8 data).

Definition writeSuccessPostTransactionDataResources `{!islaG Sigma}
    `{!threadG} (sp : bv 64) (sourceBytes decodedBytes : list (bv 8))
    (data : WriteSuccessPostTransactionData) : iProp Sigma :=
  let source := writeSuccessPostSourceWords sourceBytes in
  let tail := writeSuccessPostTailWords decodedBytes in
  (writeSuccessDescriptorResources (writeSuccessPostBytes1571c data)
     (writeSuccessPostBytes1571cPayload data) ∗
   writeSuccessHashesResources (writeSuccessPostWord source 74)
     (writeSuccessPostHashesCount data) (writeSuccessPostHashesPayload data) ∗
   writeSuccessDescriptorResources (writeSuccessPostBytes158e0 data)
     (writeSuccessPostBytes158e0Payload data) ∗
   writeSuccessDescriptorResources (writeSuccessPostBytes158f0 data)
     (writeSuccessPostBytes158f0Payload data) ∗
   writeSuccessDescriptorResources (writeSuccessPostBytes15900 data)
     (writeSuccessPostBytes15900Payload data) ∗
   writeSuccessDescriptorResources (writeSuccessPostBytes15910 data)
     (writeSuccessPostBytes15910Payload data) ∗
   writeSuccessDescriptorResources (writeSuccessPostBytes15920 data)
     (writeSuccessPostBytes15920Payload data) ∗
   byteListItemResources (bv_unsigned (writeSuccessPostWord tail 0))
     (writeSuccessPostByteLists15930 data) ∗
   byteListItemResources (bv_unsigned (writeSuccessPostWord tail 2))
     (writeSuccessPostByteLists15940 data) ∗
   byteListItemResources (bv_unsigned (writeSuccessPostWord tail 4))
     (writeSuccessPostByteLists15950 data) ∗
   writeSuccessOptionalDescriptorResources
     (writeSuccessPostConditional1596c data)
     (writeSuccessPostConditional1596cPayload data) ∗
   byteListItemResources (bv_unsigned (writeSuccessPostWord tail 14))
     (writeSuccessPostByteLists159c8 data) ∗
   ⌜writeSuccessPostTransactionDataFacts sp sourceBytes decodedBytes data⌝)%I.

Global Instance : LithiumUnfold (@writeSuccessDescriptorResources) := I.
Global Instance : LithiumUnfold (@writeSuccessHashesResources) := I.
Global Instance : LithiumUnfold (@writeSuccessOptionalDescriptorResources) := I.
Global Instance : LithiumUnfold (@writeSuccessPostTransactionDataResources) := I.
