Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.

Import ListNotations.
Open Scope Z_scope.

(** This file is the pure representation boundary for the pinned Zig object.
    The offsets follow [input.StatelessInput] and its nested types in the
    DWARF data from the pinned endpoint ELF. *)

Definition writeSuccessBytesAt
    (offset width : nat) (bytes : list (bv 8)) : ByteString :=
  writeSuccessPublicBytes (take width (drop offset bytes)).

Definition writeSuccessWordValue (word : bv 64) : Z := bv_unsigned word.

Fixpoint writeSuccessWordsValue (words : list (bv 64)) : Z :=
  match words with
  | [] => 0
  | word :: rest => bv_unsigned word + 2 ^ 64 * writeSuccessWordsValue rest
  end.

Definition writeSuccessPairValue (words : bv 64 * bv 64) : Z :=
  bv_unsigned words.1 + 2 ^ 64 * bv_unsigned words.2.

Definition writeSuccessOptionalWordValue
    (value : option (bv 64)) : option Z :=
  option_map bv_unsigned value.

Definition writeSuccessOptionalPairValue
    (value : option (bv 64 * bv 64)) : option Z :=
  option_map writeSuccessPairValue value.

Definition writeSuccessByteListsObservation
    (items : list ByteListItem) : list ByteString :=
  map (fun item => writeSuccessPublicBytes (byteListBytes item)) items.

Definition writeSuccessFixedChunks
    (width count : nat) (bytes : list (bv 8)) : list ByteString :=
  map (fun index => writeSuccessBytesAt (width * index) width bytes)
    (seq 0 count).

Definition writeSuccessAccessObservation
    (entry : writeSuccessAccessEntry) : WriteSuccessAccessEntryObservation := {|
  observationAccessAddress :=
    writeSuccessBytesAt 16 20 (writeSuccessAccessEntryBytes entry);
  observationStorageKeys :=
    writeSuccessFixedChunks 32 (writeSuccessAccessEntryStorageCount entry)
      (writeSuccessAccessEntryStorageBytes entry)
|}.

Definition writeSuccessAuthorizationObservationOfBytes
    (bytes : list (bv 8)) : WriteSuccessAuthorizationObservation := {|
  observationAuthorizationChainId :=
    little_endian_to_bv 8 (take 32 bytes);
  observationAuthorizationAddress := writeSuccessBytesAt 112 20 bytes;
  observationAuthorizationNonce :=
    little_endian_to_bv 8 (take 8 (drop 96 bytes));
  observationAuthorizationV :=
    little_endian_to_bv 8 (take 8 (drop 104 bytes));
  observationAuthorizationR :=
    little_endian_to_bv 8 (take 32 (drop 32 bytes));
  observationAuthorizationS :=
    little_endian_to_bv 8 (take 32 (drop 64 bytes))
|}.

Definition writeSuccessTransactionObservationOfNative
    (transaction : writeSuccessTransaction) :
    WriteSuccessTransactionObservation := {|
  observationTransactionType :=
    bv_unsigned (writeSuccessTransactionType transaction);
  observationTransactionChainId :=
    writeSuccessOptionalWordValue (writeSuccessTransactionChainId transaction);
  observationTransactionNonce :=
    bv_unsigned (writeSuccessTransactionNonce transaction);
  observationTransactionGasPrice :=
    writeSuccessPairValue (writeSuccessTransactionGasPrice transaction);
  observationTransactionPriorityFee :=
    writeSuccessOptionalPairValue
      (writeSuccessTransactionGasPriorityFee transaction);
  observationTransactionGasLimit :=
    bv_unsigned (writeSuccessTransactionGasLimit transaction);
  observationTransactionTo :=
    option_map writeSuccessPublicBytes (writeSuccessTransactionTo transaction);
  observationTransactionValue :=
    writeSuccessWordsValue (writeSuccessTransactionValue transaction);
  observationTransactionData :=
    writeSuccessPublicBytes (writeSuccessTransactionData transaction);
  observationTransactionAccessList :=
    map writeSuccessAccessObservation
      (writeSuccessTransactionAccessEntries transaction);
  observationTransactionBlobHashes :=
    map writeSuccessPublicBytes
      (writeSuccessTransactionBlobHashes transaction);
  observationTransactionMaxBlobFee :=
    writeSuccessPairValue
      (writeSuccessTransactionMaxFeePerBlobGas transaction);
  observationTransactionAuthorizations :=
    map writeSuccessAuthorizationObservationOfBytes
      (writeSuccessTransactionAuthorizations transaction);
  observationTransactionV := bv_unsigned (writeSuccessTransactionV transaction);
  observationTransactionR :=
    writeSuccessWordsValue (writeSuccessTransactionR transaction);
  observationTransactionS :=
    writeSuccessWordsValue (writeSuccessTransactionS transaction)
|}.

Definition writeSuccessWithdrawalObservationOfBytes
    (bytes : list (bv 8)) : WriteSuccessWithdrawalObservation := {|
  observationWithdrawalIndex :=
    little_endian_to_bv 8 (take 8 bytes);
  observationWithdrawalValidatorIndex :=
    little_endian_to_bv 8 (take 8 (drop 8 bytes));
  observationWithdrawalAddress := writeSuccessBytesAt 24 20 bytes;
  observationWithdrawalAmount :=
    little_endian_to_bv 8 (take 8 (drop 16 bytes))
|}.

Definition writeSuccessNativeObservation
    (decodedBytes : list (bv 8)) (values : list (bv 64))
    (payload : list (bv 8)) (transactions : list writeSuccessTransaction)
    (rawTransactions : list ByteListItem) (withdrawalsBytes : list (bv 8))
    (withdrawalsCount : nat) (post : WriteSuccessPostTransactionData) :
    WriteSuccessObservation :=
  let source := take 720 decodedBytes in
  let tail := writeSuccessPostTailWords decodedBytes in
  {|
    observationParentHash := writeSuccessBytesAt 152 32 source;
    observationFeeRecipient := writeSuccessBytesAt 184 20 source;
    observationStateRoot := writeSuccessBytesAt 204 32 source;
    observationReceiptsRoot := writeSuccessBytesAt 236 32 source;
    observationLogsBloom := writeSuccessBytesAt 268 256 source;
    observationPrevRandao := writeSuccessBytesAt 524 32 source;
    observationBlockNumber := bv_unsigned (writeSuccessValueWord values 0);
    observationGasLimit := bv_unsigned (writeSuccessValueWord values 1);
    observationGasUsed := bv_unsigned (writeSuccessValueWord values 2);
    observationTimestamp := bv_unsigned (writeSuccessValueWord values 3);
    observationExtraData := writeSuccessPublicBytes payload;
    observationBaseFee := bv_unsigned (writeSuccessValueWord values 6);
    observationBlockHash := writeSuccessBytesAt 556 32 source;
    observationTransactions :=
      map writeSuccessTransactionObservationOfNative transactions;
    observationRawTransactions :=
      writeSuccessByteListsObservation rawTransactions;
    observationWithdrawals :=
      map writeSuccessWithdrawalObservationOfBytes
        (map (fun index => take 48 (drop (48 * index) withdrawalsBytes))
          (seq 0 withdrawalsCount));
    observationBlobGasUsed := bv_unsigned (writeSuccessValueWord values 13);
    observationExcessBlobGas := bv_unsigned (writeSuccessValueWord values 14);
    observationSlotNumber :=
      writeSuccessOptionalWordValue (writeSuccessPostOptional15700 post);
    observationBlockAccessList :=
      writeSuccessPublicBytes (writeSuccessPostBytes1571cPayload post);
    observationParentBeaconRoot := writeSuccessBytesAt 688 32 source;
    observationVersionedHashes :=
      writeSuccessFixedChunks 32 (writeSuccessPostHashesCount post)
        (writeSuccessPostHashesPayload post);
    observationDeposits :=
      writeSuccessPublicBytes (writeSuccessPostBytes158e0Payload post);
    observationWithdrawalRequests :=
      writeSuccessPublicBytes (writeSuccessPostBytes158f0Payload post);
    observationConsolidations :=
      writeSuccessPublicBytes (writeSuccessPostBytes15900Payload post);
    observationBuilderDeposits :=
      writeSuccessPublicBytes (writeSuccessPostBytes15910Payload post);
    observationBuilderExits :=
      writeSuccessPublicBytes (writeSuccessPostBytes15920Payload post);
    observationWitnessNodes :=
      writeSuccessByteListsObservation (writeSuccessPostByteLists15930 post);
    observationWitnessCodes :=
      writeSuccessByteListsObservation (writeSuccessPostByteLists15940 post);
    observationWitnessHeaders :=
      writeSuccessByteListsObservation (writeSuccessPostByteLists15950 post);
    observationChainId := bv_unsigned (writeSuccessPostWord tail 6);
    observationForkName :=
      option_map writeSuccessPublicBytes
        (writeSuccessPostConditional1596cPayload post);
    observationActiveForkIndex := bv_unsigned (writeSuccessPostWord tail 9);
    observationActivationBlock :=
      writeSuccessOptionalWordValue (writeSuccessPostOptional159b0 post);
    observationActivationTimestamp :=
      writeSuccessOptionalWordValue (writeSuccessPostOptional159bc post);
    observationPublicKeys :=
      writeSuccessByteListsObservation (writeSuccessPostByteLists159c8 post)
  |}.

(** A representation instance gives one decoder result type a memory layout. *)
Class WriteSuccessMemoryRepresentation (Decoded : Type) := {
  writeSuccessMemoryRepresents :
    list (bv 8) -> list (bv 64) -> list (bv 8) ->
    list writeSuccessTransaction -> list ByteListItem -> list (bv 8) -> nat ->
    WriteSuccessPostTransactionData -> Decoded -> Prop
}.

(** The decoder and writer share this exact pure relation at their boundary. *)
Definition writeSuccessMemoryRepresentsObservation
    (decodedBytes : list (bv 8)) (values : list (bv 64))
    (payload : list (bv 8)) (transactions : list writeSuccessTransaction)
    (rawTransactions : list ByteListItem) (withdrawalsBytes : list (bv 8))
    (withdrawalsCount : nat) (post : WriteSuccessPostTransactionData)
    (observation : WriteSuccessObservation) : Prop :=
  writeSuccessNativeObservation decodedBytes values payload transactions
    rawTransactions withdrawalsBytes withdrawalsCount post = observation /\
  writeSuccessObservationValid observation.

Global Instance writeSuccessObservationMemoryRepresentation :
    WriteSuccessMemoryRepresentation WriteSuccessObservation := {|
  writeSuccessMemoryRepresents := writeSuccessMemoryRepresentsObservation
|}.
