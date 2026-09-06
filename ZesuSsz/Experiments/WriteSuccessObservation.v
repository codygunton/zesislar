From Coq Require Import Lists.List ZArith.ZArith Lia.
Require Import ZesuSsz.Contracts.Level1.

Import ListNotations.
Open Scope Z_scope.

(** This model follows [ssz_decode_observation.zig].  Each fixed byte array
    uses a [ByteString].  The validity predicate fixes its required width. *)
Record WriteSuccessAccessEntryObservation : Type := {
  observationAccessAddress : ByteString;
  observationStorageKeys : list ByteString
}.

Record WriteSuccessAuthorizationObservation : Type := {
  observationAuthorizationChainId : Z;
  observationAuthorizationAddress : ByteString;
  observationAuthorizationNonce : Z;
  observationAuthorizationV : Z;
  observationAuthorizationR : Z;
  observationAuthorizationS : Z
}.

Record WriteSuccessTransactionObservation : Type := {
  observationTransactionType : Z;
  observationTransactionChainId : option Z;
  observationTransactionNonce : Z;
  observationTransactionGasPrice : Z;
  observationTransactionPriorityFee : option Z;
  observationTransactionGasLimit : Z;
  observationTransactionTo : option ByteString;
  observationTransactionValue : Z;
  observationTransactionData : ByteString;
  observationTransactionAccessList : list WriteSuccessAccessEntryObservation;
  observationTransactionBlobHashes : list ByteString;
  observationTransactionMaxBlobFee : Z;
  observationTransactionAuthorizations :
    list WriteSuccessAuthorizationObservation;
  observationTransactionV : Z;
  observationTransactionR : Z;
  observationTransactionS : Z
}.

Record WriteSuccessWithdrawalObservation : Type := {
  observationWithdrawalIndex : Z;
  observationWithdrawalValidatorIndex : Z;
  observationWithdrawalAddress : ByteString;
  observationWithdrawalAmount : Z
}.

Record WriteSuccessObservation : Type := {
  observationParentHash : ByteString;
  observationFeeRecipient : ByteString;
  observationStateRoot : ByteString;
  observationReceiptsRoot : ByteString;
  observationLogsBloom : ByteString;
  observationPrevRandao : ByteString;
  observationBlockNumber : Z;
  observationGasLimit : Z;
  observationGasUsed : Z;
  observationTimestamp : Z;
  observationExtraData : ByteString;
  observationBaseFee : Z;
  observationBlockHash : ByteString;
  observationTransactions : list WriteSuccessTransactionObservation;
  observationRawTransactions : list ByteString;
  observationWithdrawals : list WriteSuccessWithdrawalObservation;
  observationBlobGasUsed : Z;
  observationExcessBlobGas : Z;
  observationSlotNumber : option Z;
  observationBlockAccessList : ByteString;
  observationParentBeaconRoot : ByteString;
  observationVersionedHashes : list ByteString;
  observationDeposits : ByteString;
  observationWithdrawalRequests : ByteString;
  observationConsolidations : ByteString;
  observationBuilderDeposits : ByteString;
  observationBuilderExits : ByteString;
  observationWitnessNodes : list ByteString;
  observationWitnessCodes : list ByteString;
  observationWitnessHeaders : list ByteString;
  observationChainId : Z;
  observationForkName : option ByteString;
  observationActiveForkIndex : Z;
  observationActivationBlock : option Z;
  observationActivationTimestamp : option Z;
  observationPublicKeys : list ByteString
}.

Fixpoint writeSuccessEncodeLe (width : nat) (value : Z) : ByteString :=
  match width with
  | O => []
  | S rest => Z.modulo value 256 :: writeSuccessEncodeLe rest (Z.div value 256)
  end.

Definition writeSuccessEncodeU8 := writeSuccessEncodeLe 1.
Definition writeSuccessEncodeU64 := writeSuccessEncodeLe 8.
Definition writeSuccessEncodeU128 := writeSuccessEncodeLe 16.
Definition writeSuccessEncodeU256 := writeSuccessEncodeLe 32.

Definition writeSuccessEncodeBytes (bytes : ByteString) : ByteString :=
  writeSuccessEncodeU64 (Z.of_nat (length bytes)) ++ bytes.

Definition writeSuccessEncodeOptional
    (encode : Z -> ByteString) (value : option Z) : ByteString :=
  match value with
  | None => [0]
  | Some item => 1 :: encode item
  end.

Definition writeSuccessEncodeOptionalBytes
    (value : option ByteString) : ByteString :=
  match value with
  | None => [0]
  | Some bytes => 1 :: bytes
  end.

Definition writeSuccessEncodeList {A : Type}
    (encode : A -> ByteString) (items : list A) : ByteString :=
  writeSuccessEncodeU64 (Z.of_nat (length items)) ++
  concat (map encode items).

Definition writeSuccessEncodeAccessEntry
    (entry : WriteSuccessAccessEntryObservation) : ByteString :=
  observationAccessAddress entry ++
  writeSuccessEncodeList (fun bytes => bytes) (observationStorageKeys entry).

Definition writeSuccessEncodeAuthorization
    (authorization : WriteSuccessAuthorizationObservation) : ByteString :=
  writeSuccessEncodeU256 (observationAuthorizationChainId authorization) ++
  observationAuthorizationAddress authorization ++
  writeSuccessEncodeU64 (observationAuthorizationNonce authorization) ++
  writeSuccessEncodeU64 (observationAuthorizationV authorization) ++
  writeSuccessEncodeU256 (observationAuthorizationR authorization) ++
  writeSuccessEncodeU256 (observationAuthorizationS authorization).

Definition writeSuccessEncodeTransaction
    (transaction : WriteSuccessTransactionObservation) : ByteString :=
  writeSuccessEncodeU8 (observationTransactionType transaction) ++
  writeSuccessEncodeOptional writeSuccessEncodeU64
    (observationTransactionChainId transaction) ++
  writeSuccessEncodeU64 (observationTransactionNonce transaction) ++
  writeSuccessEncodeU128 (observationTransactionGasPrice transaction) ++
  writeSuccessEncodeOptional writeSuccessEncodeU128
    (observationTransactionPriorityFee transaction) ++
  writeSuccessEncodeU64 (observationTransactionGasLimit transaction) ++
  writeSuccessEncodeOptionalBytes (observationTransactionTo transaction) ++
  writeSuccessEncodeU256 (observationTransactionValue transaction) ++
  writeSuccessEncodeBytes (observationTransactionData transaction) ++
  writeSuccessEncodeList writeSuccessEncodeAccessEntry
    (observationTransactionAccessList transaction) ++
  writeSuccessEncodeList (fun bytes => bytes)
    (observationTransactionBlobHashes transaction) ++
  writeSuccessEncodeU128 (observationTransactionMaxBlobFee transaction) ++
  writeSuccessEncodeList writeSuccessEncodeAuthorization
    (observationTransactionAuthorizations transaction) ++
  writeSuccessEncodeU64 (observationTransactionV transaction) ++
  writeSuccessEncodeU256 (observationTransactionR transaction) ++
  writeSuccessEncodeU256 (observationTransactionS transaction).

Definition writeSuccessEncodeWithdrawal
    (withdrawal : WriteSuccessWithdrawalObservation) : ByteString :=
  writeSuccessEncodeU64 (observationWithdrawalIndex withdrawal) ++
  writeSuccessEncodeU64 (observationWithdrawalValidatorIndex withdrawal) ++
  observationWithdrawalAddress withdrawal ++
  writeSuccessEncodeU64 (observationWithdrawalAmount withdrawal).

Definition writeSuccessEncodeObservation
    (observation : WriteSuccessObservation) : ByteString :=
  [90; 83; 83; 90; 1; 1] ++
  observationParentHash observation ++
  observationFeeRecipient observation ++
  observationStateRoot observation ++
  observationReceiptsRoot observation ++
  observationLogsBloom observation ++
  observationPrevRandao observation ++
  writeSuccessEncodeU64 (observationBlockNumber observation) ++
  writeSuccessEncodeU64 (observationGasLimit observation) ++
  writeSuccessEncodeU64 (observationGasUsed observation) ++
  writeSuccessEncodeU64 (observationTimestamp observation) ++
  writeSuccessEncodeBytes (observationExtraData observation) ++
  writeSuccessEncodeU64 (observationBaseFee observation) ++
  observationBlockHash observation ++
  writeSuccessEncodeList writeSuccessEncodeTransaction
    (observationTransactions observation) ++
  writeSuccessEncodeList writeSuccessEncodeBytes
    (observationRawTransactions observation) ++
  writeSuccessEncodeList writeSuccessEncodeWithdrawal
    (observationWithdrawals observation) ++
  writeSuccessEncodeU64 (observationBlobGasUsed observation) ++
  writeSuccessEncodeU64 (observationExcessBlobGas observation) ++
  writeSuccessEncodeOptional writeSuccessEncodeU64
    (observationSlotNumber observation) ++
  writeSuccessEncodeBytes (observationBlockAccessList observation) ++
  observationParentBeaconRoot observation ++
  writeSuccessEncodeList (fun bytes => bytes)
    (observationVersionedHashes observation) ++
  writeSuccessEncodeBytes (observationDeposits observation) ++
  writeSuccessEncodeBytes (observationWithdrawalRequests observation) ++
  writeSuccessEncodeBytes (observationConsolidations observation) ++
  writeSuccessEncodeBytes (observationBuilderDeposits observation) ++
  writeSuccessEncodeBytes (observationBuilderExits observation) ++
  writeSuccessEncodeList writeSuccessEncodeBytes
    (observationWitnessNodes observation) ++
  writeSuccessEncodeList writeSuccessEncodeBytes
    (observationWitnessCodes observation) ++
  writeSuccessEncodeList writeSuccessEncodeBytes
    (observationWitnessHeaders observation) ++
  writeSuccessEncodeU64 (observationChainId observation) ++
  (match observationForkName observation with
   | None => [0]
   | Some name => 1 :: writeSuccessEncodeBytes name
   end) ++
  writeSuccessEncodeU64 (observationActiveForkIndex observation) ++
  writeSuccessEncodeOptional writeSuccessEncodeU64
    (observationActivationBlock observation) ++
  writeSuccessEncodeOptional writeSuccessEncodeU64
    (observationActivationTimestamp observation) ++
  writeSuccessEncodeList writeSuccessEncodeBytes
    (observationPublicKeys observation).

Definition writeSuccessByte (value : Z) : Prop := 0 <= value < 256.

Definition writeSuccessBytesValid (width : nat) (bytes : ByteString) : Prop :=
  length bytes = width /\ Forall writeSuccessByte bytes.

Definition writeSuccessLengthValid {A : Type} (items : list A) : Prop :=
  (Z.of_nat (length items) < 2 ^ 64)%Z.

Definition writeSuccessVariableBytesValid (bytes : ByteString) : Prop :=
  writeSuccessLengthValid bytes /\ Forall writeSuccessByte bytes.

Definition writeSuccessListValid {A : Type}
    (valid : A -> Prop) (items : list A) : Prop :=
  writeSuccessLengthValid items /\ Forall valid items.

Definition writeSuccessUnsignedValid (width : nat) (value : Z) : Prop :=
  0 <= value < 2 ^ Z.of_nat (Nat.mul 8 width).

Definition writeSuccessOptionValid
    (valid : Z -> Prop) (value : option Z) : Prop :=
  match value with
  | None => True
  | Some item => valid item
  end.

Definition writeSuccessOptionalBytesValid
    (width : nat) (value : option ByteString) : Prop :=
  match value with
  | None => True
  | Some bytes => writeSuccessBytesValid width bytes
  end.

Definition writeSuccessAccessEntryValid
    (entry : WriteSuccessAccessEntryObservation) : Prop :=
  writeSuccessBytesValid 20 (observationAccessAddress entry) /\
  writeSuccessListValid (writeSuccessBytesValid 32)
    (observationStorageKeys entry).

Definition writeSuccessAuthorizationValid
    (authorization : WriteSuccessAuthorizationObservation) : Prop :=
  writeSuccessUnsignedValid 32
    (observationAuthorizationChainId authorization) /\
  writeSuccessBytesValid 20
    (observationAuthorizationAddress authorization) /\
  writeSuccessUnsignedValid 8
    (observationAuthorizationNonce authorization) /\
  writeSuccessUnsignedValid 8 (observationAuthorizationV authorization) /\
  writeSuccessUnsignedValid 32 (observationAuthorizationR authorization) /\
  writeSuccessUnsignedValid 32 (observationAuthorizationS authorization).

Definition writeSuccessTransactionObservationValid
    (transaction : WriteSuccessTransactionObservation) : Prop :=
  writeSuccessUnsignedValid 1 (observationTransactionType transaction) /\
  writeSuccessOptionValid (writeSuccessUnsignedValid 8)
    (observationTransactionChainId transaction) /\
  writeSuccessUnsignedValid 8 (observationTransactionNonce transaction) /\
  writeSuccessUnsignedValid 16
    (observationTransactionGasPrice transaction) /\
  writeSuccessOptionValid (writeSuccessUnsignedValid 16)
    (observationTransactionPriorityFee transaction) /\
  writeSuccessUnsignedValid 8 (observationTransactionGasLimit transaction) /\
  writeSuccessOptionalBytesValid 20 (observationTransactionTo transaction) /\
  writeSuccessUnsignedValid 32 (observationTransactionValue transaction) /\
  writeSuccessVariableBytesValid (observationTransactionData transaction) /\
  writeSuccessListValid writeSuccessAccessEntryValid
    (observationTransactionAccessList transaction) /\
  writeSuccessListValid (writeSuccessBytesValid 32)
    (observationTransactionBlobHashes transaction) /\
  writeSuccessUnsignedValid 16
    (observationTransactionMaxBlobFee transaction) /\
  writeSuccessListValid writeSuccessAuthorizationValid
    (observationTransactionAuthorizations transaction) /\
  writeSuccessUnsignedValid 8 (observationTransactionV transaction) /\
  writeSuccessUnsignedValid 32 (observationTransactionR transaction) /\
  writeSuccessUnsignedValid 32 (observationTransactionS transaction).

Definition writeSuccessWithdrawalObservationValid
    (withdrawal : WriteSuccessWithdrawalObservation) : Prop :=
  writeSuccessUnsignedValid 8 (observationWithdrawalIndex withdrawal) /\
  writeSuccessUnsignedValid 8
    (observationWithdrawalValidatorIndex withdrawal) /\
  writeSuccessBytesValid 20 (observationWithdrawalAddress withdrawal) /\
  writeSuccessUnsignedValid 8 (observationWithdrawalAmount withdrawal).

Definition writeSuccessObservationValid
    (observation : WriteSuccessObservation) : Prop :=
  writeSuccessBytesValid 32 (observationParentHash observation) /\
  writeSuccessBytesValid 20 (observationFeeRecipient observation) /\
  writeSuccessBytesValid 32 (observationStateRoot observation) /\
  writeSuccessBytesValid 32 (observationReceiptsRoot observation) /\
  writeSuccessBytesValid 256 (observationLogsBloom observation) /\
  writeSuccessBytesValid 32 (observationPrevRandao observation) /\
  writeSuccessUnsignedValid 8 (observationBlockNumber observation) /\
  writeSuccessUnsignedValid 8 (observationGasLimit observation) /\
  writeSuccessUnsignedValid 8 (observationGasUsed observation) /\
  writeSuccessUnsignedValid 8 (observationTimestamp observation) /\
  writeSuccessVariableBytesValid (observationExtraData observation) /\
  writeSuccessUnsignedValid 8 (observationBaseFee observation) /\
  writeSuccessBytesValid 32 (observationBlockHash observation) /\
  writeSuccessListValid writeSuccessTransactionObservationValid
    (observationTransactions observation) /\
  writeSuccessListValid writeSuccessVariableBytesValid
    (observationRawTransactions observation) /\
  writeSuccessListValid writeSuccessWithdrawalObservationValid
    (observationWithdrawals observation) /\
  writeSuccessUnsignedValid 8 (observationBlobGasUsed observation) /\
  writeSuccessUnsignedValid 8 (observationExcessBlobGas observation) /\
  writeSuccessOptionValid (writeSuccessUnsignedValid 8)
    (observationSlotNumber observation) /\
  writeSuccessVariableBytesValid (observationBlockAccessList observation) /\
  writeSuccessBytesValid 32 (observationParentBeaconRoot observation) /\
  writeSuccessListValid (writeSuccessBytesValid 32)
    (observationVersionedHashes observation) /\
  writeSuccessVariableBytesValid (observationDeposits observation) /\
  writeSuccessVariableBytesValid (observationWithdrawalRequests observation) /\
  writeSuccessVariableBytesValid (observationConsolidations observation) /\
  writeSuccessVariableBytesValid (observationBuilderDeposits observation) /\
  writeSuccessVariableBytesValid (observationBuilderExits observation) /\
  writeSuccessListValid writeSuccessVariableBytesValid
    (observationWitnessNodes observation) /\
  writeSuccessListValid writeSuccessVariableBytesValid
    (observationWitnessCodes observation) /\
  writeSuccessListValid writeSuccessVariableBytesValid
    (observationWitnessHeaders observation) /\
  writeSuccessUnsignedValid 8 (observationChainId observation) /\
  (match observationForkName observation with
   | None => True
   | Some name => writeSuccessVariableBytesValid name
   end) /\
  writeSuccessUnsignedValid 8 (observationActiveForkIndex observation) /\
  writeSuccessOptionValid (writeSuccessUnsignedValid 8)
    (observationActivationBlock observation) /\
  writeSuccessOptionValid (writeSuccessUnsignedValid 8)
    (observationActivationTimestamp observation) /\
  writeSuccessListValid writeSuccessVariableBytesValid
    (observationPublicKeys observation).

