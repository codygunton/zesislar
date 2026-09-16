Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Bool.Bool Lists.List ZArith.ZArith Lia.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Import ListNotations.
Open Scope Z_scope.

Definition WriteSuccessParser (A : Type) : Type :=
  ByteString -> option (A * ByteString).
Definition writeSuccessParserBind {A B}
    (result : option (A * ByteString))
    (next : A -> ByteString -> option (B * ByteString)) :=
  match result with Some (value, rest) => next value rest | None => None end.
Local Notation "x '<@' rest '<-' p ';;' q" :=
  (writeSuccessParserBind p (fun x rest => q))
  (at level 100, p at next level, right associativity).

Definition writeSuccessByteb (byte : Z) : bool :=
  (0 <=? byte) && (byte <? 256).
Definition writeSuccessParseFixed (width : nat) :
    WriteSuccessParser ByteString :=
  fun input =>
    if Nat.leb width (length input) then
      let bytes := firstn width input in
      if forallb writeSuccessByteb bytes
      then Some (bytes, skipn width input) else None
    else None.
Fixpoint writeSuccessDecodeLe (bytes : ByteString) : Z :=
  match bytes with
  | [] => 0
  | byte :: tail => byte + 256 * writeSuccessDecodeLe tail
  end.
Definition writeSuccessParseInteger (width : nat) : WriteSuccessParser Z :=
  fun input =>
    bytes <@ rest <- writeSuccessParseFixed width input ;;
    Some (writeSuccessDecodeLe bytes, rest).
Definition writeSuccessParseBytes : WriteSuccessParser ByteString :=
  fun input =>
    declared <@ rest <- writeSuccessParseInteger 8 input ;;
    if declared <=? Z.of_nat (length rest)
    then writeSuccessParseFixed (Z.to_nat declared) rest else None.
Fixpoint writeSuccessParseItems {A} (parse : WriteSuccessParser A)
    (count : nat) (input : ByteString) : option (list A * ByteString) :=
  match count with
  | O => Some ([], input)
  | S count =>
      item <@ rest <- parse input ;;
      items <@ tail <- writeSuccessParseItems parse count rest ;;
      Some (item :: items, tail)
  end.
Definition writeSuccessParseList {A} (parse : WriteSuccessParser A) :
    WriteSuccessParser (list A) :=
  fun input =>
    declared <@ rest <- writeSuccessParseInteger 8 input ;;
    if declared <=? Z.of_nat (length rest)
    then writeSuccessParseItems parse (Z.to_nat declared) rest else None.
Definition writeSuccessParseOptionalInteger (width : nat) :
    WriteSuccessParser (option Z) :=
  fun input =>
    tag <@ rest <- writeSuccessParseInteger 1 input ;;
    match tag with
    | 0 => Some (None, rest)
    | 1 => value <@ tail <- writeSuccessParseInteger width rest ;;
           Some (Some value, tail)
    | _ => None
    end.
Definition writeSuccessParseOptionalFixed (width : nat) :
    WriteSuccessParser (option ByteString) :=
  fun input =>
    tag <@ rest <- writeSuccessParseInteger 1 input ;;
    match tag with
    | 0 => Some (None, rest)
    | 1 => value <@ tail <- writeSuccessParseFixed width rest ;;
           Some (Some value, tail)
    | _ => None
    end.
Definition writeSuccessParseOptionalBytes :
    WriteSuccessParser (option ByteString) :=
  fun input =>
    tag <@ rest <- writeSuccessParseInteger 1 input ;;
    match tag with
    | 0 => Some (None, rest)
    | 1 => value <@ tail <- writeSuccessParseBytes rest ;;
           Some (Some value, tail)
    | _ => None
    end.

Definition writeSuccessParseAccessEntry :
    WriteSuccessParser WriteSuccessAccessEntryObservation :=
  fun input =>
    address <@ rest <- writeSuccessParseFixed 20 input ;;
    keys <@ tail <- writeSuccessParseList (writeSuccessParseFixed 32) rest ;;
    Some ({| observationAccessAddress := address;
             observationStorageKeys := keys |}, tail).
Definition writeSuccessParseAuthorization :
    WriteSuccessParser WriteSuccessAuthorizationObservation :=
  fun input =>
    chainId <@ r1 <- writeSuccessParseInteger 32 input ;;
    address <@ r2 <- writeSuccessParseFixed 20 r1 ;;
    nonce <@ r3 <- writeSuccessParseInteger 8 r2 ;;
    v <@ r4 <- writeSuccessParseInteger 8 r3 ;;
    r <@ r5 <- writeSuccessParseInteger 32 r4 ;;
    s <@ tail <- writeSuccessParseInteger 32 r5 ;;
    Some ({| observationAuthorizationChainId := chainId;
             observationAuthorizationAddress := address;
             observationAuthorizationNonce := nonce;
             observationAuthorizationV := v;
             observationAuthorizationR := r;
             observationAuthorizationS := s |}, tail).
Definition writeSuccessParseTransaction :
    WriteSuccessParser WriteSuccessTransactionObservation :=
  fun input =>
    transactionType <@ r1 <- writeSuccessParseInteger 1 input ;;
    chainId <@ r2 <- writeSuccessParseOptionalInteger 8 r1 ;;
    nonce <@ r3 <- writeSuccessParseInteger 8 r2 ;;
    gasPrice <@ r4 <- writeSuccessParseInteger 16 r3 ;;
    priorityFee <@ r5 <- writeSuccessParseOptionalInteger 16 r4 ;;
    gasLimit <@ r6 <- writeSuccessParseInteger 8 r5 ;;
    to <@ r7 <- writeSuccessParseOptionalFixed 20 r6 ;;
    value <@ r8 <- writeSuccessParseInteger 32 r7 ;;
    data <@ r9 <- writeSuccessParseBytes r8 ;;
    accessList <@ r10 <- writeSuccessParseList writeSuccessParseAccessEntry r9 ;;
    blobHashes <@ r11 <- writeSuccessParseList (writeSuccessParseFixed 32) r10 ;;
    maxBlobFee <@ r12 <- writeSuccessParseInteger 16 r11 ;;
    authorizations <@ r13 <-
      writeSuccessParseList writeSuccessParseAuthorization r12 ;;
    v <@ r14 <- writeSuccessParseInteger 8 r13 ;;
    r <@ r15 <- writeSuccessParseInteger 32 r14 ;;
    s <@ tail <- writeSuccessParseInteger 32 r15 ;;
    Some ({| observationTransactionType := transactionType;
             observationTransactionChainId := chainId;
             observationTransactionNonce := nonce;
             observationTransactionGasPrice := gasPrice;
             observationTransactionPriorityFee := priorityFee;
             observationTransactionGasLimit := gasLimit;
             observationTransactionTo := to;
             observationTransactionValue := value;
             observationTransactionData := data;
             observationTransactionAccessList := accessList;
             observationTransactionBlobHashes := blobHashes;
             observationTransactionMaxBlobFee := maxBlobFee;
             observationTransactionAuthorizations := authorizations;
             observationTransactionV := v;
             observationTransactionR := r;
             observationTransactionS := s |}, tail).
Definition writeSuccessParseWithdrawal :
    WriteSuccessParser WriteSuccessWithdrawalObservation :=
  fun input =>
    index <@ r1 <- writeSuccessParseInteger 8 input ;;
    validatorIndex <@ r2 <- writeSuccessParseInteger 8 r1 ;;
    address <@ r3 <- writeSuccessParseFixed 20 r2 ;;
    amount <@ tail <- writeSuccessParseInteger 8 r3 ;;
    Some ({| observationWithdrawalIndex := index;
             observationWithdrawalValidatorIndex := validatorIndex;
             observationWithdrawalAddress := address;
             observationWithdrawalAmount := amount |}, tail).

Definition writeSuccessParseObservation :
    WriteSuccessParser WriteSuccessObservation :=
  fun input =>
    magic <@ r0 <- writeSuccessParseFixed 6 input ;;
    if list_eq_dec Z.eq_dec magic [90; 83; 83; 90; 1; 1] then
    parentHash <@ r1 <- writeSuccessParseFixed 32 r0 ;;
    feeRecipient <@ r2 <- writeSuccessParseFixed 20 r1 ;;
    stateRoot <@ r3 <- writeSuccessParseFixed 32 r2 ;;
    receiptsRoot <@ r4 <- writeSuccessParseFixed 32 r3 ;;
    logsBloom <@ r5 <- writeSuccessParseFixed 256 r4 ;;
    prevRandao <@ r6 <- writeSuccessParseFixed 32 r5 ;;
    blockNumber <@ r7 <- writeSuccessParseInteger 8 r6 ;;
    gasLimit <@ r8 <- writeSuccessParseInteger 8 r7 ;;
    gasUsed <@ r9 <- writeSuccessParseInteger 8 r8 ;;
    timestamp <@ r10 <- writeSuccessParseInteger 8 r9 ;;
    extraData <@ r11 <- writeSuccessParseBytes r10 ;;
    baseFee <@ r12 <- writeSuccessParseInteger 8 r11 ;;
    blockHash <@ r13 <- writeSuccessParseFixed 32 r12 ;;
    transactions <@ r14 <-
      writeSuccessParseList writeSuccessParseTransaction r13 ;;
    rawTransactions <@ r15 <-
      writeSuccessParseList writeSuccessParseBytes r14 ;;
    withdrawals <@ r16 <-
      writeSuccessParseList writeSuccessParseWithdrawal r15 ;;
    blobGasUsed <@ r17 <- writeSuccessParseInteger 8 r16 ;;
    excessBlobGas <@ r18 <- writeSuccessParseInteger 8 r17 ;;
    slotNumber <@ r19 <- writeSuccessParseOptionalInteger 8 r18 ;;
    blockAccessList <@ r20 <- writeSuccessParseBytes r19 ;;
    parentBeaconRoot <@ r21 <- writeSuccessParseFixed 32 r20 ;;
    versionedHashes <@ r22 <-
      writeSuccessParseList (writeSuccessParseFixed 32) r21 ;;
    deposits <@ r23 <- writeSuccessParseBytes r22 ;;
    withdrawalRequests <@ r24 <- writeSuccessParseBytes r23 ;;
    consolidations <@ r25 <- writeSuccessParseBytes r24 ;;
    builderDeposits <@ r26 <- writeSuccessParseBytes r25 ;;
    builderExits <@ r27 <- writeSuccessParseBytes r26 ;;
    witnessNodes <@ r28 <- writeSuccessParseList writeSuccessParseBytes r27 ;;
    witnessCodes <@ r29 <- writeSuccessParseList writeSuccessParseBytes r28 ;;
    witnessHeaders <@ r30 <-
      writeSuccessParseList writeSuccessParseBytes r29 ;;
    chainId <@ r31 <- writeSuccessParseInteger 8 r30 ;;
    forkName <@ r32 <- writeSuccessParseOptionalBytes r31 ;;
    activeForkIndex <@ r33 <- writeSuccessParseInteger 8 r32 ;;
    activationBlock <@ r34 <- writeSuccessParseOptionalInteger 8 r33 ;;
    activationTimestamp <@ r35 <-
      writeSuccessParseOptionalInteger 8 r34 ;;
    publicKeys <@ tail <- writeSuccessParseList writeSuccessParseBytes r35 ;;
    Some ({| observationParentHash := parentHash;
             observationFeeRecipient := feeRecipient;
             observationStateRoot := stateRoot;
             observationReceiptsRoot := receiptsRoot;
             observationLogsBloom := logsBloom;
             observationPrevRandao := prevRandao;
             observationBlockNumber := blockNumber;
             observationGasLimit := gasLimit;
             observationGasUsed := gasUsed;
             observationTimestamp := timestamp;
             observationExtraData := extraData;
             observationBaseFee := baseFee;
             observationBlockHash := blockHash;
             observationTransactions := transactions;
             observationRawTransactions := rawTransactions;
             observationWithdrawals := withdrawals;
             observationBlobGasUsed := blobGasUsed;
             observationExcessBlobGas := excessBlobGas;
             observationSlotNumber := slotNumber;
             observationBlockAccessList := blockAccessList;
             observationParentBeaconRoot := parentBeaconRoot;
             observationVersionedHashes := versionedHashes;
             observationDeposits := deposits;
             observationWithdrawalRequests := withdrawalRequests;
             observationConsolidations := consolidations;
             observationBuilderDeposits := builderDeposits;
             observationBuilderExits := builderExits;
             observationWitnessNodes := witnessNodes;
             observationWitnessCodes := witnessCodes;
             observationWitnessHeaders := witnessHeaders;
             observationChainId := chainId;
             observationForkName := forkName;
             observationActiveForkIndex := activeForkIndex;
             observationActivationBlock := activationBlock;
             observationActivationTimestamp := activationTimestamp;
             observationPublicKeys := publicKeys |}, tail)
    else None.

Definition writeSuccessDecodeObservation
    (bytes : ByteString) : option WriteSuccessObservation :=
  match writeSuccessParseObservation bytes with
  | Some (observation, []) => Some observation
  | _ => None
  end.
Definition writeSuccessObservationRoundTrip : Prop :=
  forall observation tail,
    writeSuccessObservationValid observation ->
    writeSuccessParseObservation
      (writeSuccessEncodeObservation observation ++ tail) =
    Some (observation, tail).
Definition writeSuccessParserSound : Prop :=
  forall bytes observation rest,
    writeSuccessParseObservation bytes = Some (observation, rest) ->
    bytes = writeSuccessEncodeObservation observation ++ rest /\
    writeSuccessObservationValid observation.
Lemma writeSuccessDecodeFromRoundTrip :
  writeSuccessObservationRoundTrip ->
  forall observation,
    writeSuccessObservationValid observation ->
    writeSuccessDecodeObservation (writeSuccessEncodeObservation observation) =
      Some observation.
Proof.
  intros HroundTrip observation Hvalid.
  pose proof (HroundTrip observation [] Hvalid) as Hparse.
  rewrite app_nil_r in Hparse.
  unfold writeSuccessDecodeObservation. rewrite Hparse. reflexivity.
Qed.

Lemma writeSuccessDecodeRejectsNonemptyTail :
  writeSuccessObservationRoundTrip ->
  forall observation tail,
    writeSuccessObservationValid observation ->
    tail <> [] ->
    writeSuccessDecodeObservation
      (writeSuccessEncodeObservation observation ++ tail) = None.
Proof.
  intros HroundTrip observation tail Hvalid Htail.
  pose proof (HroundTrip observation tail Hvalid) as Hparse.
  unfold writeSuccessDecodeObservation. rewrite Hparse.
  destruct tail; [contradiction | reflexivity].
Qed.

Print Assumptions writeSuccessDecodeRejectsNonemptyTail.

Example writeSuccessParseBaseFeeDistinct :
  writeSuccessParseInteger 8
      (writeSuccessEncodeU64 1 ++ writeSuccessEncodeU64 2) =
    Some (1, writeSuccessEncodeU64 2) /\
  writeSuccessParseInteger 8 (writeSuccessEncodeU64 2) = Some (2, []).
Proof. vm_compute. auto. Qed.
Example writeSuccessParseVariablePublicKeys :
  writeSuccessParseList writeSuccessParseBytes
    (writeSuccessEncodeList writeSuccessEncodeBytes [[1; 2]; [3]] ++ [9]) =
  Some ([[1; 2]; [3]], [9]).
Proof. vm_compute. reflexivity. Qed.
Example writeSuccessParseOptionalTags :
  writeSuccessParseOptionalInteger 8 [0; 9] = Some (None, [9]) /\
  writeSuccessParseOptionalInteger 8
    (1 :: writeSuccessEncodeU64 7 ++ [9]) = Some (Some 7, [9]) /\
  writeSuccessParseOptionalInteger 8 [2] = None.
Proof. vm_compute. auto. Qed.
Example writeSuccessParseTruncation :
  writeSuccessParseBytes [1; 0; 0; 0; 0; 0; 0] = None /\
  writeSuccessParseBytes (writeSuccessEncodeU64 2 ++ [7]) = None.
Proof. vm_compute. auto. Qed.

Example writeSuccessParseRejectsNonBytes :
  writeSuccessParseFixed 1 [-1] = None /\
  writeSuccessParseFixed 1 [256] = None.
Proof. vm_compute. auto. Qed.
