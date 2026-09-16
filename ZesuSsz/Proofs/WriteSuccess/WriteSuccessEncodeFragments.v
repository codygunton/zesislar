Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.

Import ListNotations.

(** Each list element is the payload of one native [write_output] call. *)
Definition writeSuccessBytesFragments (bytes : ByteString) : list ByteString :=
  [writeSuccessEncodeU64 (Z.of_nat (length bytes)); bytes].

Definition writeSuccessOptionalFragments
    (encode : Z -> ByteString) (value : option Z) : list ByteString :=
  match value with
  | None => [[0]]
  | Some item => [[1]; encode item]
  end.

Definition writeSuccessOptionalBytesFragments
    (value : option ByteString) : list ByteString :=
  match value with
  | None => [[0]]
  | Some bytes => [[1]; bytes]
  end.

Definition writeSuccessListFragments {A : Type}
    (fragments : A -> list ByteString) (items : list A) : list ByteString :=
  writeSuccessEncodeU64 (Z.of_nat (length items)) ::
  concat (map fragments items).

Definition writeSuccessAccessFragments
    (entry : WriteSuccessAccessEntryObservation) : list ByteString :=
  [observationAccessAddress entry] ++
  writeSuccessListFragments (fun bytes => [bytes])
    (observationStorageKeys entry).

Definition writeSuccessAuthorizationFragments
    (authorization : WriteSuccessAuthorizationObservation) : list ByteString :=
  [writeSuccessEncodeU256 (observationAuthorizationChainId authorization);
   observationAuthorizationAddress authorization;
   writeSuccessEncodeU64 (observationAuthorizationNonce authorization);
   writeSuccessEncodeU64 (observationAuthorizationV authorization);
   writeSuccessEncodeU256 (observationAuthorizationR authorization);
   writeSuccessEncodeU256 (observationAuthorizationS authorization)].

Definition writeSuccessTransactionFragments
    (transaction : WriteSuccessTransactionObservation) : list ByteString :=
  [[Z.modulo (observationTransactionType transaction) 256]] ++
  writeSuccessOptionalFragments writeSuccessEncodeU64
    (observationTransactionChainId transaction) ++
  [writeSuccessEncodeU64 (observationTransactionNonce transaction);
   writeSuccessEncodeU128 (observationTransactionGasPrice transaction)] ++
  writeSuccessOptionalFragments writeSuccessEncodeU128
    (observationTransactionPriorityFee transaction) ++
  [writeSuccessEncodeU64 (observationTransactionGasLimit transaction)] ++
  writeSuccessOptionalBytesFragments (observationTransactionTo transaction) ++
  [writeSuccessEncodeU256 (observationTransactionValue transaction)] ++
  writeSuccessBytesFragments (observationTransactionData transaction) ++
  writeSuccessListFragments writeSuccessAccessFragments
    (observationTransactionAccessList transaction) ++
  writeSuccessListFragments (fun bytes => [bytes])
    (observationTransactionBlobHashes transaction) ++
  [writeSuccessEncodeU128 (observationTransactionMaxBlobFee transaction)] ++
  writeSuccessListFragments writeSuccessAuthorizationFragments
    (observationTransactionAuthorizations transaction) ++
  [writeSuccessEncodeU64 (observationTransactionV transaction);
   writeSuccessEncodeU256 (observationTransactionR transaction);
   writeSuccessEncodeU256 (observationTransactionS transaction)].

Definition writeSuccessWithdrawalFragments
    (withdrawal : WriteSuccessWithdrawalObservation) : list ByteString :=
  [writeSuccessEncodeU64 (observationWithdrawalIndex withdrawal);
   writeSuccessEncodeU64 (observationWithdrawalValidatorIndex withdrawal);
   observationWithdrawalAddress withdrawal;
   writeSuccessEncodeU64 (observationWithdrawalAmount withdrawal)].

Definition writeSuccessForkFragments (value : option ByteString) :
    list ByteString :=
  match value with
  | None => [[0]]
  | Some name => [[1]] ++ writeSuccessBytesFragments name
  end.

Definition writeSuccessEncodeFragments
    (observation : WriteSuccessObservation) : list ByteString :=
  [[90; 83; 83; 90; 1; 1];
   observationParentHash observation;
   observationFeeRecipient observation;
   observationStateRoot observation;
   observationReceiptsRoot observation;
   observationLogsBloom observation;
   observationPrevRandao observation;
   writeSuccessEncodeU64 (observationBlockNumber observation);
   writeSuccessEncodeU64 (observationGasLimit observation);
   writeSuccessEncodeU64 (observationGasUsed observation);
   writeSuccessEncodeU64 (observationTimestamp observation)] ++
  writeSuccessBytesFragments (observationExtraData observation) ++
  [writeSuccessEncodeU64 (observationBaseFee observation);
   observationBlockHash observation] ++
  writeSuccessListFragments writeSuccessTransactionFragments
    (observationTransactions observation) ++
  writeSuccessListFragments writeSuccessBytesFragments
    (observationRawTransactions observation) ++
  writeSuccessListFragments writeSuccessWithdrawalFragments
    (observationWithdrawals observation) ++
  [writeSuccessEncodeU64 (observationBlobGasUsed observation);
   writeSuccessEncodeU64 (observationExcessBlobGas observation)] ++
  writeSuccessOptionalFragments writeSuccessEncodeU64
    (observationSlotNumber observation) ++
  writeSuccessBytesFragments (observationBlockAccessList observation) ++
  [observationParentBeaconRoot observation] ++
  writeSuccessListFragments (fun bytes => [bytes])
    (observationVersionedHashes observation) ++
  writeSuccessBytesFragments (observationDeposits observation) ++
  writeSuccessBytesFragments (observationWithdrawalRequests observation) ++
  writeSuccessBytesFragments (observationConsolidations observation) ++
  writeSuccessBytesFragments (observationBuilderDeposits observation) ++
  writeSuccessBytesFragments (observationBuilderExits observation) ++
  writeSuccessListFragments writeSuccessBytesFragments
    (observationWitnessNodes observation) ++
  writeSuccessListFragments writeSuccessBytesFragments
    (observationWitnessCodes observation) ++
  writeSuccessListFragments writeSuccessBytesFragments
    (observationWitnessHeaders observation) ++
  [writeSuccessEncodeU64 (observationChainId observation)] ++
  writeSuccessForkFragments (observationForkName observation) ++
  [writeSuccessEncodeU64 (observationActiveForkIndex observation)] ++
  writeSuccessOptionalFragments writeSuccessEncodeU64
    (observationActivationBlock observation) ++
  writeSuccessOptionalFragments writeSuccessEncodeU64
    (observationActivationTimestamp observation) ++
  writeSuccessListFragments writeSuccessBytesFragments
    (observationPublicKeys observation).

Lemma writeSuccessBytesFragments_concat bytes :
  concat (writeSuccessBytesFragments bytes) = writeSuccessEncodeBytes bytes.
Proof. unfold writeSuccessBytesFragments, writeSuccessEncodeBytes. simpl.
  rewrite app_nil_r. reflexivity. Qed.

Lemma writeSuccessOptionalFragments_concat encode value :
  concat (writeSuccessOptionalFragments encode value) =
    writeSuccessEncodeOptional encode value.
Proof. destruct value; unfold writeSuccessOptionalFragments,
    writeSuccessEncodeOptional; simpl; rewrite ?app_nil_r; reflexivity. Qed.

Lemma writeSuccessOptionalBytesFragments_concat value :
  concat (writeSuccessOptionalBytesFragments value) =
    writeSuccessEncodeOptionalBytes value.
Proof. destruct value; unfold writeSuccessOptionalBytesFragments,
    writeSuccessEncodeOptionalBytes; simpl; rewrite ?app_nil_r; reflexivity. Qed.

Lemma writeSuccessConcatMapFragments {A : Type}
    (encode : A -> ByteString) (fragments : A -> list ByteString)
    (Hfragments : forall item, concat (fragments item) = encode item)
    (items : list A) :
  concat (concat (map fragments items)) = concat (map encode items).
Proof.
  induction items as [|item items IHitems]; simpl; [reflexivity|].
  rewrite concat_app.
  rewrite (Hfragments item). rewrite IHitems. reflexivity.
Qed.

Lemma writeSuccessListFragments_concat {A : Type}
    (encode : A -> ByteString) (fragments : A -> list ByteString)
    (Hfragments : forall item, concat (fragments item) = encode item)
    (items : list A) :
  concat (writeSuccessListFragments fragments items) =
    writeSuccessEncodeList encode items.
Proof.
  unfold writeSuccessListFragments, writeSuccessEncodeList. simpl.
  rewrite (writeSuccessConcatMapFragments encode fragments Hfragments items).
  reflexivity.
Qed.

Lemma writeSuccessAccessFragments_concat entry :
  concat (writeSuccessAccessFragments entry) = writeSuccessEncodeAccessEntry entry.
Proof.
  unfold writeSuccessAccessFragments, writeSuccessEncodeAccessEntry.
  rewrite concat_app.
  rewrite (writeSuccessListFragments_concat (fun bytes => bytes)
    (fun bytes => [bytes])); [|intros; simpl; rewrite app_nil_r; reflexivity].
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma writeSuccessAuthorizationFragments_concat authorization :
  concat (writeSuccessAuthorizationFragments authorization) =
    writeSuccessEncodeAuthorization authorization.
Proof. unfold writeSuccessAuthorizationFragments,
    writeSuccessEncodeAuthorization. simpl. repeat rewrite app_nil_r.
  reflexivity. Qed.

Lemma writeSuccessTransactionFragments_concat transaction :
  concat (writeSuccessTransactionFragments transaction) =
    writeSuccessEncodeTransaction transaction.
Proof.
  unfold writeSuccessTransactionFragments, writeSuccessEncodeTransaction.
  repeat rewrite concat_app.
  rewrite writeSuccessOptionalFragments_concat.
  rewrite writeSuccessOptionalFragments_concat.
  rewrite writeSuccessOptionalBytesFragments_concat.
  rewrite writeSuccessBytesFragments_concat.
  rewrite (writeSuccessListFragments_concat writeSuccessEncodeAccessEntry
    writeSuccessAccessFragments writeSuccessAccessFragments_concat).
  rewrite (writeSuccessListFragments_concat (fun bytes => bytes)
    (fun bytes => [bytes]));
    [|intros; simpl; rewrite app_nil_r; reflexivity].
  rewrite (writeSuccessListFragments_concat writeSuccessEncodeAuthorization
    writeSuccessAuthorizationFragments
    writeSuccessAuthorizationFragments_concat).
  simpl. repeat rewrite app_nil_r. reflexivity.
Qed.

Lemma writeSuccessWithdrawalFragments_concat withdrawal :
  concat (writeSuccessWithdrawalFragments withdrawal) =
    writeSuccessEncodeWithdrawal withdrawal.
Proof. unfold writeSuccessWithdrawalFragments, writeSuccessEncodeWithdrawal.
  simpl. repeat rewrite app_nil_r. reflexivity. Qed.

Lemma writeSuccessForkFragments_concat value :
  concat (writeSuccessForkFragments value) =
    match value with
    | None => [0]
    | Some name => 1 :: writeSuccessEncodeBytes name
    end.
Proof.
  destruct value; unfold writeSuccessForkFragments, writeSuccessBytesFragments,
    writeSuccessEncodeBytes; simpl; rewrite ?app_nil_r; reflexivity.
Qed.

Theorem writeSuccessEncodeFragments_concat observation :
  concat (writeSuccessEncodeFragments observation) =
    writeSuccessEncodeObservation observation.
Proof.
  unfold writeSuccessEncodeFragments, writeSuccessEncodeObservation.
  repeat rewrite concat_app.
  rewrite writeSuccessBytesFragments_concat.
  rewrite (writeSuccessListFragments_concat writeSuccessEncodeTransaction
    writeSuccessTransactionFragments writeSuccessTransactionFragments_concat).
  rewrite (writeSuccessListFragments_concat writeSuccessEncodeBytes
    writeSuccessBytesFragments writeSuccessBytesFragments_concat).
  rewrite (writeSuccessListFragments_concat writeSuccessEncodeWithdrawal
    writeSuccessWithdrawalFragments writeSuccessWithdrawalFragments_concat).
  rewrite writeSuccessOptionalFragments_concat.
  repeat rewrite writeSuccessBytesFragments_concat.
  rewrite (writeSuccessListFragments_concat (fun bytes => bytes)
    (fun bytes => [bytes]));
    [|intros; simpl; rewrite app_nil_r; reflexivity].
  repeat rewrite (writeSuccessListFragments_concat writeSuccessEncodeBytes
    writeSuccessBytesFragments writeSuccessBytesFragments_concat).
  rewrite writeSuccessForkFragments_concat.
  repeat rewrite writeSuccessOptionalFragments_concat.
  cbn [concat].
  repeat rewrite concat_app.
  repeat rewrite app_assoc.
  repeat rewrite app_nil_r. reflexivity.
Qed.

Print Assumptions writeSuccessEncodeFragments_concat.
