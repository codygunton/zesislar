Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncodeFragments.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Import ListNotations.

Definition writeSuccessAllDescriptors
    (sp : bv 64) (values : list (bv 64))
    (transactions : list writeSuccessTransaction)
    (rawTransactions : list ByteListItem) (withdrawalsCount : nat)
    (post : WriteSuccessPostTransactionData) : list WriteOutputDescriptor :=
  writeSuccessMainDescriptors sp values transactions ++
  writeSuccessByteListsDescriptors sp rawTransactions ++
  writeSuccessAfterTransactionsDescriptors sp withdrawalsCount post.

Definition writeSuccessExactObservation
    (decodedBytes : list (bv 8)) (values : list (bv 64))
    (payload : list (bv 8)) (transactions : list writeSuccessTransaction)
    (rawTransactions : list ByteListItem) (withdrawalsBytes : list (bv 8))
    (withdrawalsCount : nat) (post : WriteSuccessPostTransactionData) :
    WriteSuccessObservation :=
  writeSuccessNativeObservation decodedBytes values payload transactions
    rawTransactions withdrawalsBytes withdrawalsCount post.

Definition writeSuccessExactPayloads
    (decodedBytes : list (bv 8)) (values : list (bv 64))
    (payload : list (bv 8)) (transactions : list writeSuccessTransaction)
    (rawTransactions : list ByteListItem) (withdrawalsBytes : list (bv 8))
    (withdrawalsCount : nat) (post : WriteSuccessPostTransactionData) :
    list (list (bv 8)) :=
  map writeSuccessPrivateBytes
    (writeSuccessEncodeFragments
      (writeSuccessExactObservation decodedBytes values payload transactions
        rawTransactions withdrawalsBytes withdrawalsCount post)).

Definition writeSuccessExactEvents
    (sp : bv 64) (decodedBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (transactions : list writeSuccessTransaction)
    (rawTransactions : list ByteListItem) (withdrawalsBytes : list (bv 8))
    (withdrawalsCount : nat) (post : WriteSuccessPostTransactionData)
    (tail : spec) : spec :=
  writeOutputPayloadsSpec
    (writeSuccessAllDescriptors sp values transactions rawTransactions
      withdrawalsCount post)
    (writeSuccessExactPayloads decodedBytes values payload transactions
      rawTransactions withdrawalsBytes withdrawalsCount post)
    tail.

Lemma writeSuccessRepeatedDescriptors_length data size count :
  length (writeSuccessRepeatedDescriptors data size count) = count.
Proof. induction count; simpl; lia. Qed.

Lemma byteListItemDescriptors_length sp items :
  length (byteListItemDescriptors sp items) = (2 * length items)%nat.
Proof. induction items; simpl; lia. Qed.

Lemma writeSuccessByteListsDescriptors_length sp items :
  length (writeSuccessByteListsDescriptors sp items) =
    (1 + 2 * length items)%nat.
Proof. simpl. rewrite byteListItemDescriptors_length. lia. Qed.

Lemma concat_map_constant_length {A B : Type}
    (fragments : A -> list B) (width : nat) (items : list A)
    (Hwidth : forall item, length (fragments item) = width) :
  length (concat (map fragments items)) = (width * length items)%nat.
Proof.
  induction items as [|item items IH]; simpl; [lia|].
  rewrite app_length Hwidth IH. simpl. lia.
Qed.

Lemma writeSuccessListFragments_constant_length {A : Type}
    (fragments : A -> list ByteString) (width : nat) (items : list A)
    (Hwidth : forall item, length (fragments item) = width) :
  length (writeSuccessListFragments fragments items) =
    (1 + width * length items)%nat.
Proof.
  unfold writeSuccessListFragments. simpl.
  rewrite (concat_map_constant_length fragments width items Hwidth). lia.
Qed.

Lemma writeSuccessBytesFragments_length bytes :
  length (writeSuccessBytesFragments bytes) = 2%nat.
Proof. reflexivity. Qed.

Lemma writeSuccessNativeByteListsFragments_length sp items :
  length (writeSuccessListFragments writeSuccessBytesFragments
    (writeSuccessByteListsObservation items)) =
  length (writeSuccessByteListsDescriptors sp items).
Proof.
  rewrite (writeSuccessListFragments_constant_length
    writeSuccessBytesFragments 2%nat);
    [|exact writeSuccessBytesFragments_length].
  rewrite writeSuccessByteListsDescriptors_length.
  rewrite /writeSuccessByteListsObservation map_length. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsItemDescriptors_length sp count :
  length (writeSuccessWithdrawalsItemDescriptors sp count) =
    (4 * count)%nat.
Proof. induction count; simpl; lia. Qed.

Lemma writeSuccessNativeWithdrawalFragments_length sp withdrawalsBytes count :
  length (writeSuccessListFragments writeSuccessWithdrawalFragments
    (map writeSuccessWithdrawalObservationOfBytes
      (map (fun index => take 48 (drop (48 * index) withdrawalsBytes))
        (seq 0 count)))) =
  length (writeSuccessWithdrawalsDescriptors sp count).
Proof.
  rewrite (writeSuccessListFragments_constant_length
    writeSuccessWithdrawalFragments 4%nat).
  2: intros; reflexivity.
  rewrite !map_length seq_length.
  unfold writeSuccessWithdrawalsDescriptors.
  simpl. rewrite writeSuccessWithdrawalsItemDescriptors_length. lia.
Qed.

Lemma writeSuccessStorageKeysDescriptors_length sp count :
  length (writeSuccessStorageKeysDescriptors sp count) = count.
Proof. apply writeSuccessRepeatedDescriptors_length. Qed.

Lemma writeSuccessAccessFragments_native_length entry :
  length (writeSuccessAccessFragments
    (writeSuccessAccessObservation entry)) =
  (2 + writeSuccessAccessEntryStorageCount entry)%nat.
Proof.
  unfold writeSuccessAccessFragments, writeSuccessAccessObservation.
  unfold writeSuccessListFragments. rewrite app_length. simpl.
  rewrite (concat_map_constant_length
    (fun bytes : ByteString => [bytes]) 1%nat).
  2: intros; reflexivity.
  unfold writeSuccessFixedChunks. rewrite map_length seq_length. lia.
Qed.

Lemma writeSuccessAccessListsDescriptors_fragments_length sp entries :
  length (writeSuccessAccessListsDescriptors sp entries) =
  length (concat (map writeSuccessAccessFragments
    (map writeSuccessAccessObservation entries))).
Proof.
  induction entries as [|entry entries IH]; [reflexivity|].
  change (length
    ([((sp + BV 64 1760)%bv, BV 64 20);
       ((sp - BV 64 16)%bv, BV 64 8)] ++
     writeSuccessStorageKeysDescriptors sp
       (writeSuccessAccessEntryStorageCount entry) ++
     writeSuccessAccessListsDescriptors sp entries) =
    length (writeSuccessAccessFragments (writeSuccessAccessObservation entry) ++
      concat (map writeSuccessAccessFragments
        (map writeSuccessAccessObservation entries)))).
  rewrite (app_length
    (writeSuccessAccessFragments (writeSuccessAccessObservation entry))
    (concat (map writeSuccessAccessFragments
      (map writeSuccessAccessObservation entries)))).
  rewrite writeSuccessAccessFragments_native_length.
  rewrite !app_length writeSuccessStorageKeysDescriptors_length IH.
  cbn [length]. lia.
Qed.

Lemma writeSuccessBlobHashesDescriptors_length sp count :
  length (writeSuccessBlobHashesDescriptors sp count) = count.
Proof. apply writeSuccessRepeatedDescriptors_length. Qed.

Lemma writeSuccessAuthorizationsDescriptors_length sp count :
  length (writeSuccessAuthorizationsDescriptors sp count) =
    (6 * count)%nat.
Proof. induction count; simpl; lia. Qed.

Lemma writeSuccessOptionalU64Descriptors_fragments_length sp value :
  length (writeSuccessOptionalU64Descriptors sp value) =
  length (writeSuccessOptionalFragments writeSuccessEncodeU64
    (writeSuccessOptionalWordValue value)).
Proof. destruct value; reflexivity. Qed.

Lemma writeSuccessOptionalU128Descriptors_fragments_length sp value :
  length (writeSuccessOptionalU128Descriptors sp value) =
  length (writeSuccessOptionalFragments writeSuccessEncodeU128
    (writeSuccessOptionalPairValue value)).
Proof. destruct value as [[first second]|]; reflexivity. Qed.

Lemma writeSuccessOptionalAddressDescriptors_fragments_length sp value :
  length (writeSuccessOptionalAddressDescriptors sp value) =
  length (writeSuccessOptionalBytesFragments
    (option_map writeSuccessPublicBytes value)).
Proof. destruct value; reflexivity. Qed.

Lemma writeSuccessTransactionDescriptors_fragments_length sp transaction :
  length (writeSuccessTransactionDescriptors sp transaction) =
  length (writeSuccessTransactionFragments
    (writeSuccessTransactionObservationOfNative transaction)).
Proof.
  unfold writeSuccessTransactionDescriptors,
    writeSuccessTransactionFragments,
    writeSuccessTransactionObservationOfNative.
  repeat rewrite app_length.
  rewrite writeSuccessOptionalU64Descriptors_fragments_length.
  rewrite writeSuccessOptionalU128Descriptors_fragments_length.
  rewrite writeSuccessOptionalAddressDescriptors_fragments_length.
  rewrite writeSuccessAccessListsDescriptors_fragments_length.
  rewrite writeSuccessBlobHashesDescriptors_length.
  rewrite writeSuccessAuthorizationsDescriptors_length.
  rewrite (writeSuccessListFragments_constant_length
    (fun bytes : ByteString => [bytes]) 1%nat).
  2: intros; reflexivity.
  rewrite (writeSuccessListFragments_constant_length
    writeSuccessAuthorizationFragments 6%nat).
  2: intros; reflexivity.
  rewrite !map_length. simpl. lia.
Qed.

Lemma writeSuccessTransactionsDescriptors_fragments_length sp transactions :
  length (writeSuccessTransactionsDescriptors sp transactions) =
  length (concat (map writeSuccessTransactionFragments
    (map writeSuccessTransactionObservationOfNative transactions))).
Proof.
  induction transactions as [|transaction transactions IH];
    [reflexivity|].
  change (length
    (writeSuccessTransactionDescriptors sp transaction ++
      writeSuccessTransactionsDescriptors sp transactions) =
    length (writeSuccessTransactionFragments
      (writeSuccessTransactionObservationOfNative transaction) ++
      concat (map writeSuccessTransactionFragments
        (map writeSuccessTransactionObservationOfNative transactions)))).
  rewrite (app_length (writeSuccessTransactionDescriptors sp transaction)
    (writeSuccessTransactionsDescriptors sp transactions)).
  rewrite writeSuccessTransactionDescriptors_fragments_length.
  rewrite (app_length
    (writeSuccessTransactionFragments
      (writeSuccessTransactionObservationOfNative transaction))
    (concat (map writeSuccessTransactionFragments
      (map writeSuccessTransactionObservationOfNative transactions)))).
  rewrite IH.
  reflexivity.
Qed.

Definition writeSuccessMainFragments
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
    (observationTransactions observation).

Definition writeSuccessRawTransactionFragments
    (observation : WriteSuccessObservation) : list ByteString :=
  writeSuccessListFragments writeSuccessBytesFragments
    (observationRawTransactions observation).

Definition writeSuccessWithdrawalListFragments
    (observation : WriteSuccessObservation) : list ByteString :=
  writeSuccessListFragments writeSuccessWithdrawalFragments
    (observationWithdrawals observation).

Definition writeSuccessPostFragments
    (observation : WriteSuccessObservation) : list ByteString :=
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

Lemma writeSuccessEncodeFragments_groups observation :
  writeSuccessEncodeFragments observation =
    writeSuccessMainFragments observation ++
    writeSuccessRawTransactionFragments observation ++
    writeSuccessWithdrawalListFragments observation ++
    writeSuccessPostFragments observation.
Proof.
  unfold writeSuccessEncodeFragments, writeSuccessMainFragments,
    writeSuccessRawTransactionFragments, writeSuccessWithdrawalListFragments,
    writeSuccessPostFragments.
  repeat rewrite app_assoc. reflexivity.
Qed.

Lemma writeSuccessListFragments_length {A : Type}
    (fragments : A -> list ByteString) items :
  length (writeSuccessListFragments fragments items) =
    (1 + length (concat (map fragments items)))%nat.
Proof. reflexivity. Qed.

Lemma writeSuccessMainDescriptors_fragments_length sp decodedBytes values
    payload transactions rawTransactions withdrawalsBytes withdrawalsCount post :
  length (writeSuccessMainDescriptors sp values transactions) =
  length (writeSuccessMainFragments
    (writeSuccessExactObservation decodedBytes values payload transactions
      rawTransactions withdrawalsBytes withdrawalsCount post)).
Proof.
  pose proof
    (writeSuccessTransactionsDescriptors_fragments_length sp transactions)
    as Htransactions.
  unfold writeSuccessMainDescriptors, writeSuccessMainFragments,
    writeSuccessExactObservation, writeSuccessNativeObservation.
  cbn.
  rewrite Htransactions. reflexivity.
Qed.

Definition writeSuccessPostPayloadShape
    (post : WriteSuccessPostTransactionData) : Prop :=
  match writeSuccessPostConditional1596c post,
      writeSuccessPostConditional1596cPayload post with
  | None, None => True
  | Some _, Some _ => True
  | _, _ => False
  end.

Definition writeSuccessOptionCount {A : Type} (value : option A) : nat :=
  match value with None => 1%nat | Some _ => 2%nat end.

Definition writeSuccessForkCount (value : option ByteString) : nat :=
  match value with None => 1%nat | Some _ => 3%nat end.

Lemma writeSuccessOptionCount_map {A B : Type} (f : A -> B) value :
  writeSuccessOptionCount (option_map f value) = writeSuccessOptionCount value.
Proof. destruct value; reflexivity. Qed.

Lemma writeSuccessOptionalFragments_length
    (encode : Z -> ByteString) value :
  length (writeSuccessOptionalFragments encode value) =
    writeSuccessOptionCount value.
Proof. destruct value; reflexivity. Qed.

Lemma writeSuccessOptionalBytesFragments_length value :
  length (writeSuccessOptionalBytesFragments value) =
    writeSuccessOptionCount value.
Proof. destruct value; reflexivity. Qed.

Lemma writeSuccessForkFragments_length value :
  length (writeSuccessForkFragments value) = writeSuccessForkCount value.
Proof. destruct value; reflexivity. Qed.

Lemma writeSuccessPostFragments_length observation :
  length (writeSuccessPostFragments observation) =
    (2 + writeSuccessOptionCount (observationSlotNumber observation) +
     2 + 1 + (1 + length (observationVersionedHashes observation)) +
     10 + (1 + 2 * length (observationWitnessNodes observation)) +
     (1 + 2 * length (observationWitnessCodes observation)) +
     (1 + 2 * length (observationWitnessHeaders observation)) + 1 +
     writeSuccessForkCount (observationForkName observation) + 1 +
     writeSuccessOptionCount (observationActivationBlock observation) +
     writeSuccessOptionCount (observationActivationTimestamp observation) +
     (1 + 2 * length (observationPublicKeys observation)))%nat.
Proof.
  unfold writeSuccessPostFragments.
  repeat rewrite app_length.
  rewrite !writeSuccessBytesFragments_length.
  rewrite !writeSuccessOptionalFragments_length.
  rewrite writeSuccessForkFragments_length.
  rewrite (writeSuccessListFragments_constant_length
    (fun bytes : ByteString => [bytes]) 1%nat); [|intros; reflexivity].
  rewrite !(@writeSuccessListFragments_constant_length ByteString
    writeSuccessBytesFragments 2%nat _ writeSuccessBytesFragments_length).
  cbn [length]. lia.
Qed.

Lemma writeSuccessOptionalU64Descriptors_length sp value :
  length (writeSuccessOptionalU64Descriptors sp value) =
    writeSuccessOptionCount value.
Proof. destruct value; reflexivity. Qed.

Lemma writeSuccessHashesDescriptors_length sp count :
  length (writeSuccessHashesDescriptors sp count) = (1 + count)%nat.
Proof.
  unfold writeSuccessHashesDescriptors. simpl.
  rewrite writeSuccessRepeatedDescriptors_length. lia.
Qed.

Lemma writeSuccessPostDescriptors_length sp post :
  length (writeSuccessPost156e8Descriptors sp post) =
    (2 + writeSuccessOptionCount (writeSuccessPostOptional15700 post) +
     2 + 1 + (1 + writeSuccessPostHashesCount post) + 10 +
     (1 + 2 * length (writeSuccessPostByteLists15930 post)) +
     (1 + 2 * length (writeSuccessPostByteLists15940 post)) +
     (1 + 2 * length (writeSuccessPostByteLists15950 post)) + 1 +
     (match writeSuccessPostConditional1596c post with
      | None => 1%nat | Some _ => 3%nat end) + 1 +
     writeSuccessOptionCount (writeSuccessPostOptional159b0 post) +
     writeSuccessOptionCount (writeSuccessPostOptional159bc post) +
     (1 + 2 * length (writeSuccessPostByteLists159c8 post)))%nat.
Proof.
  unfold writeSuccessPost156e8Descriptors,
    writeSuccessPost1573cDescriptors, writeSuccessPost158e0Descriptors,
    writeSuccessPost15930Descriptors, writeSuccessPost15960Descriptors,
    writeSuccessPost1596cDescriptors, writeSuccessPost159a0Descriptors,
    writeSuccessPost159b0Descriptors, writeSuccessPost159bcDescriptors,
    writeSuccessPost159c8Descriptors.
  repeat rewrite app_length.
  rewrite writeSuccessHashesDescriptors_length.
  rewrite !writeSuccessByteListsDescriptors_length.
  destruct (writeSuccessPostConditional1596c post);
    destruct (writeSuccessPostOptional15700 post);
    destruct (writeSuccessPostOptional159b0 post);
    destruct (writeSuccessPostOptional159bc post); cbn; lia.
Qed.

Lemma writeSuccessPostDescriptors_fragments_length sp decodedBytes values
    payload transactions rawTransactions withdrawalsBytes withdrawalsCount
    post :
  writeSuccessPostPayloadShape post ->
  length (writeSuccessPost156e8Descriptors sp post) =
  length (writeSuccessPostFragments
    (writeSuccessExactObservation decodedBytes values payload transactions
      rawTransactions withdrawalsBytes withdrawalsCount post)).
Proof.
  intros Hshape.
  rewrite writeSuccessPostDescriptors_length.
  rewrite writeSuccessPostFragments_length.
  unfold writeSuccessExactObservation, writeSuccessNativeObservation.
  cbn.
  unfold writeSuccessByteListsObservation, writeSuccessFixedChunks.
  rewrite !map_length !seq_length.
  rewrite !writeSuccessOptionCount_map.
  unfold writeSuccessPostPayloadShape in Hshape.
  destruct (writeSuccessPostConditional1596c post);
    destruct (writeSuccessPostConditional1596cPayload post);
    try contradiction; cbn; reflexivity.
Qed.

Theorem writeSuccessAllDescriptors_payloads_length sp decodedBytes values
    payload transactions rawTransactions withdrawalsBytes withdrawalsCount
    post :
  writeSuccessPostPayloadShape post ->
  length (writeSuccessAllDescriptors sp values transactions rawTransactions
    withdrawalsCount post) =
  length (writeSuccessExactPayloads decodedBytes values payload transactions
    rawTransactions withdrawalsBytes withdrawalsCount post).
Proof.
  intros Hshape.
  pose proof (writeSuccessMainDescriptors_fragments_length sp decodedBytes
    values payload transactions rawTransactions withdrawalsBytes
    withdrawalsCount post) as Hmain.
  pose proof (writeSuccessNativeByteListsFragments_length sp rawTransactions)
    as Hraw.
  pose proof (writeSuccessNativeWithdrawalFragments_length sp
    withdrawalsBytes withdrawalsCount) as Hwithdrawals.
  pose proof (writeSuccessPostDescriptors_fragments_length sp decodedBytes
    values payload transactions rawTransactions withdrawalsBytes
    withdrawalsCount post Hshape) as Hpost.
  have Hdescriptors :
    length (writeSuccessAllDescriptors sp values transactions rawTransactions
      withdrawalsCount post) =
    (length (writeSuccessMainDescriptors sp values transactions) +
     length (writeSuccessByteListsDescriptors sp rawTransactions) +
     length (writeSuccessWithdrawalsDescriptors sp withdrawalsCount) +
     length (writeSuccessPost156e8Descriptors sp post))%nat.
  { unfold writeSuccessAllDescriptors, writeSuccessAfterTransactionsDescriptors.
    rewrite !app_length. lia. }
  have Hfragments :
    length (writeSuccessExactPayloads decodedBytes values payload transactions
      rawTransactions withdrawalsBytes withdrawalsCount post) =
    (length (writeSuccessMainFragments
       (writeSuccessExactObservation decodedBytes values payload transactions
         rawTransactions withdrawalsBytes withdrawalsCount post)) +
     length (writeSuccessRawTransactionFragments
       (writeSuccessExactObservation decodedBytes values payload transactions
         rawTransactions withdrawalsBytes withdrawalsCount post)) +
     length (writeSuccessWithdrawalListFragments
       (writeSuccessExactObservation decodedBytes values payload transactions
         rawTransactions withdrawalsBytes withdrawalsCount post)) +
     length (writeSuccessPostFragments
       (writeSuccessExactObservation decodedBytes values payload transactions
         rawTransactions withdrawalsBytes withdrawalsCount post)))%nat.
  { unfold writeSuccessExactPayloads. rewrite map_length.
    rewrite writeSuccessEncodeFragments_groups !app_length. lia. }
  unfold writeSuccessRawTransactionFragments,
    writeSuccessWithdrawalListFragments in Hraw, Hwithdrawals.
  rewrite Hdescriptors Hfragments Hmain Hraw Hwithdrawals Hpost. reflexivity.
Qed.

Print Assumptions writeSuccessAllDescriptors_payloads_length.
