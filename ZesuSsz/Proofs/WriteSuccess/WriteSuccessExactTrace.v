Require Import ZesuSsz.Automation.All.
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

Lemma writeSuccessNativeByteListsFragments_length items :
  length (writeSuccessListFragments writeSuccessBytesFragments
    (writeSuccessByteListsObservation items)) =
  length (writeSuccessByteListsDescriptors (BV 64 0) items).
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

Lemma writeSuccessNativeWithdrawalFragments_length withdrawalsBytes count :
  length (writeSuccessListFragments writeSuccessWithdrawalFragments
    (map writeSuccessWithdrawalObservationOfBytes
      (map (fun index => take 48 (drop (48 * index) withdrawalsBytes))
        (seq 0 count)))) =
  length (writeSuccessWithdrawalsDescriptors (BV 64 0) count).
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
