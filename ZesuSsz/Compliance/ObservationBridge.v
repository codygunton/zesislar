Require Import ZesuSsz.Automation.All.
From Coq Require Import Lia Lists.List ZArith.ZArith.
From stdpp Require Import base.
Require Import SailStdpp.Values.
Require Import EvmSail.evm_decoder_types.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservationDecoder.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessParserLemmas.

Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Definition observationByte (value : Z) : byte := mword_of_int value.

Definition observationFixedBytes (width : Z) (bytes : ByteString) :
    vec byte width :=
  match vec_of_list width (map observationByte bytes) with
  | Some result => result
  | None => inhabitant
  end.

(** Sail slice records contain offsets into the decoder input.  The output
    observation contains values but no decoder offsets.  This bridge therefore
    maps every value field and leaves reference-only fields at their canonical
    inhabited value. *)
Definition observationToStatelessInput
    (observation : WriteSuccessObservation) : StatelessInput :=
  let header :=
    {| BlockHeader_number :=
         {| block_number_value := observationBlockNumber observation |};
       BlockHeader_timestamp :=
         {| block_timestamp_value := observationTimestamp observation |};
       BlockHeader_gas_limit :=
         {| block_gas_limit_value := observationGasLimit observation |};
       BlockHeader_gas_used :=
         {| block_gas_value := observationGasUsed observation |};
       BlockHeader_prev_randao :=
         {| word_value :=
              writeSuccessDecodeLe (observationPrevRandao observation) |};
       BlockHeader_base_fee :=
         {| word_value := observationBaseFee observation |};
       BlockHeader_blob_gas_used := observationBlobGasUsed observation;
       BlockHeader_excess_blob_gas :=
         {| excess_blob_gas_value := observationExcessBlobGas observation |};
       BlockHeader_state_root :=
         observationFixedBytes 32 (observationStateRoot observation);
       BlockHeader_receipts_root :=
         observationFixedBytes 32 (observationReceiptsRoot observation);
       BlockHeader_logs_bloom := inhabitant;
       BlockHeader_fee_recipient :=
         observationFixedBytes 20 (observationFeeRecipient observation);
       BlockHeader_parent_hash :=
         observationFixedBytes 32 (observationParentHash observation);
       BlockHeader_parent_beacon_block_root :=
         observationFixedBytes 32 (observationParentBeaconRoot observation);
       BlockHeader_slot_number :=
         {| slot_number_value :=
              match observationSlotNumber observation with
              | Some slot => slot
              | None => 0
              end |};
       BlockHeader_extra_data := inhabitant |} in
  {| StatelessInput_payload :=
       {| ExecutionPayload_expected_block_hash :=
            observationFixedBytes 32 (observationBlockHash observation);
          ExecutionPayload_block :=
            {| Block_header := header;
               Block_body :=
                 {| BlockBody_transactions := inhabitant;
                    BlockBody_withdrawals := inhabitant;
                    BlockBody_block_access_list := inhabitant |} |} |};
     StatelessInput_chain_config :=
       {| ChainConfig_chain_id :=
            {| chain_identifier_value := observationChainId observation |} |} |}.

Lemma writeSuccessConcatMapAtLeastOne {A : Type}
    (encode : A -> ByteString) (items : list A) :
  (forall item, In item items -> (1 <= length (encode item))%nat) ->
  (length items <= length (concat (map encode items)))%nat.
Proof.
  intros Hitems. induction items as [|item items IH]; simpl; [lia |].
  rewrite app_length.
  specialize (IH ltac:(intros next Hnext; apply Hitems; right; exact Hnext)).
  specialize (Hitems item ltac:(left; reflexivity)). lia.
Qed.

Lemma writeSuccessParseU8RoundTrip value tail :
  writeSuccessUnsignedValid 1 value ->
  writeSuccessParseInteger 1 (writeSuccessEncodeU8 value ++ tail) =
    Some (value, tail).
Proof. apply writeSuccessParseIntegerRoundTrip. Qed.

Lemma writeSuccessParseU64RoundTrip value tail :
  writeSuccessUnsignedValid 8 value ->
  writeSuccessParseInteger 8 (writeSuccessEncodeU64 value ++ tail) =
    Some (value, tail).
Proof. apply writeSuccessParseIntegerRoundTrip. Qed.

Lemma writeSuccessParseU128RoundTrip value tail :
  writeSuccessUnsignedValid 16 value ->
  writeSuccessParseInteger 16 (writeSuccessEncodeU128 value ++ tail) =
    Some (value, tail).
Proof. apply writeSuccessParseIntegerRoundTrip. Qed.

Lemma writeSuccessParseU256RoundTrip value tail :
  writeSuccessUnsignedValid 32 value ->
  writeSuccessParseInteger 32 (writeSuccessEncodeU256 value ++ tail) =
    Some (value, tail).
Proof. apply writeSuccessParseIntegerRoundTrip. Qed.

Lemma writeSuccessParseItemsValidRoundTrip {A : Type}
    (valid : A -> Prop) (parse : WriteSuccessParser A)
    (encode : A -> ByteString) :
  (forall item tail, valid item ->
     parse (encode item ++ tail) = Some (item, tail)) ->
  forall items tail,
    Forall valid items ->
    writeSuccessParseItems parse (length items)
      (concat (map encode items) ++ tail) = Some (items, tail).
Proof.
  intros Hitem items. induction items as [|item items IH]; intros tail Hvalid;
    inversion Hvalid; subst; simpl; [reflexivity |].
  rewrite <- app_assoc, Hitem by assumption.
  cbn [writeSuccessParserBind]. rewrite IH by assumption. reflexivity.
Qed.

Lemma writeSuccessParseListValidRoundTrip {A : Type}
    (valid : A -> Prop) (parse : WriteSuccessParser A)
    (encode : A -> ByteString) :
  (forall item tail, valid item ->
     parse (encode item ++ tail) = Some (item, tail)) ->
  forall items tail,
    writeSuccessListValid valid items ->
    (length items <= length (concat (map encode items)))%nat ->
    writeSuccessParseList parse
      (writeSuccessEncodeList encode items ++ tail) = Some (items, tail).
Proof.
  intros Hitem items tail [Hlength Hvalid] Hsize.
  unfold writeSuccessEncodeList, writeSuccessParseList.
  rewrite <- app_assoc, writeSuccessParseIntegerRoundTrip.
  2: { unfold writeSuccessUnsignedValid. cbn. split; [lia | exact Hlength]. }
  cbn [writeSuccessParserBind].
  assert (Hfits : (Z.of_nat (length items) <=?
      Z.of_nat (length (concat (map encode items) ++ tail))) = true).
  { apply Z.leb_le. rewrite app_length. lia. }
  rewrite Hfits, Nat2Z.id.
  apply (writeSuccessParseItemsValidRoundTrip valid parse encode); assumption.
Qed.

Lemma writeSuccessParseAccessEntryRoundTrip entry tail :
  writeSuccessAccessEntryValid entry ->
  writeSuccessParseAccessEntry (writeSuccessEncodeAccessEntry entry ++ tail) =
    Some (entry, tail).
Proof.
  destruct entry as [address keys]. simpl.
  intros [[HaddressLength HaddressBytes] [HkeysLength Hkeys]].
  unfold writeSuccessParseAccessEntry, writeSuccessEncodeAccessEntry.
  rewrite <- !app_assoc.
  rewrite writeSuccessParseFixedApp.
  2: exact HaddressLength.
  2: exact HaddressBytes.
  cbn [writeSuccessParserBind].
  rewrite (writeSuccessParseListValidRoundTrip
    (writeSuccessBytesValid 32) (writeSuccessParseFixed 32)
    (fun bytes => bytes)).
  - reflexivity.
  - intros key rest [HkeyLength HkeyBytes].
    apply writeSuccessParseFixedApp; assumption.
  - split; assumption.
  - apply writeSuccessConcatMapAtLeastOne. intros key Hkey.
    pose proof (proj1 (Forall_forall (writeSuccessBytesValid 32) keys)
      Hkeys key Hkey) as [HkeyLength _]. lia.
Qed.

Lemma writeSuccessParseAuthorizationRoundTrip authorization tail :
  writeSuccessAuthorizationValid authorization ->
  writeSuccessParseAuthorization
    (writeSuccessEncodeAuthorization authorization ++ tail) =
    Some (authorization, tail).
Proof.
  destruct authorization as [chainId address nonce v r s]. simpl.
  intros (HchainId & [HaddressLength HaddressBytes] & Hnonce & Hv & Hr & Hs).
  unfold writeSuccessParseAuthorization, writeSuccessEncodeAuthorization.
  rewrite <- app_assoc.
  rewrite writeSuccessParseU256RoundTrip by exact HchainId.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseFixedApp.
  2: exact HaddressLength.
  2: exact HaddressBytes.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by exact Hnonce.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by exact Hv.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU256RoundTrip by exact Hr.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU256RoundTrip by exact Hs.
  reflexivity.
Qed.

Lemma writeSuccessParseWithdrawalRoundTrip withdrawal tail :
  writeSuccessWithdrawalObservationValid withdrawal ->
  writeSuccessParseWithdrawal
    (writeSuccessEncodeWithdrawal withdrawal ++ tail) =
    Some (withdrawal, tail).
Proof.
  destruct withdrawal as [index validator address amount]. simpl.
  intros (Hindex & Hvalidator & [HaddressLength HaddressBytes] & Hamount).
  unfold writeSuccessParseWithdrawal, writeSuccessEncodeWithdrawal.
  rewrite <- app_assoc.
  rewrite writeSuccessParseU64RoundTrip by exact Hindex.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by exact Hvalidator.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseFixedApp.
  2: exact HaddressLength.
  2: exact HaddressBytes.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by exact Hamount.
  reflexivity.
Qed.

Lemma writeSuccessParseOptionalIntegerRoundTrip width value tail :
  writeSuccessOptionValid (writeSuccessUnsignedValid width) value ->
  writeSuccessParseOptionalInteger width
    (writeSuccessEncodeOptional (writeSuccessEncodeLe width) value ++ tail) =
    Some (value, tail).
Proof.
  destruct value as [value |]; simpl.
  - apply writeSuccessParseOptionalIntegerSome.
  - intros _. apply writeSuccessParseOptionalIntegerNone.
Qed.

Lemma writeSuccessParseOptionalU64RoundTrip value tail :
  writeSuccessOptionValid (writeSuccessUnsignedValid 8) value ->
  writeSuccessParseOptionalInteger 8
    (writeSuccessEncodeOptional writeSuccessEncodeU64 value ++ tail) =
    Some (value, tail).
Proof.
  change (writeSuccessOptionValid (writeSuccessUnsignedValid 8) value ->
    writeSuccessParseOptionalInteger 8
      (writeSuccessEncodeOptional (writeSuccessEncodeLe 8) value ++ tail) =
    Some (value, tail)).
  apply writeSuccessParseOptionalIntegerRoundTrip.
Qed.

Lemma writeSuccessParseOptionalU128RoundTrip value tail :
  writeSuccessOptionValid (writeSuccessUnsignedValid 16) value ->
  writeSuccessParseOptionalInteger 16
    (writeSuccessEncodeOptional writeSuccessEncodeU128 value ++ tail) =
    Some (value, tail).
Proof.
  change (writeSuccessOptionValid (writeSuccessUnsignedValid 16) value ->
    writeSuccessParseOptionalInteger 16
      (writeSuccessEncodeOptional (writeSuccessEncodeLe 16) value ++ tail) =
    Some (value, tail)).
  apply writeSuccessParseOptionalIntegerRoundTrip.
Qed.

Lemma writeSuccessParseOptionalFixedRoundTrip width value tail :
  writeSuccessOptionalBytesValid width value ->
  writeSuccessParseOptionalFixed width
    (writeSuccessEncodeOptionalBytes value ++ tail) = Some (value, tail).
Proof.
  destruct value as [value |]; simpl.
  - apply writeSuccessParseOptionalFixedSome.
  - intros _. apply writeSuccessParseOptionalFixedNone.
Qed.

Lemma writeSuccessParseOptionalBytesRoundTrip value tail :
  (match value with
   | Some bytes => writeSuccessVariableBytesValid bytes
   | None => True
   end) ->
  writeSuccessParseOptionalBytes
    ((match value with
      | Some bytes => 1 :: writeSuccessEncodeBytes bytes
      | None => [0]
      end) ++ tail) = Some (value, tail).
Proof.
  destruct value as [value |]; simpl.
  - apply writeSuccessParseOptionalBytesSome.
  - intros _. apply writeSuccessParseOptionalBytesNone.
Qed.

Lemma writeSuccessParseFixedListRoundTrip width items tail :
  (0 < width)%nat ->
  writeSuccessListValid (writeSuccessBytesValid width) items ->
  writeSuccessParseList (writeSuccessParseFixed width)
    (writeSuccessEncodeList (fun bytes => bytes) items ++ tail) =
    Some (items, tail).
Proof.
  intros Hwidth Hvalid.
  apply (writeSuccessParseListValidRoundTrip
    (writeSuccessBytesValid width) (writeSuccessParseFixed width)
    (fun bytes => bytes)).
  - intros item rest [Hlength Hbytes].
    apply writeSuccessParseFixedApp; assumption.
  - exact Hvalid.
  - apply writeSuccessConcatMapAtLeastOne. intros item Hitem.
    destruct Hvalid as [_ Hitems].
    pose proof (proj1 (Forall_forall (writeSuccessBytesValid width) items)
      Hitems item Hitem) as [HitemLength _]. lia.
Qed.

Lemma writeSuccessParseBytesListRoundTrip items tail :
  writeSuccessListValid writeSuccessVariableBytesValid items ->
  writeSuccessParseList writeSuccessParseBytes
    (writeSuccessEncodeList writeSuccessEncodeBytes items ++ tail) =
    Some (items, tail).
Proof.
  intros Hvalid. apply (writeSuccessParseListValidRoundTrip
    writeSuccessVariableBytesValid writeSuccessParseBytes
    writeSuccessEncodeBytes).
  - intros item rest Hitem. apply writeSuccessParseBytesRoundTrip. exact Hitem.
  - exact Hvalid.
  - apply writeSuccessConcatMapAtLeastOne. intros item Hitem.
    unfold writeSuccessEncodeBytes. rewrite app_length.
    rewrite writeSuccessEncodeLeLength. lia.
Qed.

Lemma writeSuccessParseAccessListRoundTrip items tail :
  writeSuccessListValid writeSuccessAccessEntryValid items ->
  writeSuccessParseList writeSuccessParseAccessEntry
    (writeSuccessEncodeList writeSuccessEncodeAccessEntry items ++ tail) =
    Some (items, tail).
Proof.
  intros Hvalid. apply (writeSuccessParseListValidRoundTrip
    writeSuccessAccessEntryValid writeSuccessParseAccessEntry
    writeSuccessEncodeAccessEntry).
  - intros item rest Hitem. apply writeSuccessParseAccessEntryRoundTrip. exact Hitem.
  - exact Hvalid.
  - apply writeSuccessConcatMapAtLeastOne. intros [address keys] Hitem.
    destruct Hvalid as [_ Hitems].
    pose proof (proj1 (Forall_forall writeSuccessAccessEntryValid items)
      Hitems {| observationAccessAddress := address;
                observationStorageKeys := keys |} Hitem) as Hentry.
    simpl in Hentry. destruct Hentry as [[HaddressLength _] _].
    unfold writeSuccessEncodeAccessEntry. simpl.
    rewrite app_length, HaddressLength. lia.
Qed.

Lemma writeSuccessParseAuthorizationListRoundTrip items tail :
  writeSuccessListValid writeSuccessAuthorizationValid items ->
  writeSuccessParseList writeSuccessParseAuthorization
    (writeSuccessEncodeList writeSuccessEncodeAuthorization items ++ tail) =
    Some (items, tail).
Proof.
  intros Hvalid. apply (writeSuccessParseListValidRoundTrip
    writeSuccessAuthorizationValid writeSuccessParseAuthorization
    writeSuccessEncodeAuthorization).
  - intros item rest Hitem. apply writeSuccessParseAuthorizationRoundTrip. exact Hitem.
  - exact Hvalid.
  - apply writeSuccessConcatMapAtLeastOne. intros item Hitem.
    unfold writeSuccessEncodeAuthorization. rewrite !app_length.
    rewrite !writeSuccessEncodeLeLength. lia.
Qed.

Local Opaque writeSuccessEncodeU8 writeSuccessEncodeU64.
Local Opaque writeSuccessEncodeU128 writeSuccessEncodeU256.
Local Opaque writeSuccessEncodeBytes writeSuccessEncodeList.
Local Opaque writeSuccessEncodeAccessEntry writeSuccessEncodeAuthorization.

Lemma writeSuccessParseTransactionRoundTrip transaction tail :
  writeSuccessTransactionObservationValid transaction ->
  writeSuccessParseTransaction
    (writeSuccessEncodeTransaction transaction ++ tail) =
    Some (transaction, tail).
Proof.
  destruct transaction as
    [transactionType chainId nonce gasPrice priorityFee gasLimit to value data
     accessList blobHashes maxBlobFee authorizations v r s].
  simpl.
  intros (Htype & Hchain & Hnonce & HgasPrice & Hpriority & HgasLimit & Hto &
          Hvalue & Hdata & Haccess & Hblobs & HmaxBlob & Hauthorizations &
          Hv & Hr & Hs).
  unfold writeSuccessParseTransaction, writeSuccessEncodeTransaction.
  rewrite <- !app_assoc.
  rewrite writeSuccessParseU8RoundTrip by exact Htype.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseOptionalU64RoundTrip by exact Hchain.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by exact Hnonce.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU128RoundTrip by exact HgasPrice.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseOptionalU128RoundTrip by exact Hpriority.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by exact HgasLimit.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseOptionalFixedRoundTrip by exact Hto.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU256RoundTrip by exact Hvalue.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesRoundTrip by exact Hdata.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseAccessListRoundTrip by exact Haccess.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseFixedListRoundTrip by (assumption || lia).
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU128RoundTrip by exact HmaxBlob.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseAuthorizationListRoundTrip by exact Hauthorizations.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by exact Hv.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU256RoundTrip by exact Hr.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU256RoundTrip by exact Hs.
  reflexivity.
Qed.

Local Transparent writeSuccessEncodeU8 writeSuccessEncodeU64.

Lemma writeSuccessParseTransactionListRoundTrip items tail :
  writeSuccessListValid writeSuccessTransactionObservationValid items ->
  writeSuccessParseList writeSuccessParseTransaction
    (writeSuccessEncodeList writeSuccessEncodeTransaction items ++ tail) =
    Some (items, tail).
Proof.
  intros Hvalid. apply (writeSuccessParseListValidRoundTrip
    writeSuccessTransactionObservationValid writeSuccessParseTransaction
    writeSuccessEncodeTransaction).
  - intros item rest Hitem. apply writeSuccessParseTransactionRoundTrip. exact Hitem.
  - exact Hvalid.
  - apply writeSuccessConcatMapAtLeastOne. intros item Hitem.
    unfold writeSuccessEncodeTransaction. rewrite app_length.
    unfold writeSuccessEncodeU8. rewrite writeSuccessEncodeLeLength. lia.
Qed.

Lemma writeSuccessParseWithdrawalListRoundTrip items tail :
  writeSuccessListValid writeSuccessWithdrawalObservationValid items ->
  writeSuccessParseList writeSuccessParseWithdrawal
    (writeSuccessEncodeList writeSuccessEncodeWithdrawal items ++ tail) =
    Some (items, tail).
Proof.
  intros Hvalid. apply (writeSuccessParseListValidRoundTrip
    writeSuccessWithdrawalObservationValid writeSuccessParseWithdrawal
    writeSuccessEncodeWithdrawal).
  - intros item rest Hitem. apply writeSuccessParseWithdrawalRoundTrip. exact Hitem.
  - exact Hvalid.
  - apply writeSuccessConcatMapAtLeastOne. intros item Hitem.
    unfold writeSuccessEncodeWithdrawal. rewrite app_length.
    unfold writeSuccessEncodeU64. rewrite writeSuccessEncodeLeLength. lia.
Qed.

Local Opaque writeSuccessEncodeU8 writeSuccessEncodeU64.
Local Opaque writeSuccessEncodeTransaction writeSuccessEncodeWithdrawal.

Lemma writeSuccessParseMagic tail :
  writeSuccessParseFixed 6 ([90; 83; 83; 90; 1; 1] ++ tail) =
    Some ([90; 83; 83; 90; 1; 1], tail).
Proof.
  apply writeSuccessParseFixedApp.
  - reflexivity.
  - repeat constructor; unfold writeSuccessByte; lia.
Qed.

Lemma writeSuccessParseObservationRoundTrip observation tail :
  writeSuccessObservationValid observation ->
  writeSuccessParseObservation
    (writeSuccessEncodeObservation observation ++ tail) =
    Some (observation, tail).
Proof.
  destruct observation as
    [parentHash feeRecipient stateRoot receiptsRoot logsBloom prevRandao
     blockNumber gasLimit gasUsed timestamp extraData baseFee blockHash
     transactions rawTransactions withdrawals blobGasUsed excessBlobGas
     slotNumber blockAccessList parentBeaconRoot versionedHashes deposits
     withdrawalRequests consolidations builderDeposits builderExits witnessNodes
     witnessCodes witnessHeaders chainId forkName activeForkIndex activationBlock
     activationTimestamp publicKeys].
  cbn. intros Hvalid. unfold writeSuccessObservationValid in Hvalid. cbn in Hvalid.
  repeat match type of Hvalid with
  | _ /\ _ => destruct Hvalid as [? Hvalid]
  end.
  repeat match goal with
  | H : writeSuccessBytesValid _ _ |- _ => destruct H
  end.
  unfold writeSuccessParseObservation, writeSuccessEncodeObservation.
  rewrite <- !app_assoc.
  rewrite writeSuccessParseMagic. cbn [writeSuccessParserBind].
  rewrite writeSuccessParseFixedApp by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseFixedApp by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseFixedApp by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseFixedApp by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseFixedApp by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseFixedApp by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseFixedApp by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseTransactionListRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesListRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseWithdrawalListRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseOptionalU64RoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseFixedApp by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseFixedListRoundTrip by (assumption || lia).
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesListRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesListRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesListRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseOptionalBytesRoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseU64RoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseOptionalU64RoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseOptionalU64RoundTrip by assumption.
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesListRoundTrip by assumption.
  reflexivity.
Qed.

Theorem writeSuccessObservationDecodeEncode observation :
  writeSuccessObservationValid observation ->
  writeSuccessDecodeObservation (writeSuccessEncodeObservation observation) =
    Some observation.
Proof.
  intros Hvalid. unfold writeSuccessDecodeObservation.
  pose proof (writeSuccessParseObservationRoundTrip observation [] Hvalid) as Hparse.
  rewrite app_nil_r in Hparse. rewrite Hparse.
  reflexivity.
Qed.

Print Assumptions writeSuccessObservationDecodeEncode.
