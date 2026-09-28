Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List.
Require Import ZesuSsz.Contracts.Endpoints.
Open Scope Z_scope.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsPayloadJunction.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTrace WriteSuccessRepresentation WriteSuccessObservation
  WriteSuccessEncodeFragments WriteSuccessOutputSemantic WriteSuccessOutputDescriptors
  WriteSuccessPostTransactionDescriptors WriteSuccessByteLists WriteSuccessHashesLoop
  WriteSuccessExactByteListsModel WriteSuccessPrivatePublicBytes.
Import ListNotations.

Definition tailFieldsBeforeDescriptors (sp : bv 64)
    (post : WriteSuccessPostTransactionData) : list WriteOutputDescriptor :=
  [((sp - BV 64 16)%bv, BV 64 8)] ++
  [((sp - BV 64 16)%bv, BV 64 8)] ++
  writeSuccessOptionalU64Descriptors sp (writeSuccessPostOptional15700 post) ++
  writeSuccessBytesDescriptors sp (writeSuccessPostBytes1571c post).1
    (writeSuccessPostBytes1571c post).2 ++
  [((sp + BV 64 1000)%bv, BV 64 32)] ++
  writeSuccessHashesDescriptors sp (writeSuccessPostHashesCount post).

Definition tailFieldsBeforeFragments (observation : WriteSuccessObservation) :
    list ByteString :=
  [writeSuccessEncodeU64 (observationBlobGasUsed observation);
   writeSuccessEncodeU64 (observationExcessBlobGas observation)] ++
  writeSuccessOptionalFragments writeSuccessEncodeU64
    (observationSlotNumber observation) ++
  writeSuccessBytesFragments (observationBlockAccessList observation) ++
  [observationParentBeaconRoot observation] ++
  writeSuccessListFragments (fun bytes => [bytes])
    (observationVersionedHashes observation).

Definition tailFieldsFromFragments (observation : WriteSuccessObservation) :
    list ByteString :=
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

Lemma tail_fields_before_descriptors sp post :
  writeSuccessPost156e8Descriptors sp post =
  tailFieldsBeforeDescriptors sp post ++ writeSuccessPost158e0Descriptors sp post.
Proof.
  rewrite /writeSuccessPost156e8Descriptors /writeSuccessPost1573cDescriptors /tailFieldsBeforeDescriptors.
  rewrite !app_assoc; reflexivity.
Qed.

Lemma tail_fields_before_fragments observation :
  writeSuccessPostFragments observation =
  tailFieldsBeforeFragments observation ++ tailFieldsFromFragments observation.
Proof.
  rewrite /writeSuccessPostFragments /tailFieldsBeforeFragments /tailFieldsFromFragments.
  rewrite !app_assoc; reflexivity.
Qed.

Lemma tail_fields_before_length {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  let observation := writeSuccessExactObservation
    (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
    (writeSuccessPayload witness) (writeSuccessTransactions witness)
    (writeSuccessRawTransactions witness) (writeSuccessWithdrawalsBytes witness)
    (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness) in
  length (tailFieldsBeforeDescriptors (writeSuccessFrameSp witness)
    (writeSuccessPostData witness)) = length (tailFieldsBeforeFragments observation).
Proof.
  cbn zeta; rewrite /tailFieldsBeforeDescriptors /tailFieldsBeforeFragments !length_app.
  rewrite writeSuccessHashesDescriptors_length !writeSuccessBytesFragments_length writeSuccessOptionalFragments_length.
  rewrite (writeSuccessListFragments_constant_length (fun bytes : ByteString => [bytes]) 1 _ ltac:(intros; reflexivity)).
  rewrite /writeSuccessExactObservation /writeSuccessNativeObservation /writeSuccessOptionalWordValue /writeSuccessFixedChunks /= !map_length seq_length; destruct (writeSuccessPostOptional15700 (writeSuccessPostData witness)); rewrite /writeSuccessOptionalU64Descriptors /writeSuccessOptionCount /=; lia.
Qed.

Lemma tail_fields_witness_payload_suffix {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  let observation := writeSuccessExactObservation
    (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
    (writeSuccessPayload witness) (writeSuccessTransactions witness)
    (writeSuccessRawTransactions witness) (writeSuccessWithdrawalsBytes witness)
    (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness) in
  writeSuccessExactPostPayloadsAt
    (writeSuccessPost158e0Descriptors (writeSuccessFrameSp witness)
      (writeSuccessPostData witness)) witness =
  map writeSuccessPrivateBytes (tailFieldsFromFragments observation).
Proof.
  cbn zeta; rewrite /writeSuccessExactPostPayloadsAt exact_post_withdrawals_payloads tail_fields_before_descriptors length_app Nat.add_sub tail_fields_before_fragments map_app.
  rewrite (tail_fields_before_length witness) -(map_length writeSuccessPrivateBytes) drop_app_length.
  reflexivity.
Qed.
Print Assumptions tail_fields_witness_payload_suffix.

Definition tailFieldsFirstFragments (observation : WriteSuccessObservation) : list ByteString :=
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
  [writeSuccessEncodeU64 (observationChainId observation)].

Definition tailFieldsAfterFragments (observation : WriteSuccessObservation) : list ByteString :=
  writeSuccessForkFragments (observationForkName observation) ++
  [writeSuccessEncodeU64 (observationActiveForkIndex observation)] ++
  writeSuccessOptionalFragments writeSuccessEncodeU64
    (observationActivationBlock observation) ++
  writeSuccessOptionalFragments writeSuccessEncodeU64
    (observationActivationTimestamp observation) ++
  writeSuccessListFragments writeSuccessBytesFragments
    (observationPublicKeys observation).

Definition tailFieldsFirstDescriptors (sp : bv 64)
    (post : WriteSuccessPostTransactionData) : list WriteOutputDescriptor :=
  writeSuccessBytesDescriptors sp (writeSuccessPostBytes158e0 post).1 (writeSuccessPostBytes158e0 post).2 ++
  writeSuccessBytesDescriptors sp (writeSuccessPostBytes158f0 post).1 (writeSuccessPostBytes158f0 post).2 ++
  writeSuccessBytesDescriptors sp (writeSuccessPostBytes15900 post).1 (writeSuccessPostBytes15900 post).2 ++
  writeSuccessBytesDescriptors sp (writeSuccessPostBytes15910 post).1 (writeSuccessPostBytes15910 post).2 ++
  writeSuccessBytesDescriptors sp (writeSuccessPostBytes15920 post).1 (writeSuccessPostBytes15920 post).2 ++
  writeSuccessByteListsDescriptors sp (writeSuccessPostByteLists15930 post) ++
  writeSuccessByteListsDescriptors sp (writeSuccessPostByteLists15940 post) ++
  writeSuccessByteListsDescriptors sp (writeSuccessPostByteLists15950 post) ++
  [((sp - BV 64 16)%bv, BV 64 8)].

Lemma tail_fields_first_descriptors sp post :
  writeSuccessPost158e0Descriptors sp post =
  tailFieldsFirstDescriptors sp post ++ writeSuccessPost1596cDescriptors sp post.
Proof.
  rewrite /writeSuccessPost158e0Descriptors /writeSuccessPost15930Descriptors /writeSuccessPost15960Descriptors /tailFieldsFirstDescriptors.
  rewrite !app_assoc; reflexivity.
Qed.

Lemma tail_fields_first_fragments observation :
  tailFieldsFromFragments observation =
  tailFieldsFirstFragments observation ++ tailFieldsAfterFragments observation.
Proof.
  rewrite /tailFieldsFromFragments /tailFieldsFirstFragments /tailFieldsAfterFragments.
  rewrite !app_assoc; reflexivity.
Qed.

Lemma tail_fields_bytes_call_model sp descriptor payload tail :
  bv_unsigned descriptor.2 = Z.of_nat (length payload) ->
  writeOutputPayloadsSpec
    (writeSuccessBytesDescriptors sp descriptor.1 descriptor.2)
    (map writeSuccessPrivateBytes (writeSuccessBytesFragments (writeSuccessPublicBytes payload))) tail =
  tailFieldsBytesCallEvents sp descriptor payload tail.
Proof.
  intros Hsize; rewrite /writeSuccessBytesDescriptors /writeSuccessBytesFragments /tailFieldsBytesCallEvents /=.
  rewrite writeSuccessPrivatePublicBytes /writeSuccessPublicBytes map_length -Hsize; reflexivity.
Qed.

Lemma tail_fields_first_length {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  let observation := writeSuccessExactObservation
    (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
    (writeSuccessPayload witness) (writeSuccessTransactions witness)
    (writeSuccessRawTransactions witness) (writeSuccessWithdrawalsBytes witness)
    (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness) in
  length (tailFieldsFirstDescriptors (writeSuccessFrameSp witness)
    (writeSuccessPostData witness)) = length (tailFieldsFirstFragments observation).
Proof.
  cbn zeta; rewrite /tailFieldsFirstDescriptors /tailFieldsFirstFragments !length_app !writeSuccessBytesFragments_length.
  rewrite !(writeSuccessNativeByteListsFragments_length (writeSuccessFrameSp witness)).
  rewrite /writeSuccessBytesDescriptors /=; reflexivity.
Qed.

Lemma tail_fields_witness_after_payloads {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  let observation := writeSuccessExactObservation
    (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
    (writeSuccessPayload witness) (writeSuccessTransactions witness)
    (writeSuccessRawTransactions witness) (writeSuccessWithdrawalsBytes witness)
    (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness) in
  writeSuccessExactPostPayloadsAt
    (writeSuccessPost1596cDescriptors (writeSuccessFrameSp witness)
      (writeSuccessPostData witness)) witness =
  map writeSuccessPrivateBytes (tailFieldsAfterFragments observation).
Proof.
  cbn zeta; have Hindex : (length (writeSuccessPost156e8Descriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness)) - length (writeSuccessPost1596cDescriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness)))%nat = (length (tailFieldsBeforeDescriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness)) + length (tailFieldsFirstDescriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness)))%nat by rewrite tail_fields_before_descriptors tail_fields_first_descriptors !length_app; lia.
  set (observation := writeSuccessExactObservation (writeSuccessDecodedBytes witness) (writeSuccessValues witness) (writeSuccessPayload witness) (writeSuccessTransactions witness) (writeSuccessRawTransactions witness) (writeSuccessWithdrawalsBytes witness) (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness)).
  rewrite /writeSuccessExactPostPayloadsAt Hindex exact_post_withdrawals_payloads tail_fields_before_fragments tail_fields_first_fragments (map_app writeSuccessPrivateBytes (tailFieldsBeforeFragments observation)) (map_app writeSuccessPrivateBytes (tailFieldsFirstFragments observation)).
  rewrite -drop_drop (tail_fields_before_length witness) -(map_length writeSuccessPrivateBytes) drop_app_length.
  rewrite (tail_fields_first_length witness) -(map_length writeSuccessPrivateBytes) drop_app_length; reflexivity.
Qed.

Definition tailFieldsPayloadSizeFacts (post : WriteSuccessPostTransactionData) : Prop :=
  bv_unsigned (writeSuccessPostBytes158e0 post).2 = length (writeSuccessPostBytes158e0Payload post) /\
  bv_unsigned (writeSuccessPostBytes158f0 post).2 = length (writeSuccessPostBytes158f0Payload post) /\
  bv_unsigned (writeSuccessPostBytes15900 post).2 = length (writeSuccessPostBytes15900Payload post) /\
  bv_unsigned (writeSuccessPostBytes15910 post).2 = length (writeSuccessPostBytes15910Payload post) /\
  bv_unsigned (writeSuccessPostBytes15920 post).2 = length (writeSuccessPostBytes15920Payload post) /\
  Forall (fun item => bv_unsigned (byteListSize item) = Z.of_nat (length (byteListBytes item))) (writeSuccessPostByteLists15930 post) /\
  Forall (fun item => bv_unsigned (byteListSize item) = Z.of_nat (length (byteListBytes item))) (writeSuccessPostByteLists15940 post) /\
  Forall (fun item => bv_unsigned (byteListSize item) = Z.of_nat (length (byteListBytes item))) (writeSuccessPostByteLists15950 post).

Lemma tail_fields_first_trace_model {Decoded}
    (witness : writeSuccessNativeWitness Decoded) (tail : spec) :
  tailFieldsPayloadSizeFacts (writeSuccessPostData witness) ->
  let observation := writeSuccessExactObservation
    (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
    (writeSuccessPayload witness) (writeSuccessTransactions witness)
    (writeSuccessRawTransactions witness) (writeSuccessWithdrawalsBytes witness)
    (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness) in
  writeOutputPayloadsSpec
    (tailFieldsFirstDescriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness))
    (map writeSuccessPrivateBytes (tailFieldsFirstFragments observation)) tail =
  tailFieldsFirstSegmentEvents (writeSuccessFrameSp witness)
    (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) tail.
Proof.
  intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7); cbn zeta.
  rewrite /tailFieldsFirstDescriptors /tailFieldsFirstFragments !map_app.
  rewrite !writeOutputPayloadsSpec_app; try reflexivity; try (rewrite map_length; symmetry; apply writeSuccessNativeByteListsFragments_length).
  rewrite !tail_fields_bytes_call_model; try assumption; rewrite (exact_byte_lists_model (writeSuccessFrameSp witness) (writeSuccessPostByteLists15930 (writeSuccessPostData witness)) _ H5) (exact_byte_lists_model (writeSuccessFrameSp witness) (writeSuccessPostByteLists15940 (writeSuccessPostData witness)) _ H6) (exact_byte_lists_model (writeSuccessFrameSp witness) (writeSuccessPostByteLists15950 (writeSuccessPostData witness)) _ H7).
  rewrite /tailFieldsFirstSegmentEvents /tailFieldsByteListsCallEvents /=; reflexivity.
Qed.

Lemma tail_fields_witness_trace_connection {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  tailFieldsPayloadSizeFacts (writeSuccessPostData witness) ->
  writeOutputPayloadsSpec
    (writeSuccessPost158e0Descriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness))
    (writeSuccessExactPostPayloadsAt
      (writeSuccessPost158e0Descriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness)) witness)
    (writeSuccessTraceTail witness) =
  tailFieldsFirstSegmentEvents (writeSuccessFrameSp witness)
    (writeSuccessDecodedBytes witness) (writeSuccessPostData witness)
    (writeSuccessExactTailFirstBranchEvents witness).
Proof.
  intros Hsizes; rewrite tail_fields_witness_payload_suffix tail_fields_first_descriptors tail_fields_first_fragments map_app.
  rewrite writeOutputPayloadsSpec_app; last (rewrite map_length; apply tail_fields_first_length).
  rewrite (tail_fields_first_trace_model witness _ Hsizes) /writeSuccessExactTailFirstBranchEvents tail_fields_witness_after_payloads; reflexivity.
Qed.
Print Assumptions tail_fields_witness_trace_connection.

Lemma tail_fields_byte_list_sizes `{!islaG Sigma}
    (address : Z) (items : list ByteListItem) :
  byteListItemResources address items -∗
  byteListItemResources address items ∗
  ⌜Forall (fun item => bv_unsigned (byteListSize item) = Z.of_nat (length (byteListBytes item))) items⌝.
Proof.
  iInduction items as [|item rest] "IH" forall (address); cbn.
  - iIntros "_"; iSplit; first done; iPureIntro; constructor.
  - iIntros "(Hdata & Hsize & Hbytes & %Hsize & Hrest)".
    iDestruct ("IH" $! (address + 16) with "Hrest") as "[Hrest %Hrest]".
    iFrame; iSplit; iPureIntro; first done; constructor; done.
Qed.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Lemma tail_fields_resource_size_facts `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (sourceBytes decodedBytes : list (bv 8))
    (post : WriteSuccessPostTransactionData) :
  writeSuccessPostTransactionDataResources sp sourceBytes decodedBytes post -∗
  writeSuccessPostTransactionDataResources sp sourceBytes decodedBytes post ∗
  ⌜tailFieldsPayloadSizeFacts post⌝.
Proof.
  rewrite /writeSuccessPostTransactionDataResources /writeSuccessDescriptorResources; iIntros "(Hpre & Hhash & (Hb0 & %H0) & (Hb1 & %H1) & (Hb2 & %H2) & (Hb3 & %H3) & (Hb4 & %H4) & Hl0 & Hl1 & Hl2 & Hopt & Hpublic & %Hfacts)".
  iDestruct (tail_fields_byte_list_sizes with "Hl0") as "[Hl0 %H5]".
  iDestruct (tail_fields_byte_list_sizes with "Hl1") as "[Hl1 %H6]".
  iDestruct (tail_fields_byte_list_sizes with "Hl2") as "[Hl2 %H7]".
  iFrame "∗%"; iPureIntro; rewrite /tailFieldsPayloadSizeFacts; repeat split; assumption.
Qed.
Print Assumptions tail_fields_resource_size_facts.
