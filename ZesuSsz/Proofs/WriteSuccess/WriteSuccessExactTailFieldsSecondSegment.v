Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Alignment.
Require Import ZesuSsz.Automation.CallScratchBoolean.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanClosedCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrivatePublicBytes.
Require Import isla.riscv64.riscv64.
From stdpp Require Import list.
From IslaTraces.write_success_blocks Require Import Index.
From Coq Require Import Lia.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessRepresentation
  WriteSuccessObservation WriteSuccessExactTrace WriteSuccessEncodeFragments
  WriteSuccessPostTransactionDescriptors WriteSuccessPostTransactionResources
  WriteSuccessOutputSemantic
  WriteSuccessOutputDescriptors.

Local Definition postAfterForkFragments (observation : WriteSuccessObservation) :
    list ByteString :=
  [writeSuccessEncodeU64 (observationActiveForkIndex observation)] ++
  writeSuccessOptionalFragments writeSuccessEncodeU64
    (observationActivationBlock observation) ++
  writeSuccessOptionalFragments writeSuccessEncodeU64
    (observationActivationTimestamp observation) ++
  writeSuccessListFragments writeSuccessBytesFragments
    (observationPublicKeys observation).

Local Definition postAfterActiveForkFragments
    (observation : WriteSuccessObservation) : list ByteString :=
  writeSuccessOptionalFragments writeSuccessEncodeU64
    (observationActivationBlock observation) ++
  writeSuccessOptionalFragments writeSuccessEncodeU64
    (observationActivationTimestamp observation) ++
  writeSuccessListFragments writeSuccessBytesFragments
    (observationPublicKeys observation).

Local Lemma post_after_fork_active_split observation :
  postAfterForkFragments observation =
    [writeSuccessEncodeU64 (observationActiveForkIndex observation)] ++
    postAfterActiveForkFragments observation.
Proof. reflexivity. Qed.

Local Lemma post_fragments_split observation : exists prefix,
  writeSuccessPostFragments observation = prefix ++
    (writeSuccessForkFragments (observationForkName observation) ++
     postAfterForkFragments observation).
Proof.
  eexists. unfold writeSuccessPostFragments, postAfterForkFragments.
  repeat rewrite app_assoc. reflexivity.
Qed.

Local Lemma drop_suffix_by_lengths {A B} (wholeD suffixD : list A)
    (prefix suffix : list B) :
  length wholeD = length (prefix ++ suffix) ->
  length suffixD = length suffix ->
  drop (length wholeD - length suffixD) (prefix ++ suffix) = suffix.
Proof.
  intros Hwhole Hsuffix.
  rewrite Hwhole Hsuffix app_length.
  replace (length prefix + length suffix - length suffix)%nat with
    (length prefix) by lia.
  apply drop_app_length.
Qed.

Local Lemma post1596c_suffix_length sp decodedBytes post :
  writeSuccessPostPayloadShape post ->
  length (writeSuccessPost1596cDescriptors sp post) =
  length (map writeSuccessPrivateBytes
    (writeSuccessForkFragments
      (option_map writeSuccessPublicBytes
        (writeSuccessPostConditional1596cPayload post)) ++
     postAfterForkFragments
       (writeSuccessNativeObservation decodedBytes [] [] [] [] [] 0 post))).
Proof.
  intros Hshape. rewrite map_length.
  unfold writeSuccessPost1596cDescriptors,
    writeSuccessPost159a0Descriptors, writeSuccessPost159b0Descriptors,
    writeSuccessPost159bcDescriptors, writeSuccessPost159c8Descriptors,
    postAfterForkFragments.
  unfold writeSuccessNativeObservation.
  rewrite !app_length. rewrite !writeSuccessOptionalU64Descriptors_length.
  rewrite !writeSuccessOptionalFragments_length.
  rewrite (writeSuccessNativeByteListsFragments_length sp
    (writeSuccessPostByteLists159c8 post)).
  unfold writeSuccessForkFragments, writeSuccessBytesDescriptors.
  unfold writeSuccessPostPayloadShape in Hshape.
  destruct (writeSuccessPostConditional1596c post);
    destruct (writeSuccessPostConditional1596cPayload post);
    try contradiction;
    destruct (writeSuccessPostOptional159b0 post);
    destruct (writeSuccessPostOptional159bc post);
    cbn [option_map writeSuccessBytesFragments writeSuccessNativeObservation]; reflexivity.
Qed.

Local Lemma exact_post_payloads_at_1596c {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessPostPayloadShape (writeSuccessPostData witness) ->
  writeSuccessExactPostPayloadsAt
    (writeSuccessPost1596cDescriptors
      (writeSuccessFrameSp witness) (writeSuccessPostData witness)) witness =
  map writeSuccessPrivateBytes
    (writeSuccessForkFragments
      (option_map writeSuccessPublicBytes
        (writeSuccessPostConditional1596cPayload
          (writeSuccessPostData witness))) ++
     postAfterForkFragments
       (writeSuccessExactObservation
         (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
         (writeSuccessPayload witness) (writeSuccessTransactions witness)
         (writeSuccessRawTransactions witness)
         (writeSuccessWithdrawalsBytes witness)
         (writeSuccessWithdrawalsCount witness)
         (writeSuccessPostData witness))).
Proof.
  intros Hshape. unfold writeSuccessExactPostPayloadsAt.
  rewrite exact_post_withdrawals_payloads.
  destruct (post_fragments_split
    (writeSuccessExactObservation
      (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
      (writeSuccessPayload witness) (writeSuccessTransactions witness)
      (writeSuccessRawTransactions witness)
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessWithdrawalsCount witness)
      (writeSuccessPostData witness))) as [prefix Hsplit].
  rewrite Hsplit.
  rewrite map_app.
  apply drop_suffix_by_lengths.
  - rewrite -map_app -Hsplit map_length.
    apply writeSuccessPostDescriptors_fragments_length. exact Hshape.
  - apply post1596c_suffix_length. exact Hshape.
Qed.

Local Lemma post159a0_suffix_length sp decodedBytes post :
  length (writeSuccessPost159a0Descriptors sp post) =
  length (map writeSuccessPrivateBytes
    (postAfterForkFragments
      (writeSuccessNativeObservation decodedBytes [] [] [] [] [] 0 post))).
Proof.
  rewrite map_length.
  unfold writeSuccessPost159a0Descriptors, writeSuccessPost159b0Descriptors,
    writeSuccessPost159bcDescriptors, writeSuccessPost159c8Descriptors,
    postAfterForkFragments, writeSuccessNativeObservation.
  rewrite !app_length. rewrite !writeSuccessOptionalU64Descriptors_length.
  rewrite !writeSuccessOptionalFragments_length.
  rewrite (writeSuccessNativeByteListsFragments_length sp
    (writeSuccessPostByteLists159c8 post)).
  destruct (writeSuccessPostOptional159b0 post);
    destruct (writeSuccessPostOptional159bc post); reflexivity.
Qed.

Local Lemma post_fragments_after_fork_split observation : exists prefix,
  writeSuccessPostFragments observation =
    prefix ++ postAfterForkFragments observation.
Proof.
  destruct (post_fragments_split observation) as [prefix Hsplit].
  exists (prefix ++ writeSuccessForkFragments
    (observationForkName observation)).
  rewrite Hsplit app_assoc. reflexivity.
Qed.

Local Lemma exact_post_payloads_at_159a0 {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessPostPayloadShape (writeSuccessPostData witness) ->
  writeSuccessExactPostPayloadsAt
    (writeSuccessPost159a0Descriptors
      (writeSuccessFrameSp witness) (writeSuccessPostData witness)) witness =
  map writeSuccessPrivateBytes
    (postAfterForkFragments
      (writeSuccessExactObservation
        (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
        (writeSuccessPayload witness) (writeSuccessTransactions witness)
        (writeSuccessRawTransactions witness)
        (writeSuccessWithdrawalsBytes witness)
        (writeSuccessWithdrawalsCount witness)
        (writeSuccessPostData witness))).
Proof.
  intros Hshape. unfold writeSuccessExactPostPayloadsAt.
  rewrite exact_post_withdrawals_payloads.
  destruct (post_fragments_after_fork_split
    (writeSuccessExactObservation
      (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
      (writeSuccessPayload witness) (writeSuccessTransactions witness)
      (writeSuccessRawTransactions witness)
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessWithdrawalsCount witness)
      (writeSuccessPostData witness))) as [prefix Hsplit].
  rewrite Hsplit map_app.
  apply drop_suffix_by_lengths.
  - rewrite -map_app -Hsplit map_length.
    apply writeSuccessPostDescriptors_fragments_length. exact Hshape.
  - apply post159a0_suffix_length.
Qed.

Local Lemma post159b0_suffix_length sp decodedBytes post :
  length (writeSuccessPost159b0Descriptors sp post) =
  length (map writeSuccessPrivateBytes
    (postAfterActiveForkFragments
      (writeSuccessNativeObservation decodedBytes [] [] [] [] [] 0 post))).
Proof.
  rewrite map_length.
  unfold writeSuccessPost159b0Descriptors, writeSuccessPost159bcDescriptors,
    writeSuccessPost159c8Descriptors, postAfterActiveForkFragments,
    writeSuccessNativeObservation.
  rewrite !app_length. rewrite !writeSuccessOptionalU64Descriptors_length.
  rewrite !writeSuccessOptionalFragments_length.
  rewrite (writeSuccessNativeByteListsFragments_length sp
    (writeSuccessPostByteLists159c8 post)).
  destruct (writeSuccessPostOptional159b0 post);
    destruct (writeSuccessPostOptional159bc post); reflexivity.
Qed.

Local Lemma post_fragments_after_active_fork_split observation : exists prefix,
  writeSuccessPostFragments observation =
    prefix ++ postAfterActiveForkFragments observation.
Proof.
  destruct (post_fragments_after_fork_split observation) as [prefix Hsplit].
  exists (prefix ++ [writeSuccessEncodeU64
    (observationActiveForkIndex observation)]).
  rewrite Hsplit. unfold postAfterForkFragments,
    postAfterActiveForkFragments. repeat rewrite app_assoc. reflexivity.
Qed.

Local Lemma exact_post_payloads_at_159b0 {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessPostPayloadShape (writeSuccessPostData witness) ->
  writeSuccessExactPostPayloadsAt
    (writeSuccessPost159b0Descriptors
      (writeSuccessFrameSp witness) (writeSuccessPostData witness)) witness =
  map writeSuccessPrivateBytes
    (postAfterActiveForkFragments
      (writeSuccessExactObservation
        (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
        (writeSuccessPayload witness) (writeSuccessTransactions witness)
        (writeSuccessRawTransactions witness)
        (writeSuccessWithdrawalsBytes witness)
        (writeSuccessWithdrawalsCount witness)
        (writeSuccessPostData witness))).
Proof.
  intros Hshape. unfold writeSuccessExactPostPayloadsAt.
  rewrite exact_post_withdrawals_payloads.
  destruct (post_fragments_after_active_fork_split
    (writeSuccessExactObservation
      (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
      (writeSuccessPayload witness) (writeSuccessTransactions witness)
      (writeSuccessRawTransactions witness)
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessWithdrawalsCount witness)
      (writeSuccessPostData witness))) as [prefix Hsplit].
  rewrite Hsplit map_app.
  apply drop_suffix_by_lengths.
  - rewrite -map_app -Hsplit map_length.
    apply writeSuccessPostDescriptors_fragments_length. exact Hshape.
  - apply (post159b0_suffix_length (writeSuccessFrameSp witness)
      (writeSuccessDecodedBytes witness) (writeSuccessPostData witness)).
Qed.

Local Lemma first_events_none {Decoded}
    (witness : writeSuccessNativeWitness Decoded)
    (Hconditional : writeSuccessPostConditional1596c
      (writeSuccessPostData witness) = None)
    (Hpayload : writeSuccessPostConditional1596cPayload
      (writeSuccessPostData witness) = None) :
  writeSuccessExactTailFirstBranchEvents witness =
  writeOutputEvents (writeSuccessFrameSp witness - BV 64 9)%bv (BV 64 1)
    (writeSuccessBooleanWordPayload (BV 64 0))
    (writeSuccessExactTailAfterConditionalEvents witness).
Proof.
  unfold writeSuccessExactTailFirstBranchEvents.
  rewrite exact_post_payloads_at_1596c.
  2: { unfold writeSuccessPostPayloadShape. rewrite Hconditional Hpayload. done. }
  unfold writeSuccessPost1596cDescriptors.
  rewrite Hconditional Hpayload.
  cbn [writeSuccessForkFragments option_map writeOutputPayloadsSpec].
  unfold writeSuccessExactTailAfterConditionalEvents.
  rewrite exact_post_payloads_at_159a0.
  2: { unfold writeSuccessPostPayloadShape. rewrite Hconditional Hpayload. done. }
  reflexivity.
Qed.

Local Lemma first_events_some {Decoded}
    (witness : writeSuccessNativeWitness Decoded)
    (data size : bv 64) (payload : list (bv 8))
    (Hconditional : writeSuccessPostConditional1596c
      (writeSuccessPostData witness) = Some (data, size))
    (Hpayload : writeSuccessPostConditional1596cPayload
      (writeSuccessPostData witness) = Some payload)
    (Hsize : bv_unsigned size = Z.of_nat (length payload)) :
  writeSuccessExactTailFirstBranchEvents witness =
  writeOutputEvents (writeSuccessFrameSp witness - BV 64 9)%bv (BV 64 1)
    (writeSuccessBooleanWordPayload (BV 64 1))
    (writeOutputEvents (writeSuccessFrameSp witness - BV 64 48)%bv
      (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
      (writeOutputEvents data size payload
        (writeSuccessExactTailAfterConditionalEvents witness))).
Proof.
  unfold writeSuccessExactTailFirstBranchEvents.
  rewrite exact_post_payloads_at_1596c.
  2: { unfold writeSuccessPostPayloadShape. rewrite Hconditional Hpayload. done. }
  unfold writeSuccessPost1596cDescriptors.
  rewrite Hconditional Hpayload.
  unfold writeSuccessBytesDescriptors, writeSuccessBytesFragments.
  cbn [writeSuccessForkFragments option_map writeOutputPayloadsSpec].
  unfold writeSuccessBytesFragments.
  cbn [writeOutputPayloadsSpec].
  rewrite map_app. rewrite map_app.
  cbn [writeOutputPayloadsSpec].
  cbn [List.map List.app writeOutputPayloadsSpec].
  rewrite writeSuccessPrivatePublicBytes.
  unfold writeSuccessPublicBytes. rewrite map_length -Hsize.
  unfold writeSuccessExactTailAfterConditionalEvents.
  rewrite exact_post_payloads_at_159a0.
  2: { unfold writeSuccessPostPayloadShape. rewrite Hconditional Hpayload. done. }
  reflexivity.
Qed.

Local Lemma post_conditional_pointer_none sp source decoded post
    (Hfacts : writeSuccessPostTransactionDataFacts sp source decoded post)
    (Hconditional : writeSuccessPostConditional1596c post = None) :
  writeSuccessPostWord (writeSuccessPostTailWords decoded) 7 = BV 64 0.
Proof.
  unfold writeSuccessPostTransactionDataFacts in Hfacts.
  cbn zeta in Hfacts.
  decompose [and] Hfacts; clear Hfacts.
  match goal with Hwords : writeSuccessOptionalBytesWords _ _ _ |- _ =>
    unfold writeSuccessOptionalBytesWords in Hwords;
    rewrite Hconditional in Hwords;
    destruct Hwords as [[Hzero _]|[Hnonzero Hbad]];
      [exact Hzero|discriminate]
  end.
Qed.

Local Lemma post_conditional_pointer_some sp source decoded post data size
    (Hfacts : writeSuccessPostTransactionDataFacts sp source decoded post)
    (Hconditional : writeSuccessPostConditional1596c post = Some (data, size)) :
  writeSuccessPostWord (writeSuccessPostTailWords decoded) 7 <> BV 64 0.
Proof.
  unfold writeSuccessPostTransactionDataFacts in Hfacts.
  cbn zeta in Hfacts.
  decompose [and] Hfacts; clear Hfacts.
  match goal with Hwords : writeSuccessOptionalBytesWords _ _ _ |- _ =>
    unfold writeSuccessOptionalBytesWords in Hwords;
    rewrite Hconditional in Hwords;
    destruct Hwords as [[_ Hbad]|[Hnonzero _]];
      [discriminate|exact Hnonzero]
  end.
Qed.

Local Lemma post_conditional_words_some sp source decoded post data size
    (Hfacts : writeSuccessPostTransactionDataFacts sp source decoded post)
    (Hconditional : writeSuccessPostConditional1596c post = Some (data, size)) :
  writeSuccessPostWord (writeSuccessPostTailWords decoded) 7 = data /\
  writeSuccessPostWord (writeSuccessPostTailWords decoded) 8 = size.
Proof.
  unfold writeSuccessPostTransactionDataFacts in Hfacts.
  cbn zeta in Hfacts. decompose [and] Hfacts; clear Hfacts.
  match goal with Hwords : writeSuccessOptionalBytesWords _ _ _ |- _ =>
    unfold writeSuccessOptionalBytesWords in Hwords;
    rewrite Hconditional in Hwords;
    destruct Hwords as [[_ Hbad]|[_ Hsame]];
      [discriminate|inversion Hsame; auto]
  end.
Qed.

Local Lemma after_conditional_first_explicit {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessPostPayloadShape (writeSuccessPostData witness) ->
  writeSuccessExactTailAfterConditionalEvents witness =
    writeOutputEvents (writeSuccessFrameSp witness - BV 64 16)%bv
      (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64
        (bv_unsigned (writeSuccessPostWord
          (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 9))))
      (writeSuccessExactTailSecondBranchEvents witness).
Proof.
  intros Hshape.
  unfold writeSuccessExactTailAfterConditionalEvents,
    writeSuccessExactTailSecondBranchEvents.
  rewrite (exact_post_payloads_at_159a0 witness Hshape).
  rewrite (exact_post_payloads_at_159b0 witness Hshape).
  unfold writeSuccessPost159a0Descriptors.
  rewrite post_after_fork_active_split map_app.
  rewrite writeOutputPayloadsSpec_app; [|reflexivity].
  cbn [writeOutputPayloadsSpec List.map writeSuccessExactObservation
    writeSuccessNativeObservation].
  Unshelve. all: try exact Hshape. all: try reflexivity.
Qed.

Local Lemma tail_stack_facts {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessWitnessWellFormed args witness ->
  bv_extract 0 4 (writeSuccessFrameSp witness) = BV 4 0 /\
  0 <= bv_unsigned (writeSuccessFrameSp witness) - 48.
Proof.
  intros Hwf.
  unfold writeSuccessWitnessWellFormed in Hwf.
  decompose [and] Hwf; clear Hwf.
  split.
  - unfold writeSuccessFrameSp. bv_solve.
  - unfold writeSuccessFrameSp. cbn [mapRamBase defaultMap] in *.
    bv_solve.
Qed.

Lemma write_success_exact_tail_fields_second_segment
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15b9c encoderBooleanEntryBoundary -∗
  □ instr_pre 0x15c6c encoderBytesEntryBoundary -∗
  □ instr_pre 0x15d10 encoderIntEntryBoundary -∗
  instr_body 0x159b8
    (writeSuccessExactTailSecondBranchState args witness) -∗
  instr_body 0x1596c
    (writeSuccessExactTailFirstBranchState args witness
      (writeSuccessExactTailFirstBranchEvents witness)).
Proof.
  zesu_block.
  all: iRename select (writeSuccessExactPostWithdrawalsCallerFrameRest args witness)%I into "Hcaller".
  all: iEval (rewrite writeSuccessExactPostWithdrawalsCallerFrameRest_unfold
    /writeSuccessExactPostWithdrawalsCallerFrameRestRaw
    /writeSuccessExactPostWithdrawalsMemoryFrame
    /writeSuccessExactCopiedTailWordsWithout7
    /writeSuccessPostTransactionDataResources
    /writeSuccessOptionalDescriptorResources) in "Hcaller".
  all: zesu_open_resource_groups.
  all: destruct (writeSuccessPostConditional1596c
    (writeSuccessPostData witness)) as [[data size]|] eqn:Hconditional;
  destruct (writeSuccessPostConditional1596cPayload
    (writeSuccessPostData witness)) as [payload|] eqn:Hpayload.
  all: try (iDestruct select False%I as %[]).
  all: try match goal with
  | Hzero : _ = BV 64 0, Hconditional : _ = Some (?data, ?size),
    Hfacts : writeSuccessPostTransactionDataFacts _ _ _ _ |- _ =>
      exfalso; apply (post_conditional_pointer_some _ _ _ _ data size
        Hfacts Hconditional); exact Hzero
  | Hnonzero : _ <> BV 64 0, Hconditional : _ = None,
    Hfacts : writeSuccessPostTransactionDataFacts _ _ _ _ |- _ =>
      exfalso; apply Hnonzero;
      exact (post_conditional_pointer_none _ _ _ _ Hfacts Hconditional)
  end.
  - rename select (writeSuccessPostTransactionDataFacts _ _ _ _) into HpostFacts.
    have Hpointer := post_conditional_pointer_none _ _ _ _
      HpostFacts Hconditional.
    zesu_run; try bv_solve.
    match goal with Hwf : writeSuccessWitnessWellFormed args witness |- _ =>
      pose proof (tail_stack_facts args witness Hwf) as [Halign4 HframeLow]
    end.
    iExists (writeSuccessExactTailAfterConditionalEvents witness, tt)ₗ.
    rewrite (first_events_none witness Hconditional Hpayload).
    zesu_run. Unshelve. all: try assumption. all: try bv_solve.
  - iRename select (writeSuccessDescriptorResources _ _)%I into "Hdescriptor".
    iDestruct "Hdescriptor" as "[HpayloadMemory %Hsize]".
    rename select (writeSuccessPostTransactionDataFacts _ _ _ _) into HpostFacts.
    have Hpointer := post_conditional_pointer_some _ _ _ _ _ _
      HpostFacts Hconditional.
    zesu_run; try bv_solve.
    match goal with Hwf : writeSuccessWitnessWellFormed args witness |- _ =>
      pose proof (tail_stack_facts args witness Hwf) as [Halign4 HframeLow]
    end.
    iExists ((writeOutputEvents
      (writeSuccessFrameSp witness - BV 64 48)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
      (writeOutputEvents data size payload
        (writeSuccessExactTailAfterConditionalEvents witness))), tt)ₗ.
    rewrite (first_events_some witness data size payload
      Hconditional Hpayload Hsize).
    zesu_run. Unshelve. all: try assumption. all: try bv_solve.
    iEval (replace (bv_unsigned (Z_to_bv 64 88444 + 4)) with 88448 by bv_solve).
    iEval (vm_compute [IslaTraces.write_success_blocks.Index.lookup]).
    iApply subsume_instr_some_pre. iExists tt. iSplit; last done.
    iIntros "Hreturn HPC".
    iEval (unfold encoderBooleanClosedReturn, writeSuccessBooleanWordPayload) in "Hreturn".
    iDestruct "Hreturn" as
      "(Hsys & H1 & H2 & Hra & H5 & H10 & H11 & Hbyte & Hlow & Hmmio & Htrace & _)".
    iEval (replace (bv_unsigned (writeSuccessFrameSp witness - BV 64 9)%bv) with
      (bv_unsigned (writeSuccessFrameSp witness) - 9)%Z by bv_solve) in "Hbyte".
    iEval (rewrite mem_mapsto_array_singleton) in "Hbyte".
    iPoseProof (call_boolean_scratch_reuse (writeSuccessFrameSp witness)
      (Z_to_bv 64 88444 + 4) _ with "[$Hlow $Hbyte $Hra]") as "Hscratch".
    iFrame. zesu_run.
    have [HdataWord HsizeWord] := post_conditional_words_some _ _ _ _ _ _
      HpostFacts Hconditional.
    rewrite HdataWord HsizeWord.
    iExists (writeSuccessExactTailAfterConditionalEvents witness, payload, tt)ₗ.
    zesu_run. Unshelve. all: try assumption. all: try bv_solve. all: try lia.
    iEval (replace (bv_unsigned (Z_to_bv 64 88460 + 4)) with 88464 by bv_solve).
    iEval (vm_compute [IslaTraces.write_success_blocks.Index.lookup]).
    iApply subsume_instr_some_pre. iExists tt. iSplit; last done.
    iIntros "Hreturn HPC".
    iEval (unfold encoderBytesExactReturn, encoderBytesExactPost) in "Hreturn".
    iDestruct "Hreturn" as
      "(HsysR & H1R & H5R & H10R & H11R & HpayloadR & HmmioR & HtraceR & HoutputR & _)".
    iEval (unfold encoderBytesExactOutputResources) in "HoutputR".
    iDestruct "HoutputR" as
      "(H6R & H2R & H8R & H9R & Hstack0R & Hstack1R & Hstack2R & Hstack3R & Hstack4R & Hstack5R & _)".
    iFrame. zesu_run.
    have Hshape : writeSuccessPostPayloadShape (writeSuccessPostData witness).
    { unfold writeSuccessPostPayloadShape. rewrite Hconditional Hpayload. done. }
    iExists (writeSuccessExactTailSecondBranchEvents witness, tt)ₗ.
    rewrite (after_conditional_first_explicit witness Hshape).
    zesu_run. Unshelve. all: try assumption. all: try bv_solve. all: try lia.
Qed.
Print Assumptions write_success_exact_tail_fields_second_segment.
