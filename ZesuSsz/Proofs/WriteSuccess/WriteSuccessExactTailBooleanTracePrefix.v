Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.GuardedTracePrefix.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsTraceJunction.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTrace.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncodeFragments.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrivatePublicBytes.
From Coq Require Import Lia.

Lemma tail_boolean_after_payload_drop {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessExactPostPayloadsAt
    (writeSuccessPost159a0Descriptors (writeSuccessFrameSp witness)
      (writeSuccessPostData witness)) witness =
  drop
    (length (writeSuccessPost1596cDescriptors (writeSuccessFrameSp witness)
      (writeSuccessPostData witness)) -
     length (writeSuccessPost159a0Descriptors (writeSuccessFrameSp witness)
      (writeSuccessPostData witness)))
    (writeSuccessExactPostPayloadsAt
      (writeSuccessPost1596cDescriptors (writeSuccessFrameSp witness)
        (writeSuccessPostData witness)) witness).
Proof.
  have Hle : (length (writeSuccessPost159a0Descriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness)) <= length (writeSuccessPost1596cDescriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness)))%nat.
  { unfold writeSuccessPost1596cDescriptors.
  destruct (writeSuccessPostConditional1596c (writeSuccessPostData witness)) as [[data size] |]; rewrite /= ?length_app; lia.
  }
  unfold writeSuccessExactPostPayloadsAt.
  rewrite tail_fields_before_descriptors tail_fields_first_descriptors !length_app drop_drop.
  f_equal.
  lia.
Qed.

Lemma tail_boolean_none_trace_equality {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessPostConditional1596c (writeSuccessPostData witness) = None ->
  writeSuccessPostConditional1596cPayload (writeSuccessPostData witness) = None ->
  writeSuccessExactTailFirstBranchEvents witness =
    writeOutputEvents (writeSuccessFrameSp witness - BV 64 9)%bv (BV 64 1)
      (writeSuccessBooleanWordPayload (BV 64 0))
      (writeSuccessExactTailAfterConditionalEvents witness).
Proof.
  intros Hnone HpayloadNone.
  rewrite /writeSuccessExactTailFirstBranchEvents /writeSuccessExactTailAfterConditionalEvents tail_boolean_after_payload_drop !tail_fields_witness_after_payloads /writeSuccessPost1596cDescriptors Hnone /tailFieldsAfterFragments /writeSuccessExactObservation /writeSuccessNativeObservation HpayloadNone.
  cbn [observationForkName List.map List.app option_map writeSuccessForkFragments writeOutputPayloadsSpec].
  replace (S (length (writeSuccessPost159a0Descriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness))) - length (writeSuccessPost159a0Descriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness)))%nat with 1%nat by lia.
  cbn [drop].
  reflexivity.
Qed.

Lemma tail_boolean_some_trace_equality {Decoded}
    (witness : writeSuccessNativeWitness Decoded)
    (data size : bv 64) (payload : list (bv 8)) :
  writeSuccessPostConditional1596c (writeSuccessPostData witness) = Some (data,size) ->
  writeSuccessPostConditional1596cPayload (writeSuccessPostData witness) = Some payload ->
  bv_unsigned size = Z.of_nat (length payload) ->
  writeSuccessExactTailFirstBranchEvents witness =
    writeOutputEvents (writeSuccessFrameSp witness - BV 64 9)%bv (BV 64 1)
      (writeSuccessBooleanWordPayload (BV 64 1))
      (writeOutputEvents (writeSuccessFrameSp witness - BV 64 48)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
        (writeOutputEvents data size payload
          (writeSuccessExactTailAfterConditionalEvents witness))).
Proof.
  intros Hsome HpayloadSome Hsize.
  rewrite /writeSuccessExactTailFirstBranchEvents /writeSuccessExactTailAfterConditionalEvents tail_boolean_after_payload_drop !tail_fields_witness_after_payloads /writeSuccessPost1596cDescriptors Hsome /tailFieldsAfterFragments /writeSuccessExactObservation /writeSuccessNativeObservation HpayloadSome.
  cbn [observationForkName List.map List.app option_map writeSuccessForkFragments writeSuccessBytesFragments writeSuccessBytesDescriptors writeOutputPayloadsSpec].
  replace (length (((writeSuccessFrameSp witness - BV 64 9)%bv, BV 64 1) :: writeSuccessBytesDescriptors (writeSuccessFrameSp witness) data size ++ writeSuccessPost159a0Descriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness)) - length (writeSuccessPost159a0Descriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness)))%nat with 3%nat by (unfold writeSuccessBytesDescriptors; rewrite /= ?length_app; lia).
  cbn [drop].
  rewrite writeSuccessPrivatePublicBytes /writeSuccessPublicBytes map_length -Hsize.
  reflexivity.
Qed.

Section CanonicalFrameTests.
Context `{!islaG Sigma} `{!threadG} {Decoded}
  `{!WriteSuccessMemoryRepresentation Decoded}.
Lemma tail_boolean_zero_trace_from_frame
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 = BV 64 0 ->
  writeSuccessExactPostWithdrawalsCallerFrameRest args witness -∗
  ⌜writeSuccessExactTailFirstBranchEvents witness =
    writeOutputEvents (writeSuccessFrameSp witness - BV 64 9)%bv (BV 64 1)
      (writeSuccessBooleanWordPayload (BV 64 0))
      (writeSuccessExactTailAfterConditionalEvents witness)⌝ ∗
  writeSuccessExactPostWithdrawalsCallerFrameRest args witness.
Proof.
  intros Hword.
  iIntros "Hframe".
  iEval (rewrite writeSuccessExactPostWithdrawalsCallerFrameRest_unfold /writeSuccessExactPostWithdrawalsCallerFrameRestRaw /writeSuccessExactPostWithdrawalsMemoryFrame) in "Hframe".
  iDestruct "Hframe" as "(Hreg & %Hwf & Hs0 & Hs1 & Hs2 & Hwords & Hsource & Hvalues & Hscratch & Hsaved & Hdecoded & Hpayload & Htx & Hpost & Hstatic & Hinv & _)".
  iEval (unfold writeSuccessPostTransactionDataResources) in "Hpost".
  iDestruct "Hpost" as "(Hp0 & Hhash & Hp1 & Hp2 & Hp3 & Hp4 & Hp5 & Hl0 & Hl1 & Hl2 & Hconditional & Hl3 & %Hfacts)".
  iDestruct (writeSuccessOptionalDescriptorResources_shape with "Hconditional") as %Hshape.
  pose proof Hfacts as HfactsCopy.
  unfold writeSuccessPostTransactionDataFacts in HfactsCopy.
  cbn zeta in HfactsCopy.
  decompose [and] HfactsCopy.
  have Hnone : WriteSuccessPostTransactionDescriptors.writeSuccessPostConditional1596c (writeSuccessPostData witness) = None.
  { match goal with Hwords : writeSuccessOptionalBytesWords _ _ _ |- _ => unfold writeSuccessOptionalBytesWords in Hwords; rewrite Hword in Hwords; naive_solver end.
  } have HpayloadNone : WriteSuccessPostTransactionDescriptors.writeSuccessPostConditional1596cPayload (writeSuccessPostData witness) = None.
  { rewrite Hnone in Hshape.
  destruct (WriteSuccessPostTransactionDescriptors.writeSuccessPostConditional1596cPayload (writeSuccessPostData witness)); naive_solver.
  } iSplitR.
  2: { rewrite writeSuccessExactPostWithdrawalsCallerFrameRest_unfold /writeSuccessExactPostWithdrawalsCallerFrameRestRaw /writeSuccessExactPostWithdrawalsMemoryFrame /writeSuccessPostTransactionDataResources.
  iFrame "Hreg Hs0 Hs1 Hs2 Hwords Hsource Hvalues Hscratch Hsaved Hdecoded Hpayload Htx Hp0 Hhash Hp1 Hp2 Hp3 Hp4 Hp5 Hl0 Hl1 Hl2 Hconditional Hl3 Hstatic Hinv".
  iSplit; iPureIntro; [exact Hwf | exact Hfacts].
  } iPureIntro.
  exact (tail_boolean_none_trace_equality witness Hnone HpayloadNone).
Qed.
Lemma tail_boolean_one_trace_from_frame
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 <> BV 64 0 ->
  writeSuccessExactPostWithdrawalsCallerFrameRest args witness -∗
  ⌜exists payload : list (bv 8),
    writeSuccessExactTailFirstBranchEvents witness =
    writeOutputEvents (writeSuccessFrameSp witness - BV 64 9)%bv (BV 64 1)
      (writeSuccessBooleanWordPayload (BV 64 1))
      (writeOutputEvents (writeSuccessFrameSp witness - BV 64 48)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64
          (bv_unsigned (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 8))))
        (writeOutputEvents
          (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7)
          (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 8)
          payload (writeSuccessExactTailAfterConditionalEvents witness)))⌝ ∗
  writeSuccessExactPostWithdrawalsCallerFrameRest args witness.
Proof.
  intros Hword.
  iIntros "Hframe".
  iEval (rewrite writeSuccessExactPostWithdrawalsCallerFrameRest_unfold /writeSuccessExactPostWithdrawalsCallerFrameRestRaw /writeSuccessExactPostWithdrawalsMemoryFrame) in "Hframe".
  iDestruct "Hframe" as "(Hreg & %Hwf & Hs0 & Hs1 & Hs2 & Hwords & Hsource & Hvalues & Hscratch & Hsaved & Hdecoded & Hpayload & Htx & Hpost & Hstatic & Hinv & _)".
  iEval (unfold writeSuccessPostTransactionDataResources) in "Hpost".
  iDestruct "Hpost" as "(Hp0 & Hhash & Hp1 & Hp2 & Hp3 & Hp4 & Hp5 & Hl0 & Hl1 & Hl2 & Hconditional & Hl3 & %Hfacts)".
  iDestruct (writeSuccessOptionalDescriptorResources_shape with "Hconditional") as %Hshape.
  pose proof Hfacts as HfactsCopy.
  unfold writeSuccessPostTransactionDataFacts in HfactsCopy.
  cbn zeta in HfactsCopy.
  decompose [and] HfactsCopy.
  have Hsome : writeSuccessPostConditional1596c (writeSuccessPostData witness) = Some (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7, writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 8).
  { match goal with Hwords : writeSuccessOptionalBytesWords _ _ _ |- _ => unfold writeSuccessOptionalBytesWords in Hwords; naive_solver end.
  } rewrite Hsome in Hshape.
  destruct (writeSuccessPostConditional1596cPayload (writeSuccessPostData witness)) as [payload |] eqn:HpayloadSome; last contradiction.
  iEval (rewrite Hsome /writeSuccessOptionalDescriptorResources /writeSuccessDescriptorResources) in "Hconditional".
  iDestruct "Hconditional" as "[HconditionalMemory %Hsize]".
  iAssert (writeSuccessOptionalDescriptorResources (writeSuccessPostConditional1596c (writeSuccessPostData witness)) (Some payload))%I with "[HconditionalMemory]" as "Hconditional".
  { rewrite Hsome /writeSuccessOptionalDescriptorResources /writeSuccessDescriptorResources.
  iFrame "HconditionalMemory".
  done.
  } iSplitR.
  2: { rewrite writeSuccessExactPostWithdrawalsCallerFrameRest_unfold /writeSuccessExactPostWithdrawalsCallerFrameRestRaw /writeSuccessExactPostWithdrawalsMemoryFrame /writeSuccessPostTransactionDataResources HpayloadSome.
  iFrame "Hreg Hs0 Hs1 Hs2 Hwords Hsource Hvalues Hscratch Hsaved Hdecoded Hpayload Htx Hp0 Hhash Hp1 Hp2 Hp3 Hp4 Hp5 Hl0 Hl1 Hl2 Hconditional Hl3 Hstatic Hinv".
  iSplit; iPureIntro; [exact Hwf | exact Hfacts].
  } iPureIntro.
  exists payload.
  apply tail_boolean_some_trace_equality; assumption.
Qed.
End CanonicalFrameTests.


Require Import ZesuSsz.Automation.GuardedTracePrefix.
Section TailBooleanPrefixRegistration.
Context `{!islaG Sigma} `{!threadG} {Decoded}
  `{!WriteSuccessMemoryRepresentation Decoded}.
Global Instance tail_boolean_zero_prefix_registration (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  ZesuGuardedTracePrefix
    (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 = BV 64 0)
    (writeSuccessExactPostWithdrawalsCallerFrameRest args witness)
    (writeSuccessExactTailFirstBranchEvents witness)
    (fun tail => writeOutputEvents (writeSuccessFrameSp witness - BV 64 9)%bv
      (BV 64 1) (writeSuccessBooleanWordPayload (BV 64 0)) tail).
Proof.
  intros Hguard.
  iIntros "Hframe".
  iDestruct (tail_boolean_zero_trace_from_frame args witness Hguard with "Hframe") as "[%Hconnection Hframe]".
  iExists (writeSuccessExactTailAfterConditionalEvents witness).
  iFrame.
  done.
Qed.
Global Instance tail_boolean_one_prefix_registration (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  ZesuGuardedTracePrefix
    (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 <> BV 64 0)
    (writeSuccessExactPostWithdrawalsCallerFrameRest args witness)
    (writeSuccessExactTailFirstBranchEvents witness)
    (fun tail => writeOutputEvents (writeSuccessFrameSp witness - BV 64 9)%bv
      (BV 64 1) (writeSuccessBooleanWordPayload (BV 64 1)) tail).
Proof.
  intros Hguard.
  iIntros "Hframe".
  iDestruct (tail_boolean_one_trace_from_frame args witness Hguard with "Hframe") as "[%Hconnection Hframe]".
  destruct Hconnection as (payload & Hconnection).
  iExists (writeOutputEvents (writeSuccessFrameSp witness - BV 64 48)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned
      (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 8))))
    (writeOutputEvents
      (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7)
      (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 8)
      payload (writeSuccessExactTailAfterConditionalEvents witness))).
  iFrame.
  done.
Qed.
Global Instance tail_boolean_zero_entry_prefix_registration
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  ZesuGuardedTracePrefix
    (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 = BV 64 0)
    (writeSuccessExactPostWithdrawalsCallerFrameRest args witness)
    (writeSuccessExactTailFirstBranchEvents witness)
    (fun tail => writeOutputEvents
      (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 9))%bv
      (BV 64 1) (writeSuccessBooleanWordPayload (BV 64 0)) tail).
Proof.
  have Haddr : (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 9))%bv =
    (writeSuccessFrameSp witness - BV 64 9)%bv.
  { unfold writeSuccessFrameSp.
  bv_solve.
  }
  rewrite Haddr.
  apply tail_boolean_zero_prefix_registration.
Qed.

Global Instance tail_boolean_one_entry_prefix_registration
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  ZesuGuardedTracePrefix
    (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 <> BV 64 0)
    (writeSuccessExactPostWithdrawalsCallerFrameRest args witness)
    (writeSuccessExactTailFirstBranchEvents witness)
    (fun tail => writeOutputEvents
      (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 9))%bv
      (BV 64 1) (writeSuccessBooleanWordPayload (BV 64 1)) tail).
Proof.
  have Haddr : (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 9))%bv =
    (writeSuccessFrameSp witness - BV 64 9)%bv.
  { unfold writeSuccessFrameSp.
  bv_solve.
  }
  rewrite Haddr.
  apply tail_boolean_one_prefix_registration.
Qed.

End TailBooleanPrefixRegistration.

Print Assumptions tail_boolean_zero_trace_from_frame.
Print Assumptions tail_boolean_one_trace_from_frame.

Print Assumptions tail_boolean_zero_entry_prefix_registration.
Print Assumptions tail_boolean_one_entry_prefix_registration.
