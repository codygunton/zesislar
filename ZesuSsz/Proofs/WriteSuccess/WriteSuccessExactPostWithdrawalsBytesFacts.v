Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueSpec.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTrace.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncodeFragments.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrivatePublicBytes.

Require Import ZesuSsz.Automation.PackedWordValues.
Require Import ZesuSsz.Automation.ByteArrays.

Definition pw_binding_data {Decoded} (witness : writeSuccessNativeWitness Decoded) :=
  take 69 (writeSuccessValues witness) !!! Z.to_nat (136 `div` 8).
Definition pw_binding_size {Decoded} (witness : writeSuccessNativeWitness Decoded) :=
  take 69 (writeSuccessValues witness) !!! IslarisMemory.array_region_start 64
    (bv_unsigned (writeSuccessFrameSp witness) + 1032)
    (bv_unsigned (writeSuccessFrameSp witness) + 1176).
Definition pw_binding_payload {Decoded} (witness : writeSuccessNativeWitness Decoded) :=
  writeSuccessPostBytes1571cPayload (writeSuccessPostData witness).
Definition pw_binding_descriptors {Decoded} (witness : writeSuccessNativeWitness Decoded) :=
  [((writeSuccessEntrySp witness - (BV 64 2000 + BV 64 48))%bv, BV 64 8);
   writeSuccessPostBytes1571c (writeSuccessPostData witness);
   ((writeSuccessFrameSp witness + BV 64 1000)%bv, BV 64 32)] ++
  writeSuccessPost1573cDescriptors (writeSuccessFrameSp witness) (writeSuccessPostData witness).
Definition pw_binding_declared {Decoded} (witness : writeSuccessNativeWitness Decoded) :=
  writeOutputPayloadsSpec (pw_binding_descriptors witness)
    (writeSuccessExactPostPayloadsAt (pw_binding_descriptors witness) witness)
    (writeSuccessTraceTail witness).
Definition pw_binding_tail {Decoded} (witness : writeSuccessNativeWitness Decoded) :=
  writeOutputPayloadsSpec (drop 2 (pw_binding_descriptors witness))
    (drop 2 (writeSuccessExactPostPayloadsAt (pw_binding_descriptors witness) witness))
    (writeSuccessTraceTail witness).
Definition pw_binding_prefix {Decoded} (witness : writeSuccessNativeWitness Decoded)
    (y : spec *ₗ list (bv 8) *ₗ ()) :=
  writeOutputEvents (writeSuccessFrameSp witness - BV 64 48)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned (pw_binding_size witness))))
    (writeOutputEvents (pw_binding_data witness) (pw_binding_size witness) y.2ₗ y.1ₗ).

Lemma pw_binding_equivalence {Decoded} (witness : writeSuccessNativeWitness Decoded)
    (rest : list (list (bv 8))) :
  writeSuccessExactPostPayloadsAt (pw_binding_descriptors witness) witness =
    writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned (pw_binding_size witness))) ::
    pw_binding_payload witness :: rest ->
  writeSuccessPostBytes1571c (writeSuccessPostData witness) =
    (pw_binding_data witness, pw_binding_size witness) ->
  pw_binding_declared witness =
    pw_binding_prefix witness (pw_binding_tail witness, pw_binding_payload witness, tt)ₗ.
Proof.
  intros Hpayloads Hdescriptor.
  unfold pw_binding_declared, pw_binding_tail, pw_binding_prefix.
  rewrite Hpayloads.
  unfold pw_binding_descriptors. rewrite Hdescriptor.
  cbn [drop writeOutputPayloadsSpec].
  have Hsp : (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 48))%bv =
    (writeSuccessFrameSp witness - BV 64 48)%bv.
  { unfold writeSuccessFrameSp. bv_solve. }
  rewrite Hsp. reflexivity.
Qed.
Print Assumptions pw_binding_equivalence.

Lemma pw_binding_payload_offset {Decoded} (witness : writeSuccessNativeWitness Decoded) :
  (length (writeSuccessPost156e8Descriptors (writeSuccessFrameSp witness)
       (writeSuccessPostData witness)) - length (pw_binding_descriptors witness))%nat =
  (2 + writeSuccessOptionCount (writeSuccessPostOptional15700 (writeSuccessPostData witness)))%nat.
Proof.
  unfold writeSuccessPost156e8Descriptors, pw_binding_descriptors,
    writeSuccessBytesDescriptors.
  rewrite !app_length writeSuccessOptionalU64Descriptors_length.
  cbn [length]. lia.
Qed.
Print Assumptions pw_binding_payload_offset.

Lemma pw_binding_actual_payloads {Decoded} (witness : writeSuccessNativeWitness Decoded) :
  bv_unsigned (pw_binding_size witness) = Z.of_nat (length (pw_binding_payload witness)) ->
  writeSuccessExactPostPayloadsAt (pw_binding_descriptors witness) witness =
    writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned (pw_binding_size witness))) ::
    pw_binding_payload witness ::
    drop 2 (writeSuccessExactPostPayloadsAt (pw_binding_descriptors witness) witness).
Proof.
intros Hsize.
rewrite /writeSuccessExactPostPayloadsAt pw_binding_payload_offset exact_post_withdrawals_payloads.
unfold writeSuccessPostFragments, writeSuccessExactObservation, writeSuccessNativeObservation.
cbv beta iota zeta.
destruct (writeSuccessPostOptional15700 (writeSuccessPostData witness)) as [value |] eqn:Hoptional.
all: cbn.
all: unfold pw_binding_payload in Hsize |- *.
all: pose proof (writeSuccessPrivatePublicBytes (writeSuccessPostBytes1571cPayload (writeSuccessPostData witness))) as Hroundtrip.
all: unfold writeSuccessPrivateBytes in Hroundtrip.
all: rewrite Hroundtrip.
all: rewrite /writeSuccessPublicBytes !map_length -Hsize.
all: reflexivity.
Time Qed.
Print Assumptions pw_binding_actual_payloads.


Lemma pw_source_word_projection (values : list (bv 64)) (source : list (bv 8))
    (index : nat) :
  length values = 74%nat -> length source = 720%nat ->
  IslarisMemory.bytes_of_u64s values = take 592 source ->
  (index < 69)%nat ->
  writeSuccessPostWord (writeSuccessPostSourceWords source) index =
    take 69 values !!! index.
Proof.
  intros Hvalues Hsource Hbytes Hindex.
  rewrite lookup_total_take; [|exact Hindex].
  unfold writeSuccessPostWord, writeSuccessPostSourceWords.
  have Hchunk : forall (words : list (bv 64)) (i : nat) (word : bv 64),
      words !! i = Some word ->
      take 8 (drop (i * 8) (IslarisMemory.bytes_of_u64s words)) =
        bv_to_little_endian 8 8 (bv_unsigned word).
  { intros words i word. revert i.
    induction words as [|head words IH]; intros [|i] Hread; try discriminate.
    - cbn in Hread. injection Hread as ->. rewrite /IslarisMemory.bytes_of_u64s /=. reflexivity.
    - cbn in Hread.
      change (take 8 (drop (S i * 8) (bv_to_little_endian 8 8 (bv_unsigned head) ++
        IslarisMemory.bytes_of_u64s words)) = bv_to_little_endian 8 8 (bv_unsigned word)).
      rewrite drop_app length_bv_to_little_endian; [|lia].
      rewrite drop_ge; [|rewrite length_bv_to_little_endian; lia].
      rewrite app_nil_l. replace (S i * 8 - Z.to_nat 8)%nat with (i * 8)%nat by lia.
      exact (IH i Hread). }
  rewrite zesu_packed_u64_lookup; [|exact Hsource |lia]. cbn [default].
  have Hread : values !! index = Some (values !!! index)
    by (apply list_lookup_lookup_total_lt; lia).
  have Hword := Hchunk values index (values !!! index) Hread.
  rewrite Hbytes in Hword.
  rewrite take_drop_commute take_take Nat.min_l in Hword; [|lia].
  rewrite <- take_drop_commute in Hword. rewrite Hword.
  apply zesu_u64_little_endian_roundtrip.
Qed.
Print Assumptions pw_source_word_projection.

Lemma pw_binding_descriptor_from_facts {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  length (writeSuccessValues witness) = 74%nat ->
  length (writeSuccessSourceBytes witness) = 720%nat ->
  IslarisMemory.bytes_of_u64s (writeSuccessValues witness) =
    take 592 (writeSuccessSourceBytes witness) ->
  writeSuccessPostTransactionDataFacts (writeSuccessFrameSp witness)
    (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness)
    (writeSuccessPostData witness) ->
  writeSuccessPostBytes1571c (writeSuccessPostData witness) =
    (pw_binding_data witness, pw_binding_size witness).
Proof.
  intros Hvalues Hsource Hbytes Hfacts.
  unfold writeSuccessPostTransactionDataFacts in Hfacts.
  cbn zeta in Hfacts. destruct Hfacts as [_ [Hdescriptor _]].
  rewrite Hdescriptor. unfold writeSuccessPostDescriptor.
  unfold pw_binding_data, pw_binding_size, IslarisMemory.array_region_start.
  ring_simplify (bv_unsigned (writeSuccessFrameSp witness) + 1176 -
    (bv_unsigned (writeSuccessFrameSp witness) + 1032))%Z.
  change ((writeSuccessPostWord (writeSuccessPostSourceWords (writeSuccessSourceBytes witness)) 17,
      writeSuccessPostWord (writeSuccessPostSourceWords (writeSuccessSourceBytes witness)) 18) =
    (take 69 (writeSuccessValues witness) !!! 17%nat, take 69 (writeSuccessValues witness) !!! 18%nat)).
  f_equal.
  all: apply pw_source_word_projection; [exact Hvalues | exact Hsource | exact Hbytes | lia].
Qed.
Print Assumptions pw_binding_descriptor_from_facts.

Lemma pw_binding_guard_from_existing_facts {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  length (writeSuccessValues witness) = 74%nat ->
  length (writeSuccessSourceBytes witness) = 720%nat ->
  IslarisMemory.bytes_of_u64s (writeSuccessValues witness) =
    take 592 (writeSuccessSourceBytes witness) ->
  writeSuccessPostTransactionDataFacts (writeSuccessFrameSp witness)
    (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness)
    (writeSuccessPostData witness) ->
  bv_unsigned (writeSuccessPostBytes1571c (writeSuccessPostData witness)).2 =
    Z.of_nat (length (pw_binding_payload witness)) ->
  pw_binding_declared witness = pw_binding_prefix witness
      (pw_binding_tail witness, pw_binding_payload witness, tt)ₗ /\
    ((writeSuccessPostBytes1571c (writeSuccessPostData witness)).1 = pw_binding_data witness /\
     bv_unsigned (pw_binding_size witness) = Z.of_nat (length (pw_binding_payload witness))).
Proof.
  intros Hvalues Hsource Hbytes Hfacts Hsize.
  have Hdescriptor := pw_binding_descriptor_from_facts witness Hvalues Hsource Hbytes Hfacts.
  have HloadedSize : bv_unsigned (pw_binding_size witness) =
      Z.of_nat (length (pw_binding_payload witness)).
  { rewrite Hdescriptor in Hsize. exact Hsize. }
  have Hpayloads := pw_binding_actual_payloads witness HloadedSize.
  have Hprefix := pw_binding_equivalence witness
    (drop 2 (writeSuccessExactPostPayloadsAt (pw_binding_descriptors witness) witness))
    Hpayloads Hdescriptor.
  split; [exact Hprefix |]. split; [rewrite Hdescriptor; reflexivity | exact HloadedSize].
Qed.
Print Assumptions pw_binding_guard_from_existing_facts.

Lemma write_success_post_withdrawals_optional_outcome {Decoded}
    (witness : writeSuccessNativeWitness Decoded)
    (Hvalues : length (writeSuccessValues witness) = 74%nat)
    (Hsource : length (writeSuccessSourceBytes witness) = 720%nat)
    (Hbytes : IslarisMemory.bytes_of_u64s (writeSuccessValues witness) =
      take 592 (writeSuccessSourceBytes witness))
    (Hfacts : writeSuccessPostTransactionDataFacts (writeSuccessFrameSp witness)
      (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness)
      (writeSuccessPostData witness)) :
  encoderOptionalU64Outcome
    (bv_to_little_endian 8 8 (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 15)) ++
     bv_to_little_endian 8 8 (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 16))) =
    writeSuccessPostOptional15700 (writeSuccessPostData witness).
Proof.
  have Hpayload := pw_source_word_projection (writeSuccessValues witness)
    (writeSuccessSourceBytes witness) 15 Hvalues Hsource Hbytes ltac:(lia).
  have Htag := pw_source_word_projection (writeSuccessValues witness)
    (writeSuccessSourceBytes witness) 16 Hvalues Hsource Hbytes ltac:(lia).
  rewrite lookup_total_take in Hpayload; [|lia].
  rewrite lookup_total_take in Htag; [|lia].
  have HpayloadValue : writeSuccessValueWord (writeSuccessValues witness) 15 =
    writeSuccessPostWord (writeSuccessPostSourceWords (writeSuccessSourceBytes witness)) 15.
  { rewrite Hpayload. unfold writeSuccessValueWord.
    have Hread := list_lookup_lookup_total_lt (writeSuccessValues witness) 15%nat ltac:(lia).
    by rewrite Hread. }
  have HtagValue : writeSuccessValueWord (writeSuccessValues witness) 16 =
    writeSuccessPostWord (writeSuccessPostSourceWords (writeSuccessSourceBytes witness)) 16.
  { rewrite Htag. unfold writeSuccessValueWord.
    have Hread := list_lookup_lookup_total_lt (writeSuccessValues witness) 16%nat ltac:(lia).
    by rewrite Hread. }
  rewrite HpayloadValue HtagValue.
  unfold writeSuccessPostTransactionDataFacts in Hfacts. destruct Hfacts as [Hoptional _].
  unfold writeSuccessOptionalU64Words in Hoptional.
  destruct Hoptional as [[Hzero Hnone] | [Hnonzero Hsome]].
  all: unfold encoderOptionalU64Outcome; cbn [bv_to_little_endian]; rewrite !lookup_cons.
  all: have HtagByte : Z_to_bv 8 (Z.land
    (bv_unsigned (writeSuccessPostWord (writeSuccessPostSourceWords (writeSuccessSourceBytes witness)) 16))
    (Z.ones 8)) = bv_extract 0 8
      (writeSuccessPostWord (writeSuccessPostSourceWords (writeSuccessSourceBytes witness)) 16)
    by (apply bv_eq; rewrite Z_to_bv_unsigned bv_extract_0_unsigned;
      rewrite <- (bv_wrap_land 8); apply bv_wrap_bv_wrap; lia).
  all: rewrite HtagByte.
  1: by rewrite Hzero Hnone /=.
  1: rewrite Hsome; case_decide; [contradiction |].
  1: f_equal.
  1: change (Z_to_bv 64 (little_endian_to_bv 8 (bv_to_little_endian 8 8
    (bv_unsigned (writeSuccessPostWord (writeSuccessPostSourceWords (writeSuccessSourceBytes witness)) 15)))) =
    writeSuccessPostWord (writeSuccessPostSourceWords (writeSuccessSourceBytes witness)) 15).
  1: apply Z_to_bv_little_endian_to_bv_to_little_endian; [lia | reflexivity].
Qed.
Print Assumptions write_success_post_withdrawals_optional_outcome.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsOptionalJunction.
Lemma write_success_post_withdrawals_optional_tail {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessExactPostWithdrawalsSecondTail witness =
    match writeSuccessPostOptional15700 (writeSuccessPostData witness) with
    | Some value => writeOutputEvents (writeSuccessEntrySp witness - (2000 + 25))%bv
        (BV 64 1) (WriteSuccessExactBooleanSpec.writeSuccessBooleanWordPayload (BV 64 1))
        (writeOutputEvents (writeSuccessEntrySp witness - (2000 + 16))%bv
          (BV 64 8) (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value)))
          (pw_binding_declared witness))
    | None => writeOutputEvents (writeSuccessEntrySp witness - (2000 + 9))%bv
        (BV 64 1) (WriteSuccessExactBooleanSpec.writeSuccessBooleanWordPayload (BV 64 0))
        (pw_binding_declared witness)
    end.
Proof.
  unfold writeSuccessExactPostWithdrawalsSecondTail, pw_binding_declared.
  rewrite /writeSuccessExactPostPayloadsAt exact_post_withdrawals_payloads.
  unfold pw_binding_descriptors, writeSuccessPost156e8Descriptors,
    writeSuccessPostFragments, writeSuccessExactObservation, writeSuccessNativeObservation.
  cbv beta iota zeta.
  destruct (writeSuccessPostOptional15700 (writeSuccessPostData witness)) as [value |] eqn:Hoptional.
  all: cbn.
  all: rewrite !app_length; cbn [length].
  1: lazymatch goal with |- context[drop (?a - ?b) ?payloads] => replace (a - b)%nat with 4%nat by lia end.
  2: lazymatch goal with |- context[drop (?a - ?b) ?payloads] => replace (a - b)%nat with 3%nat by lia end.
  all: cbn [drop].
  all: unfold writeSuccessFrameSp; bv_simplify; autorewrite with zesu_indices.
  all: rewrite ?(WriteSuccessExactBooleanSpec.writeSuccessBooleanWordPayload_encoder true)
    ?(WriteSuccessExactBooleanSpec.writeSuccessBooleanWordPayload_encoder false).
  all: unfold writeSuccessPrivateBytes.
  all: destruct (writeSuccessPostBytes1571c (writeSuccessPostData witness)) as [bytesData bytesSize].
  all: reflexivity.
Qed.
Print Assumptions write_success_post_withdrawals_optional_tail.
