Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisMemory.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsSourceJunction.
From ZesuSsz.Proofs.WriteSuccess Require Import Interfaces WriteSuccessRepresentation WriteSuccessExactValueSpec WriteSuccessValueBlock WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.

Definition tailFieldsActivePayloads `{!islaG Sigma}
    (decodedBytes : list (bv 8))
    (data : WriteSuccessPostTransactionData) : iProp Sigma :=
  let tail := writeSuccessPostTailWords decodedBytes in
  (writeSuccessDescriptorResources (writeSuccessPostBytes158f0 data)
     (writeSuccessPostBytes158f0Payload data) ∗
   writeSuccessDescriptorResources (writeSuccessPostBytes15900 data)
     (writeSuccessPostBytes15900Payload data) ∗
   writeSuccessDescriptorResources (writeSuccessPostBytes15910 data)
     (writeSuccessPostBytes15910Payload data) ∗
   writeSuccessDescriptorResources (writeSuccessPostBytes15920 data)
     (writeSuccessPostBytes15920Payload data) ∗
   byteListItemResources (bv_unsigned (writeSuccessPostWord tail 0))
     (writeSuccessPostByteLists15930 data) ∗
   byteListItemResources (bv_unsigned (writeSuccessPostWord tail 2))
     (writeSuccessPostByteLists15940 data) ∗
   byteListItemResources (bv_unsigned (writeSuccessPostWord tail 4))
     (writeSuccessPostByteLists15950 data) ∗ True)%I.

Definition tailFieldsInactivePayloads `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (sourceBytes decodedBytes : list (bv 8))
    (data : WriteSuccessPostTransactionData) : iProp Sigma :=
  let source := writeSuccessPostSourceWords sourceBytes in
  let tail := writeSuccessPostTailWords decodedBytes in
  (writeSuccessDescriptorResources (writeSuccessPostBytes1571c data)
     (writeSuccessPostBytes1571cPayload data) ∗
   writeSuccessHashesResources (writeSuccessPostWord source 74)
     (writeSuccessPostHashesCount data) (writeSuccessPostHashesPayload data) ∗
   writeSuccessOptionalDescriptorResources
     (writeSuccessPostConditional1596c data)
     (writeSuccessPostConditional1596cPayload data) ∗
   byteListItemResources (bv_unsigned (writeSuccessPostWord tail 14))
     (writeSuccessPostByteLists159c8 data) ∗
   ⌜writeSuccessPostTransactionDataFacts sp sourceBytes decodedBytes data⌝ ∗ True)%I.

Lemma tailFieldsActivePayloads_unfold `{!islaG Sigma}
    (decodedBytes : list (bv 8)) (data : WriteSuccessPostTransactionData) :
  tailFieldsActivePayloads decodedBytes data ⊣⊢
  let tail := writeSuccessPostTailWords decodedBytes in
  (writeSuccessDescriptorResources (writeSuccessPostBytes158f0 data)
     (writeSuccessPostBytes158f0Payload data) ∗
   writeSuccessDescriptorResources (writeSuccessPostBytes15900 data)
     (writeSuccessPostBytes15900Payload data) ∗
   writeSuccessDescriptorResources (writeSuccessPostBytes15910 data)
     (writeSuccessPostBytes15910Payload data) ∗
   writeSuccessDescriptorResources (writeSuccessPostBytes15920 data)
     (writeSuccessPostBytes15920Payload data) ∗
   byteListItemResources (bv_unsigned (writeSuccessPostWord tail 0))
     (writeSuccessPostByteLists15930 data) ∗
   byteListItemResources (bv_unsigned (writeSuccessPostWord tail 2))
     (writeSuccessPostByteLists15940 data) ∗
   byteListItemResources (bv_unsigned (writeSuccessPostWord tail 4))
     (writeSuccessPostByteLists15950 data) ∗ True)%I.
Proof. done. Qed.

Lemma tail_fields_payload_junction `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (sourceBytes decodedBytes : list (bv 8))
    (data : WriteSuccessPostTransactionData) :
  writeSuccessPostTransactionDataResources sp sourceBytes decodedBytes data ⊣⊢
  (writeSuccessDescriptorResources (writeSuccessPostBytes158e0 data)
     (writeSuccessPostBytes158e0Payload data) ∗
   tailFieldsActivePayloads decodedBytes data ∗
   tailFieldsInactivePayloads sp sourceBytes decodedBytes data)%I.
Proof.
  rewrite /writeSuccessPostTransactionDataResources /tailFieldsActivePayloads /tailFieldsInactivePayloads /=.
  iSplit; [iIntros "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12)" | iIntros "(H2 & (H3 & H4 & H5 & H6 & H7 & H8 & H9 & _) & H0 & H1 & H10 & H11 & H12 & _)"]; iFrame.
Qed.
Lemma tailFieldsInactivePayloads_unfold `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (sourceBytes decodedBytes : list (bv 8))
    (data : WriteSuccessPostTransactionData) :
  tailFieldsInactivePayloads sp sourceBytes decodedBytes data ⊣⊢
  let source := writeSuccessPostSourceWords sourceBytes in
  let tail := writeSuccessPostTailWords decodedBytes in
  (writeSuccessDescriptorResources (writeSuccessPostBytes1571c data)
     (writeSuccessPostBytes1571cPayload data) ∗
   writeSuccessHashesResources (writeSuccessPostWord source 74)
     (writeSuccessPostHashesCount data) (writeSuccessPostHashesPayload data) ∗
   writeSuccessOptionalDescriptorResources
     (writeSuccessPostConditional1596c data)
     (writeSuccessPostConditional1596cPayload data) ∗
   byteListItemResources (bv_unsigned (writeSuccessPostWord tail 14))
     (writeSuccessPostByteLists159c8 data) ∗
   ⌜writeSuccessPostTransactionDataFacts sp sourceBytes decodedBytes data⌝ ∗ True)%I.
Proof. done. Qed.

Global Opaque tailFieldsActivePayloads.
Global Opaque tailFieldsInactivePayloads.

Print Assumptions tail_fields_payload_junction.

Definition tailFieldsBytesCallEvents (sp : bv 64)
    (descriptor : WriteOutputDescriptor) (payload : list (bv 8))
    (tail : spec) : spec :=
  writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned descriptor.2)))
    (writeOutputEvents descriptor.1 descriptor.2 payload tail).

Definition tailFieldsByteListsCallEvents (sp : bv 64)
    (items : list ByteListItem) (tail : spec) : spec :=
  writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64 (Z.of_nat (length items))))
    (byteListItemPayloadEvents (sp - BV 64 32)%bv items tail).

Definition tailFieldsFirstSegmentEvents (sp : bv 64)
    (decodedBytes : list (bv 8)) (data : WriteSuccessPostTransactionData)
    (tail : spec) : spec :=
  tailFieldsBytesCallEvents sp (writeSuccessPostBytes158e0 data)
    (writeSuccessPostBytes158e0Payload data)
  (tailFieldsBytesCallEvents sp (writeSuccessPostBytes158f0 data)
    (writeSuccessPostBytes158f0Payload data)
  (tailFieldsBytesCallEvents sp (writeSuccessPostBytes15900 data)
    (writeSuccessPostBytes15900Payload data)
  (tailFieldsBytesCallEvents sp (writeSuccessPostBytes15910 data)
    (writeSuccessPostBytes15910Payload data)
  (tailFieldsBytesCallEvents sp (writeSuccessPostBytes15920 data)
    (writeSuccessPostBytes15920Payload data)
  (tailFieldsByteListsCallEvents sp (writeSuccessPostByteLists15930 data)
  (tailFieldsByteListsCallEvents sp (writeSuccessPostByteLists15940 data)
  (tailFieldsByteListsCallEvents sp (writeSuccessPostByteLists15950 data)
  (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64
      (bv_unsigned (writeSuccessPostWord (writeSuccessPostTailWords decodedBytes) 6))))
    tail)))))))).

Definition tailFieldsCallerInactive `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  ((bv_unsigned sp - 80) ↦ₘ? 32 ∗
   bv_unsigned sp ↦ₘ? 8 ∗
   writeSuccessExactCopiedTailWords sp (writeSuccessDecodedBytes witness) ∗
   writeSuccessExactValueMemory sp values ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ writeSuccessPayload witness ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   tailFieldsInactivePayloads sp (writeSuccessSourceBytes witness)
     (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) [] (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ True)%I.


Global Instance : LithiumUnfold (@tailFieldsCallerInactive) := I.

Lemma tail_fields_caller_payload_junction `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  tailFieldsCallerUntouched args witness ⊣⊢
  (writeSuccessDescriptorResources
     (writeSuccessPostBytes158e0 (writeSuccessPostData witness))
     (writeSuccessPostBytes158e0Payload (writeSuccessPostData witness)) ∗
   tailFieldsActivePayloads (writeSuccessDecodedBytes witness)
     (writeSuccessPostData witness) ∗
   tailFieldsCallerInactive args witness ∗ True)%I.
Proof.
  rewrite tailFieldsCallerUntouched_unfold /tailFieldsCallerInactive tail_fields_payload_junction /=.
  iSplit; [iIntros "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & (Hfirst & Hactive & Hremaining) & H11 & H12 & H13 & _)" | iIntros "(Hfirst & Hactive & (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & Hremaining & H11 & H12 & H13 & _) & _)"]; iFrame.
Qed.

Print Assumptions tail_fields_caller_payload_junction.

Require Import ZesuSsz.Automation.PackedWordValues.
Definition tailFieldsDescriptorWords (post : WriteSuccessPostTransactionData) : list (bv 64) :=
  [ (writeSuccessPostBytes158f0 post).1; (writeSuccessPostBytes158f0 post).2;
    (writeSuccessPostBytes15900 post).1; (writeSuccessPostBytes15900 post).2;
    (writeSuccessPostBytes15910 post).1; (writeSuccessPostBytes15910 post).2;
    (writeSuccessPostBytes15920 post).1; (writeSuccessPostBytes15920 post).2 ].

Lemma tail_fields_descriptor_words (sp : bv 64)
    (sourceBytes decodedBytes : list (bv 8))
    (post : WriteSuccessPostTransactionData) :
  length sourceBytes = 720%nat ->
  writeSuccessPostTransactionDataFacts sp sourceBytes decodedBytes post ->
  u64s_of_bytes 8 (take 64 (drop 624 sourceBytes)) = tailFieldsDescriptorWords post.
Proof.
intros Hlength Hfacts; have Hdescriptors : writeSuccessPostBytes158f0 post = writeSuccessPostDescriptor (writeSuccessPostSourceWords sourceBytes) 78 79 /\ writeSuccessPostBytes15900 post = writeSuccessPostDescriptor (writeSuccessPostSourceWords sourceBytes) 80 81 /\ writeSuccessPostBytes15910 post = writeSuccessPostDescriptor (writeSuccessPostSourceWords sourceBytes) 82 83 /\ writeSuccessPostBytes15920 post = writeSuccessPostDescriptor (writeSuccessPostSourceWords sourceBytes) 84 85 by rewrite /writeSuccessPostTransactionDataFacts in Hfacts; naive_solver.
destruct Hdescriptors as (H0 & H1 & H2 & H3); rewrite /tailFieldsDescriptorWords H0 H1 H2 H3 /writeSuccessPostDescriptor /writeSuccessPostWord /writeSuccessPostSourceWords; cbv beta iota delta [fst snd].
apply (list_eq_same_length _ _ 8); [reflexivity|rewrite /u64s_of_bytes length_fmap length_reshape length_replicate; reflexivity|]; intros i x y Hi Hx Hy.
rewrite zesu_packed_u64_lookup in Hx; [|rewrite length_take length_drop; lia|exact Hi]; rewrite zesu_packed_window_take_drop in Hx; [|lia]; inversion Hx; subst x.
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia; rewrite !zesu_packed_u64_lookup in Hy; try lia; cbv beta iota delta [default list_lookup] in Hy; injection Hy as <-; reflexivity.
Qed.
Print Assumptions tail_fields_descriptor_words.
