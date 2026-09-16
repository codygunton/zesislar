Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputDescriptors.

Import ListNotations.

(**
  This file describes the output calls after the transaction loop.
  The trace call boundaries are 0x156e8, 0x1573c, 0x158e0,
  0x15930, 0x15960, and 0x159d8.  The CFG back edge at 0x158d4
  is represented by [writeSuccessHashesDescriptors].
 *)

Record WriteSuccessPostTransactionData : Type := {
  writeSuccessPostOptional15700 : option (bv 64);
  writeSuccessPostBytes1571c : WriteOutputDescriptor;
  writeSuccessPostBytes1571cPayload : list (bv 8);
  writeSuccessPostHashesCount : nat;
  writeSuccessPostHashesPayload : list (bv 8);
  writeSuccessPostBytes158e0 : WriteOutputDescriptor;
  writeSuccessPostBytes158e0Payload : list (bv 8);
  writeSuccessPostBytes158f0 : WriteOutputDescriptor;
  writeSuccessPostBytes158f0Payload : list (bv 8);
  writeSuccessPostBytes15900 : WriteOutputDescriptor;
  writeSuccessPostBytes15900Payload : list (bv 8);
  writeSuccessPostBytes15910 : WriteOutputDescriptor;
  writeSuccessPostBytes15910Payload : list (bv 8);
  writeSuccessPostBytes15920 : WriteOutputDescriptor;
  writeSuccessPostBytes15920Payload : list (bv 8);
  writeSuccessPostByteLists15930 : list ByteListItem;
  writeSuccessPostByteLists15940 : list ByteListItem;
  writeSuccessPostByteLists15950 : list ByteListItem;
  writeSuccessPostConditional1596c : option WriteOutputDescriptor;
  writeSuccessPostConditional1596cPayload : option (list (bv 8));
  writeSuccessPostOptional159b0 : option (bv 64);
  writeSuccessPostOptional159bc : option (bv 64);
  writeSuccessPostByteLists159c8 : list ByteListItem
}.

Definition writeSuccessPost159d8Descriptors : list WriteOutputDescriptor := [].

Definition writeSuccessPost159d8Events (tail : spec) : spec := tail.

Lemma writeSuccessPost159d8Descriptors_spec tail :
  writeOutputDescriptorsSpec writeSuccessPost159d8Descriptors tail =
  writeSuccessPost159d8Events tail.
Proof. reflexivity. Qed.

Definition writeSuccessPost159c8Descriptors sp data :=
  writeSuccessByteListsDescriptors sp
    (writeSuccessPostByteLists159c8 data).

Definition writeSuccessPost159c8Events sp data tail :=
  writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
    (byteListItemEvents (sp - BV 64 32)%bv
      (writeSuccessPostByteLists159c8 data) tail).

Lemma writeSuccessPost159c8Descriptors_spec sp data tail :
  writeOutputDescriptorsSpec (writeSuccessPost159c8Descriptors sp data) tail =
  writeSuccessPost159c8Events sp data tail.
Proof. apply writeSuccessByteListsDescriptors_spec. Qed.

Definition writeSuccessPost159bcDescriptors sp data :=
  writeSuccessOptionalU64Descriptors sp
    (writeSuccessPostOptional159bc data) ++
  writeSuccessPost159c8Descriptors sp data.

Definition writeSuccessPost159bcEvents sp data tail :=
  writeSuccessOptionalU64Events sp (writeSuccessPostOptional159bc data)
    (writeSuccessPost159c8Events sp data tail).

Lemma writeSuccessPost159bcDescriptors_spec sp data tail :
  writeOutputDescriptorsSpec (writeSuccessPost159bcDescriptors sp data) tail =
  writeSuccessPost159bcEvents sp data tail.
Proof.
  unfold writeSuccessPost159bcDescriptors, writeSuccessPost159bcEvents.
  rewrite writeOutputDescriptorsSpec_app.
  rewrite writeSuccessOptionalU64Descriptors_spec.
  rewrite writeSuccessPost159c8Descriptors_spec. reflexivity.
Qed.

Definition writeSuccessPost159b0Descriptors sp data :=
  writeSuccessOptionalU64Descriptors sp
    (writeSuccessPostOptional159b0 data) ++
  writeSuccessPost159bcDescriptors sp data.

Definition writeSuccessPost159b0Events sp data tail :=
  writeSuccessOptionalU64Events sp (writeSuccessPostOptional159b0 data)
    (writeSuccessPost159bcEvents sp data tail).

Lemma writeSuccessPost159b0Descriptors_spec sp data tail :
  writeOutputDescriptorsSpec (writeSuccessPost159b0Descriptors sp data) tail =
  writeSuccessPost159b0Events sp data tail.
Proof.
  unfold writeSuccessPost159b0Descriptors, writeSuccessPost159b0Events.
  rewrite writeOutputDescriptorsSpec_app.
  rewrite writeSuccessOptionalU64Descriptors_spec.
  rewrite writeSuccessPost159bcDescriptors_spec. reflexivity.
Qed.

Definition writeSuccessPost159a0Descriptors sp data :=
  [((sp - BV 64 16)%bv, BV 64 8)] ++
  writeSuccessPost159b0Descriptors sp data.

Definition writeSuccessPost159a0Events sp data tail :=
  writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPost159b0Events sp data tail).

Lemma writeSuccessPost159a0Descriptors_spec sp data tail :
  writeOutputDescriptorsSpec (writeSuccessPost159a0Descriptors sp data) tail =
  writeSuccessPost159a0Events sp data tail.
Proof.
  unfold writeSuccessPost159a0Descriptors, writeSuccessPost159a0Events.
  rewrite writeOutputDescriptorsSpec_app.
  simpl. rewrite writeSuccessPost159b0Descriptors_spec. reflexivity.
Qed.

Definition writeSuccessPost1596cDescriptors sp data :=
  [((sp - BV 64 9)%bv, BV 64 1)] ++
  match writeSuccessPostConditional1596c data with
  | None => []
  | Some bytes => writeSuccessBytesDescriptors sp (fst bytes) (snd bytes)
  end ++ writeSuccessPost159a0Descriptors sp data.

Definition writeSuccessPost1596cEvents sp data tail :=
  writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
    (match writeSuccessPostConditional1596c data with
     | None => writeSuccessPost159a0Events sp data tail
     | Some bytes =>
         writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
           (writeOutputEventsAny (fst bytes) (snd bytes)
             (writeSuccessPost159a0Events sp data tail))
     end).

Lemma writeSuccessPost1596cDescriptors_spec sp data tail :
  writeOutputDescriptorsSpec (writeSuccessPost1596cDescriptors sp data) tail =
  writeSuccessPost1596cEvents sp data tail.
Proof.
  unfold writeSuccessPost1596cDescriptors, writeSuccessPost1596cEvents.
  destruct (writeSuccessPostConditional1596c data) as [bytes|].
  - rewrite !writeOutputDescriptorsSpec_app.
    rewrite writeSuccessBytesDescriptors_spec.
    cbn [writeOutputDescriptorsSpec].
    rewrite !writeSuccessOptionalU64Descriptors_spec.
    rewrite writeSuccessPost159c8Descriptors_spec. reflexivity.
  - rewrite !writeOutputDescriptorsSpec_app.
    cbn [writeOutputDescriptorsSpec].
    rewrite !writeSuccessOptionalU64Descriptors_spec.
    rewrite writeSuccessPost159c8Descriptors_spec. reflexivity.
Qed.

Definition writeSuccessPost15960Descriptors sp data :=
  [((sp - BV 64 16)%bv, BV 64 8)] ++
  writeSuccessPost1596cDescriptors sp data.

Definition writeSuccessPost15960Events sp data tail :=
  writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPost1596cEvents sp data tail).

Lemma writeSuccessPost15960Descriptors_spec sp data tail :
  writeOutputDescriptorsSpec (writeSuccessPost15960Descriptors sp data) tail =
  writeSuccessPost15960Events sp data tail.
Proof.
  unfold writeSuccessPost15960Descriptors, writeSuccessPost15960Events.
  rewrite writeOutputDescriptorsSpec_app.
  rewrite writeSuccessPost1596cDescriptors_spec. reflexivity.
Qed.

Definition writeSuccessPost15930Descriptors sp data :=
  writeSuccessByteListsDescriptors sp
    (writeSuccessPostByteLists15930 data) ++
  writeSuccessByteListsDescriptors sp
    (writeSuccessPostByteLists15940 data) ++
  writeSuccessByteListsDescriptors sp
    (writeSuccessPostByteLists15950 data) ++
  writeSuccessPost15960Descriptors sp data.

Definition writeSuccessPost15930Events sp data tail :=
  writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
    (byteListItemEvents (sp - BV 64 32)%bv
      (writeSuccessPostByteLists15930 data)
      (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
        (byteListItemEvents (sp - BV 64 32)%bv
          (writeSuccessPostByteLists15940 data)
          (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
            (byteListItemEvents (sp - BV 64 32)%bv
              (writeSuccessPostByteLists15950 data)
              (writeSuccessPost15960Events sp data tail)))))).

Lemma writeSuccessPost15930Descriptors_spec sp data tail :
  writeOutputDescriptorsSpec (writeSuccessPost15930Descriptors sp data) tail =
  writeSuccessPost15930Events sp data tail.
Proof.
  unfold writeSuccessPost15930Descriptors, writeSuccessPost15930Events.
  rewrite !writeOutputDescriptorsSpec_app.
  rewrite !writeSuccessByteListsDescriptors_spec.
  destruct (writeSuccessPostConditional1596c data) as [bytes|] eqn:Hconditional.
  - cbn [writeOutputDescriptorsSpec].
    rewrite !writeSuccessOptionalU64Descriptors_spec.
    rewrite writeSuccessBytesDescriptors_spec.
    unfold writeSuccessPost15960Events, writeSuccessPost1596cEvents.
    rewrite Hconditional. reflexivity.
  - cbn [writeOutputDescriptorsSpec].
    rewrite !writeSuccessOptionalU64Descriptors_spec.
    unfold writeSuccessPost15960Events, writeSuccessPost1596cEvents.
    rewrite Hconditional. reflexivity.
Qed.

Definition writeSuccessPost158e0Descriptors sp data :=
  writeSuccessBytesDescriptors sp
    (fst (writeSuccessPostBytes158e0 data))
    (snd (writeSuccessPostBytes158e0 data)) ++
  writeSuccessBytesDescriptors sp
    (fst (writeSuccessPostBytes158f0 data))
    (snd (writeSuccessPostBytes158f0 data)) ++
  writeSuccessBytesDescriptors sp
    (fst (writeSuccessPostBytes15900 data))
    (snd (writeSuccessPostBytes15900 data)) ++
  writeSuccessBytesDescriptors sp
    (fst (writeSuccessPostBytes15910 data))
    (snd (writeSuccessPostBytes15910 data)) ++
  writeSuccessBytesDescriptors sp
    (fst (writeSuccessPostBytes15920 data))
    (snd (writeSuccessPostBytes15920 data)) ++
  writeSuccessPost15930Descriptors sp data.

Definition writeSuccessPost158e0Events sp data tail :=
  let bytesEvents bytes rest :=
    writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
      (writeOutputEventsAny (fst bytes) (snd bytes) rest) in
  bytesEvents (writeSuccessPostBytes158e0 data)
    (bytesEvents (writeSuccessPostBytes158f0 data)
      (bytesEvents (writeSuccessPostBytes15900 data)
        (bytesEvents (writeSuccessPostBytes15910 data)
          (bytesEvents (writeSuccessPostBytes15920 data)
            (writeSuccessPost15930Events sp data tail))))).

Lemma writeSuccessPost158e0Descriptors_spec sp data tail :
  writeOutputDescriptorsSpec (writeSuccessPost158e0Descriptors sp data) tail =
  writeSuccessPost158e0Events sp data tail.
Proof.
  unfold writeSuccessPost158e0Descriptors, writeSuccessPost158e0Events.
  do 5 rewrite writeOutputDescriptorsSpec_app.
  do 5 rewrite writeSuccessBytesDescriptors_spec.
  rewrite writeSuccessPost15930Descriptors_spec. reflexivity.
Qed.

Definition writeSuccessPost1573cDescriptors sp data :=
  writeSuccessHashesDescriptors sp (writeSuccessPostHashesCount data) ++
  writeSuccessPost158e0Descriptors sp data.

Definition writeSuccessPost1573cEvents sp data tail :=
  writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessHashesEvents sp (writeSuccessPostHashesCount data)
      (writeSuccessPost158e0Events sp data tail)).

Lemma writeSuccessPost1573cDescriptors_spec sp data tail :
  writeOutputDescriptorsSpec (writeSuccessPost1573cDescriptors sp data) tail =
  writeSuccessPost1573cEvents sp data tail.
Proof.
  unfold writeSuccessPost1573cDescriptors, writeSuccessPost1573cEvents.
  rewrite writeOutputDescriptorsSpec_app.
  rewrite writeSuccessHashesDescriptors_spec.
  rewrite writeSuccessPost158e0Descriptors_spec. reflexivity.
Qed.

Definition writeSuccessPost156e8Descriptors sp data :=
  [((sp - BV 64 16)%bv, BV 64 8)] ++
  [((sp - BV 64 16)%bv, BV 64 8)] ++
  writeSuccessOptionalU64Descriptors sp
    (writeSuccessPostOptional15700 data) ++
  writeSuccessBytesDescriptors sp
    (fst (writeSuccessPostBytes1571c data))
    (snd (writeSuccessPostBytes1571c data)) ++
  [((sp + BV 64 1000)%bv, BV 64 32)] ++
  writeSuccessPost1573cDescriptors sp data.

Definition writeSuccessPost156e8Events sp data tail :=
  writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
    (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessOptionalU64Events sp (writeSuccessPostOptional15700 data)
        (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
          (writeOutputEventsAny (fst (writeSuccessPostBytes1571c data))
            (snd (writeSuccessPostBytes1571c data))
            (writeOutputEventsAny (sp + BV 64 1000)%bv (BV 64 32)
              (writeSuccessPost1573cEvents sp data tail)))))).

Lemma writeSuccessPost156e8Descriptors_spec sp data tail :
  writeOutputDescriptorsSpec (writeSuccessPost156e8Descriptors sp data) tail =
  writeSuccessPost156e8Events sp data tail.
Proof.
  unfold writeSuccessPost156e8Descriptors, writeSuccessPost156e8Events.
  do 5 rewrite writeOutputDescriptorsSpec_app.
  rewrite writeSuccessOptionalU64Descriptors_spec.
  rewrite writeSuccessBytesDescriptors_spec.
  rewrite writeSuccessPost1573cDescriptors_spec. reflexivity.
Qed.

Definition writeSuccessAfterTransactionsDescriptors sp withdrawalsCount data :=
  writeSuccessWithdrawalsDescriptors sp withdrawalsCount ++
  writeSuccessPost156e8Descriptors sp data.

Definition writeSuccessAfterTransactionsEvents sp withdrawalsCount data tail :=
  writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessWithdrawalsEvents sp withdrawalsCount
      (writeSuccessPost156e8Events sp data tail)).

Lemma writeSuccessAfterTransactionsDescriptors_spec sp withdrawalsCount data tail :
  writeOutputDescriptorsSpec
      (writeSuccessAfterTransactionsDescriptors sp withdrawalsCount data) tail =
  writeSuccessAfterTransactionsEvents sp withdrawalsCount data tail.
Proof.
  unfold writeSuccessAfterTransactionsDescriptors,
    writeSuccessAfterTransactionsEvents.
  rewrite writeOutputDescriptorsSpec_app.
  rewrite writeSuccessWithdrawalsDescriptors_spec.
  rewrite writeSuccessPost156e8Descriptors_spec. reflexivity.
Qed.
