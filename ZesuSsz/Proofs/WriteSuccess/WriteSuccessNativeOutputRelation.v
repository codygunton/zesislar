Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessToLoadWithFrame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.

Import ListNotations.

(** The sequence starts with the caller tag and ends with public keys. *)
Definition writeSuccessNativeDescriptors {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
    list WriteOutputDescriptor :=
  writeSuccessMainDescriptors
    (writeSuccessFrameSp witness)
    (writeSuccessValues witness)
    (writeSuccessTransactions witness) ++
  writeSuccessAfterTransactionsDescriptors
    (writeSuccessFrameSp witness)
    (writeSuccessWithdrawalsCount witness)
    (writeSuccessPostData witness).

Lemma writeSuccessNativeDescriptors_spec {Decoded}
    (witness : writeSuccessNativeWitness Decoded) tail :
  writeOutputDescriptorsSpec (writeSuccessNativeDescriptors witness) tail =
  writeSuccessHeaderEvents (writeSuccessFrameSp witness)
    (writeSuccessValueEvents (writeSuccessFrameSp witness)
      (writeSuccessValues witness)
      (writeSuccessTransactionsEvents (writeSuccessFrameSp witness)
        (writeSuccessTransactions witness)
        (writeSuccessAfterTransactionsEvents
          (writeSuccessFrameSp witness)
          (writeSuccessWithdrawalsCount witness)
          (writeSuccessPostData witness) tail))).
Proof.
  unfold writeSuccessNativeDescriptors.
  rewrite writeOutputDescriptorsSpec_app.
  rewrite writeSuccessMainDescriptors_spec.
  rewrite writeSuccessAfterTransactionsDescriptors_spec.
  reflexivity.
Qed.

(** The write index distinguishes repeated writes from the same stack slot. *)
Definition writeSuccessMemoryOutputRelation {Decoded}
    (memoryAtWrite : nat -> bv 64 -> list (bv 8) -> Prop) :
    WriteSuccessOutputRelation Decoded :=
  fun _ witness bytes =>
    writeOutputSequenceObservation memoryAtWrite
      (writeSuccessNativeDescriptors witness) bytes.

Definition writeSuccessMemorySemanticPremise {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop)
    (memoryAtWrite : nat -> bv 64 -> list (bv 8) -> Prop) : Prop :=
  forall args witness bytes,
    writeSuccessWitnessWellFormed args witness ->
    writeOutputSequenceObservation memoryAtWrite
      (writeSuccessNativeDescriptors witness) bytes ->
    allows args bytes.

Lemma writeSuccessMemorySemanticPremise_sound {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop)
    (memoryAtWrite : nat -> bv 64 -> list (bv 8) -> Prop) :
  writeSuccessMemorySemanticPremise allows memoryAtWrite ->
  writeSuccessSemanticPremise allows
    (writeSuccessMemoryOutputRelation memoryAtWrite).
Proof. intros Hsemantic args witness bytes. apply Hsemantic. Qed.

Print Assumptions writeSuccessMemorySemanticPremise_sound.

(** This sequence covers every output after the transaction loop, including
    withdrawals and the final public-key list. *)
Definition writeSuccessCompleteNativeDescriptors {Decoded}
    (witness : writeSuccessNativeWitness Decoded)
    (postData : WriteSuccessPostTransactionData) :
    list WriteOutputDescriptor :=
  writeSuccessMainDescriptors
    (writeSuccessFrameSp witness)
    (writeSuccessValues witness)
    (writeSuccessTransactions witness) ++
  writeSuccessAfterTransactionsDescriptors
    (writeSuccessFrameSp witness)
    (writeSuccessWithdrawalsCount witness) postData.

Lemma writeSuccessCompleteNativeDescriptors_spec {Decoded}
    (witness : writeSuccessNativeWitness Decoded)
    (postData : WriteSuccessPostTransactionData) tail :
  writeOutputDescriptorsSpec
      (writeSuccessCompleteNativeDescriptors witness postData) tail =
  writeSuccessHeaderEvents (writeSuccessFrameSp witness)
    (writeSuccessValueEvents (writeSuccessFrameSp witness)
      (writeSuccessValues witness)
      (writeSuccessTransactionsEvents (writeSuccessFrameSp witness)
        (writeSuccessTransactions witness)
        (writeSuccessAfterTransactionsEvents
          (writeSuccessFrameSp witness)
          (writeSuccessWithdrawalsCount witness) postData tail))).
Proof.
  unfold writeSuccessCompleteNativeDescriptors.
  rewrite writeOutputDescriptorsSpec_app.
  rewrite writeSuccessMainDescriptors_spec.
  rewrite writeSuccessAfterTransactionsDescriptors_spec.
  reflexivity.
Qed.

Definition writeSuccessCompleteMemoryOutputRelation {Decoded}
    (memoryAtWrite : nat -> bv 64 -> list (bv 8) -> Prop)
    (postDataOf : writeSuccessNativeWitness Decoded ->
      WriteSuccessPostTransactionData) :
    WriteSuccessOutputRelation Decoded :=
  fun _ witness bytes =>
    writeOutputSequenceObservation memoryAtWrite
      (writeSuccessCompleteNativeDescriptors witness (postDataOf witness))
      bytes.

Definition writeSuccessCompleteMemorySemanticPremise {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop)
    (memoryAtWrite : nat -> bv 64 -> list (bv 8) -> Prop)
    (postDataOf : writeSuccessNativeWitness Decoded ->
      WriteSuccessPostTransactionData) : Prop :=
  forall args witness bytes,
    writeSuccessWitnessWellFormed args witness ->
    writeOutputSequenceObservation memoryAtWrite
      (writeSuccessCompleteNativeDescriptors witness (postDataOf witness))
      bytes ->
    allows args bytes.

Lemma writeSuccessCompleteMemorySemanticPremise_sound {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop)
    (memoryAtWrite : nat -> bv 64 -> list (bv 8) -> Prop)
    (postDataOf : writeSuccessNativeWitness Decoded ->
      WriteSuccessPostTransactionData) :
  writeSuccessCompleteMemorySemanticPremise allows memoryAtWrite postDataOf ->
  writeSuccessSemanticPremise allows
    (writeSuccessCompleteMemoryOutputRelation memoryAtWrite postDataOf).
Proof. intros Hsemantic args witness bytes. apply Hsemantic. Qed.

Print Assumptions writeSuccessCompleteMemorySemanticPremise_sound.
