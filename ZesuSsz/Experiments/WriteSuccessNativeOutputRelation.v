From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Experiments.WriteSuccessNativeContract.
Require Import ZesuSsz.Experiments.WriteSuccessOutputDescriptors.
Require Import ZesuSsz.Experiments.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Experiments.WriteSuccessToLoadWithFrame.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessValueBlock.

Import ListNotations.

(** The header descriptor sequence starts with the caller's fixed tag. *)
Definition writeSuccessNativeDescriptors {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
    list WriteOutputDescriptor :=
  writeSuccessMainDescriptors
    (writeSuccessFrameSp witness)
    (writeSuccessValues witness)
    (writeSuccessTransactions witness).

Lemma writeSuccessNativeDescriptors_spec {Decoded}
    (witness : writeSuccessNativeWitness Decoded) tail :
  writeOutputDescriptorsSpec (writeSuccessNativeDescriptors witness) tail =
  writeSuccessHeaderEvents (writeSuccessFrameSp witness)
    (writeSuccessValueEvents (writeSuccessFrameSp witness)
      (writeSuccessValues witness)
      (writeSuccessTransactionsEvents (writeSuccessFrameSp witness)
        (writeSuccessTransactions witness) tail)).
Proof.
  unfold writeSuccessNativeDescriptors.
  rewrite writeSuccessMainDescriptors_spec. reflexivity.
Qed.

(** The write index distinguishes repeated writes from the same stack slot. *)
Definition writeSuccessMemoryOutputRelation {Decoded}
    (memoryAtWrite : nat -> bv 64 -> list (bv 8) -> Prop) :
    WriteSuccessOutputRelation Decoded :=
  fun _ witness bytes =>
    writeOutputSequenceObservation memoryAtWrite
      (writeSuccessNativeDescriptors witness) bytes.

Definition writeSuccessMemorySemanticPremise {State Decoded}
    (model : Level1MachineModel State Decoded)
    (memoryAtWrite : nat -> bv 64 -> list (bv 8) -> Prop) : Prop :=
  forall args witness bytes,
    writeSuccessWitnessWellFormed args witness ->
    writeOutputSequenceObservation memoryAtWrite
      (writeSuccessNativeDescriptors witness) bytes ->
    decodeObservationSuccess State Decoded model bytes
      (successDecoded Decoded args).

Lemma writeSuccessMemorySemanticPremise_sound {State Decoded}
    (model : Level1MachineModel State Decoded)
    (memoryAtWrite : nat -> bv 64 -> list (bv 8) -> Prop) :
  writeSuccessMemorySemanticPremise model memoryAtWrite ->
  writeSuccessSemanticPremise model
    (writeSuccessMemoryOutputRelation memoryAtWrite).
Proof. intros Hsemantic args witness bytes. apply Hsemantic. Qed.
