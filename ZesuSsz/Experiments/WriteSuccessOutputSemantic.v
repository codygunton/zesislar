From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.

Import ListNotations.

Definition writeSuccessPublicBytes (bytes : list (bv 8)) : ByteString :=
  List.map bv_unsigned bytes.

(** The MMIO descriptor needs a memory snapshot to determine output bytes. *)
Definition writeOutputPayloadObservation
    (memoryAtWrite : bv 64 -> list (bv 8) -> Prop)
    (data size : bv 64) (bytes : ByteString) : Prop :=
  exists payload : list (bv 8),
    memoryAtWrite data payload /\
    bv_unsigned size = Z.of_nat (length payload) /\
    bytes = writeSuccessPublicBytes payload.

Definition WriteOutputDescriptor : Type := (bv 64 * bv 64)%type.

Definition writeOutputDescriptorEvents
    (descriptor : WriteOutputDescriptor) : list seq_label :=
  let '(data, size) := descriptor in
  [SWriteMem (BV 64 0x2401a0c0) data;
   SWriteMem (BV 64 0x2401a0c8) size].

Fixpoint writeOutputDescriptorsEvents
    (descriptors : list WriteOutputDescriptor) : list seq_label :=
  match descriptors with
  | [] => []
  | descriptor :: tail =>
      writeOutputDescriptorEvents descriptor ++
      writeOutputDescriptorsEvents tail
  end.

Fixpoint writeOutputDescriptorsSpec
    (descriptors : list WriteOutputDescriptor) (tail : spec) : spec :=
  match descriptors with
  | [] => tail
  | (data, size) :: descriptorTail =>
      writeOutputEvents data size
        (writeOutputDescriptorsSpec descriptorTail tail)
  end.

(** This relation supplies the liveness fact that prefix-closed [spec] lacks. *)
Definition writeOutputCompleteTrace
    (descriptors : list WriteOutputDescriptor)
    (tailEvents observed : list seq_label) : Prop :=
  observed = writeOutputDescriptorsEvents descriptors ++ tailEvents.

Lemma writeOutputCompleteTrace_allowed descriptors tail tailEvents observed :
  writeOutputCompleteTrace descriptors tailEvents observed ->
  tail tailEvents ->
  writeOutputDescriptorsSpec descriptors tail observed.
Proof.
  intros -> Htail. induction descriptors as [|[data size] descriptorTail IH].
  - exact Htail.
  - simpl. unfold writeOutputDescriptorEvents, writeOutputEvents, scons.
    right. eexists. split; first reflexivity. right.
    right. eexists. split; first reflexivity.
    destruct descriptorTail as [|descriptor rest].
    + right. exact Htail.
    + right. exact IH.
Qed.

(** The index distinguishes repeated writes from the same address. *)
Fixpoint writeOutputPayloadSnapshots
    (memoryAtWrite : nat -> bv 64 -> list (bv 8) -> Prop)
    (index : nat) (descriptors : list WriteOutputDescriptor)
    (payloads : list (list (bv 8))) : Prop :=
  match descriptors, payloads with
  | [], [] => True
  | (data, size) :: descriptorTail, payload :: payloadTail =>
      memoryAtWrite index data payload /\
      bv_unsigned size = Z.of_nat (length payload) /\
      writeOutputPayloadSnapshots memoryAtWrite (S index)
        descriptorTail payloadTail
  | _, _ => False
  end.

Definition writeOutputSequenceObservationFrom
    (memoryAtWrite : nat -> bv 64 -> list (bv 8) -> Prop)
    (index : nat) (descriptors : list WriteOutputDescriptor)
    (bytes : ByteString) : Prop :=
  exists payloads : list (list (bv 8)),
    writeOutputPayloadSnapshots memoryAtWrite index descriptors payloads /\
    bytes = writeSuccessPublicBytes (concat payloads).

Definition writeOutputSequenceObservation
    (memoryAtWrite : nat -> bv 64 -> list (bv 8) -> Prop)
    (descriptors : list WriteOutputDescriptor) (bytes : ByteString) : Prop :=
  writeOutputSequenceObservationFrom memoryAtWrite 0 descriptors bytes.

Lemma writeSuccessPublicBytes_app (left right : list (bv 8)) :
  writeSuccessPublicBytes (left ++ right) =
    writeSuccessPublicBytes left ++ writeSuccessPublicBytes right.
Proof. apply map_app. Qed.

Lemma writeOutputPayloadSnapshots_length memoryAtWrite index descriptors payloads :
  writeOutputPayloadSnapshots memoryAtWrite index descriptors payloads ->
  length descriptors = length payloads.
Proof.
  revert index payloads.
  induction descriptors as [|[data size] descriptorTail IH];
    intros index [|payload payloadTail]; simpl; try contradiction; auto.
  intros (_ & _ & Htail). f_equal. eapply IH. exact Htail.
Qed.

Lemma writeOutputPayloadSnapshots_app memoryAtWrite index
    leftDescriptors rightDescriptors leftPayloads rightPayloads :
  writeOutputPayloadSnapshots memoryAtWrite index leftDescriptors leftPayloads ->
  writeOutputPayloadSnapshots memoryAtWrite
    (index + length leftDescriptors) rightDescriptors rightPayloads ->
  writeOutputPayloadSnapshots memoryAtWrite index
    (leftDescriptors ++ rightDescriptors) (leftPayloads ++ rightPayloads).
Proof.
  revert index leftPayloads.
  induction leftDescriptors as [|[data size] descriptorTail IH].
  - intros index [|payload payloadTail] Hleft Hright; simpl in *.
    + replace (index + 0)%nat with index in Hright by lia.
      exact Hright.
    + contradiction.
  - intros index [|payload payloadTail] Hleft Hright; simpl in *.
    + contradiction.
    + destruct Hleft as (Hmemory & Hsize & Htail).
      repeat split; try assumption.
      apply IH; [exact Htail |].
      replace (S index + length descriptorTail)%nat
        with (index + S (length descriptorTail))%nat by lia.
      exact Hright.
Qed.

Lemma writeOutputSequenceObservationFrom_app memoryAtWrite index
    leftDescriptors rightDescriptors leftBytes rightBytes :
  writeOutputSequenceObservationFrom memoryAtWrite index
      leftDescriptors leftBytes ->
  writeOutputSequenceObservationFrom memoryAtWrite
      (index + length leftDescriptors) rightDescriptors rightBytes ->
  writeOutputSequenceObservationFrom memoryAtWrite index
      (leftDescriptors ++ rightDescriptors) (leftBytes ++ rightBytes).
Proof.
  intros (leftPayloads & Hleft & ->) (rightPayloads & Hright & ->).
  exists (leftPayloads ++ rightPayloads). split.
  - eapply writeOutputPayloadSnapshots_app; eassumption.
  - rewrite concat_app writeSuccessPublicBytes_app. reflexivity.
Qed.

Lemma writeOutputSequenceObservationFrom_empty memoryAtWrite index :
  writeOutputSequenceObservationFrom memoryAtWrite index [] [].
Proof. exists []. split; reflexivity. Qed.

Lemma writeOutputSequenceObservationFrom_singleton memoryAtWrite index
    data size bytes :
  writeOutputPayloadObservation (memoryAtWrite index) data size bytes ->
  writeOutputSequenceObservationFrom memoryAtWrite index [(data, size)] bytes.
Proof.
  intros (payload & Hmemory & Hsize & ->).
  exists [payload]. split.
  - simpl. repeat split; assumption.
  - simpl. rewrite app_nil_r. reflexivity.
Qed.

(** [scons] is prefix closed, so the event specification permits no events. *)
Lemma write_output_events_accept_empty (data size : bv 64) (tail : spec) :
  writeOutputEvents data size tail [].
Proof. unfold writeOutputEvents, scons. auto. Qed.

Lemma write_output_events_accept_descriptor_prefix
    (data size : bv 64) (tail : spec) :
  writeOutputEvents data size tail
    [SWriteMem (BV 64 0x2401a0c0) data;
     SWriteMem (BV 64 0x2401a0c8) size].
Proof. unfold writeOutputEvents, scons. naive_solver. Qed.

Lemma write_output_payload_observation
    (memoryAtWrite : bv 64 -> list (bv 8) -> Prop)
    (data : bv 64) (payload : list (bv 8))
    (Hlength : (length payload < 2 ^ 64)%nat)
    (Hmemory : memoryAtWrite data payload) :
  writeOutputPayloadObservation memoryAtWrite data
    (Z_to_bv 64 (Z.of_nat (length payload)))
    (writeSuccessPublicBytes payload).
Proof.
  exists payload. split; [exact Hmemory |].
  split; [|reflexivity].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  split; [lia |].
  change (Z.of_nat (length payload) < 2 ^ 64)%Z.
  apply Nat2Z.inj_lt in Hlength.
  rewrite Nat2Z.inj_pow in Hlength. exact Hlength.
Qed.
