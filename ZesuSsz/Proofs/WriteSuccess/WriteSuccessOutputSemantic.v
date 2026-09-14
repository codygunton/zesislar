Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.

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

Definition writeSuccessPrivateBytes (bytes : ByteString) : list (bv 8) :=
  map (Z_to_bv 8) bytes.

(** This specification pairs every output descriptor with one fixed payload.
    A length mismatch rejects the trace. *)
Fixpoint writeOutputPayloadsSpec
    (descriptors : list WriteOutputDescriptor)
    (payloads : list (list (bv 8))) (tail : spec) : spec :=
  match descriptors, payloads with
  | [], [] => tail
  | (data, size) :: descriptorTail, payload :: payloadTail =>
      writeOutputEvents data size payload
        (writeOutputPayloadsSpec descriptorTail payloadTail tail)
  | _, _ => fun _ => False
  end.

Lemma writeOutputPayloadsSpec_app leftDescriptors rightDescriptors
    leftPayloads rightPayloads tail :
  length leftDescriptors = length leftPayloads ->
  writeOutputPayloadsSpec
    (leftDescriptors ++ rightDescriptors) (leftPayloads ++ rightPayloads) tail =
  writeOutputPayloadsSpec leftDescriptors leftPayloads
    (writeOutputPayloadsSpec rightDescriptors rightPayloads tail).
Proof.
  revert leftPayloads. induction leftDescriptors as [|[data size] descriptors IH];
    intros [|payload payloads] Hlength; simpl in *; try lia; [reflexivity|].
  rewrite IH; [reflexivity|lia].
Qed.

Lemma writeSuccessPublicPrivateBytes bytes :
  Forall writeSuccessByte bytes ->
  writeSuccessPublicBytes (writeSuccessPrivateBytes bytes) = bytes.
Proof.
  intros Hvalid. induction Hvalid as [|byte bytes Hbyte Hbytes IH]; simpl.
  - reflexivity.
  - f_equal; [unfold writeSuccessByte in Hbyte; bv_solve|exact IH].
Qed.

Definition writeOutputDescriptorEvents
    (snapshot : seq_snapshot)
    (descriptor : WriteOutputDescriptor) : list seq_label :=
  let '(data, size) := descriptor in
  [SWriteMem (BV 64 (machineOutputAddress defaultMap)) data snapshot;
   SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size snapshot].

Fixpoint writeOutputDescriptorsEvents
    (snapshot : seq_snapshot)
    (descriptors : list WriteOutputDescriptor) : list seq_label :=
  match descriptors with
  | [] => []
  | descriptor :: tail =>
      writeOutputDescriptorEvents snapshot descriptor ++
      writeOutputDescriptorsEvents snapshot tail
  end.

Lemma writeOutputDescriptorsEvents_app snapshot left right :
  writeOutputDescriptorsEvents snapshot (left ++ right) =
    writeOutputDescriptorsEvents snapshot left ++
    writeOutputDescriptorsEvents snapshot right.
Proof.
  induction left as [|descriptor tail IH]; simpl; [reflexivity |].
  rewrite IH app_assoc. reflexivity.
Qed.

Fixpoint writeOutputDescriptorsSpec
    (descriptors : list WriteOutputDescriptor) (tail : spec) : spec :=
  match descriptors with
  | [] => tail
  | (data, size) :: descriptorTail =>
      writeOutputEventsAny data size
        (writeOutputDescriptorsSpec descriptorTail tail)
  end.

Lemma writeOutputDescriptorsSpec_app left right tail :
  writeOutputDescriptorsSpec (left ++ right) tail =
    writeOutputDescriptorsSpec left (writeOutputDescriptorsSpec right tail).
Proof.
  induction left as [|[data size] descriptorTail IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** This relation supplies the liveness fact that prefix-closed [spec] lacks. *)
Definition writeOutputCompleteTrace
    (snapshot : seq_snapshot) (descriptors : list WriteOutputDescriptor)
    (tailEvents observed : list seq_label) : Prop :=
  observed = writeOutputDescriptorsEvents snapshot descriptors ++ tailEvents.

Lemma writeOutputCompleteTrace_app snapshot left right tailEvents observed :
  writeOutputCompleteTrace snapshot (left ++ right) tailEvents observed <->
  writeOutputCompleteTrace snapshot left
    (writeOutputDescriptorsEvents snapshot right ++ tailEvents) observed.
Proof.
  unfold writeOutputCompleteTrace.
  rewrite writeOutputDescriptorsEvents_app app_assoc. reflexivity.
Qed.

Lemma writeOutputCompleteTrace_allowed snapshot descriptors tail tailEvents observed :
  writeOutputCompleteTrace snapshot descriptors tailEvents observed ->
  tail tailEvents ->
  writeOutputDescriptorsSpec descriptors tail observed.
Proof.
  intros -> Htail. induction descriptors as [|[data size] descriptorTail IH].
  - exact Htail.
  - simpl. unfold writeOutputDescriptorEvents, writeOutputEventsAny, scons.
    right. eexists snapshot, _. split; first reflexivity. right.
    right. eexists snapshot, _. split; first reflexivity.
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

Lemma writeOutputPayloadSnapshots_app_inv memoryAtWrite index
    leftDescriptors rightDescriptors payloads :
  writeOutputPayloadSnapshots memoryAtWrite index
    (leftDescriptors ++ rightDescriptors) payloads ->
  exists leftPayloads rightPayloads,
    payloads = leftPayloads ++ rightPayloads /\
    writeOutputPayloadSnapshots memoryAtWrite index
      leftDescriptors leftPayloads /\
    writeOutputPayloadSnapshots memoryAtWrite
      (index + length leftDescriptors) rightDescriptors rightPayloads.
Proof.
  revert index payloads.
  induction leftDescriptors as [|[data size] descriptorTail IH].
  - intros index payloads Hpayloads.
    exists [], payloads. simpl in *.
    replace (index + 0)%nat with index by lia.
    auto.
  - intros index [|payload payloadTail] Hpayloads; simpl in Hpayloads.
    + contradiction.
    + destruct Hpayloads as (Hmemory & Hsize & Htail).
      destruct (IH (S index) payloadTail Htail) as
        (leftPayloads & rightPayloads & -> & Hleft & Hright).
      exists (payload :: leftPayloads), rightPayloads.
      split; first reflexivity.
      split.
      * simpl. repeat split; assumption.
      * replace (index + S (length descriptorTail))%nat
          with (S index + length descriptorTail)%nat by lia.
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

Lemma writeOutputSequenceObservationFrom_app_inv memoryAtWrite index
    leftDescriptors rightDescriptors bytes :
  writeOutputSequenceObservationFrom memoryAtWrite index
    (leftDescriptors ++ rightDescriptors) bytes ->
  exists leftBytes rightBytes,
    bytes = leftBytes ++ rightBytes /\
    writeOutputSequenceObservationFrom memoryAtWrite index
      leftDescriptors leftBytes /\
    writeOutputSequenceObservationFrom memoryAtWrite
      (index + length leftDescriptors) rightDescriptors rightBytes.
Proof.
  intros (payloads & Hpayloads & ->).
  destruct (writeOutputPayloadSnapshots_app_inv memoryAtWrite index
    leftDescriptors rightDescriptors payloads Hpayloads) as
    (leftPayloads & rightPayloads & -> & Hleft & Hright).
  exists (writeSuccessPublicBytes (concat leftPayloads)),
    (writeSuccessPublicBytes (concat rightPayloads)).
  split.
  - rewrite concat_app writeSuccessPublicBytes_app. reflexivity.
  - split; [exists leftPayloads | exists rightPayloads]; auto.
Qed.

Corollary writeOutputSequenceObservationFrom_app_iff memoryAtWrite index
    leftDescriptors rightDescriptors bytes :
  writeOutputSequenceObservationFrom memoryAtWrite index
      (leftDescriptors ++ rightDescriptors) bytes <->
  exists leftBytes rightBytes,
    bytes = leftBytes ++ rightBytes /\
    writeOutputSequenceObservationFrom memoryAtWrite index
      leftDescriptors leftBytes /\
    writeOutputSequenceObservationFrom memoryAtWrite
      (index + length leftDescriptors) rightDescriptors rightBytes.
Proof.
  split.
  - apply writeOutputSequenceObservationFrom_app_inv.
  - intros (leftBytes & rightBytes & -> & Hleft & Hright).
    eapply writeOutputSequenceObservationFrom_app; eassumption.
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
  writeOutputEventsAny data size tail [].
Proof. unfold writeOutputEventsAny, scons. auto. Qed.

Lemma write_output_events_accept_descriptor_prefix
    (data size : bv 64) (tail : spec) snapshot :
  writeOutputEventsAny data size tail
    [SWriteMem (BV 64 (machineOutputAddress defaultMap)) data snapshot;
     SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size snapshot].
Proof. unfold writeOutputEventsAny, scons. naive_solver. Qed.

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
  split; [apply Nat2Z.is_nonneg |].
  change (Z.of_nat (length payload) < 2 ^ 64)%Z.
  apply Nat2Z.inj_lt in Hlength.
  rewrite Nat2Z.inj_pow in Hlength. exact Hlength.
Qed.
