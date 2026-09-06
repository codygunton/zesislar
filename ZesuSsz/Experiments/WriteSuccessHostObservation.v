From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import isla.opsem.
Require Import isla.adequacy.
Require Import ZesuSsz.Contracts.IslarisMemory.

Import ListNotations.

Definition WriteSuccessHostObservation
    (memory : mem_map) (eventIndex : nat)
    (data size : bv 64) (payload : list (bv 8)) : Prop :=
  read_mem_list memory (bv_unsigned data)
    (N.of_nat (length payload)) = Some payload /\
  bv_unsigned size = Z.of_nat (length payload).

Fixpoint writeSuccessOutputEventCount (labels : list seq_label) : nat :=
  match labels with
  | [] => 0%nat
  | SWriteMem address _ :: labels =>
      if Z.eqb (bv_unsigned address) 0x2401a0c0
      then S (writeSuccessOutputEventCount labels)
      else writeSuccessOutputEventCount labels
  | _ :: labels => writeSuccessOutputEventCount labels
  end.

Definition WriteSuccessOutputEventState
    (initialLocal : seq_local_state) (initialState : seq_global_state)
    (eventIndex : nat) (eventLocal : seq_local_state)
    (eventState : seq_global_state) (data : bv 64) : Prop :=
  exists microSteps labels localAfter stateAfter,
    nsteps microSteps ([initialLocal], initialState) labels
      ([eventLocal], eventState) /\
    writeSuccessOutputEventCount labels = eventIndex /\
    seq_step eventLocal eventState
      [SWriteMem (BV 64 0x2401a0c0) data]
      localAfter stateAfter [].

Definition WriteSuccessExecutionHostObservation
    (initialLocal : seq_local_state) (initialState : seq_global_state)
    (eventIndex : nat) (eventLocal : seq_local_state)
    (eventState : seq_global_state)
    (data size : bv 64) (payload : list (bv 8)) : Prop :=
  WriteSuccessOutputEventState initialLocal initialState eventIndex
    eventLocal eventState data /\
  WriteSuccessHostObservation eventState.(seq_mem)
    eventIndex data size payload.

Section memory_reflection.
  Context `{!islaG Sigma}.

  Lemma writeSuccessOwnedPayloadRead
      (state : seq_global_state) (labels : list seq_label)
      (data : bv 64) (payload : list (bv 8)) :
    state_ctx state labels -∗
    bv_unsigned data ↦ₘ∗ payload -∗
    ⌜read_mem_list state.(seq_mem) (bv_unsigned data)
       (N.of_nat (length payload)) = Some payload⌝.
  Proof.
    iIntros "(_ & _ & Hmemory) Hpayload".
    iDestruct (mem_mapsto_byte_array_to_mapsto with "Hpayload")
      as "Hpayload".
    iDestruct (mem_mapsto_lookup_list with "Hmemory Hpayload")
      as %[length [Hlength Hread]].
    have Hlength' : length = Datatypes.length payload by nia.
    subst length.
    iPureIntro.
    rewrite Hread.
    f_equal.
    replace (Z.to_N (Z.of_nat (Datatypes.length payload))) with
      (N.of_nat (Datatypes.length payload)).
    2: { apply N2Z.inj. rewrite Z2N.id.
         - apply nat_N_Z.
         - lia. }
    rewrite Z_to_bv_small.
    - apply bv_to_little_endian_to_bv. lia.
    - pose proof (little_endian_to_bv_bound 8 payload) as Hbound.
      unfold bv_modulus in Hbound |- *.
      rewrite N2Z.inj_mul nat_N_Z. cbn. lia.
  Qed.

  Lemma writeSuccessOwnedPayloadObservation
      (state : seq_global_state) (labels : list seq_label)
      (eventIndex : nat) (data size : bv 64) (payload : list (bv 8)) :
    bv_unsigned size = Z.of_nat (length payload) ->
    state_ctx state labels -∗
    bv_unsigned data ↦ₘ∗ payload -∗
    ⌜WriteSuccessHostObservation
       state.(seq_mem) eventIndex data size payload⌝.
  Proof.
    iIntros (Hsize) "Hstate Hpayload".
    iDestruct (writeSuccessOwnedPayloadRead with "Hstate Hpayload")
      as %Hread.
    iPureIntro. split; done.
  Qed.

  Lemma writeSuccessOwnedExecutionPayloadObservation
      (initialLocal eventLocal : seq_local_state)
      (initialState eventState : seq_global_state)
      (labels : list seq_label) (eventIndex : nat)
      (data size : bv 64) (payload : list (bv 8)) :
    WriteSuccessOutputEventState initialLocal initialState eventIndex
      eventLocal eventState data ->
    bv_unsigned size = Z.of_nat (length payload) ->
    state_ctx eventState labels -∗
    bv_unsigned data ↦ₘ∗ payload -∗
    ⌜WriteSuccessExecutionHostObservation initialLocal initialState
       eventIndex eventLocal eventState data size payload⌝.
  Proof.
    iIntros (Hevent Hsize) "Hstate Hpayload".
    iDestruct (writeSuccessOwnedPayloadObservation
      eventState labels eventIndex data size payload Hsize with
      "Hstate Hpayload") as %Hobservation.
    iPureIntro. split; done.
  Qed.

  Lemma writeSuccessOwnedExecutionPayloadObservationFrame
      (initialLocal eventLocal : seq_local_state)
      (initialState eventState : seq_global_state)
      (labels : list seq_label) (eventIndex : nat)
      (data size : bv 64) (payload : list (bv 8)) :
    WriteSuccessOutputEventState initialLocal initialState eventIndex
      eventLocal eventState data ->
    bv_unsigned size = Z.of_nat (length payload) ->
    state_ctx eventState labels ∗ bv_unsigned data ↦ₘ∗ payload -∗
    ⌜WriteSuccessExecutionHostObservation initialLocal initialState
       eventIndex eventLocal eventState data size payload⌝ ∗
    state_ctx eventState labels ∗ bv_unsigned data ↦ₘ∗ payload.
  Proof.
    iIntros (Hevent Hsize) "[Hstate Hpayload]".
    iAssert ⌜WriteSuccessExecutionHostObservation
      initialLocal initialState eventIndex eventLocal eventState
      data size payload⌝%I as %Hobservation.
    { iApply (writeSuccessOwnedExecutionPayloadObservation
        initialLocal eventLocal initialState eventState labels eventIndex
        data size payload Hevent Hsize with "Hstate Hpayload"). }
    iFrame. done.
  Qed.
End memory_reflection.

Section separate_execution_states.
  Context `{!islaG Sigma}.

  Lemma writeSuccessOwnedExecutionSamePointerSeparateStates
      (initialLocal firstLocal secondLocal : seq_local_state)
      (initialState firstState secondState : seq_global_state)
      (firstLabels secondLabels : list seq_label)
      (firstIndex secondIndex : nat) (data size : bv 64)
      (firstPayload secondPayload : list (bv 8)) :
    firstPayload <> secondPayload ->
    length firstPayload = length secondPayload ->
    WriteSuccessOutputEventState initialLocal initialState firstIndex
      firstLocal firstState data ->
    WriteSuccessOutputEventState initialLocal initialState secondIndex
      secondLocal secondState data ->
    bv_unsigned size = Z.of_nat (length firstPayload) ->
    (⊢ state_ctx firstState firstLabels -∗
       bv_unsigned data ↦ₘ∗ firstPayload -∗
       ⌜WriteSuccessExecutionHostObservation
         initialLocal initialState firstIndex firstLocal firstState
         data size firstPayload⌝) /\
    (⊢ state_ctx secondState secondLabels -∗
       bv_unsigned data ↦ₘ∗ secondPayload -∗
       ⌜WriteSuccessExecutionHostObservation
         initialLocal initialState secondIndex secondLocal secondState
         data size secondPayload⌝).
  Proof.
    intros _ Hlength Hfirst Hsecond Hsize. split.
    - iIntros "Hstate Hpayload".
      iApply (writeSuccessOwnedExecutionPayloadObservation
        initialLocal firstLocal initialState firstState firstLabels
        firstIndex data size firstPayload Hfirst Hsize with
        "Hstate Hpayload").
    - iIntros "Hstate Hpayload".
      iApply (writeSuccessOwnedExecutionPayloadObservation
        initialLocal secondLocal initialState secondState secondLabels
        secondIndex data size secondPayload Hsecond with
        "Hstate Hpayload").
      rewrite <- Hlength. exact Hsize.
  Qed.
End separate_execution_states.

Fixpoint writeSuccessRepeatedHostObservationsFrom
    (memoryAt : nat -> mem_map)
    (index : nat)
    (descriptors : list (bv 64 * bv 64))
    (payloads : list (list (bv 8))) : Prop :=
  match descriptors, payloads with
  | [], [] => True
  | (data, size) :: descriptors, payload :: payloads =>
      WriteSuccessHostObservation
        (memoryAt index) index data size payload /\
      writeSuccessRepeatedHostObservationsFrom
        memoryAt (S index) descriptors payloads
  | _, _ => False
  end.

Definition WriteSuccessRepeatedHostObservations :=
  fun memoryAt descriptors payloads =>
    writeSuccessRepeatedHostObservationsFrom
      memoryAt 0 descriptors payloads.

Fixpoint writeSuccessRepeatedExecutionObservationsFrom
    (initialLocal : seq_local_state) (initialState : seq_global_state)
    (index : nat)
    (eventStates : list (seq_local_state * seq_global_state))
    (descriptors : list (bv 64 * bv 64))
    (payloads : list (list (bv 8))) : Prop :=
  match eventStates, descriptors, payloads with
  | [], [], [] => True
  | (eventLocal, eventState) :: eventStates,
      (data, size) :: descriptors, payload :: payloads =>
      WriteSuccessExecutionHostObservation
        initialLocal initialState index eventLocal eventState
        data size payload /\
      writeSuccessRepeatedExecutionObservationsFrom
        initialLocal initialState (S index)
        eventStates descriptors payloads
  | _, _, _ => False
  end.

Definition WriteSuccessRepeatedExecutionObservations
    (initialLocal : seq_local_state) (initialState : seq_global_state)
    eventStates descriptors payloads : Prop :=
  writeSuccessRepeatedExecutionObservationsFrom
    initialLocal initialState 0 eventStates descriptors payloads.

Lemma writeSuccessHostObservationSeparateStates
    firstMemory secondMemory index data size firstPayload secondPayload :
  length firstPayload = length secondPayload ->
  read_mem_list firstMemory (bv_unsigned data)
    (N.of_nat (length firstPayload)) = Some firstPayload ->
  read_mem_list secondMemory (bv_unsigned data)
    (N.of_nat (length secondPayload)) = Some secondPayload ->
  bv_unsigned size = Z.of_nat (length firstPayload) ->
  WriteSuccessHostObservation
    firstMemory index data size firstPayload /\
  WriteSuccessHostObservation
    secondMemory index data size secondPayload.
Proof.
  intros Hlength Hfirst Hsecond Hsize.
  split; split; try assumption. rewrite <- Hlength. exact Hsize.
Qed.
