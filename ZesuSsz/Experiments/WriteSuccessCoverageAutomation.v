From Coq Require Import Lists.List.
Require Import isla.opsem.
Require Import ZesuSsz.Contracts.InstructionBoundary.

Lemma writeSuccessInstructionPrefixAllNonblocking before observations done :
  IslaInstructionPrefixPath before observations done ->
  done.1.(seq_nb_state) = false ->
  Forall (fun observation =>
    observation.(microAfter).1.(seq_nb_state) = false) observations.
Proof.
  intros Hpath. induction Hpath.
  - intros _. constructor.
  - intros Hdone. constructor.
    + destruct observations as [|next rest].
      * inversion Hpath; subst. exact Hdone.
      * inversion Hpath; subst.
        eapply seqStepSourceBlocking. exact H5.
    + apply IHHpath. exact Hdone.
Qed.

Lemma writeSuccessInstructionSegmentPrefixAllNonblocking
    before observations after :
  IslaInstructionSegment before observations after ->
  exists prefix doneObservation,
    observations = prefix ++ [doneObservation] /\
    Forall (fun observation =>
      observation.(microAfter).1.(seq_nb_state) = false) prefix.
Proof.
  intros Hsegment.
  destruct Hsegment as
    [Hstart done prefix labels spawned Hprefix Hnil Hstep -> Hend].
  exists prefix,
    {| microLabels := labels; microAfter := after |}.
  split; first reflexivity.
  eapply writeSuccessInstructionPrefixAllNonblocking; first exact Hprefix.
  eapply seqStepSourceBlocking. exact Hstep.
Qed.

Ltac writeSuccessRejectBlockingPrefix Hsegment :=
  let prefix := fresh "prefix" in
  let doneObservation := fresh "doneObservation" in
  let Hobservations := fresh "Hobservations" in
  let Hnonblocking := fresh "Hnonblocking" in
  destruct (writeSuccessInstructionSegmentPrefixAllNonblocking
    _ _ _ Hsegment) as
    (prefix & doneObservation & Hobservations & Hnonblocking).

Print Assumptions writeSuccessInstructionPrefixAllNonblocking.
Print Assumptions writeSuccessInstructionSegmentPrefixAllNonblocking.
