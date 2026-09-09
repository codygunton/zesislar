Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationCore.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationHeaderTop.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.

Lemma writeSuccessConcreteRepresentationHeaderOkReadsEqual
    ok decoded before after address beforeTail afterTail :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessConcreteRepresentationHeaderOk ok decoded before address
    beforeTail ->
  afterTail ->
  writeSuccessConcreteRepresentationHeaderOk ok decoded after address afterTail.
Proof.
  intros Hreads Hheader Htail.
  change (writeSuccessObservationValid decoded /\
    writeSuccessRepresentationTopOk ok before address /\
    writeSuccessRepresentationHeaderFieldsOk ok decoded before address
      beforeTail) in Hheader.
  change (writeSuccessObservationValid decoded /\
    writeSuccessRepresentationTopOk ok after address /\
    writeSuccessRepresentationHeaderFieldsOk ok decoded after address
      afterTail).
  destruct Hheader as (Hvalid & Htop & Hfields).
  split; first exact Hvalid. split.
  - eapply writeSuccessRepresentationTopOkReadsEqual; eassumption.
  - eapply writeSuccessRepresentationHeaderFieldsOkReadsEqual; eassumption.
Qed.

Print Assumptions writeSuccessConcreteRepresentationHeaderOkReadsEqual.
