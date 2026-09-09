Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOff.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.

Lemma writeSuccessConcreteRepresentationOffValid sp decoded memory address :
  writeSuccessConcreteRepresentationOff sp decoded memory address ->
  writeSuccessObservationValid decoded.
Proof.
  unfold writeSuccessConcreteRepresentationOff,
    writeSuccessConcreteRepresentationOk,
    writeSuccessConcreteRepresentationHeaderOk.
  tauto.
Qed.

Print Assumptions writeSuccessConcreteRepresentationOffValid.
