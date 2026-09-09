Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueLeaves.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueNested.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueParts.

Lemma writeSuccessConcreteRepresentationHeaderOkTrue
    decoded memory address tail tail' :
  (tail <-> tail') ->
  writeSuccessConcreteRepresentationHeaderOk (fun _ _ => True)
      decoded memory address tail <->
  writeSuccessConcreteRepresentationHeaderPreR9
      decoded memory address tail'.
Proof.
  intros Htail.
  unfold writeSuccessConcreteRepresentationHeaderOk,
    writeSuccessConcreteRepresentationHeaderPreR9.
  repeat apply writeSuccessAndIff.
  all: first
    [ reflexivity
    | exact Htail
    | apply writeSuccessObjectBytesOkTrue
    | apply writeSuccessMemoryIntegerOkTrue
    | apply writeSuccessMemorySliceOkTrue ].
Qed.

Print Assumptions writeSuccessConcreteRepresentationHeaderOkTrue.
