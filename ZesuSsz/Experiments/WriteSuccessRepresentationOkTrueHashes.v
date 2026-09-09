Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueLeaves.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueNested.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueParts.

Lemma writeSuccessConcreteRepresentationHashesOkTrue
    decoded memory address tail tail' :
  (tail <-> tail') ->
  writeSuccessConcreteRepresentationHashesOk (fun _ _ => True)
      decoded memory address tail <->
  writeSuccessConcreteRepresentationHashesPreR9
      decoded memory address tail'.
Proof.
  intros Htail.
  unfold writeSuccessConcreteRepresentationHashesOk,
    writeSuccessConcreteRepresentationHashesPreR9.
  repeat apply writeSuccessAndIff.
  all: first
    [ exact Htail
    | apply writeSuccessMemoryBytesOkTrue
    | apply writeSuccessMemoryFixedListOkTrue
    | apply writeSuccessMemorySliceOkTrue ].
Qed.

Print Assumptions writeSuccessConcreteRepresentationHashesOkTrue.
