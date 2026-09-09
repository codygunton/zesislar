Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueLeaves.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueNested.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueParts.

Lemma writeSuccessConcreteRepresentationPostDataOkTrue
    decoded memory address :
  writeSuccessConcreteRepresentationPostDataOk (fun _ _ => True)
      decoded memory address <->
  writeSuccessConcreteRepresentationPostDataPreR9 decoded memory address.
Proof.
  unfold writeSuccessConcreteRepresentationPostDataOk,
    writeSuccessConcreteRepresentationPostDataPreR9.
  repeat apply writeSuccessAndIff.
  all: first
    [ apply writeSuccessMemoryByteListsOkTrue
    | apply writeSuccessMemoryIntegerOkTrue
    | apply writeSuccessMemoryOptionalBytesOkTrue
    | apply writeSuccessMemoryOptionalU64OkTrue ].
Qed.

Print Assumptions writeSuccessConcreteRepresentationPostDataOkTrue.
