Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueLeaves.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueNested.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueParts.

Lemma writeSuccessConcreteRepresentationListsOkTrue
    decoded memory address tail tail' :
  (tail <-> tail') ->
  writeSuccessConcreteRepresentationListsOk (fun _ _ => True)
      decoded memory address tail <->
  writeSuccessConcreteRepresentationListsPreR9
      decoded memory address tail'.
Proof.
  intros Htail.
  unfold writeSuccessConcreteRepresentationListsOk,
    writeSuccessConcreteRepresentationListsPreR9.
  repeat apply writeSuccessAndIff.
  all: first
    [ exact Htail
    | apply writeSuccessTransactionListMemoryOkTrue
    | apply writeSuccessMemoryByteListsOkTrue
    | apply writeSuccessWithdrawalListMemoryOkTrue
    | apply writeSuccessMemoryIntegerOkTrue
    | apply writeSuccessMemoryOptionalU64OkTrue
    | apply writeSuccessMemorySliceOkTrue ].
Qed.

Print Assumptions writeSuccessConcreteRepresentationListsOkTrue.
