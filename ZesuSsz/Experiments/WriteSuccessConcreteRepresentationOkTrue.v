Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueHeader.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueLists.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueHashes.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTruePostData.

Lemma writeSuccessConcreteRepresentationOkTrue decoded memory address :
  writeSuccessConcreteRepresentationOk (fun _ _ => True)
      decoded memory address <->
  writeSuccessConcreteRepresentationPreR9 decoded memory address.
Proof.
  unfold writeSuccessConcreteRepresentationOk,
    writeSuccessConcreteRepresentationPreR9.
  apply writeSuccessConcreteRepresentationHeaderOkTrue.
  apply writeSuccessConcreteRepresentationListsOkTrue.
  apply writeSuccessConcreteRepresentationHashesOkTrue.
  apply writeSuccessConcreteRepresentationPostDataOkTrue.
Qed.

Lemma writeSuccessConcreteRepresentationPreR9Iff decoded memory address :
  writeSuccessConcreteRepresentation decoded memory address <->
  writeSuccessConcreteRepresentationPreR9 decoded memory address.
Proof.
  unfold writeSuccessConcreteRepresentation.
  apply writeSuccessConcreteRepresentationOkTrue.
Qed.

Print Assumptions writeSuccessConcreteRepresentationOkTrue.
Print Assumptions writeSuccessConcreteRepresentationPreR9Iff.
