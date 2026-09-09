Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationCore.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationParts.

Lemma writeSuccessConcreteRepresentationOkReadsEqual
    ok decoded before after address :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessConcreteRepresentationOk ok decoded before address ->
  writeSuccessConcreteRepresentationOk ok decoded after address.
Proof.
  intros Hreads Hrepresentation.
  unfold writeSuccessConcreteRepresentationOk in Hrepresentation |- *.
  eapply writeSuccessConcreteRepresentationHeaderOkReadsEqual;
    [exact Hreads|exact Hrepresentation|].
  unfold writeSuccessConcreteRepresentationHeaderOk in Hrepresentation.
  destruct Hrepresentation as
    (_ & _ & _ & _ & _ & _ & _ & _ & Hlists).
  eapply writeSuccessConcreteRepresentationListsOkReadsEqual;
    [exact Hreads|exact Hlists|].
  unfold writeSuccessConcreteRepresentationListsOk in Hlists.
  destruct Hlists as (_ & _ & _ & _ & _ & _ & _ & Hhashes).
  eapply writeSuccessConcreteRepresentationHashesOkReadsEqual;
    [exact Hreads|exact Hhashes|].
  unfold writeSuccessConcreteRepresentationHashesOk in Hhashes.
  destruct Hhashes as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpost).
  eapply writeSuccessConcreteRepresentationPostDataOkReadsEqual; eassumption.
Qed.

Print Assumptions writeSuccessConcreteRepresentationOkReadsEqual.
