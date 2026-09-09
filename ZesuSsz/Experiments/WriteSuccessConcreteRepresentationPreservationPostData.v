From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationCore.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationRecords.

Lemma writeSuccessConcreteRepresentationPostDataOkReadsEqual
    ok decoded before after address :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessConcreteRepresentationPostDataOk ok decoded before address ->
  writeSuccessConcreteRepresentationPostDataOk ok decoded after address.
Proof.
  intros Hreads (Hnodes & Hcodes & Hheaders & Hchain & Hfork & Hindex &
    Hblock & Htimestamp & Hkeys).
  repeat first
    [ solve [eapply writeSuccessMemoryByteListsOkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemoryOptionalBytesOkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemoryOptionalU64OkReadsEqual; eassumption]
    | split ].
Qed.
