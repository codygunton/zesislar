From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationCore.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationRecords.

Lemma writeSuccessConcreteRepresentationHashesOkReadsEqual
    ok decoded before after address beforeTail afterTail :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessConcreteRepresentationHashesOk ok decoded before address
    beforeTail ->
  afterTail ->
  writeSuccessConcreteRepresentationHashesOk ok decoded after address afterTail.
Proof.
  intros Hreads (Hparent & Hfee & Hstate & Hreceipts & Hlogs & Hrandao &
    Hblock & Hversions & Hdeposits & Hwithdrawals & Hconsolidations &
    HbuilderDeposits & HbuilderExits & Hbeacon & HbeforeTail) HafterTail.
  repeat first
    [ solve [eapply writeSuccessMemoryBytesOkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemoryFixedListOkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemorySliceOkReadsEqual; eassumption]
    | split ].
  exact HafterTail.
Qed.
