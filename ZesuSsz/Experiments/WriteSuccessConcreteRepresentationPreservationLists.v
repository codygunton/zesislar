From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationCore.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationRecords.

Lemma writeSuccessConcreteRepresentationListsOkReadsEqual
    ok decoded before after address beforeTail afterTail :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessConcreteRepresentationListsOk ok decoded before address
    beforeTail ->
  afterTail ->
  writeSuccessConcreteRepresentationListsOk ok decoded after address afterTail.
Proof.
  intros Hreads (Htransactions & Hraw & Hwithdrawals & Hblob & Hexcess &
    Hslot & Haccess & HbeforeTail) HafterTail.
  repeat first
    [ solve [eapply writeSuccessTransactionListMemoryOkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemoryByteListsOkReadsEqual; eassumption]
    | solve [eapply writeSuccessWithdrawalListMemoryOkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemoryOptionalU64OkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemorySliceOkReadsEqual; eassumption]
    | split ].
  exact HafterTail.
Qed.
