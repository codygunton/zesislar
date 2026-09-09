From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationCore.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.

Local Opaque writeSuccessMemoryBytesOk writeSuccessMemoryIntegerOk
  writeSuccessMemorySliceOk writeSuccessMemoryOptionalU64Ok
  writeSuccessMemoryFixedListOk writeSuccessAccessListMemoryOk
  writeSuccessAuthorizationListMemoryOk.

Lemma writeSuccessAccessEntryMemoryOkReadsEqual
    ok before after address entry :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessAccessEntryMemoryOk ok before address entry ->
  writeSuccessAccessEntryMemoryOk ok after address entry.
Proof.
  intros Hreads [Haddress Hkeys]. split.
  - eapply writeSuccessMemoryBytesOkReadsEqual; eassumption.
  - eapply writeSuccessMemoryFixedListOkReadsEqual; eassumption.
Qed.

Lemma writeSuccessAccessListMemoryOkReadsEqual
    ok before after owner offset entries :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessAccessListMemoryOk ok before owner offset entries ->
  writeSuccessAccessListMemoryOk ok after owner offset entries.
Proof.
  intros Hreads (pointer & Hrange & Hpointer & Hlength & Hentries).
  exists pointer. split; first exact Hrange.
  split.
  - eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
  - split.
    + eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
    + intros index entry Hnth. eapply writeSuccessAccessEntryMemoryOkReadsEqual;
        eauto.
Qed.

Lemma writeSuccessAuthorizationMemoryOkReadsEqual
    ok before after address authorization :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessAuthorizationMemoryOk ok before address authorization ->
  writeSuccessAuthorizationMemoryOk ok after address authorization.
Proof.
  intros Hreads (Hchain & Hr & Hs & Hnonce & Hv & Haddress).
  split; first (eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption).
  split; first (eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption).
  split; first (eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption).
  split; first (eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption).
  split; first (eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption).
  eapply writeSuccessMemoryBytesOkReadsEqual; eassumption.
Qed.

Lemma writeSuccessAuthorizationListMemoryOkReadsEqual
    ok before after owner offset items :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessAuthorizationListMemoryOk ok before owner offset items ->
  writeSuccessAuthorizationListMemoryOk ok after owner offset items.
Proof.
  intros Hreads (pointer & Hrange & Hpointer & Hlength & Hitems).
  exists pointer. split; first exact Hrange.
  split.
  - eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
  - split.
    + eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
    + intros index item Hnth.
      eapply writeSuccessAuthorizationMemoryOkReadsEqual; eauto.
Qed.

Lemma writeSuccessWithdrawalMemoryOkReadsEqual
    ok before after address withdrawal :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessWithdrawalMemoryOk ok before address withdrawal ->
  writeSuccessWithdrawalMemoryOk ok after address withdrawal.
Proof.
  intros Hreads (Hindex & Hvalidator & Hamount & Haddress).
  split; first (eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption).
  split; first (eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption).
  split; first (eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption).
  eapply writeSuccessMemoryBytesOkReadsEqual; eassumption.
Qed.

Lemma writeSuccessWithdrawalListMemoryOkReadsEqual
    ok before after owner offset items :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessWithdrawalListMemoryOk ok before owner offset items ->
  writeSuccessWithdrawalListMemoryOk ok after owner offset items.
Proof.
  intros Hreads (pointer & Hrange & Hpointer & Hlength & Hitems).
  exists pointer. split; first exact Hrange.
  split.
  - eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
  - split.
    + eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
    + intros index item Hnth. eapply writeSuccessWithdrawalMemoryOkReadsEqual;
        eauto.
Qed.

Lemma writeSuccessTransactionPriorityFeeOkReadsEqual
    ok before after address value :
  writeSuccessRepresentationReadsEqual ok before after ->
  (match value with
   | None => writeSuccessMemoryIntegerOk ok before (address + 32) 1 0
   | Some item =>
       writeSuccessMemoryIntegerOk ok before (address + 16) 16 item /\
       writeSuccessMemoryIntegerOk ok before (address + 32) 1 1
   end) ->
  match value with
  | None => writeSuccessMemoryIntegerOk ok after (address + 32) 1 0
  | Some item =>
      writeSuccessMemoryIntegerOk ok after (address + 16) 16 item /\
      writeSuccessMemoryIntegerOk ok after (address + 32) 1 1
  end.
Proof.
  intros Hreads Hvalue. destruct value; cbn in Hvalue |- *.
  - destruct Hvalue. split;
      eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
  - eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
Qed.

Lemma writeSuccessTransactionToOkReadsEqual ok before after address value :
  writeSuccessRepresentationReadsEqual ok before after ->
  (match value with
   | None => writeSuccessMemoryIntegerOk ok before (address + 285) 1 0
   | Some item =>
       writeSuccessMemoryBytesOk ok before (address + 265) item /\
       writeSuccessMemoryIntegerOk ok before (address + 285) 1 1
   end) ->
  match value with
  | None => writeSuccessMemoryIntegerOk ok after (address + 285) 1 0
  | Some item =>
      writeSuccessMemoryBytesOk ok after (address + 265) item /\
      writeSuccessMemoryIntegerOk ok after (address + 285) 1 1
  end.
Proof.
  intros Hreads Hvalue. destruct value; cbn in Hvalue |- *.
  - destruct Hvalue. split.
    + eapply writeSuccessMemoryBytesOkReadsEqual; eassumption.
    + eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
  - eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
Qed.

Lemma writeSuccessTransactionMemoryOkReadsEqual
    ok before after address transaction :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessTransactionMemoryOk ok before address transaction ->
  writeSuccessTransactionMemoryOk ok after address transaction.
Proof.
  intros Hreads Htransaction.
  unfold writeSuccessTransactionMemoryOk in Htransaction |- *.
  destruct Htransaction as
    (Htype & Hchain & Hnonce & HgasPrice & Hpriority & HgasLimit & Hto &
     Hvalue & Hdata & Haccess & HblobHashes & HmaxBlobFee & Hauthorizations &
     Hv & Hr & Hs).
  repeat first
    [ solve [eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemoryOptionalU64OkReadsEqual; eassumption]
    | solve [eapply writeSuccessTransactionPriorityFeeOkReadsEqual; eassumption]
    | solve [eapply writeSuccessTransactionToOkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemoryBytesOkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemorySliceOkReadsEqual; eassumption]
    | solve [eapply writeSuccessAccessListMemoryOkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemoryFixedListOkReadsEqual; eassumption]
    | solve [eapply writeSuccessAuthorizationListMemoryOkReadsEqual;
        eassumption]
    | split ].
Qed.

Lemma writeSuccessTransactionListMemoryOkReadsEqual
    ok before after owner offset items :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessTransactionListMemoryOk ok before owner offset items ->
  writeSuccessTransactionListMemoryOk ok after owner offset items.
Proof.
  intros Hreads (pointer & Hrange & Hpointer & Hlength & Hitems).
  exists pointer. split; first exact Hrange.
  split.
  - eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
  - split.
    + eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption.
    + intros index item Hnth. eapply writeSuccessTransactionMemoryOkReadsEqual;
        eauto.
Qed.

Print Assumptions writeSuccessAccessListMemoryOkReadsEqual.
Print Assumptions writeSuccessAuthorizationListMemoryOkReadsEqual.
Print Assumptions writeSuccessWithdrawalListMemoryOkReadsEqual.
Print Assumptions writeSuccessTransactionListMemoryOkReadsEqual.
