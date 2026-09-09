Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetLeaves.

Lemma writeSuccessAccessEntryMemoryOkForget ok memory address entry :
  writeSuccessAccessEntryMemoryOk ok memory address entry ->
  writeSuccessAccessEntryMemory memory address entry.
Proof.
  intros [Haddress Hkeys]. split.
  - exact (writeSuccessMemoryBytesOkForget _ _ _ _ Haddress).
  - exact (writeSuccessMemoryFixedListOkForget _ _ _ _ _ _ Hkeys).
Qed.

Lemma writeSuccessAccessListMemoryOkForget ok memory owner offset entries :
  writeSuccessAccessListMemoryOk ok memory owner offset entries ->
  writeSuccessAccessListMemory memory owner offset entries.
Proof.
  intros (pointer & Hrange & Hpointer & Hlength & Hitems).
  exists pointer. split; first exact Hrange.
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hpointer).
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hlength).
  intros index item Hnth. apply writeSuccessAccessEntryMemoryOkForget with (ok := ok).
  exact (Hitems index item Hnth).
Qed.

Lemma writeSuccessAuthorizationMemoryOkForget ok memory address item :
  writeSuccessAuthorizationMemoryOk ok memory address item ->
  writeSuccessAuthorizationMemory memory address item.
Proof.
  unfold writeSuccessAuthorizationMemoryOk, writeSuccessAuthorizationMemory.
  intuition eapply writeSuccessMemoryIntegerOkForget +
    eapply writeSuccessMemoryBytesOkForget; eassumption.
Qed.

Lemma writeSuccessAuthorizationListMemoryOkForget ok memory owner offset items :
  writeSuccessAuthorizationListMemoryOk ok memory owner offset items ->
  writeSuccessAuthorizationListMemory memory owner offset items.
Proof.
  intros (pointer & Hrange & Hpointer & Hlength & Hitems).
  exists pointer. split; first exact Hrange.
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hpointer).
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hlength).
  intros index item Hnth. apply writeSuccessAuthorizationMemoryOkForget with (ok := ok).
  exact (Hitems index item Hnth).
Qed.

Lemma writeSuccessTransactionMemoryOkForget ok memory address item :
  writeSuccessTransactionMemoryOk ok memory address item ->
  writeSuccessTransactionMemory memory address item.
Proof.
  unfold writeSuccessTransactionMemoryOk, writeSuccessTransactionMemory.
  destruct (observationTransactionPriorityFee item);
    destruct (observationTransactionTo item); cbn;
    intuition eauto using writeSuccessMemoryIntegerOkForget,
      writeSuccessMemoryBytesOkForget, writeSuccessMemoryOptionalU64OkForget,
      writeSuccessMemorySliceOkForget, writeSuccessAccessListMemoryOkForget,
      writeSuccessMemoryFixedListOkForget,
      writeSuccessAuthorizationListMemoryOkForget.
Qed.

Lemma writeSuccessTransactionListMemoryOkForget ok memory owner offset items :
  writeSuccessTransactionListMemoryOk ok memory owner offset items ->
  writeSuccessTransactionListMemory memory owner offset items.
Proof.
  intros (pointer & Hrange & Hpointer & Hlength & Hitems).
  exists pointer. split; first exact Hrange.
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hpointer).
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hlength).
  intros index item Hnth. apply writeSuccessTransactionMemoryOkForget with (ok := ok).
  exact (Hitems index item Hnth).
Qed.

Lemma writeSuccessWithdrawalMemoryOkForget ok memory address item :
  writeSuccessWithdrawalMemoryOk ok memory address item ->
  writeSuccessWithdrawalMemory memory address item.
Proof.
  unfold writeSuccessWithdrawalMemoryOk, writeSuccessWithdrawalMemory.
  intuition eauto using writeSuccessMemoryIntegerOkForget,
    writeSuccessMemoryBytesOkForget.
Qed.

Lemma writeSuccessWithdrawalListMemoryOkForget ok memory owner offset items :
  writeSuccessWithdrawalListMemoryOk ok memory owner offset items ->
  writeSuccessWithdrawalListMemory memory owner offset items.
Proof.
  intros (pointer & Hrange & Hpointer & Hlength & Hitems).
  exists pointer. split; first exact Hrange.
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hpointer).
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hlength).
  intros index item Hnth. apply writeSuccessWithdrawalMemoryOkForget with (ok := ok).
  exact (Hitems index item Hnth).
Qed.

Print Assumptions writeSuccessTransactionListMemoryOkForget.
Print Assumptions writeSuccessWithdrawalListMemoryOkForget.
