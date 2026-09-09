Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationOkTrueLeaves.

Lemma writeSuccessAccessEntryMemoryOkTrue memory address entry :
  writeSuccessAccessEntryMemoryOk (fun _ _ => True)
      memory address entry <->
  writeSuccessAccessEntryMemory memory address entry.
Proof.
  unfold writeSuccessAccessEntryMemoryOk, writeSuccessAccessEntryMemory.
  rewrite writeSuccessMemoryBytesOkTrue.
  rewrite writeSuccessMemoryFixedListOkTrue.
  reflexivity.
Qed.

Lemma writeSuccessAccessListMemoryOkTrue memory owner offset entries :
  writeSuccessAccessListMemoryOk (fun _ _ => True)
      memory owner offset entries <->
  writeSuccessAccessListMemory memory owner offset entries.
Proof.
  unfold writeSuccessAccessListMemoryOk, writeSuccessAccessListMemory.
  setoid_rewrite writeSuccessMemoryIntegerOkTrue.
  setoid_rewrite writeSuccessAccessEntryMemoryOkTrue.
  reflexivity.
Qed.

Lemma writeSuccessAuthorizationMemoryOkTrue memory address authorization :
  writeSuccessAuthorizationMemoryOk (fun _ _ => True)
      memory address authorization <->
  writeSuccessAuthorizationMemory memory address authorization.
Proof.
  unfold writeSuccessAuthorizationMemoryOk, writeSuccessAuthorizationMemory.
  rewrite !writeSuccessMemoryIntegerOkTrue.
  rewrite writeSuccessMemoryBytesOkTrue.
  reflexivity.
Qed.

Lemma writeSuccessAuthorizationListMemoryOkTrue memory owner offset items :
  writeSuccessAuthorizationListMemoryOk (fun _ _ => True)
      memory owner offset items <->
  writeSuccessAuthorizationListMemory memory owner offset items.
Proof.
  unfold writeSuccessAuthorizationListMemoryOk,
    writeSuccessAuthorizationListMemory.
  setoid_rewrite writeSuccessMemoryIntegerOkTrue.
  setoid_rewrite writeSuccessAuthorizationMemoryOkTrue.
  reflexivity.
Qed.

Lemma writeSuccessTransactionMemoryOkTrue memory address transaction :
  writeSuccessTransactionMemoryOk (fun _ _ => True)
      memory address transaction <->
  writeSuccessTransactionMemory memory address transaction.
Proof.
  unfold writeSuccessTransactionMemoryOk, writeSuccessTransactionMemory.
  rewrite !writeSuccessMemoryIntegerOkTrue.
  rewrite writeSuccessMemoryOptionalU64OkTrue.
  rewrite writeSuccessMemorySliceOkTrue.
  rewrite writeSuccessAccessListMemoryOkTrue.
  rewrite writeSuccessMemoryFixedListOkTrue.
  rewrite writeSuccessAuthorizationListMemoryOkTrue.
  destruct (observationTransactionPriorityFee transaction);
    destruct (observationTransactionTo transaction);
    rewrite ?writeSuccessMemoryBytesOkTrue;
    rewrite !writeSuccessMemoryIntegerOkTrue; reflexivity.
Qed.

Lemma writeSuccessTransactionListMemoryOkTrue memory owner offset items :
  writeSuccessTransactionListMemoryOk (fun _ _ => True)
      memory owner offset items <->
  writeSuccessTransactionListMemory memory owner offset items.
Proof.
  unfold writeSuccessTransactionListMemoryOk, writeSuccessTransactionListMemory.
  setoid_rewrite writeSuccessMemoryIntegerOkTrue.
  setoid_rewrite writeSuccessTransactionMemoryOkTrue.
  reflexivity.
Qed.

Lemma writeSuccessWithdrawalMemoryOkTrue memory address withdrawal :
  writeSuccessWithdrawalMemoryOk (fun _ _ => True)
      memory address withdrawal <->
  writeSuccessWithdrawalMemory memory address withdrawal.
Proof.
  unfold writeSuccessWithdrawalMemoryOk, writeSuccessWithdrawalMemory.
  rewrite !writeSuccessMemoryIntegerOkTrue.
  rewrite writeSuccessMemoryBytesOkTrue.
  reflexivity.
Qed.

Lemma writeSuccessWithdrawalListMemoryOkTrue memory owner offset items :
  writeSuccessWithdrawalListMemoryOk (fun _ _ => True)
      memory owner offset items <->
  writeSuccessWithdrawalListMemory memory owner offset items.
Proof.
  unfold writeSuccessWithdrawalListMemoryOk, writeSuccessWithdrawalListMemory.
  setoid_rewrite writeSuccessMemoryIntegerOkTrue.
  setoid_rewrite writeSuccessWithdrawalMemoryOkTrue.
  reflexivity.
Qed.

Print Assumptions writeSuccessTransactionListMemoryOkTrue.
Print Assumptions writeSuccessWithdrawalListMemoryOkTrue.
