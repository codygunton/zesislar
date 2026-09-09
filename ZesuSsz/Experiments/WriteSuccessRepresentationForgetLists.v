Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetLeaves.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetNested.

Lemma writeSuccessConcreteRepresentationListsOkForget ok decoded memory address tailOk tail :
  (tailOk -> tail) ->
  writeSuccessConcreteRepresentationListsOk ok decoded memory address tailOk ->
  writeSuccessConcreteRepresentationListsPreR9 decoded memory address tail.
Proof.
  intros Htail H.
  unfold writeSuccessConcreteRepresentationListsOk,
    writeSuccessConcreteRepresentationListsPreR9 in *.
  destruct H as (Htx & Hraw & Hwithdrawals & Hblob & Hexcess & Hslot & Haccess & Hrest).
  split; first exact (writeSuccessTransactionListMemoryOkForget _ _ _ _ _ Htx).
  split; first exact (writeSuccessMemoryByteListsOkForget _ _ _ _ _ Hraw).
  split; first exact (writeSuccessWithdrawalListMemoryOkForget _ _ _ _ _ Hwithdrawals).
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hblob).
  split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hexcess).
  split; first exact (writeSuccessMemoryOptionalU64OkForget _ _ _ _ _ Hslot).
  split; first exact (writeSuccessMemorySliceOkForget _ _ _ _ _ Haccess).
  exact (Htail Hrest).
Qed.

Print Assumptions writeSuccessConcreteRepresentationListsOkForget.
