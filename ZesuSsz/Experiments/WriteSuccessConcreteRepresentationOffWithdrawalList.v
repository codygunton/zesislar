From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOff.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessStackRange.

Open Scope Z_scope.

Lemma writeSuccessConcreteRepresentationOffWithdrawalList
    sp decoded memory address :
  writeSuccessConcreteRepresentationOff sp decoded memory address ->
  writeSuccessWithdrawalListMemory memory address 88
    (observationWithdrawals decoded).
Proof.
  intros Hrepresentation.
  unfold writeSuccessConcreteRepresentationOff,
    writeSuccessConcreteRepresentationOk,
    writeSuccessConcreteRepresentationHeaderOk,
    writeSuccessConcreteRepresentationListsOk in Hrepresentation.
  assert (Hlist : writeSuccessWithdrawalListMemoryOk
      (writeSuccessAvoidsRange (writeSuccessCalleeStackLow sp) sp)
      memory address 88 (observationWithdrawals decoded)).
  { tauto. }
  unfold writeSuccessWithdrawalListMemoryOk in Hlist.
  destruct Hlist as
    (pointer & Hpointer & [HpointerRead _] & [HlengthRead _] & Hitems).
  exists pointer. split; first exact Hpointer.
  split; first exact HpointerRead.
  split; first exact HlengthRead.
  intros index item Hnth.
  specialize (Hitems index item Hnth).
  unfold writeSuccessWithdrawalMemoryOk,
    writeSuccessWithdrawalMemory in *.
  destruct Hitems as
    ([Hindex _] & [Hvalidator _] & [Hamount _] & [Haddress _]).
  repeat split; assumption.
Qed.

Print Assumptions writeSuccessConcreteRepresentationOffWithdrawalList.
