Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerLists.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerTail.

Lemma writeSuccessBlockerRepresentationPostData :
  writeSuccessConcreteRepresentationPostDataPreR9 writeSuccessBlockerDecoded
    writeSuccessBlockerRepresentedMemory writeSuccessBlockerOwner.
Proof.
  unfold writeSuccessConcreteRepresentationPostDataPreR9.
  split; first exact writeSuccessBlockerWitnessNodes.
  split; first exact writeSuccessBlockerWitnessCodes.
  split; first exact writeSuccessBlockerWitnessHeaders.
  split; first exact writeSuccessBlockerChainId.
  split; first exact writeSuccessBlockerForkName.
  split; first exact writeSuccessBlockerActiveForkIndex.
  split; first exact writeSuccessBlockerActivationBlock.
  split; first exact writeSuccessBlockerActivationTimestamp.
  exact writeSuccessBlockerPublicKeys.
Qed.

Print Assumptions writeSuccessBlockerRepresentationPostData.
