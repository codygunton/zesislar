Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerBasic.

Lemma writeSuccessBlockerRepresentationHeader tail :
  tail ->
  writeSuccessConcreteRepresentationHeaderPreR9 writeSuccessBlockerDecoded
    writeSuccessBlockerRepresentedMemory writeSuccessBlockerOwner tail.
Proof.
  intro Htail. unfold writeSuccessConcreteRepresentationHeaderPreR9.
  split; first exact writeSuccessBlockerDecodedValid.
  split; first exact writeSuccessBlockerTop.
  split; first exact writeSuccessBlockerBlockNumber.
  split; first exact writeSuccessBlockerGasLimit.
  split; first exact writeSuccessBlockerGasUsed.
  split; first exact writeSuccessBlockerTimestamp.
  split; first exact writeSuccessBlockerExtraData.
  split; first exact writeSuccessBlockerBaseFee.
  exact Htail.
Qed.

Print Assumptions writeSuccessBlockerRepresentationHeader.
