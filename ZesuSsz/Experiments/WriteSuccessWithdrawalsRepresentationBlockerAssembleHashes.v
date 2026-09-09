Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerInline.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerLists.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerTail.

Lemma writeSuccessBlockerRepresentationHashes tail :
  tail ->
  writeSuccessConcreteRepresentationHashesPreR9 writeSuccessBlockerDecoded
    writeSuccessBlockerRepresentedMemory writeSuccessBlockerOwner tail.
Proof.
  intro Htail. unfold writeSuccessConcreteRepresentationHashesPreR9.
  split; first exact writeSuccessBlockerParentHash.
  split; first exact writeSuccessBlockerFeeRecipient.
  split; first exact writeSuccessBlockerStateRoot.
  split; first exact writeSuccessBlockerReceiptsRoot.
  split; first exact writeSuccessBlockerLogsBloom.
  split; first exact writeSuccessBlockerPrevRandao.
  split; first exact writeSuccessBlockerBlockHash.
  split; first exact writeSuccessBlockerVersionedHashes.
  split; first exact writeSuccessBlockerDeposits.
  split; first exact writeSuccessBlockerWithdrawalRequests.
  split; first exact writeSuccessBlockerConsolidations.
  split; first exact writeSuccessBlockerBuilderDeposits.
  split; first exact writeSuccessBlockerBuilderExits.
  split; first exact writeSuccessBlockerParentBeaconRoot.
  exact Htail.
Qed.

Print Assumptions writeSuccessBlockerRepresentationHashes.
