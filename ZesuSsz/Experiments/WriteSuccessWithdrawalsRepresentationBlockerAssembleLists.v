Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerInline.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerLists.

Lemma writeSuccessBlockerRepresentationLists tail :
  tail ->
  writeSuccessConcreteRepresentationListsPreR9 writeSuccessBlockerDecoded
    writeSuccessBlockerRepresentedMemory writeSuccessBlockerOwner tail.
Proof.
  intro Htail. unfold writeSuccessConcreteRepresentationListsPreR9.
  split; first exact writeSuccessBlockerTransactions.
  split; first exact writeSuccessBlockerRawTransactions.
  split; first exact writeSuccessBlockerWithdrawals.
  split; first exact writeSuccessBlockerBlobGasUsed.
  split; first exact writeSuccessBlockerExcessBlobGas.
  split; first exact writeSuccessBlockerSlotNumber.
  split; first exact writeSuccessBlockerBlockAccessList.
  exact Htail.
Qed.

Print Assumptions writeSuccessBlockerRepresentationLists.
